import Project.Decode.Program
import Interpreter.Wasm.Wp.Call

/-!
# Specification for `decode`

The Rust source is

```rust
pub fn decode(bytes: &[u8]) -> String {
    String::from_utf8(bytes.to_vec()).unwrap()
}
```

`decode` copies the input bytes into a fresh buffer, validates that they are
UTF-8, and returns the owning `String`. Across the wasm ABI the owned return is
lowered to an *sret* pointer, so the exported function (wasm `func` index **24**)
has the same shape as `encode`:

```wat
(func $decode (param i32 i32)      ;; (retPtr, argPtr)
  local.get 0                      ;; retPtr — slot that receives the String
  local.get 1  i32.load            ;; dataPtr = [argPtr]       (&[u8] data pointer)
  local.get 1  i32.load offset=4   ;; len     = [argPtr + 4]   (&[u8] length)
  call decode::decode)             ;; pure decode(retPtr, dataPtr, len)
```

It receives two `i32`s:

* `retPtr` (local 0): address of the caller-provided return slot. A `String` is
  a wrapper over `Vec<u8>`, laid out as three little-endian words —
  `{ capacity @ retPtr, dataPtr @ retPtr+4, len @ retPtr+8 }`.
* `argPtr` (local 1): address of the `&[u8]` slice struct
  `{ dataPtr @ argPtr, len @ argPtr+4 }`.

`run` reverses arguments into locals, so the entry `args` list (top of stack
first) is `[argPtr, retPtr]`, giving `local 0 = retPtr`, `local 1 = argPtr`.

## What we state

Total correctness (`TerminatesWith`): the call **runs to completion and
succeeds**, leaving no stack result and writing into the return slot a `String`
whose length equals the input length and whose buffer is a byte-for-byte copy of
the input bytes.

The preconditions come in four groups:

1. **Well-formed, readable input.** The `&[u8]` struct at `argPtr` reads as
   `{ dataPtr, len }`, and both it and the return slot lie inside mapped memory.
2. **Input stays put (no aliasing).** Same window as `encode`: the input sits in
   `[1048576, 1050048)` (above the shadow stack, below `__heap_base`) and the
   12-byte return slot is disjoint from it, so nothing the callee writes clobbers
   the input before it is copied.
3. **Room to allocate (termination).** Space above the heap base for the result
   buffer. *Provisional*, exactly as in `encode`.
4. **Valid input (termination).** `from_utf8(..).unwrap()` traps on non-UTF-8, so
   `TerminatesWith` is *false* without an input-validity hypothesis. We require
   every input byte to be ASCII (`< 128`); ASCII ⊆ UTF-8, so validation provably
   succeeds. This restricts the statement to ASCII input and can be generalised
   to full UTF-8 once a validity predicate is available.

No proof is attempted here: only the statement is registered. -/

namespace Project.Decode.Spec

open Wasm

/-- The exported `decode` terminates and recovers a `String` from an ASCII byte
slice, copying the bytes into a fresh buffer. See the module doc for the ABI and
every precondition. -/
@[spec_of "rust-exported" "decode::decode"]
def DecodeSpec : Prop :=
  ∀ (env : HostEnv Unit) (st : Store Unit) (retPtr argPtr dataPtr len : UInt32),
    -- (1) well-formed, readable input struct and writable return slot
    st.mem.read32 argPtr = dataPtr →
    st.mem.read32 (argPtr + 4) = len →
    argPtr.toNat + 8 ≤ st.mem.pages * 65536 →
    retPtr.toNat + 12 ≤ st.mem.pages * 65536 →
    -- (2) input stays put: in the static window, return slot disjoint from it
    1048576 ≤ dataPtr.toNat →
    dataPtr.toNat + len.toNat ≤ 1050048 →
    (retPtr.toNat + 12 ≤ dataPtr.toNat ∨ dataPtr.toNat + len.toNat ≤ retPtr.toNat) →
    -- (3) room to allocate the result buffer (provisional termination side-condition)
    1050048 + len.toNat ≤ st.mem.pages * 65536 →
    -- (4) every input byte is ASCII (⊆ UTF-8), so `from_utf8` does not trap
    (∀ k : UInt32, k < len → st.mem.read8 (dataPtr + k) < 128) →
    TerminatesWith env «module» 24 st [.i32 argPtr, .i32 retPtr]
      (fun st' rs =>
        -- no value is left on the stack …
        rs = []
        -- … the result String's length field equals the input length …
        ∧ st'.mem.read32 (retPtr + 8) = len
        -- … and its buffer holds a byte-for-byte copy of the input bytes.
        ∧ ∀ k : UInt32, k < len →
            st'.mem.read8 (st'.mem.read32 (retPtr + 4) + k)
              = st.mem.read8 (dataPtr + k))

/-! ## Proven concrete instance

`DecodeSpec` above is the *symbolic-length* goal; discharging it in full means
verifying `dlmalloc` for arbitrary allocation sizes (the allocator frontier),
and — as for `encode` — the `∀ st` must first be **pinned** to the module's
initial store with the input written in (the allocator only behaves on pristine
heap metadata), with the allocation region starting at the page limit
`17 * 65536 = 1114112`.

Settled here for a *fixed* input, giving a fully discharged, sorry-free
total-correctness instance via `TerminatesWith.of_run_check`: decoding the
bytes `[104, 105]` (valid ASCII/UTF-8) placed at `exA` terminates, writing a
`String` of length `2` whose buffer holds `[104, 105]` — i.e. the round-trip
`decode` of what `encode "hi"` produced. -/

/-- Input byte address (`[104,105]` land here), the `&[u8]` struct address, and
the result-slot address — all inside the non-aliasing window `[1048576, 1114112)`. -/
def exA : UInt32 := 1049800
def exArgPtr : UInt32 := 1049540
def exRetPtr : UInt32 := 1049520

/-- `«module».initialStore` with bytes `[104,105]` at `exA` and a `&[u8] {exA, 2}`
struct at `exArgPtr`. -/
def exStore : Store Unit :=
  let m := («module».initialStore (α := Unit)).mem
  let m := m.write8 exA 104
  let m := m.write8 (exA + 1) 105
  let m := m.write32 exArgPtr exA
  let m := m.write32 (exArgPtr + 4) 2
  { («module».initialStore (α := Unit)) with mem := m }

/-- `Bool` success check fed to `native_decide`: empty stack, `len = 2`, buffer
bytes `104, 105`. -/
private def exCheck (vs : List Value) (st : Store Unit) : Bool :=
  (vs.length == 0) && (st.mem.read32 (exRetPtr + 8) == 2) &&
  (st.mem.read8 (st.mem.read32 (exRetPtr + 4)) == 104) &&
  (st.mem.read8 (st.mem.read32 (exRetPtr + 4) + 1) == 105)

/-- Total-correctness instance: `decode [104,105]` terminates, returning a
`String` of length `2` whose buffer holds `[104, 105]`. Fully discharged (no
`sorry`). -/
theorem decode_hi :
    TerminatesWith ({} : HostEnv Unit) «module» 24 exStore [.i32 exArgPtr, .i32 exRetPtr]
      (fun st' rs => rs = [] ∧ st'.mem.read32 (exRetPtr + 8) = 2 ∧
        st'.mem.read8 (st'.mem.read32 (exRetPtr + 4)) = 104 ∧
        st'.mem.read8 (st'.mem.read32 (exRetPtr + 4) + 1) = 105) := by
  apply TerminatesWith.of_run_check 64 exCheck
  · intro vs st h
    unfold exCheck at h
    simp only [Bool.and_eq_true, beq_iff_eq, List.length_eq_zero_iff] at h
    exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩
  · native_decide

end Project.Decode.Spec
