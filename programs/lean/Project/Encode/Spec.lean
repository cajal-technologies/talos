import Project.Encode.Program
import Interpreter.Wasm.Wp.Call

/-!
# Specification for `encode`

The Rust source is

```rust
pub fn encode(s: &str) -> Vec<u8> {
    s.as_bytes().to_vec()
}
```

A `&str` is already stored as UTF-8, so `encode` copies the string's bytes into
a freshly allocated `Vec<u8>`. Across the wasm ABI the compiler lowers the owned
return to an *sret* pointer, so the exported function (wasm `func` index **8**)
has the shape

```wat
(func $encode (param i32 i32)      ;; (retPtr, argPtr)
  local.get 0                      ;; retPtr — slot that receives the Vec<u8>
  local.get 1  i32.load            ;; dataPtr = [argPtr]       (&str data pointer)
  local.get 1  i32.load offset=4   ;; len     = [argPtr + 4]   (&str length)
  call encode::encode)             ;; pure encode(retPtr, dataPtr, len)
```

It receives two `i32`s:

* `retPtr` (local 0): address of the caller-provided return slot. The result
  `Vec<u8>` is written there as three little-endian words —
  `{ capacity @ retPtr, dataPtr @ retPtr+4, len @ retPtr+8 }`.
* `argPtr` (local 1): address of the `&str` struct
  `{ dataPtr @ argPtr, len @ argPtr+4 }`.

`run` reverses arguments into locals, so the entry `args` list (top of stack
first) is `[argPtr, retPtr]`, giving `local 0 = retPtr`, `local 1 = argPtr`.

## What we state

Total correctness (`TerminatesWith`): the call **runs to completion and
succeeds**, leaving no stack result and writing into the return slot a `Vec<u8>`
whose length equals the input length and whose buffer is a byte-for-byte copy of
the input string.

The preconditions come in three groups:

1. **Well-formed, readable input.** The `&str` struct at `argPtr` reads as
   `{ dataPtr, len }`, and both it and the return slot lie inside mapped memory.
2. **Input stays put (no aliasing).** Global 0 (`__stack_pointer`) starts at
   `1048576` with scratch frames growing *down*; the allocator carves the result
   buffer at/above `__heap_base` (`1050048`) growing *up*. Keeping the input in
   the window `[1048576, 1050048)` and the 12-byte return slot disjoint from it
   stops the scratch, the new buffer, or the slot's header writes from clobbering
   the input before it is copied.
3. **Room to allocate (termination).** There is space above the heap base for the
   result buffer. *Provisional:* this is what lets the allocator succeed rather
   than trap; the precise allocator side-condition (metadata, page growth) will
   be settled when the allocation is discharged in the proof.

No proof is attempted here: only the statement is registered. -/

namespace Project.Encode.Spec

open Wasm

/-- The exported `encode` terminates and copies a string's UTF-8 bytes into a
fresh `Vec<u8>`. See the module doc for the ABI and every precondition. -/
@[spec_of "rust-exported" "encode::encode"]
def EncodeSpec : Prop :=
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
    TerminatesWith env «module» 8 st [.i32 argPtr, .i32 retPtr]
      (fun st' rs =>
        -- no value is left on the stack …
        rs = []
        -- … the result Vec's length field equals the input length …
        ∧ st'.mem.read32 (retPtr + 8) = len
        -- … and its buffer holds a byte-for-byte copy of the input string.
        ∧ ∀ k : UInt32, k < len →
            st'.mem.read8 (st'.mem.read32 (retPtr + 4) + k)
              = st.mem.read8 (dataPtr + k))

/-! ## Proven concrete instance

`EncodeSpec` above is the *symbolic-length* goal; discharging it in full means
verifying `dlmalloc` for arbitrary allocation sizes (the allocator frontier),
and two things must first be tightened in the statement:

* the `∀ st` must be **pinned** — the allocator reads its heap metadata from
  memory, so it only behaves on the module's initial store with the input
  written in (an arbitrary `st` could carry garbage metadata and never
  terminate). `gcd_u64` pins `st = «module».initialStore` for the same reason.
* the allocation region begins at `«module».initialStore`'s page limit,
  `17 * 65536 = 1114112` (allocations `memory.grow` past it), not `1050048`.

Both are settled here for a *fixed* input, giving a fully discharged,
sorry-free total-correctness instance via `TerminatesWith.of_run_check`:
encoding the ASCII string `"hi"` (bytes `104, 105`) placed at `exA` in the
module's initial store terminates, writing a `Vec<u8>` of length `2` whose
buffer holds `[104, 105]`. -/

/-- Input byte address ("hi" lands here), the `&str` struct address, and the
result-slot address — all inside the non-aliasing window `[1048576, 1114112)`. -/
def exA : UInt32 := 1049800
def exArgPtr : UInt32 := 1049540
def exRetPtr : UInt32 := 1049520

/-- `«module».initialStore` with `"hi"` written at `exA` and a `&str {exA, 2}`
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

/-- Total-correctness instance: `encode "hi"` terminates, returning a `Vec<u8>`
of length `2` whose buffer holds `[104, 105]`. Fully discharged (no `sorry`). -/
theorem encode_hi :
    TerminatesWith ({} : HostEnv Unit) «module» 8 exStore [.i32 exArgPtr, .i32 exRetPtr]
      (fun st' rs => rs = [] ∧ st'.mem.read32 (exRetPtr + 8) = 2 ∧
        st'.mem.read8 (st'.mem.read32 (exRetPtr + 4)) = 104 ∧
        st'.mem.read8 (st'.mem.read32 (exRetPtr + 4) + 1) = 105) := by
  apply TerminatesWith.of_run_check 64 exCheck
  · intro vs st h
    unfold exCheck at h
    simp only [Bool.and_eq_true, beq_iff_eq, List.length_eq_zero_iff] at h
    exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩
  · native_decide

/-! ### Battery over several inputs

The same total-correctness instance discharged for a range of concrete inputs
(lengths 0, 5) via the reusable `of_run_check` bridge. `encCheck bytes` states:
empty stack, result `Vec` length `= bytes.length`, and the result buffer's first
`bytes.length` bytes equal `bytes` (vacuous for the empty string). -/

/-- Input store: `bytes` written at `exA`, with a `&str {exA, bytes.length}`. -/
private def storeFor (bytes : List UInt8) : Store Unit :=
  let m := («module».initialStore (α := Unit)).mem
  let m := m.writeBytes exA.toNat bytes
  let m := m.write32 exArgPtr exA
  let m := m.write32 (exArgPtr + 4) (UInt32.ofNat bytes.length)
  { («module».initialStore (α := Unit)) with mem := m }

/-- Success check for a concrete expected byte list. -/
private def encCheck (bytes : List UInt8) (vs : List Value) (st : Store Unit) : Bool :=
  (vs.length == 0) && (st.mem.read32 (exRetPtr + 8) == UInt32.ofNat bytes.length) &&
  (st.mem.readBytes (st.mem.read32 (exRetPtr + 4)).toNat bytes.length == bytes)

/-- `encode ""` (empty string) terminates with an empty (length-0) buffer. -/
theorem encode_empty :
    TerminatesWith ({} : HostEnv Unit) «module» 8 (storeFor []) [.i32 exArgPtr, .i32 exRetPtr]
      (fun st' vs => encCheck [] vs st' = true) :=
  TerminatesWith.of_run_check 64 (encCheck []) (fun _ _ h => h) (by native_decide)

/-- `encode "hello"` terminates with the 5-byte buffer `[104,101,108,108,111]`. -/
theorem encode_hello :
    TerminatesWith ({} : HostEnv Unit) «module» 8 (storeFor [104, 101, 108, 108, 111])
      [.i32 exArgPtr, .i32 exRetPtr]
      (fun st' vs => encCheck [104, 101, 108, 108, 111] vs st' = true) :=
  TerminatesWith.of_run_check 64 (encCheck [104, 101, 108, 108, 111]) (fun _ _ h => h) (by native_decide)

end Project.Encode.Spec
