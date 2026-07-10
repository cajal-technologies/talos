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

end Project.Decode.Spec
