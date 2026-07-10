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

end Project.Encode.Spec
