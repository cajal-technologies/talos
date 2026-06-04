import Project.ReverseInplace.Program

/-!
# Specification for `reverse_inplace`

The proof is deferred; the function body lives in `Program.lean`.
-/

namespace Project.ReverseInplace.Spec

open Wasm

/-- The exported `reverse_inplace` reverses, in place, `len` contiguous
`u32` words starting at `ptr` in linear memory.

Informal spec:
For any base pointer `ptr` and length `len`, the wasm export
`reverse_inplace` terminates with an empty result. Afterwards, for
every `0 ≤ i < len`, the `u32` at `ptr + 4*i` equals the original `u32`
at `ptr + 4*(len-1-i)`. All other memory is unchanged. Carries the
side condition that every offset `0..len` is in-bounds for the initial
memory. -/
@[spec_of "rust-exported" "reverse_inplace::reverse_inplace"]
def ReverseInplaceSpec : Prop :=
  ∀ (env : HostEnv Unit) (initial : Store Unit) (ptr len : UInt32)
    (_hmem : ∀ k < len.toNat, (ptr.toNat + 4 * k) % 4294967296 + 4 ≤ initial.mem.pages * 65536),
    TerminatesWith env «module» 0 initial [.i32 len, .i32 ptr]
      (fun st' rs => rs = [] ∧
        (∀ i < len.toNat,
          st'.mem.read32 (ptr + 4 * UInt32.ofNat i) =
            initial.mem.read32 (ptr + 4 * UInt32.ofNat (len.toNat - 1 - i))))

end Project.ReverseInplace.Spec
