import HexEncodeStdio.EncodePrefixOperational

namespace Project.HexEncodeStdio

open Wasm Project.HexStdio Project.HexStdio.Spec
open Wasm.SmallStep

/-- After `read_to_end` returns its vector, the main wrapper loads its pointer
and length and reaches the encoder call. -/
theorem main_after_read_to_encode_call
    (store : MachineStore Universal.State)
    (sp capacity pointer length : UInt32)
    (hcapacity : store.wasm.mem.read32 (sp + 8) = capacity)
    (hpointer : store.wasm.mem.read32 (sp + 12) = pointer)
    (hlength : store.wasm.mem.read32 (sp + 16) = length)
    (hptrBound : sp.toNat + 12 + 4 ≤ store.wasm.mem.pages * 65536)
    (hlenBound : sp.toNat + 16 + 4 ≤ store.wasm.mem.pages * 65536) :
    Reaches
      ({ expr := .running
          ⟨⟨[], [.i32 sp, .i32 0, .i32 0, .i32 0], []⟩,
            func10.drop 9, 0, [], [], []⟩
         store := store } : Config Universal.State)
      ({ expr := .running
          ⟨⟨[], [.i32 sp, .i32 pointer, .i32 0, .i32 0],
              [.i32 length, .i32 pointer, .i32 (sp + 20)]⟩,
            [.call 9] ++ func10.drop 18, 0, [], [], []⟩
         store := store } : Config Universal.State) := by
  simp only [func10, List.drop]
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend Step.add
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.load32 rfl (by simpa using hptrBound))
  rw [hpointer]
  apply Reaches.prepend (Step.localTee rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.load32 rfl (by simpa using hlenBound))
  rw [hlength]
  simp [UInt32.add_comm]
  exact ⟨[], .refl _⟩

end Project.HexEncodeStdio
