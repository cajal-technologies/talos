import Interpreter.Wasm.Wp.Tactic

/-! ## Example: memory replace

    The function `replace(new : i32) → i32` reads the `i32` stored at
    memory offset 0, writes `new` there, and returns the old value.  This
    is the first example that exercises `load32` / `store32` instructions
    end-to-end.

    The module starts with a one-page memory whose first four bytes are
    `[42, 0, 0, 0]`, so `mem[0]` holds the little-endian value `42`.

    Calling `replace(99)` on the initial store should therefore return
    `42` and leave `99` in `mem[0]`. -/

namespace Wasm

def replaceBody : Program := [
  .const 0,    -- push address 0
  .load32 0,   -- read mem[0] → old value
  .localSet 1, -- save old value to local 1
  .const 0,    -- push address 0
  .localGet 0, -- push new value (param)
  .store32 0,  -- mem[0] = new value
  .localGet 1  -- push old value (return)
]

def replaceModule : Module :=
  { funcs := [{ params := [.i32], locals := [.i32], body := replaceBody, results := [.i32] }]
    memory := some { pagesMin := 1, data := [{ offset := some 0, bytes := [42, 0, 0, 0] }] } }

theorem replaceModule_init_mem :
    replaceModule.initialStore.mem.read32 0 = 42 := by
  native_decide

/-- For any store with at least one page of memory whose `mem[0] = old`,
    running `replace(new)` terminates with `old` on top of the value stack
    and `new` written back to `mem[0]`. The `1 ≤ st.mem.pages` hypothesis
    rules out the out-of-bounds trap on the load/store at offset 0. -/
theorem replace_spec (st : Store) (new old : UInt32) (hpages : 1 ≤ st.mem.pages)
    (hmem : st.mem.read32 0 = old) :
    wp replaceModule replaceBody
      (fun c => c = .Fallthrough { st with mem := st.mem.write32 0 new }
                    { params := [.i32 new], locals := [.i32 old], values := [.i32 old] })
      st ⟨[.i32 new], [.i32 0], []⟩ := by
  unfold replaceBody
  wp_run
  have : ¬ (4 > st.mem.pages * 65536) := by
    have : 4 ≤ st.mem.pages * 65536 := by
      have : 1 * 65536 ≤ st.mem.pages * 65536 := Nat.mul_le_mul_right _ hpages
      omega
    omega
  simp [hmem, this]

end Wasm
