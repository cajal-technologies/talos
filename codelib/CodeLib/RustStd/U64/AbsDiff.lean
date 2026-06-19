import CodeLib.RustStd.Frame
import Interpreter.Wasm.Wp.Tactic
import Interpreter.Wasm.Wp.Block
import CodeLib.Entry

/-!
# `u64::abs_diff` — reusable body theorem

The inner `core::num::<impl u64>::abs_diff`, compiled at `opt-level = 0`: a real,
separately-called function, so other crates reuse this theorem through the `call`
rule. Stated in `wp` form about the body.
-/

namespace Wasm.RustStd.U64

open Wasm

/-- Verbatim opt-0 body of `absDiff`. -/
def absDiffBody : Program :=
  [
  .globalGet 0,
  .const (16 : UInt32),
  .sub,
  .localSet 2,
  .block 0 0 [
    .block 0 0 [
      .localGet 0,
      .localGet 1,
      .ltUI64,
      .const (1 : UInt32),
      .and,
      .br_if 0,
      .localGet 2,
      .localGet 0,
      .localGet 1,
      .subI64,
      .store64 (8 : UInt32),
      .br 1
    ],
    .localGet 2,
    .localGet 1,
    .localGet 0,
    .subI64,
    .store64 (8 : UInt32)
  ],
  .localGet 2,
  .load64 (8 : UInt32),
  .ret
]

def absDiffFunc : Function :=
  { params := [.i64, .i64], locals := [.i32], body := absDiffBody, results := [.i64] }

set_option maxRecDepth 4096 in
/-- `u64::abs_diff a b = if a < b then b - a else a - b`. -/
theorem absDiff_wp {α} {m : Module} {env : HostEnv α} (st : Store α)
    (sp : UInt32) (a : UInt64) (b : UInt64) (vs : List Value)
    (hsp : st.globals.globals[0]? = some (.i32 sp))
    (hlo : 16 ≤ sp.toNat) (hhi : sp.toNat ≤ st.mem.pages * 65536) :
    wp m absDiffBody
      (Returns (.i64 (if a < b then b - a else a - b) :: vs)
        -- TODO(frame-locality): this only asserts `globals` and `mem.pages` are
        -- preserved, not the caller's memory *contents* outside the spilled frame
        -- `[sp-16, sp)`. Sufficient for callers that don't read the scratch region
        -- between calls (e.g. `total_variation`), but a caller needing "this call
        -- didn't clobber address X" can't get it here. Strengthen to also assert
        -- frame-locality (memory unchanged outside `[sp-16, sp)`) so the body
        -- theorem composes for arbitrary callers.
        (fun st' => st'.globals = st.globals ∧ st'.mem.pages = st.mem.pages))
      st ⟨[.i64 a, .i64 b], [.i32 0], vs⟩ env := by
  unfold absDiffBody Returns
  wp_run
  simp only [hsp]
  apply wp_block_cons
  apply wp_block_cons
  wp_run
  have hle : (16 : UInt32) ≤ sp := UInt32.le_iff_toNat_le.mpr (by simpa using hlo)
  have hsub : (sp - 16).toNat = sp.toNat - 16 := UInt32.toNat_sub_of_le sp 16 hle
  have hnt : ¬ ((sp - 16).toNat + 8 + 8 > st.mem.pages * 65536) := by rw [hsub]; omega
  have h8 : ((8 : UInt32)).toNat = 8 := rfl
  by_cases hab : a < b <;>
    simp [hab, h8, hnt, Mem.read64_write64_same, Mem.write64_pages]

end Wasm.RustStd.U64
