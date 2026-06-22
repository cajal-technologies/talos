import CodeLib.RustStd.Frame
import Interpreter.Wasm.Wp.Tactic
import Interpreter.Wasm.Wp.Block
import CodeLib.Entry

/-! `u64::clamp` — `core::cmp::Ord::clamp`, the framed inner function the exported
`clamp` wrapper `call`s. Panics if `lo > hi` (a `block` guard, like `div`); under
`lo ≤ hi` it computes `if a < lo then lo else if a > hi then hi else a` via a
nested-block select, spilling the result. It saves/restores the global stack
pointer, so its post only asserts `mem.pages` is preserved (sufficient for the
wrapper, which reuses this via the call rule). -/

set_option linter.unusedSimpArgs false

namespace Wasm.RustStd.U64
open Wasm

/-- Verbatim opt-0 body of `core::cmp::Ord::clamp` for `u64`. The panic-handler
call index (`panicIdx`) is a parameter: it differs per crate, but the panic is
unreachable under `lo ≤ hi`, so the proof is generic over it — letting one
`clamp_wp` serve `rust_u64`'s inner (`call 76`) and any client crate's copy. -/
def clampBody (panicIdx : Nat) : Program :=
  [ .globalGet 0, .const (80 : UInt32), .sub, .localSet 4, .localGet 4, .globalSet 0,
    .block 0 0 [
      .localGet 1, .localGet 2, .leUI64, .const (1 : UInt32), .and, .br_if 0,
      .localGet 4, .localGet 1, .store64 (16 : UInt32),
      .localGet 4, .localGet 2, .store64 (24 : UInt32),
      .localGet 4, .localGet 4, .const (16 : UInt32), .add, .store32 (64 : UInt32),
      .localGet 4, .const (1 : UInt32), .store32 (68 : UInt32),
      .localGet 4, .localGet 4, .load64 (64 : UInt32), .store64 (48 : UInt32),
      .localGet 4, .localGet 4, .const (24 : UInt32), .add, .store32 (72 : UInt32),
      .localGet 4, .const (1 : UInt32), .store32 (76 : UInt32),
      .localGet 4, .localGet 4, .load64 (72 : UInt32), .store64 (56 : UInt32),
      .localGet 4, .const (32 : UInt32), .add, .localGet 4, .load64 (48 : UInt32), .store64 (0 : UInt32),
      .localGet 4, .const (32 : UInt32), .add, .const (8 : UInt32), .add,
        .localGet 4, .load64 (56 : UInt32), .store64 (0 : UInt32),
      .const (1048576 : UInt32), .localGet 4, .const (32 : UInt32), .add, .localGet 3, .call panicIdx, .unreachable ],
    .block 0 0 [
      .block 0 0 [
        .block 0 0 [
          .block 0 0 [
            .block 0 0 [
              .localGet 0, .localGet 1, .ltUI64, .const (1 : UInt32), .and, .br_if 0,
              .localGet 0, .localGet 2, .gtUI64, .const (1 : UInt32), .and, .br_if 2,
              .br 1 ],
            .localGet 4, .localGet 1, .store64 (8 : UInt32), .br 3 ],
          .localGet 4, .localGet 0, .store64 (8 : UInt32), .br 1 ],
        .localGet 4, .localGet 2, .store64 (8 : UInt32) ] ],
    .localGet 4, .load64 (8 : UInt32), .localSet 5,
    .localGet 4, .const (80 : UInt32), .add, .globalSet 0,
    .localGet 5, .ret ]

def clampFunc (panicIdx : Nat) : Function :=
  { params := [.i64, .i64, .i64, .i32], locals := [.i32, .i64], body := clampBody panicIdx, results := [.i64] }

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem clamp_wp {α} {m : Module} {env : HostEnv α} (st : Store α) (panicIdx : Nat)
    (sp : UInt32) (a lo hi : UInt64) (loc : UInt32) (vs : List Value)
    (hsp : st.globals.globals[0]? = some (.i32 sp))
    (hlo : 80 ≤ sp.toNat) (hhi : sp.toNat ≤ st.mem.pages * 65536) (hlohi : lo ≤ hi) :
    wp m (clampBody panicIdx)
      (Returns (.i64 (if a < lo then lo else if a > hi then hi else a) :: vs)
        (fun st' => st'.mem.pages = st.mem.pages))
      st ⟨[.i64 a, .i64 lo, .i64 hi, .i32 loc], [.i32 0, .i64 0], vs⟩ env := by
  unfold clampBody Returns
  have hle80 : (80 : UInt32) ≤ sp := UInt32.le_iff_toNat_le.mpr (by simpa using hlo)
  have hsub80 : (sp - 80).toNat = sp.toNat - 80 := UInt32.toNat_sub_of_le sp 80 hle80
  have hnt8 : ¬ ((sp - 80).toNat + 8 + 8 > st.mem.pages * 65536) := by rw [hsub80]; omega
  have h8 : (8 : UInt32).toNat = 8 := rfl
  have h11 : (1 : UInt32) &&& 1 = 1 := by decide
  have hgset : (st.globals.globals.set 0 (Value.i32 (sp - 80)))[0]? = some (Value.i32 (sp - 80)) := by
    cases hg : st.globals.globals with
    | nil => simp [hg] at hsp
    | cons x xs => simp [hg]
  simp only [wp_simp, Locals.get, Locals.set?, Function.toLocals,
    Function.numParams, Function.numLocals, List.take, List.drop, List.replicate, List.length,
    List.map, ValueType.zero, List.headD, List.length_cons, List.length_nil,
    List.getElem?_cons_zero, List.getElem?_cons_succ, List.set_cons_zero, List.set_cons_succ,
    Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, reduceIte, hsp, hlohi, hnt8, h8, Mem.write64_pages]
  apply wp_block_cons
  simp [hlohi, h11]
  apply wp_block_cons
  apply wp_block_cons
  apply wp_block_cons
  apply wp_block_cons
  apply wp_block_cons
  by_cases hlt : a < lo <;> by_cases hgt : hi < a <;>
    simp [hlt, hgt, hnt8, h8, Mem.read64_write64_same, Mem.write64_pages]
  all_goals exact ⟨by omega, by simp [hgset]⟩

end Wasm.RustStd.U64
