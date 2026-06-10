import Project.DynDispatch.Program

set_option maxRecDepth 1048576

/-! # Specification for the `dyn_dispatch` crate

The exported `check(sel, x)` runs two implementations of the same
dispatcher and traps via `unreachable` iff they disagree:

* `dispatch_dyn` (`func0`): looks up `OPS[sel % 2]` (a static array of
  `&dyn Op`) and calls `.apply(x)` through the vtable. Compiles to
  `call_indirect (type 0)` — exactly the wasm instruction this crate
  exists to exercise.
* `dispatch_naive` (`func2`): an inline `match` that names the
  concrete `Add(1)` / `Mul(2)` impls directly.

At `opt-level=0` the live call graph is

```
func8 (exported `check` wrapper)
  └─ func5 (compare both dispatchers, `unreachable` on disagreement)
       ├─ func0 (dyn: OPS/vtable load + call_indirect → func6 / func7)
       │    └─ func1 (abs, feeds the `sel % 2` index)
       └─ func2 (naive: direct branch on `sel % 2`)
            └─ func1
```

`func6` is `<Add as Op>::apply` (table slot 1) and `func7` is
`<Mul as Op>::apply` (table slot 2). Every function carries the
unoptimized shadow-stack discipline: the prologue claims a frame below
`global 0` and spills arguments to linear memory; with the canonical
instantiation (`global 0 = 1048576`, 17 pages) the frames sit at
`1048560` (func8), `1048544` (func5), `1048528` (func0), `1048512`
(func2 and the vtable callees), `1048496` (func1 under func2) — all
comfortably in bounds and strictly below the static data.

The spec is pinned to the module's `initialStore`: `dispatch_dyn` reads
the `OPS`/vtable pointers out of *static* linear memory (`OPS` at
`1048656`, the boxed values at `1048616`/`1048636`, the vtable `apply`
slots at `1048632`/`1048652`) and resolves the call through the
preinitialised function table, so the equivalence is meaningless
(indeed false) over an arbitrary store. The end-to-end chain —
memory-backed vtable read + table lookup + chained call — is discharged
with `wp_callIndirect_at` / `wp_call_at`, the store-specific call WP
rules; the inner lemmas are `TerminatesWith`s at parametric stores
constrained by pages/globals/static-read hypotheses, with explicit
frame conditions ("reads above the frame are preserved") so the static
data survives each call. -/

namespace Project.DynDispatch.Spec

open Wasm

/-- The module's canonical initial store: linear memory holds the folded
`OPS`/vtable data segment and `table[0]` is filled by the element
segment (slot 1 ↦ `func6` = `Add::apply`, slot 2 ↦ `func7` =
`Mul::apply`). -/
private abbrev S : Store Unit := «module».initialStore

/-- The module's single funcref table after element-segment
initialisation. -/
private def dynTable : TableInst :=
  [none, some 6, some 7, some 24, some 16, some 48, some 47, some 52,
   some 46, some 45, some 43, some 44, some 17, some 42, some 50,
   some 49, some 51, some 41, some 40, some 65]

/-- The value both dispatchers compute: `x + 1` for even `sel` (the
`Add(1)` op) and `x * 2` for odd `sel` (the `Mul(2)` op). -/
private def dispatchResult (sel x : UInt32) : UInt32 :=
  if sel &&& 1 = 0 then x + 1 else x * 2

/-! ## Parity plumbing

The unoptimized code routes `sel` through `abs` (`func1`) before taking
`sel % 2` as `1 &&& abs sel`; negation preserves parity, so both
dispatchers branch on `1 &&& sel`. -/

private theorem one_and_cases (sel : UInt32) : 1 &&& sel = 0 ∨ 1 &&& sel = 1 := by
  bv_decide

private theorem one_and_neg (sel : UInt32) : 1 &&& -sel = 1 &&& sel := by
  bv_decide

private theorem dispatchResult_even (sel x : UInt32) (h : 1 &&& sel = 0) :
    dispatchResult sel x = x + 1 := by
  rw [UInt32.and_comm] at h
  simp [dispatchResult, h]

private theorem dispatchResult_odd (sel x : UInt32) (h : 1 &&& sel = 1) :
    dispatchResult sel x = x * 2 := by
  rw [UInt32.and_comm] at h
  simp [dispatchResult, h]

private theorem shl_one (x : UInt32) : x <<< 1 = x * 2 := by
  bv_decide

/-! ## Memory framing lemmas

Every spill in the live path goes to a shadow-stack frame strictly
below the caller's `global 0`, while the static `OPS`/vtable data sits
at `1048616` and above. Reads therefore split into
read-after-same-address-write (`read32_write32_same`) and reads
strictly above all outstanding writes (`read32_write32_lo`). -/

@[simp] private theorem write32_pages (m : Mem) (a v : UInt32) :
    (m.write32 a v).pages = m.pages := rfl

private theorem write32_bytes_of_disjoint (m : Mem) (a v : UInt32) (i : Nat)
    (h : i < a.toNat ∨ a.toNat + 4 ≤ i) :
    (m.write32 a v).bytes i = m.bytes i := by
  simp only [Mem.write32]
  have h0 : i ≠ a.toNat := by omega
  have h1 : i ≠ a.toNat + 1 := by omega
  have h2 : i ≠ a.toNat + 2 := by omega
  have h3 : i ≠ a.toNat + 3 := by omega
  simp [h0, h1, h2, h3]

/-- A 32-bit read sees the value of a same-address 32-bit write. -/
@[simp] private theorem read32_write32_same (m : Mem) (a v : UInt32) :
    (m.write32 a v).read32 a = v := by
  simp only [Mem.read32, Mem.write32]
  have e1 : a.toNat + 1 ≠ a.toNat := by omega
  have e2 : a.toNat + 2 ≠ a.toNat := by omega
  have e3 : a.toNat + 3 ≠ a.toNat := by omega
  have e21 : a.toNat + 2 ≠ a.toNat + 1 := by omega
  have e31 : a.toNat + 3 ≠ a.toNat + 1 := by omega
  have e32 : a.toNat + 3 ≠ a.toNat + 2 := by omega
  simp only [e1, e2, e3, e21, e31, e32, if_true, if_false]
  bv_decide

/-- A 32-bit read is unaffected by a 32-bit write to a disjoint range. -/
private theorem read32_write32_disjoint (m : Mem) (a b v : UInt32)
    (h : b.toNat + 4 ≤ a.toNat ∨ a.toNat + 4 ≤ b.toNat) :
    (m.write32 a v).read32 b = m.read32 b := by
  simp only [Mem.read32]
  rw [write32_bytes_of_disjoint m a v b.toNat (by omega),
      write32_bytes_of_disjoint m a v (b.toNat + 1) (by omega),
      write32_bytes_of_disjoint m a v (b.toNat + 2) (by omega),
      write32_bytes_of_disjoint m a v (b.toNat + 3) (by omega)]

/-- A 32-bit read strictly above a 32-bit write is unaffected. -/
private theorem read32_write32_lo (m : Mem) (w v a : UInt32)
    (h : w.toNat + 4 ≤ a.toNat) :
    (m.write32 w v).read32 a = m.read32 a :=
  read32_write32_disjoint m w a v (Or.inr h)

/-! ## Store-specific call rules

`wp_call_cons` / `wp_callIndirect_cons` consume a store-polymorphic
`FuncSpec`, which doesn't exist for any function here (they all spill
to the shadow stack and would trap on a 0-page store). These wrappers
tie a `TerminatesWith` *at the goal's current store* into the
interpreter-side rules `wp_call_at` / `wp_callIndirect_at`; making
`st` explicit lets unification pin the callee lemma's store to the
caller's. -/

private theorem wp_call_T {env : HostEnv Unit} {m : Module} {id : Nat}
    {Q : Assertion Unit} {rest : Program} {st : Store Unit} {s : Locals}
    {P : Store Unit → List Value → Prop}
    (h : TerminatesWith env m id st s.values P)
    (hPost : ∀ st' vs, P st' vs → wp m rest Q st' { s with values := vs } env) :
    wp m (.call id :: rest) Q st s env :=
  wp_call_at h hPost

private theorem wp_callIndirect_T {env : HostEnv Unit}
    {m : Module} {st : Store Unit} {s : Locals} {Q : Assertion Unit}
    {rest : Program} {ti tj : Nat}
    {P : Store Unit → List Value → Prop}
    {i : UInt32} {vs0 : List Value} {tbl : TableInst} {fid : Nat}
    {fn : FuncType} {ty : FuncType}
    (hStack : s.values = .i32 i :: vs0)
    (hTbl  : st.tables[tj]? = some tbl)
    (hSlot : tbl[i.toNat]? = some (some fid))
    (hFn   : m.funcSig? fid = some fn)
    (hTy   : m.types[ti]? = some ty)
    (hSig  : fn.params = ty.params ∧ fn.results = ty.results)
    (h     : TerminatesWith env m fid st vs0 P)
    (hPost : ∀ st' vs, P st' vs → wp m rest Q st' { s with values := vs } env) :
    wp m (.callIndirect ti tj :: rest) Q st s env :=
  wp_callIndirect_at hStack hTbl hSlot hFn hTy hSig h hPost

/-! ## `func1`: `abs`, the parity feeder

Called once under `func0` (with `global 0 = 1048528`) and once under
`func2` (with `global 0 = 1048512`); it spills into the 16 bytes below
`global 0 − 16` without moving `global 0`. Only the parity of the
result is needed downstream, so the post exposes the result as some `r`
with `1 &&& r = 1 &&& sel`, plus pages/globals/tables preservation and
the frame condition. The two instantiations differ only in concrete
addresses, hence the two copies. -/

private theorem func1_at_528 (env : HostEnv Unit) (st0 : Store Unit) (sel : UInt32)
    (hpg : st0.mem.pages = 17)
    (hgl : st0.globals.globals = [.i32 1048528, .i32 1049841, .i32 1049856]) :
    TerminatesWith env «module» 1 st0 [.i32 sel]
      (fun st' vs => ∃ r, vs = [.i32 r] ∧ 1 &&& r = 1 &&& sel ∧
        st'.mem.pages = 17 ∧
        st'.globals.globals = [.i32 1048528, .i32 1049841, .i32 1049856] ∧
        st'.tables = st0.tables ∧
        ∀ a : UInt32, 1048528 ≤ a.toNat → st'.mem.read32 a = st0.mem.read32 a) := by
  apply TerminatesWith.of_wp_entry_for (f := ⟨[.i32], [.i32], func1, [.i32]⟩) rfl
  unfold func1
  wp_run
  simp [hgl, hpg]
  apply wp_block_cons
  apply wp_block_cons
  wp_run
  by_cases hneg : sel.toInt32 < 0
  · -- negative `sel`: result is `-sel`
    simp [hneg, one_and_neg, hpg, hgl]
    intro a ha
    rw [read32_write32_lo _ _ _ a (by have : (1048520 : UInt32).toNat = 1048520 := rfl; omega),
        read32_write32_lo _ _ _ a (by have : (1048524 : UInt32).toNat = 1048524 := rfl; omega)]
  · -- non-negative `sel`: result is `sel` itself
    simp [hneg, hpg, hgl]
    intro a ha
    rw [read32_write32_lo _ _ _ a (by have : (1048520 : UInt32).toNat = 1048520 := rfl; omega),
        read32_write32_lo _ _ _ a (by have : (1048524 : UInt32).toNat = 1048524 := rfl; omega)]

private theorem func1_at_512 (env : HostEnv Unit) (st0 : Store Unit) (sel : UInt32)
    (hpg : st0.mem.pages = 17)
    (hgl : st0.globals.globals = [.i32 1048512, .i32 1049841, .i32 1049856]) :
    TerminatesWith env «module» 1 st0 [.i32 sel]
      (fun st' vs => ∃ r, vs = [.i32 r] ∧ 1 &&& r = 1 &&& sel ∧
        st'.mem.pages = 17 ∧
        st'.globals.globals = [.i32 1048512, .i32 1049841, .i32 1049856] ∧
        st'.tables = st0.tables ∧
        ∀ a : UInt32, 1048512 ≤ a.toNat → st'.mem.read32 a = st0.mem.read32 a) := by
  apply TerminatesWith.of_wp_entry_for (f := ⟨[.i32], [.i32], func1, [.i32]⟩) rfl
  unfold func1
  wp_run
  simp [hgl, hpg]
  apply wp_block_cons
  apply wp_block_cons
  wp_run
  by_cases hneg : sel.toInt32 < 0
  · simp [hneg, one_and_neg, hpg, hgl]
    intro a ha
    rw [read32_write32_lo _ _ _ a (by have : (1048504 : UInt32).toNat = 1048504 := rfl; omega),
        read32_write32_lo _ _ _ a (by have : (1048508 : UInt32).toNat = 1048508 := rfl; omega)]
  · simp [hneg, hpg, hgl]
    intro a ha
    rw [read32_write32_lo _ _ _ a (by have : (1048504 : UInt32).toNat = 1048504 := rfl; omega),
        read32_write32_lo _ _ _ a (by have : (1048508 : UInt32).toNat = 1048508 := rfl; omega)]

/-! ## The two `Op::apply` implementations (vtable targets) -/

/-- `func6` is `<Add as Op>::apply`: called through table slot 1 with
`self = 1048616` (boxed value `1`), it returns `x + 1`. It spills to
the 16 bytes below `global 0 − 16 = 1048512` without moving
`global 0`. -/
private theorem func6_at (env : HostEnv Unit) (st0 : Store Unit) (x : UInt32)
    (hpg : st0.mem.pages = 17)
    (hgl : st0.globals.globals = [.i32 1048528, .i32 1049841, .i32 1049856])
    (h616 : st0.mem.read32 1048616 = 1) :
    TerminatesWith env «module» 6 st0 [.i32 x, .i32 1048616]
      (fun st' vs => vs = [.i32 (x + 1)] ∧
        st'.mem.pages = 17 ∧
        st'.globals.globals = [.i32 1048528, .i32 1049841, .i32 1049856] ∧
        st'.tables = st0.tables ∧
        ∀ a : UInt32, 1048528 ≤ a.toNat → st'.mem.read32 a = st0.mem.read32 a) := by
  apply TerminatesWith.of_wp_entry_for
    (f := ⟨[.i32, .i32], [.i32, .i32], func6, [.i32]⟩) rfl
  unfold func6
  wp_run
  simp [hgl, hpg]
  rw [show ((st0.mem.write32 1048512 1048616).write32 1048516 x).read32 1048616 = 1 from by
    rw [read32_write32_lo _ _ _ _ (by decide), read32_write32_lo _ _ _ _ (by decide)]
    exact h616]
  refine ⟨UInt32.add_comm 1 x, ?_⟩
  intro a ha
  rw [read32_write32_lo _ _ _ a (by have : (1048524 : UInt32).toNat = 1048524 := rfl; omega),
      read32_write32_lo _ _ _ a (by have : (1048520 : UInt32).toNat = 1048520 := rfl; omega),
      read32_write32_lo _ _ _ a (by have : (1048516 : UInt32).toNat = 1048516 := rfl; omega),
      read32_write32_lo _ _ _ a (by have : (1048512 : UInt32).toNat = 1048512 := rfl; omega)]

/-- `func7` is `<Mul as Op>::apply`: called through table slot 2 with
`self = 1048636` (boxed value `2`), it returns `x * 2`. Same frame
discipline as [`func6_at`]. -/
private theorem func7_at (env : HostEnv Unit) (st0 : Store Unit) (x : UInt32)
    (hpg : st0.mem.pages = 17)
    (hgl : st0.globals.globals = [.i32 1048528, .i32 1049841, .i32 1049856])
    (h636 : st0.mem.read32 1048636 = 2) :
    TerminatesWith env «module» 7 st0 [.i32 x, .i32 1048636]
      (fun st' vs => vs = [.i32 (x * 2)] ∧
        st'.mem.pages = 17 ∧
        st'.globals.globals = [.i32 1048528, .i32 1049841, .i32 1049856] ∧
        st'.tables = st0.tables ∧
        ∀ a : UInt32, 1048528 ≤ a.toNat → st'.mem.read32 a = st0.mem.read32 a) := by
  apply TerminatesWith.of_wp_entry_for
    (f := ⟨[.i32, .i32], [.i32, .i32], func7, [.i32]⟩) rfl
  unfold func7
  wp_run
  simp [hgl, hpg]
  rw [show ((st0.mem.write32 1048512 1048636).write32 1048516 x).read32 1048636 = 2 from by
    rw [read32_write32_lo _ _ _ _ (by decide), read32_write32_lo _ _ _ _ (by decide)]
    exact h636]
  refine ⟨UInt32.mul_comm 2 x, ?_⟩
  intro a ha
  rw [read32_write32_lo _ _ _ a (by have : (1048524 : UInt32).toNat = 1048524 := rfl; omega),
      read32_write32_lo _ _ _ a (by have : (1048520 : UInt32).toNat = 1048520 := rfl; omega),
      read32_write32_lo _ _ _ a (by have : (1048516 : UInt32).toNat = 1048516 := rfl; omega),
      read32_write32_lo _ _ _ a (by have : (1048512 : UInt32).toNat = 1048512 := rfl; omega)]

/-! ## `dispatch_dyn` (`func0`): indirect dispatch through the vtable -/

/-- The indirect dispatcher resolves `apply` through the in-memory
vtable and returns `dispatchResult sel x`. Even `sel` reads
`OPS[0] = (1048616, 1048620)` and resolves `vtable+12` to table slot 1
→ `func6`; odd `sel` reads `OPS[1] = (1048636, 1048640)` and resolves
slot 2 → `func7`. The static-read hypotheses pin exactly the eight
words of static memory the body consumes. -/
private theorem func0_at (env : HostEnv Unit) (st0 : Store Unit) (sel x : UInt32)
    (hpg : st0.mem.pages = 17)
    (hgl : st0.globals.globals = [.i32 1048544, .i32 1049841, .i32 1049856])
    (htb : st0.tables = [dynTable])
    (h656 : st0.mem.read32 1048656 = 1048616)
    (h660 : st0.mem.read32 1048660 = 1048620)
    (h664 : st0.mem.read32 1048664 = 1048636)
    (h668 : st0.mem.read32 1048668 = 1048640)
    (h632 : st0.mem.read32 1048632 = 1)
    (h652 : st0.mem.read32 1048652 = 2)
    (h616 : st0.mem.read32 1048616 = 1)
    (h636 : st0.mem.read32 1048636 = 2) :
    TerminatesWith env «module» 0 st0 [.i32 x, .i32 sel]
      (fun st' vs => vs = [.i32 (dispatchResult sel x)] ∧
        st'.mem.pages = 17 ∧
        st'.globals.globals = [.i32 1048544, .i32 1049841, .i32 1049856] ∧
        st'.tables = [dynTable] ∧
        ∀ a : UInt32, 1048544 ≤ a.toNat → st'.mem.read32 a = st0.mem.read32 a) := by
  apply TerminatesWith.of_wp_entry_for
    (f := ⟨[.i32, .i32], [.i32, .i32, .i32, .i32], func0, [.i32]⟩) rfl
  unfold func0
  wp_run
  simp [hgl, hpg]
  -- prologue done: frame at 1048528, `sel` at 1048532, `x` at 1048536;
  -- `.call 1` computes `abs sel`
  refine wp_call_T (func1_at_528 env _ sel (by simp [hpg]) (by simp)) ?_
  rintro st2 vs2 ⟨r, rfl, hr, hpg2, hgl2, htb2, hfr2⟩
  have htb2' : st2.tables = st0.tables := htb2
  have hfr2' : ∀ a : UInt32, 1048528 ≤ a.toNat →
      st2.mem.read32 a = ((st0.mem.write32 1048532 sel).write32 1048536 x).read32 a := hfr2
  wp_run
  simp [hpg2]
  apply wp_block_cons
  wp_run
  -- the static reads at the call-site store reduce to `st0`'s
  have hRead : ∀ v b w : UInt32, 1048544 ≤ b.toNat → st0.mem.read32 b = w →
      (st2.mem.write32 1048540 v).read32 b = w := by
    intro v b w hb hw
    rw [read32_write32_lo _ _ _ b (by have : (1048540 : UInt32).toNat = 1048540 := rfl; omega),
        hfr2' b (by omega),
        read32_write32_lo _ _ _ b (by have : (1048536 : UInt32).toNat = 1048536 := rfl; omega),
        read32_write32_lo _ _ _ b (by have : (1048532 : UInt32).toNat = 1048532 := rfl; omega),
        hw]
  rcases one_and_cases sel with hpar | hpar
  · -- even `sel`: OPS[0], vtable slot at 1048632 → table[1] → func6
    have hv : 1 &&& r = 0 := hr.trans hpar
    rw [hv]
    simp [hpg2]
    rw [hRead 0 1048656 1048616 (by decide) h656,
        hRead 0 1048660 1048620 (by decide) h660,
        show (1048620 : UInt32) + 12 = 1048632 from by decide,
        hRead 0 1048632 1 (by decide) h632]
    refine ⟨by decide, ?_⟩
    refine wp_callIndirect_T (i := 1) (vs0 := [.i32 x, .i32 1048616])
      (tbl := dynTable) (fid := 6)
      (fn := ⟨[.i32, .i32], [.i32]⟩)
      (ty := ⟨[.i32, .i32], [.i32]⟩)
      rfl (by simp [htb2', htb]) (by decide) rfl rfl ⟨rfl, rfl⟩
      (func6_at env _ x (by simp [hpg2]) (by simp [hgl2])
        (hRead 0 1048616 1 (by decide) h616)) ?_
    rintro st4 vs4 ⟨rfl, hpg4, hgl4, htb4, hfr4⟩
    have htb4' : st4.tables = st2.tables := htb4
    have hfr4' : ∀ a : UInt32, 1048528 ≤ a.toNat →
        st4.mem.read32 a = (st2.mem.write32 1048540 0).read32 a := hfr4
    wp_run
    simp [hgl4, hpg4, dispatchResult_even sel x hpar, htb4', htb2', htb]
    intro a ha
    have h28 : (1048528 : Nat) ≤ a.toNat := by omega
    rw [hfr4' a h28,
        read32_write32_lo _ _ _ a (by have : (1048540 : UInt32).toNat = 1048540 := rfl; omega),
        hfr2' a h28,
        read32_write32_lo _ _ _ a (by have : (1048536 : UInt32).toNat = 1048536 := rfl; omega),
        read32_write32_lo _ _ _ a (by have : (1048532 : UInt32).toNat = 1048532 := rfl; omega)]
  · -- odd `sel`: OPS[1], vtable slot at 1048652 → table[2] → func7
    have hv : 1 &&& r = 1 := hr.trans hpar
    rw [hv]
    simp [hpg2]
    rw [show (1 : UInt32) <<< 3 + 1048656 = 1048664 from by decide]
    rw [hRead 1 1048664 1048636 (by decide) h664,
        show (1048664 : UInt32) + 4 = 1048668 from by decide,
        hRead 1 1048668 1048640 (by decide) h668,
        show (1048640 : UInt32) + 12 = 1048652 from by decide,
        hRead 1 1048652 2 (by decide) h652]
    refine ⟨by decide, ?_⟩
    refine wp_callIndirect_T (i := 2) (vs0 := [.i32 x, .i32 1048636])
      (tbl := dynTable) (fid := 7)
      (fn := ⟨[.i32, .i32], [.i32]⟩)
      (ty := ⟨[.i32, .i32], [.i32]⟩)
      rfl (by simp [htb2', htb]) (by decide) rfl rfl ⟨rfl, rfl⟩
      (func7_at env _ x (by simp [hpg2]) (by simp [hgl2])
        (hRead 1 1048636 2 (by decide) h636)) ?_
    rintro st4 vs4 ⟨rfl, hpg4, hgl4, htb4, hfr4⟩
    have htb4' : st4.tables = st2.tables := htb4
    have hfr4' : ∀ a : UInt32, 1048528 ≤ a.toNat →
        st4.mem.read32 a = (st2.mem.write32 1048540 1).read32 a := hfr4
    wp_run
    simp [hgl4, hpg4, dispatchResult_odd sel x hpar, htb4', htb2', htb]
    intro a ha
    have h28 : (1048528 : Nat) ≤ a.toNat := by omega
    rw [hfr4' a h28,
        read32_write32_lo _ _ _ a (by have : (1048540 : UInt32).toNat = 1048540 := rfl; omega),
        hfr2' a h28,
        read32_write32_lo _ _ _ a (by have : (1048536 : UInt32).toNat = 1048536 := rfl; omega),
        read32_write32_lo _ _ _ a (by have : (1048532 : UInt32).toNat = 1048532 := rfl; omega)]

/-! ## `dispatch_naive` (`func2`): direct dispatch by branching -/

/-- The naive dispatcher branches on `sel % 2` directly and computes
`dispatchResult sel x` in its own 32-byte frame at `1048512`. The
`tail` parameter threads the caller's remaining operand stack through
the call. -/
private theorem func2_at (env : HostEnv Unit) (st0 : Store Unit)
    (sel x : UInt32) (tail : List Value)
    (hpg : st0.mem.pages = 17)
    (hgl : st0.globals.globals = [.i32 1048544, .i32 1049841, .i32 1049856]) :
    TerminatesWith env «module» 2 st0 (.i32 x :: .i32 sel :: tail)
      (fun st' vs => vs = .i32 (dispatchResult sel x) :: tail ∧
        st'.mem.pages = 17 ∧
        st'.globals.globals = [.i32 1048544, .i32 1049841, .i32 1049856] ∧
        st'.tables = st0.tables ∧
        ∀ a : UInt32, 1048544 ≤ a.toNat → st'.mem.read32 a = st0.mem.read32 a) := by
  apply TerminatesWith.of_wp_entry_for
    (f := ⟨[.i32, .i32], [.i32, .i32, .i32], func2, [.i32]⟩) rfl
  unfold func2
  wp_run
  simp [hgl, hpg]
  -- prologue done: frame at 1048512, `sel` at 1048516, `x` at 1048520
  refine wp_call_T (func1_at_512 env _ sel (by simp [hpg]) (by simp)) ?_
  rintro st2 vs2 ⟨r, rfl, hr, hpg2, hgl2, htb2, hfr2⟩
  have htb2' : st2.tables = st0.tables := htb2
  have hfr2' : ∀ a : UInt32, 1048512 ≤ a.toNat →
      st2.mem.read32 a = ((st0.mem.write32 1048516 sel).write32 1048520 x).read32 a := hfr2
  wp_run
  simp [hpg2]
  apply wp_block_cons
  apply wp_block_cons
  wp_run
  rcases one_and_cases sel with hpar | hpar
  · -- even `sel`: `x + 1` via the fallthrough branch
    have hv : 1 &&& r = 0 := hr.trans hpar
    rw [hv]
    simp [hpg2, hgl2, htb2', dispatchResult_even sel x hpar, UInt32.add_comm 1 x]
    intro a ha
    have h12 : (1048512 : Nat) ≤ a.toNat := by omega
    rw [read32_write32_lo _ _ _ a (by have : (1048512 : UInt32).toNat = 1048512 := rfl; omega),
        read32_write32_lo _ _ _ a (by have : (1048532 : UInt32).toNat = 1048532 := rfl; omega),
        read32_write32_lo _ _ _ a (by have : (1048528 : UInt32).toNat = 1048528 := rfl; omega),
        read32_write32_lo _ _ _ a (by have : (1048524 : UInt32).toNat = 1048524 := rfl; omega),
        hfr2' a h12,
        read32_write32_lo _ _ _ a (by have : (1048520 : UInt32).toNat = 1048520 := rfl; omega),
        read32_write32_lo _ _ _ a (by have : (1048516 : UInt32).toNat = 1048516 := rfl; omega)]
  · -- odd `sel`: `x <<< 1 = x * 2` via the taken branch
    have hv : 1 &&& r = 1 := hr.trans hpar
    rw [hv]
    simp [hpg2, hgl2, htb2', dispatchResult_odd sel x hpar, shl_one]
    intro a ha
    have h12 : (1048512 : Nat) ≤ a.toNat := by omega
    rw [read32_write32_lo _ _ _ a (by have : (1048512 : UInt32).toNat = 1048512 := rfl; omega),
        read32_write32_lo _ _ _ a (by have : (1048540 : UInt32).toNat = 1048540 := rfl; omega),
        read32_write32_lo _ _ _ a (by have : (1048536 : UInt32).toNat = 1048536 := rfl; omega),
        read32_write32_lo _ _ _ a (by have : (1048524 : UInt32).toNat = 1048524 := rfl; omega),
        hfr2' a h12,
        read32_write32_lo _ _ _ a (by have : (1048520 : UInt32).toNat = 1048520 := rfl; omega),
        read32_write32_lo _ _ _ a (by have : (1048516 : UInt32).toNat = 1048516 := rfl; omega)]

/-! ## `func5`: the equivalence check, and the exported `check` -/

/-- `func5` runs both dispatchers, and because they agree it never
trips the `br_if`/`unreachable`; it returns with an empty value stack
and `global 0` restored. -/
private theorem func5_at (env : HostEnv Unit) (st0 : Store Unit) (sel x : UInt32)
    (hpg : st0.mem.pages = 17)
    (hgl : st0.globals.globals = [.i32 1048560, .i32 1049841, .i32 1049856])
    (htb : st0.tables = [dynTable])
    (h656 : st0.mem.read32 1048656 = 1048616)
    (h660 : st0.mem.read32 1048660 = 1048620)
    (h664 : st0.mem.read32 1048664 = 1048636)
    (h668 : st0.mem.read32 1048668 = 1048640)
    (h632 : st0.mem.read32 1048632 = 1)
    (h652 : st0.mem.read32 1048652 = 2)
    (h616 : st0.mem.read32 1048616 = 1)
    (h636 : st0.mem.read32 1048636 = 2) :
    TerminatesWith env «module» 5 st0 [.i32 x, .i32 sel]
      (fun st' vs => vs = [] ∧
        st'.globals.globals = [.i32 1048560, .i32 1049841, .i32 1049856]) := by
  apply TerminatesWith.of_wp_entry_for
    (f := ⟨[.i32, .i32], [.i32], func5, []⟩) rfl
  unfold func5
  wp_run
  simp [hgl, hpg]
  apply wp_block_cons
  wp_run
  -- the spills at 1048552/1048556 don't touch the static data
  have hRead : ∀ b w : UInt32, 1048576 ≤ b.toNat → st0.mem.read32 b = w →
      ((st0.mem.write32 1048552 sel).write32 1048556 x).read32 b = w := by
    intro b w hb hw
    rw [read32_write32_lo _ _ _ b (by have : (1048556 : UInt32).toNat = 1048556 := rfl; omega),
        read32_write32_lo _ _ _ b (by have : (1048552 : UInt32).toNat = 1048552 := rfl; omega),
        hw]
  -- `.call 0` (dispatch_dyn) at the post-prologue store
  refine wp_call_T
    (func0_at env _ sel x (by simp [hpg]) (by simp) (by simp [htb])
      (hRead _ _ (by decide) h656) (hRead _ _ (by decide) h660)
      (hRead _ _ (by decide) h664) (hRead _ _ (by decide) h668)
      (hRead _ _ (by decide) h632) (hRead _ _ (by decide) h652)
      (hRead _ _ (by decide) h616) (hRead _ _ (by decide) h636)) ?_
  rintro st2 vs2 ⟨rfl, hpg2, hgl2, htb2, hfr2⟩
  wp_run
  -- `.call 2` (dispatch_naive) at the store func0 left behind
  refine wp_call_T
    (func2_at env _ sel x [.i32 (dispatchResult sel x)] hpg2 hgl2) ?_
  rintro st3 vs3 ⟨rfl, hpg3, hgl3, htb3, hfr3⟩
  wp_run
  -- both results agree, so `ne` yields 0 and the `br_if` falls through
  simp [hgl3]

/-- The exported `check` terminates without trapping (returning no
values) on every `(sel, x)` input — equivalently, the indirect dispatch
through the in-memory vtable and function table agrees with the direct
dispatch.

Stated on `initialStore` (see the module docstring): the dynamic
dispatcher reads the static vtable out of linear memory and every
function spills to the shadow stack, so the claim is only meaningful
there. -/
@[spec_of "rust-exported" "dyn_dispatch::check"]
def CheckSpec : Prop :=
  ∀ (sel x : UInt32),
    TerminatesWith ({} : HostEnv Unit) «module» 8 S [.i32 x, .i32 sel]
      (fun _ rs => rs = [])

@[proves Project.DynDispatch.Spec.CheckSpec]
theorem check_correct : CheckSpec := by
  intro sel x
  have hpg : S.mem.pages = 17 := by native_decide
  have hgl : S.globals.globals = [.i32 1048576, .i32 1049841, .i32 1049856] := by
    native_decide
  have htb : S.tables = [dynTable] := by native_decide
  -- `func8` is the exported `check` wrapper: spill, forward to `func5`.
  apply TerminatesWith.of_wp_entry_for
    (f := ⟨[.i32, .i32], [.i32], func8, []⟩) rfl
  unfold func8
  wp_run
  simp [hgl, hpg]
  have hRead : ∀ b w : UInt32, 1048576 ≤ b.toNat → S.mem.read32 b = w →
      ((S.mem.write32 1048568 sel).write32 1048572 x).read32 b = w := by
    intro b w hb hw
    rw [read32_write32_lo _ _ _ b (by have : (1048572 : UInt32).toNat = 1048572 := rfl; omega),
        read32_write32_lo _ _ _ b (by have : (1048568 : UInt32).toNat = 1048568 := rfl; omega),
        hw]
  refine wp_call_T
    (func5_at ({} : HostEnv Unit) _ sel x (by simp [hpg]) (by simp) (by simp [htb])
      (hRead _ _ (by decide) (by native_decide))
      (hRead _ _ (by decide) (by native_decide))
      (hRead _ _ (by decide) (by native_decide))
      (hRead _ _ (by decide) (by native_decide))
      (hRead _ _ (by decide) (by native_decide))
      (hRead _ _ (by decide) (by native_decide))
      (hRead _ _ (by decide) (by native_decide))
      (hRead _ _ (by decide) (by native_decide))) ?_
  rintro st' vs ⟨rfl, hglf⟩
  wp_run
  simp [hglf]

end Project.DynDispatch.Spec
