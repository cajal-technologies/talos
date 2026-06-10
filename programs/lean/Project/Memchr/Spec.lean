import Project.Memchr.Program

/-!
# Specification for `memchr`

The exported `memchr(ptr, len, needle)` returns the (0-based) index of
the first byte in `[ptr, ptr+len)` whose value equals the low byte of
`needle`, or `len` if no byte matches.

Unoptimized (`opt-level=0`) pipeline: the export `memchr` is `func1`,
which claims a 16-byte shadow-stack frame (`global 0`: `1048576 →
1048560`), spills the arguments, and calls `func0`; `func0` runs the
scan loop with all loop state in a 32-byte red-zone frame at
`global 0 − 32 = 1048528` — the index lives at frame offset 8
(`1048536`) and the result at offset 4 (`1048532`), re-read from
linear memory on every iteration.

## Differences from the previous (broken) statement

The old `Spec.lean` was written against an earlier build of the module
(a locals-only loop at function index 0, run from an arbitrary store).
Besides no longer matching the regenerated program, its statement had
two bugs that the rewrite corrects:

* **Needle masking.** The wasm code compares `mem[ptr+i] & 0xFF` with
  `needle & 0xFF` (the Rust signature takes a `u8`), so a needle
  `≥ 256` still matches its low byte. The old spec compared the loaded
  byte against the *full* 32-bit needle and therefore claimed "no
  match" for any `needle ≥ 256`. The new model compares against
  `needle.toUInt8`.
* **Argument order.** `TerminatesWith` takes the operand stack in stack
  order (top first): the caller pushes `ptr`, `len`, `needle`, so the
  argument list is `[needle, len, ptr]`. The old spec passed
  `[ptr, len, needle]`, i.e. swapped `ptr` and `needle`.

The old spec's "every scanned offset is in bounds" side condition is
replaced by canonical-instantiation hypotheses (pages / stack pointer,
both satisfied by `«module».initialStore`) plus the requirement that
the scanned range lies below the shadow-stack frames
(`ptr + len ≤ 1048528`); under the unoptimized build the frame spills
would otherwise alias or trap. The memory contents themselves stay
fully symbolic, so the spec is as strong as the old one intended.
-/

namespace Project.Memchr.Spec

open Wasm

set_option maxRecDepth 1048576

/-! ## Functional model -/

/-- Scan `rem` bytes starting at byte index `k`. Returns the absolute
index of the first byte equal to `needle`, or `k + rem` (= original
`len`) if absent. -/
def memchrAux (m : Mem) (ptr : UInt32) (needle : UInt8) : Nat → Nat → UInt32
  | 0, k => UInt32.ofNat k
  | rem + 1, k =>
    if m.read8 (UInt32.ofNat k + ptr) = needle then UInt32.ofNat k
    else memchrAux m ptr needle rem (k + 1)

/-! ## Top spec -/

/-- The exported `memchr` returns the index of the first occurrence of
the low byte of `needle` in `[ptr, ptr+len)`, or `len` if absent.

The canonical-instantiation hypotheses (16 pages, stack pointer
`global 0 = 1048576`) are load-bearing: the unoptimized body spills
every intermediate to shadow-stack frames below `global 0`, so under an
adversarial store the very first spill would trap. Both hold for
`«module».initialStore`, but the memory *contents* stay symbolic so the
spec covers arbitrary buffer data. `ptr + len ≤ 1048528` keeps the
scanned range disjoint from (and below) the two shadow-stack frames
`[1048528, 1048576)`.

Informal spec:
Given a base pointer `ptr`, a length `len`, and a needle byte `needle`,
the wasm export `memchr` terminates and leaves a single i32 on the
value stack equal to the (0-based) index of the first byte in
`[ptr, ptr+len)` equal to `needle`'s low byte, or `len` if no such byte
exists. -/
@[spec_of "rust-exported" "memchr::memchr"]
def MemchrSpec : Prop :=
  ∀ (env : HostEnv Unit) (initial : Store Unit) (ptr len needle : UInt32),
    initial.mem.pages = 16 →
    initial.globals.globals[0]? = some (.i32 1048576) →
    ptr.toNat + len.toNat ≤ 1048528 →
    -- Args in stack order (top first): the Wasm caller pushes `ptr`,
    -- then `len`, then `needle`, and `run` reverses on entry to make
    -- local 0 = ptr.
    TerminatesWith env «module» 1 initial [.i32 needle, .i32 len, .i32 ptr]
      (fun _ rs => rs = [.i32 (memchrAux initial.mem ptr needle.toUInt8 len.toNat 0)])

/-! ## Memory framing lemmas -/

@[simp] private theorem write32_pages (m : Mem) (a v : UInt32) :
    (m.write32 a v).pages = m.pages := rfl

@[simp] private theorem write8_pages (m : Mem) (a : UInt32) (v : UInt8) :
    (m.write8 a v).pages = m.pages := rfl

private theorem write32_bytes_of_disjoint (m : Mem) (a v : UInt32) (i : Nat)
    (h : i < a.toNat ∨ a.toNat + 4 ≤ i) :
    (m.write32 a v).bytes i = m.bytes i := by
  simp only [Mem.write32]
  have h0 : i ≠ a.toNat := by omega
  have h1 : i ≠ a.toNat + 1 := by omega
  have h2 : i ≠ a.toNat + 2 := by omega
  have h3 : i ≠ a.toNat + 3 := by omega
  simp [h0, h1, h2, h3]

private theorem write8_bytes_of_disjoint (m : Mem) (a : UInt32) (v : UInt8) (i : Nat)
    (h : i ≠ a.toNat) :
    (m.write8 a v).bytes i = m.bytes i := by
  simp [Mem.write8, h]

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
@[simp] private theorem read32_write32_disjoint (m : Mem) (a b v : UInt32)
    (h : b.toNat + 4 ≤ a.toNat ∨ a.toNat + 4 ≤ b.toNat) :
    (m.write32 a v).read32 b = m.read32 b := by
  simp only [Mem.read32]
  rw [write32_bytes_of_disjoint m a v b.toNat (by omega),
      write32_bytes_of_disjoint m a v (b.toNat + 1) (by omega),
      write32_bytes_of_disjoint m a v (b.toNat + 2) (by omega),
      write32_bytes_of_disjoint m a v (b.toNat + 3) (by omega)]

/-- A 32-bit read is unaffected by a byte write outside its range. -/
@[simp] private theorem read32_write8_disjoint (m : Mem) (a b : UInt32) (v : UInt8)
    (h : b.toNat + 4 ≤ a.toNat ∨ a.toNat + 1 ≤ b.toNat) :
    (m.write8 a v).read32 b = m.read32 b := by
  simp only [Mem.read32]
  rw [write8_bytes_of_disjoint m a v b.toNat (by omega),
      write8_bytes_of_disjoint m a v (b.toNat + 1) (by omega),
      write8_bytes_of_disjoint m a v (b.toNat + 2) (by omega),
      write8_bytes_of_disjoint m a v (b.toNat + 3) (by omega)]

/-- A byte read is unaffected by a 32-bit write to a disjoint range. -/
private theorem read8_write32_disjoint (m : Mem) (a b v : UInt32)
    (h : b.toNat + 1 ≤ a.toNat ∨ a.toNat + 4 ≤ b.toNat) :
    (m.write32 a v).read8 b = m.read8 b := by
  simp only [Mem.read8]
  rw [write32_bytes_of_disjoint m a v b.toNat (by omega)]

/-! ## Bridging the byte comparison

The wasm code compares `(loaded byte) & 255` with `needle & 255`; the
loaded byte is already `< 256`, so this is exactly equality with the
needle's low byte. -/

private theorem and255_eq_iff (b : UInt8) (n : UInt32) :
    255 &&& b.toUInt32 = 255 &&& n ↔ b = n.toUInt8 := by
  bv_decide

/-! ## `memchrAux` unfolding and congruence -/

private theorem memchrAux_match {m : Mem} {ptr : UInt32} {needle : UInt8} {k rem : Nat}
    (h : m.read8 (UInt32.ofNat k + ptr) = needle) :
    memchrAux m ptr needle (rem + 1) k = UInt32.ofNat k := by
  simp [memchrAux, h]

private theorem memchrAux_no_match {m : Mem} {ptr : UInt32} {needle : UInt8} {k rem : Nat}
    (h : ¬ m.read8 (UInt32.ofNat k + ptr) = needle) :
    memchrAux m ptr needle (rem + 1) k = memchrAux m ptr needle rem (k + 1) := by
  simp [memchrAux, h]

/-- `memchrAux` only looks at bytes in `[ptr+k, ptr+k+rem)`; two memories
agreeing below `1048528` give the same scan when the range fits there. -/
private theorem memchrAux_congr (m m' : Mem) (ptr : UInt32) (needle : UInt8)
    (hagree : ∀ j : Nat, j < 1048528 → m'.bytes j = m.bytes j) :
    ∀ rem k : Nat, ptr.toNat + k + rem ≤ 1048528 →
      memchrAux m' ptr needle rem k = memchrAux m ptr needle rem k := by
  intro rem
  induction rem with
  | zero => intro k _; rfl
  | succ n ih =>
    intro k hk
    have haddr : (UInt32.ofNat k + ptr).toNat = ptr.toNat + k := by
      have hp := UInt32.toNat_lt ptr
      rw [UInt32.toNat_add]
      simp
      omega
    simp only [memchrAux, Mem.read8, haddr, hagree (ptr.toNat + k) (by omega)]
    split
    · rfl
    · exact ih (k + 1) (by omega)

/-! ## A store-specific `call` rule

`wp_call_cons` consumes a `FuncSpec`, which quantifies over *all*
initial stores. That is unusable here: `func0` spills to linear memory
and traps on a too-small store, so no total `FuncSpec` exists for it.
We step `call` against a `TerminatesWith` *at the concrete current
store* instead (`wp_call_at` is the interpreter-side core of this). -/

private theorem wp_call_of_terminates {α : Type} {env : HostEnv α} {m : Module}
    {id : Nat} {Q : Assertion α} {rest : Program} {st : Store α} {s : Locals}
    {P : Store α → List Value → Prop}
    (h : TerminatesWith env m id st s.values P)
    (hPost : ∀ st' vs, P st' vs → wp m rest Q st' { s with values := vs } env) :
    wp m (.call id :: rest) Q st s env :=
  wp_call_at h hPost

/-! ## `func0`: the scan loop over the shadow-stack frame

`func0` is called with `global 0 = 1048560` and claims the red zone
`[1048528, 1048560)` (no `globalSet`): the index lives at `1048536`,
the result slot at `1048532`, and the argument/debug spills at
`1048540`/`1048544`/`1048551`/`1048552`/`1048556`. Each iteration
re-loads the index from memory, tests `index < len`, loads the byte at
`ptr + index`, and either exits (match → result = index;
exhaustion → result = len) or stores `index + 1` and re-enters. -/

theorem func0_terminates (env : HostEnv Unit) (st0 : Store Unit)
    (ptr len needle : UInt32)
    (hpg : st0.mem.pages = 16)
    (hg0 : st0.globals.globals[0]? = some (.i32 1048560))
    (hbuf : ptr.toNat + len.toNat ≤ 1048528) :
    TerminatesWith env «module» 0 st0 [.i32 needle, .i32 len, .i32 ptr]
      (fun st' vs => st'.globals = st0.globals ∧
        vs = [.i32 (memchrAux st0.mem ptr needle.toUInt8 len.toNat 0)]) := by
  have hlen32 := UInt32.toNat_lt len
  have hofNat : ∀ k : Nat, k ≤ len.toNat → (UInt32.ofNat k).toNat = k := fun k hk => by
    simp; omega
  apply TerminatesWith.of_wp_entry_for
    (f := ⟨[.i32, .i32, .i32], [.i32, .i32], func0, [.i32]⟩) rfl
  unfold func0
  wp_run
  simp [hg0, hpg]
  apply wp_block_cons   -- OUTER
  apply wp_loop_cons
    (Inv := fun st' s' => ∃ (k : Nat) (w4 : Value),
      k ≤ len.toNat ∧
      s' = { params := [.i32 ptr, .i32 len, .i32 needle],
             locals := [.i32 1048528, w4], values := [] } ∧
      st'.mem.pages = 16 ∧
      st'.globals = st0.globals ∧
      st'.mem.read32 1048536 = UInt32.ofNat k ∧
      memchrAux st0.mem ptr needle.toUInt8 (len.toNat - k) k
        = memchrAux st0.mem ptr needle.toUInt8 len.toNat 0 ∧
      (∀ j : Nat, j < 1048532 → st'.mem.bytes j = st0.mem.bytes j))
    (μ := fun st' _ => len.toNat + 1 - (st'.mem.read32 1048536).toNat)
  · -- Invariant on entry (`k = 0`).
    refine ⟨0, .i32 0, by omega, rfl, by simp [hpg], rfl, by simp, by simp, ?_⟩
    intro j hj
    rw [write32_bytes_of_disjoint _ _ _ _ (by simp; omega),
        write8_bytes_of_disjoint _ _ _ _ (by simp; omega),
        write32_bytes_of_disjoint _ _ _ _ (by simp; omega),
        write32_bytes_of_disjoint _ _ _ _ (by simp; omega)]
  · -- One loop iteration.
    rintro st s ⟨k, w4, hk, rfl, hpg', hgl', hK, hinv, hfr⟩
    have hKt : (UInt32.ofNat k).toNat = k := hofNat k hk
    apply wp_block_cons   -- A: the `index < len` test
    wp_run
    simp [hK, hpg']
    by_cases hklt : (UInt32.ofNat k : UInt32) < len
    · -- `k < len`: scan position `k`.
      have hkltn : k < len.toNat := by
        have := UInt32.lt_iff_toNat_lt.mp hklt
        rwa [hKt] at this
      have haddr : (UInt32.ofNat k + ptr).toNat = ptr.toNat + k := by
        have hp := UInt32.toNat_lt ptr
        rw [UInt32.toNat_add, hKt]
        omega
      simp [hklt]
      apply wp_block_cons   -- B: the byte test
      wp_run
      simp [hpg', haddr]
      -- The byte under test comes from the original store: the two
      -- frame spills this iteration and everything the loop wrote so
      -- far live at `≥ 1048532 > ptr + k`.
      have hrd : ((st.mem.write32 1048552 ptr).write32 1048556 (UInt32.ofNat k)).read8
          (UInt32.ofNat k + ptr) = st0.mem.read8 (UInt32.ofNat k + ptr) := by
        rw [read8_write32_disjoint _ _ _ _ (by rw [haddr]; simp; omega),
            read8_write32_disjoint _ _ _ _ (by rw [haddr]; simp; omega)]
        simp only [Mem.read8, haddr]
        exact hfr _ (by omega)
      rw [hrd]
      have hrem : len.toNat - k = (len.toNat - k - 1) + 1 := by omega
      by_cases hmatch : st0.mem.read8 (UInt32.ofNat k + ptr) = needle.toUInt8
      · -- Match: exit the loop; result slot gets the index `k`.
        have hcond : 255 &&& (st0.mem.read8 (UInt32.ofNat k + ptr)).toUInt32
            = 255 &&& needle := (and255_eq_iff _ _).mpr hmatch
        simp [hcond, hgl', hK]
        rw [← hinv, hrem, memchrAux_match hmatch]
        exact ⟨by omega, rfl⟩
      · -- No match: bump the index slot and re-enter the loop.
        have hcond : ¬ 255 &&& (st0.mem.read8 (UInt32.ofNat k + ptr)).toUInt32
            = 255 &&& needle := fun h => hmatch ((and255_eq_iff _ _).mp h)
        have hk1 : 1 + UInt32.ofNat k = UInt32.ofNat (k + 1) := by
          apply UInt32.toNat.inj
          rw [UInt32.toNat_add, hKt, hofNat (k + 1) (by omega)]
          simp only [show (1 : UInt32).toNat = 1 from rfl]
          omega
        simp [hcond, hK, hgl']
        refine ⟨by omega, ⟨k + 1, by omega, hk1, ?_, ?_⟩, ?_⟩
        · rw [← hinv, hrem, memchrAux_no_match hmatch]
          congr 1
        · intro j hj
          rw [write32_bytes_of_disjoint _ _ _ _ (by simp; omega),
              write32_bytes_of_disjoint _ _ _ _ (by simp; omega),
              write32_bytes_of_disjoint _ _ _ _ (by simp; omega)]
          exact hfr j hj
        · omega
    · -- `k = len`: exhausted; result slot gets `len`.
      have hkeq : k = len.toNat := by
        have : ¬ k < len.toNat := fun h =>
          hklt (UInt32.lt_iff_toNat_lt.mpr (by rwa [hKt]))
        omega
      simp [hklt, hgl']
      rw [← hinv, hkeq]
      simp [memchrAux, UInt32.ofNat_toNat]

/-! ## The export wrapper (`func1` = `memchr`) -/

@[proves Project.Memchr.Spec.MemchrSpec]
theorem memchr_correct : MemchrSpec := by
  intro env initial ptr len needle hpg hg0 hbuf
  have hlen0 : 0 < initial.globals.globals.length := by
    rcases List.getElem?_eq_some_iff.mp hg0 with ⟨h, _⟩
    omega
  apply TerminatesWith.of_wp_entry_for
    (f := ⟨[.i32, .i32, .i32], [.i32, .i32], func1, [.i32]⟩) rfl
  have hg0' : initial.globals.globals[0]'hlen0 = .i32 1048576 := by
    rw [List.getElem?_eq_getElem hlen0] at hg0
    exact Option.some.inj hg0
  unfold func1
  wp_run
  simp [hg0', hpg, hlen0]
  apply wp_call_of_terminates
    (func0_terminates env _ ptr len needle (by simp [hpg])
      (by simp [hlen0]) hbuf)
  rintro st' vs ⟨hgl, rfl⟩
  wp_run
  simp [hgl, hlen0]
  -- The callee scanned the spilled store, which agrees with `initial`
  -- below the shadow-stack frames.
  rw [memchrAux_congr _ initial.mem ptr needle.toUInt8 ?_ len.toNat 0 (by omega)]
  intro j hj
  rw [write8_bytes_of_disjoint _ _ _ _ (by simp; omega),
      write32_bytes_of_disjoint _ _ _ _ (by simp; omega),
      write32_bytes_of_disjoint _ _ _ _ (by simp; omega)]

end Project.Memchr.Spec
