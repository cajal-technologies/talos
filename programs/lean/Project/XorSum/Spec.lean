import Project.XorSum.Program

/-!
# Specification for `xor_sum`

The exported `check(seed, len)` seeds a length-`len` buffer from `seed`,
XOR-folds it both ways — left-to-right (the implementation under test)
and right-to-left (the obviously-correct oracle) — and traps via
`unreachable` iff they disagree. Proving the wasm export terminates
without trapping for every `(seed, len)` is therefore the same as
proving the forward and backward XOR-folds agree on every seeded
buffer, which is the associativity-and-commutativity content of `xor`.
-/

namespace Project.XorSum.Spec

open Wasm

set_option maxRecDepth 1048576

/-- The exported `check` terminates without trapping (and returns no
values) on every `(seed, len)` input, when run from the module's
canonical instantiation.

The `initial = «module».initialStore` hypothesis is load-bearing: the
body allocates a scratch buffer at `global 0 − 128` and writes 128
bytes there via `memory.fill`/`i32.store`. That is in-bounds precisely
because the canonical store sets `global 0 = 1048576` and allocates
`16` pages (`16 · 65536 = 1048576` bytes), so the buffer
`[1048448, 1048576)` fits exactly. Under an adversarial store (e.g.
`mem.pages = 0`) the fill would trap, so this property genuinely needs
the canonical store — unlike the pure-arithmetic equivalence checks,
which hold for every store.

Informal spec:
For `seed len : UInt32`, the wasm export `check` terminates and leaves
an empty value stack. Termination-without-trapping is the whole content
of the spec — the body traps via `unreachable` iff the forward and
backward XOR-folds disagree, so this property *is* the
associativity-and-commutativity claim for `xor` over the seeded
buffer. -/
@[spec_of "rust-exported" "xor_sum::check"]
def CheckSpec : Prop :=
  ∀ (env : HostEnv Unit) (initial : Store Unit) (seed len : UInt32),
    initial = «module».initialStore →
    TerminatesWith env «module» 3 initial [.i32 len, .i32 seed]
      (fun _ rs => rs = [])

/-! ## XOR fold and its order-independence

`xorFwd m ptr n` is the forward (left-to-right) XOR fold of the `n`
little-endian `u32` words at `ptr, ptr+4, …, ptr+4*(n-1)`. The forward
loop (`func1`) computes this directly. The backward loop (`func2`)
reads the same words high-to-low; because `xor` is commutative,
associative and self-inverse, it lands on the *same* value — that
order-independence is the entire mathematical content of the check. -/

def xorFwd (m : Mem) (ptr : UInt32) : Nat → UInt32
  | 0     => 0
  | n + 1 => xorFwd m ptr n ^^^ m.read32 (ptr + 4 * UInt32.ofNat n)

@[simp] lemma xorFwd_zero (m : Mem) (ptr : UInt32) : xorFwd m ptr 0 = 0 := rfl

lemma xorFwd_succ (m : Mem) (ptr : UInt32) (n : Nat) :
    xorFwd m ptr (n + 1) = xorFwd m ptr n ^^^ m.read32 (ptr + 4 * UInt32.ofNat n) := rfl

/-! ## A store-specific `call` rule

`wp_call_cons` consumes a `FuncSpec`, which quantifies over *all* initial
stores. That is unusable here: `func1`/`func2` `load32` from memory and
trap on a too-small store, so no total `FuncSpec` exists for them. We
step `call` against a `TerminatesWith` *at the concrete current store*
instead — same proof as `wp_call_cons`, just sourcing the success run
from the store-specific hypothesis. -/

private theorem wp_call_of_terminates {α : Type} {env : HostEnv α} {m : Module}
    {id : Nat} {Q : Assertion α} {rest : Program} {st : Store α} {s : Locals}
    {P : Store α → List Value → Prop}
    (h : TerminatesWith env m id st s.values P)
    (hPost : ∀ st' vs, P st' vs → wp m rest Q st' { s with values := vs } env) :
    wp m (.call id :: rest) Q st s env := by
  unfold wp
  obtain ⟨Ns, hNs⟩ := h
  obtain ⟨vs, st', hRun, hP⟩ := hNs Ns le_rfl
  have hRun_ne : run Ns m id st s.values env ≠ .OutOfFuel := by rw [hRun]; intro h; cases h
  have hwp_rest := hPost st' vs hP
  unfold wp at hwp_rest
  obtain ⟨Nr, hNr⟩ := hwp_rest
  refine ⟨max (Ns + 1) (Nr + 1), fun fuel hfuel => ?_⟩
  obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
  have hRun_f : run f m id st s.values env = .Success vs st' := by
    rw [run_fuel_mono (by omega : f ≥ Ns) hRun_ne]; exact hRun
  rw [exec_call_cons, hRun_f]
  exact hNr (f + 1) (by omega)

/-! ## UInt32 ↔ Nat bridges for the loop counters -/

private lemma uint32_ofNat_le_of_le {k : Nat} {len : UInt32}
    (hk : k ≤ len.toNat) : UInt32.ofNat k ≤ len := by
  have hk32 : k < UInt32.size := Nat.lt_of_le_of_lt hk (UInt32.toNat_lt len)
  exact (UInt32.ofNat_le_iff hk32).mpr hk

private lemma uint32_sub_toNat_of_nat_le {k : Nat} {len : UInt32}
    (hk : k ≤ len.toNat) : (len - UInt32.ofNat k).toNat = len.toNat - k := by
  have hk32 : k < UInt32.size := Nat.lt_of_le_of_lt hk (UInt32.toNat_lt len)
  have hle := uint32_ofNat_le_of_le hk
  rw [UInt32.toNat_sub_of_le len (UInt32.ofNat k) hle,
      UInt32.toNat_ofNat_of_lt' hk32]

/-! ## Per-function correctness -/

/-- `func1` (forward fold) returns `xorFwd` of the `cl` words at `ptr`,
leaving the store untouched. The bounds hypotheses keep every `load32`
in range so the loop never traps. -/
theorem func1_terminates (env : HostEnv Unit) (st0 : Store Unit) (ptr cl : UInt32)
    (tail : List Value)
    (hpages : st0.mem.pages = 16)
    (hb : ptr.toNat + 4 * cl.toNat ≤ st0.mem.pages * 65536) :
    TerminatesWith env «module» 1 st0 ([.i32 cl, .i32 ptr] ++ tail)
      (fun st' vs => st' = st0 ∧ vs = .i32 (xorFwd st0.mem ptr cl.toNat) :: tail) := by
  -- Every word read sits inside the legal byte span.
  have hmem : ∀ k, k < cl.toNat →
      (ptr.toNat + 4 * k) % 4294967296 + 4 ≤ st0.mem.pages * 65536 := by
    intro k hk
    have hclt := UInt32.toNat_lt cl
    rw [hpages] at hb ⊢
    omega
  apply TerminatesWith.of_wp_entry_for (f := ⟨[.i32, .i32], [.i32], func1, [.i32]⟩) rfl
  unfold func1
  wp_run
  simp
  apply wp_block_cons
  wp_run
  simp
  by_cases hlen : cl = 0
  · -- cl = 0: eqz gives 1, br_if breaks block; acc = 0
    simp [hlen]
  · -- cl ≠ 0: br_if falls through; enter loop
    simp [hlen]
    apply wp_loop_cons
      (Inv := fun st' s' =>
        st' = st0 ∧
        ∃ k : Nat, k < cl.toNat ∧
          s' = ⟨[.i32 (ptr + 4 * UInt32.ofNat k),
                  .i32 (cl - UInt32.ofNat k)],
                 [.i32 (xorFwd st0.mem ptr k)], []⟩)
      (μ := fun _ s' => match s'.params with
        | [_, .i32 rem] => rem.toNat
        | _ => 0)
    · -- Initial invariant: k = 0
      refine ⟨rfl, 0, ?_, ?_⟩
      · exact Nat.pos_of_ne_zero (fun h => hlen (UInt32.toNat.inj (by simpa using h)))
      · simp [xorFwd]
    · -- Loop step
      rintro st' s' ⟨rfl, k, hk, rfl⟩
      wp_run
      simp
      have h_nxt_eq : (4294967295 : UInt32) + (cl - UInt32.ofNat k) =
          cl - UInt32.ofNat (k + 1) := by
        apply UInt32.toNat.inj
        have hlt := UInt32.toNat_lt cl
        rw [uint32_sub_toNat_of_nat_le (by omega : k + 1 ≤ cl.toNat)]
        simp [UInt32.toNat_add, uint32_sub_toNat_of_nat_le hk.le]
        omega
      by_cases hexit : (4294967295 : UInt32) + (cl - UInt32.ofNat k) = 0
      · -- Loop exits: accumulate final element
        simp [hexit]
        have hk1 : k + 1 = cl.toNat := by
          have h1 := uint32_sub_toNat_of_nat_le (k := k + 1) (len := cl) (by omega)
          have h0 : cl - UInt32.ofNat (k + 1) = 0 := h_nxt_eq ▸ hexit
          rw [h0] at h1; simp at h1; omega
        refine ⟨hmem k hk, ?_⟩
        simp only [xorFwd_succ, ← hk1]
        exact UInt32.xor_comm _ _
      · -- Loop continues with invariant at k+1
        simp
        have hk1 : k + 1 < cl.toNat := by
          have h1 := uint32_sub_toNat_of_nat_le (k := k + 1) (len := cl) (by omega)
          have hexit' : cl - UInt32.ofNat (k + 1) ≠ 0 :=
            fun h => hexit (h_nxt_eq.symm ▸ h)
          have hne : (cl - UInt32.ofNat (k + 1)).toNat ≠ 0 :=
            fun h => hexit' (UInt32.toNat.inj (by simpa using h))
          rw [h1] at hne; omega
        refine ⟨hmem k hk, ⟨k + 1, hk1, ⟨⟨?_, ?_⟩, ?_⟩⟩, ?_⟩
        · apply UInt32.toNat.inj; simp [UInt32.toNat_add]; omega
        · exact h_nxt_eq
        · simp only [xorFwd_succ]; exact UInt32.xor_comm _ _
        · have hlt := UInt32.toNat_lt cl
          rw [uint32_sub_toNat_of_nat_le hk.le]
          omega

/-! ### Bridges specific to the backward loop -/

/-- `i32.shl` by 2 is multiplication by 4. -/
private lemma shl_two (x : UInt32) : x <<< 2 = x * 4 := by
  apply UInt32.toNat.inj
  rw [UInt32.toNat_shiftLeft, UInt32.toNat_mul, Nat.shiftLeft_eq]
  norm_num [UInt32.toNat_ofNat]

/-- The backward loop's read address `(ptr − 4) + bl` (with the `−4`
encoded as `+ 0xFFFFFFFC`) coincides with `xorFwd`'s forward address for
index `n`, when the byte-length `bl` equals `4·(n+1)`. -/
private lemma bwd_addr {ptr bl : UInt32} {n : Nat}
    (hbl : bl.toNat = 4 * (n + 1)) (hlo : 4 ≤ ptr.toNat)
    (hhi : ptr.toNat + 4 * (n + 1) ≤ 4294967296) :
    bl + (4294967292 + ptr) = ptr + 4 * UInt32.ofNat n := by
  have hsz : UInt32.size = 4294967296 := rfl
  have hpt := ptr.toNat_lt
  apply UInt32.toNat.inj
  have hn : (UInt32.ofNat n).toNat = n := UInt32.toNat_ofNat_of_lt' (by omega : n < UInt32.size)
  have hc : (4294967292 : UInt32).toNat = 4294967292 := rfl
  have h4 : (4 : UInt32).toNat = 4 := rfl
  simp only [UInt32.toNat_add, UInt32.toNat_mul, hn, h4, hc, hbl]
  omega

/-- Order-independence step: folding the top element in undoes the two
copies of `M` that the running accumulator and the suffix fold share. -/
private lemma xor_shuffle (M X Y : UInt32) : M ^^^ (X ^^^ (Y ^^^ M)) = X ^^^ Y := by
  rw [← UInt32.xor_assoc X Y M, UInt32.xor_comm (X ^^^ Y) M,
      ← UInt32.xor_assoc M M (X ^^^ Y), UInt32.xor_self, UInt32.zero_xor]

/-- `func2` (backward fold) returns the *same* value as `func1`: the
forward `xorFwd`. Order-independence of `xor` is discharged inside the
loop invariant via [`xor_shuffle`]. -/
theorem func2_terminates (env : HostEnv Unit) (st0 : Store Unit) (ptr cl : UInt32)
    (tail : List Value)
    (hpages : st0.mem.pages = 16) (hlo : 4 ≤ ptr.toNat)
    (hb : ptr.toNat + 4 * cl.toNat ≤ st0.mem.pages * 65536) :
    TerminatesWith env «module» 2 st0 ([.i32 cl, .i32 ptr] ++ tail)
      (fun st' vs => st' = st0 ∧ vs = .i32 (xorFwd st0.mem ptr cl.toNat) :: tail) := by
  have hclb : cl.toNat ≤ 262144 := by rw [hpages] at hb; omega
  apply TerminatesWith.of_wp_entry_for (f := ⟨[.i32, .i32], [.i32, .i32], func2, [.i32]⟩) rfl
  unfold func2
  apply wp_block_cons
  apply wp_block_cons
  wp_run
  by_cases hcl0 : cl = 0
  · -- cl = 0: inner block falls through, `br 1` exits with acc 0
    simp [hcl0]
  · -- cl ≠ 0: `br_if 0` breaks inner block; run the setup then the loop
    simp
    apply wp_loop_cons
      (Inv := fun st' s' =>
        st' = st0 ∧
        ∃ (k : Nat) (bl : UInt32) (d : Value),
          k < cl.toNat ∧ bl.toNat = 4 * (cl.toNat - k) ∧
          s' = { params := [.i32 (xorFwd st0.mem ptr cl.toNat ^^^
                                  xorFwd st0.mem ptr (cl.toNat - k)),
                            .i32 bl],
                 locals := [.i32 (4294967292 + ptr), d], values := [] })
      (μ := fun _ s' => match s'.params with
        | [_, .i32 bl] => bl.toNat
        | _ => 0)
    · -- Initial invariant: k = 0, bl = cl <<< 2
      have hclpos : 0 < cl.toNat := Nat.pos_of_ne_zero (fun h =>
        hcl0 (UInt32.toNat.inj (by simpa using h)))
      refine ⟨rfl, 0, cl <<< 2, .i32 0, hclpos, ?_, ?_⟩
      · rw [shl_two, UInt32.toNat_mul]
        have h4 : (4 : UInt32).toNat = 4 := rfl
        rw [h4]; omega
      · simp [UInt32.xor_self]
    · -- Loop step
      rintro st' s' ⟨rfl, k, bl, d, hk, hbl, rfl⟩
      obtain ⟨n, hn⟩ : ∃ n, cl.toNat - k = n + 1 := ⟨cl.toNat - k - 1, by omega⟩
      have haddr : bl + (4294967292 + ptr) = ptr + 4 * UInt32.ofNat n :=
        bwd_addr (by rw [hbl, hn]) hlo (by rw [hpages] at hb; omega)
      wp_run
      simp [haddr]
      have hsucc : xorFwd st'.mem ptr (cl.toNat - k)
          = xorFwd st'.mem ptr n ^^^ st'.mem.read32 (ptr + 4 * UInt32.ofNat n) := by
        rw [hn]; rfl
      have hmod : (4294967292 + bl.toNat) % 4294967296 = bl.toNat - 4 := by
        rw [hbl] at *; omega
      refine ⟨?_, ?_⟩
      · -- read stays in bounds
        rw [hpages] at hb ⊢; omega
      · by_cases hexit : (4294967292 : UInt32) + bl = 0
        · -- bl - 4 = 0: this was the last (index-0) read; result is the full fold
          simp only [hexit]
          have hn0 : n = 0 := by
            have hbt : (4294967292 + bl).toNat = 0 := by rw [hexit]; rfl
            rw [UInt32.toNat_add] at hbt
            have hc : (4294967292 : UInt32).toNat = 4294967292 := rfl
            rw [hc, hmod] at hbt
            omega
          rw [hsucc, xor_shuffle, hn0, xorFwd_zero, UInt32.xor_zero]
        · -- bl - 4 ≠ 0: keep folding with the invariant at k + 1
          have hbt : bl.toNat - 4 ≠ 0 := by
            intro h
            apply hexit; apply UInt32.toNat.inj
            rw [UInt32.toNat_add]
            have hc : (4294967292 : UInt32).toNat = 4294967292 := rfl
            rw [hc, hmod, h]; rfl
          simp only [hmod]
          refine ⟨⟨k + 1, ?_, ?_, ?_⟩, ?_⟩
          · omega
          · rw [hbl]; omega
          · rw [hsucc, xor_shuffle]
            congr 2
            omega
          · omega

/-- The comparison block: call the forward fold (`func1`) and backward
fold (`func2`) over the same `cl`-word buffer at `1048448`, compare them,
and (because they agree) fall through the `br_if`, restore the stack
pointer and `ret`. Holds for *any* seeded store of 16 pages, so it is
shared by the `len = 0` and `len ≠ 0` paths of `func0`. -/
private theorem compare_block_ok (env : HostEnv Unit) (st2 : Store Unit) (Q : Assertion Unit)
    (p0 p1 l4 l5 : Value) (cl : UInt32)
    (hpg : st2.mem.pages = 16) (hcl : cl.toNat ≤ 32)
    (hgl : 0 < st2.globals.globals.length)
    (hQ : ∀ (st : Store Unit) (vs : List Value), Q (.Return st vs)) :
    wp «module»
      [.block 0 0 [.localGet 2, .localGet 3, .call 1, .localGet 2, .localGet 3, .call 2,
                   .ne, .br_if 0, .localGet 2, .const 128, .add, .globalSet 0, .ret],
       .unreachable]
      Q
      st2 { params := [p0, p1], locals := [.i32 1048448, .i32 cl, l4, l5] } env := by
  have h1 : (1048448 : UInt32).toNat = 1048448 := rfl
  have hb1 : (1048448 : UInt32).toNat + 4 * cl.toNat ≤ st2.mem.pages * 65536 := by
    rw [hpg, h1]; omega
  apply wp_block_cons
  wp_run
  apply wp_call_of_terminates (func1_terminates env st2 1048448 cl [] hpg hb1)
  rintro stA vsA ⟨rfl, rfl⟩
  wp_run
  apply wp_call_of_terminates
    (func2_terminates env stA 1048448 cl [.i32 (xorFwd stA.mem 1048448 cl.toNat)]
      hpg (by rw [h1]; omega) hb1)
  rintro stB vsB ⟨rfl, rfl⟩
  wp_run
  simp only [ne_eq, not_true_eq_false, if_false]
  simp [List.getElem?_eq_getElem hgl]
  apply hQ

/-- `func0` (the real `check`): allocate a 128-byte scratch buffer at
`global 0 − 128`, zero it, seed `min(len,32)` words, fold both ways and
compare. The two folds always agree, so the `unreachable` is dead; the
function returns with an empty value stack. -/
theorem func0_terminates (env : HostEnv Unit) (seed len : UInt32) :
    TerminatesWith env «module» 0 «module».initialStore [.i32 len, .i32 seed]
      (fun _ rs => rs = []) := by
  have hg : («module».initialStore : Store Unit).globals.globals[0]? = some (.i32 1048576) := by
    rfl
  have hp : («module».initialStore : Store Unit).mem.pages = 16 := by rfl
  apply TerminatesWith.of_wp_entry_for
    (f := ⟨[.i32, .i32], [.i32, .i32, .i32, .i32], func0, []⟩) rfl
  unfold func0
  wp_run
  simp [hg, hp]
  apply wp_block_cons
  wp_run
  by_cases hlen0 : len = 0
  · -- len = 0: seeding loop is skipped
    simp [hlen0]
    apply compare_block_ok
    · exact hp
    · decide
    · decide
    · intro _ _; trivial
  · -- len ≠ 0: run the seeding loop (contents irrelevant), then compare
    simp [hlen0]
    rw [show (if len < 32 then Value.i32 len else Value.i32 32)
          = Value.i32 (if len < 32 then len else 32) from (apply_ite Value.i32 _ _ _).symm]
    set clu : UInt32 := if len < 32 then len else 32 with hcludef
    have hclu32 : clu.toNat ≤ 32 := by
      rw [hcludef]; split
      · rename_i h; have hh := UInt32.lt_iff_toNat_lt.mp h; simp at hh; omega
      · decide
    have hclupos : 0 < clu.toNat := by
      rw [hcludef]; split
      · rename_i h
        exact Nat.pos_of_ne_zero (fun hz => hlen0 (UInt32.toNat.inj (by simpa using hz)))
      · decide
    apply wp_loop_cons
      (Inv := fun st' s' =>
        st'.mem.pages = 16 ∧ 0 < st'.globals.globals.length ∧
        ∃ (j : Nat) (vacc : UInt32), j < clu.toNat ∧
          s' = { params := [.i32 vacc, .i32 (1048448 + 4 * UInt32.ofNat j)],
                 locals := [.i32 1048448, .i32 clu, .i32 (1 + seed),
                            .i32 (clu - UInt32.ofNat j)], values := [] })
      (μ := fun _ s' => match s'.locals with
        | [_, _, _, .i32 cnt] => cnt.toNat
        | _ => 0)
    · -- Initial invariant: j = 0
      refine ⟨hp, by decide, 0, seed, hclupos, ?_⟩
      simp
    · -- Loop step
      rintro st' s' ⟨hpg, hgl, j, vacc, hj, rfl⟩
      have hsz : UInt32.size = 4294967296 := rfl
      have hbufp : (1048448 + 4 * UInt32.ofNat j).toNat = 1048448 + 4 * j := by
        rw [UInt32.toNat_add, UInt32.toNat_mul,
            UInt32.toNat_ofNat_of_lt' (by omega : j < UInt32.size)]
        have h4 : (4 : UInt32).toNat = 4 := rfl
        have h8 : (1048448 : UInt32).toNat = 1048448 := rfl
        rw [h4, h8]; omega
      have hnxt : (4294967295 : UInt32) + (clu - UInt32.ofNat j) = clu - UInt32.ofNat (j + 1) := by
        apply UInt32.toNat.inj
        have hlt := UInt32.toNat_lt clu
        rw [uint32_sub_toNat_of_nat_le (by omega : j + 1 ≤ clu.toNat)]
        simp [UInt32.toNat_add, uint32_sub_toNat_of_nat_le hj.le]
        omega
      wp_run
      simp [hbufp, hpg, hnxt]
      refine ⟨by omega, ?_⟩
      have hofs : UInt32.ofNat (j + 1) = UInt32.ofNat j + 1 := by
        apply UInt32.toNat.inj
        rw [UInt32.toNat_add, UInt32.toNat_ofNat_of_lt' (by omega : j + 1 < UInt32.size),
            UInt32.toNat_ofNat_of_lt' (by omega : j < UInt32.size)]
        have h1 : (1 : UInt32).toNat = 1 := rfl
        rw [h1]; omega
      have hcnt : (clu - (UInt32.ofNat j + 1)).toNat = clu.toNat - (j + 1) := by
        rw [← hofs, uint32_sub_toNat_of_nat_le hj]
      -- Split on the loop-back test (counter after decrement).
      split
      · -- counter = 0: buffer fully seeded, exit to the comparison block
        apply compare_block_ok
        · exact hpg
        · exact hclu32
        · exact hgl
        · intro _ _; trivial
      · -- counter ≠ 0: keep seeding with the invariant at j + 1
        rename_i _ n _ hn0 heq
        have hWn : clu - (UInt32.ofNat j + 1) = n := by
          rw [List.cons.injEq, Value.i32.injEq] at heq; exact heq.1
        have hj1 : j + 1 < clu.toNat := by
          have hne : (clu - (UInt32.ofNat j + 1)).toNat ≠ 0 := by
            rw [hWn]; exact fun h => hn0 (UInt32.toNat.inj (by rw [h]; rfl))
          rw [hcnt] at hne; omega
        refine ⟨⟨hpg, hgl, j + 1, hj1, ?_, hofs.symm⟩, ?_⟩
        · apply UInt32.toNat.inj
          have e1 : (UInt32.ofNat j).toNat = j := UInt32.toNat_ofNat_of_lt' (by omega)
          have e2 : (UInt32.ofNat (j + 1)).toNat = j + 1 := UInt32.toNat_ofNat_of_lt' (by omega)
          have h4 : (4 : UInt32).toNat = 4 := rfl
          have h8 : (1048448 : UInt32).toNat = 1048448 := rfl
          simp only [UInt32.toNat_add, UInt32.toNat_mul, e1, e2, h4, h8]
          omega
        · rw [hcnt, uint32_sub_toNat_of_nat_le hj.le]; omega
      · -- the residual catch-all arm is unreachable
        rename_i _ _ hc
        exact (hc _ _ rfl).elim

@[proves Project.XorSum.Spec.CheckSpec]
theorem check_correct : CheckSpec := by
  intro env initial seed len hinit
  subst hinit
  -- `func3` is the exported `check` wrapper: pushes both args and calls `func0`.
  apply TerminatesWith.of_wp_entry_for (f := ⟨[.i32, .i32], [], func3, []⟩) rfl
  unfold func3
  wp_run
  apply wp_call_of_terminates (func0_terminates env seed len)
  rintro st' vs rfl
  wp_run
  rfl

end Project.XorSum.Spec
