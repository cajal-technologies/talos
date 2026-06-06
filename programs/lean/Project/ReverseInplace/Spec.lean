import Project.ReverseInplace.Program

/-!
# Specification for `reverse_inplace`

The exported `check(seed, len)` runs two in-place reversers on
identically-seeded buffers — one via the swap-from-both-ends pattern,
one via copy-reversed-into-scratch-then-back — and traps via
`unreachable` iff they disagree on any element. Proving the wasm
export terminates without trapping for every input is therefore the
same as proving the two reversers compute the same permutation on
every seeded buffer.
-/

namespace Project.ReverseInplace.Spec

open Wasm

/-! ## Memory framing lemmas

The `check` body writes the seeded buffers, reverses them, and reads
them back. Reasoning about that needs the basic read-after-write
algebra over the function-model `Mem`: a 32-bit read sees the value of
a same-address 32-bit write, and is unchanged by a disjoint write or
fill. These are generic facts about `Mem`; they belong eventually in
the interpreter, but are developed here while the `reverse_inplace`
proof drives them out. -/

/-- A 32-bit read sees the value of a same-address 32-bit write. -/
theorem read32_write32_same (m : Mem) (a v : UInt32) :
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

/-- A byte outside the 4-byte footprint of a `write32` is unchanged. -/
theorem write32_bytes_of_disjoint (m : Mem) (a v : UInt32) (i : Nat)
    (h : i < a.toNat ∨ a.toNat + 4 ≤ i) :
    (m.write32 a v).bytes i = m.bytes i := by
  simp only [Mem.write32]
  have h0 : i ≠ a.toNat := by omega
  have h1 : i ≠ a.toNat + 1 := by omega
  have h2 : i ≠ a.toNat + 2 := by omega
  have h3 : i ≠ a.toNat + 3 := by omega
  simp [h0, h1, h2, h3]

/-- A 32-bit read is unaffected by a 32-bit write to a disjoint 4-byte
range. -/
theorem read32_write32_disjoint (m : Mem) (a b v : UInt32)
    (h : b.toNat + 4 ≤ a.toNat ∨ a.toNat + 4 ≤ b.toNat) :
    (m.write32 a v).read32 b = m.read32 b := by
  simp only [Mem.read32]
  rw [write32_bytes_of_disjoint m a v b.toNat (by omega),
      write32_bytes_of_disjoint m a v (b.toNat + 1) (by omega),
      write32_bytes_of_disjoint m a v (b.toNat + 2) (by omega),
      write32_bytes_of_disjoint m a v (b.toNat + 3) (by omega)]

/-- A byte outside a `fill` range is unchanged. -/
theorem fill_bytes_of_disjoint (m : Mem) (off len : Nat) (val : UInt8) (i : Nat)
    (h : i < off ∨ off + len ≤ i) :
    (m.fill off len val).bytes i = m.bytes i := by
  simp only [Mem.fill]
  have : ¬ (off ≤ i ∧ i < off + len) := by omega
  simp [this]

/-- A 32-bit read is unaffected by a `fill` over a disjoint range. -/
theorem read32_fill_disjoint (m : Mem) (off len : Nat) (val : UInt8) (b : UInt32)
    (h : b.toNat + 4 ≤ off ∨ off + len ≤ b.toNat) :
    (m.fill off len val).read32 b = m.read32 b := by
  simp only [Mem.read32]
  rw [fill_bytes_of_disjoint m off len val b.toNat (by omega),
      fill_bytes_of_disjoint m off len val (b.toNat + 1) (by omega),
      fill_bytes_of_disjoint m off len val (b.toNat + 2) (by omega),
      fill_bytes_of_disjoint m off len val (b.toNat + 3) (by omega)]

/-- A 32-bit read depends only on its four bytes: if two memories agree
on `[a, a+4)` they agree on `read32 a`. -/
theorem read32_eq_of_bytes (m m' : Mem) (a : UInt32)
    (h0 : m'.bytes a.toNat = m.bytes a.toNat)
    (h1 : m'.bytes (a.toNat + 1) = m.bytes (a.toNat + 1))
    (h2 : m'.bytes (a.toNat + 2) = m.bytes (a.toNat + 2))
    (h3 : m'.bytes (a.toNat + 3) = m.bytes (a.toNat + 3)) :
    m'.read32 a = m.read32 a := by
  simp only [Mem.read32, h0, h1, h2, h3]

@[simp] theorem write32_pages (m : Mem) (a v : UInt32) :
    (m.write32 a v).pages = m.pages := rfl

@[simp] theorem fill_pages (m : Mem) (off len : Nat) (val : UInt8) :
    (m.fill off len val).pages = m.pages := rfl

/-! ## Relational function specs

The internal `reverse_*` functions transform memory *relative to the
pre-call state*: the result buffer is the reversal of whatever was
there on entry. The stock `FuncSpec`/`wp_call_cons` only expose the
final store to the post-condition, so they cannot phrase that. The
relational variant below threads the pre-call store `st0` into both the
pre- and post-condition. The proofs are line-for-line the stock ones
with `st0` carried along. -/

variable {α : Type}

/-- A `FuncSpec` whose pre/post may mention the pre-call store. -/
def FuncSpecR (env : HostEnv α) (m : Module) (id : Nat)
    (Pre : Store α → List Value → Prop) (Post : Store α → Store α → List Value → Prop) : Prop :=
  ∀ args (initial : Store α), Pre initial args →
    ∃ N, ∀ fuel ≥ N, ∃ vs st, run fuel m id initial args env = .Success vs st ∧ Post initial st vs

theorem FuncSpecR.of_wp_body
    {env : HostEnv α} {m : Module} {id : Nat} {f : Function}
    {Pre : Store α → List Value → Prop} {Post : Store α → Store α → List Value → Prop}
    (hf : m.funcs[id - m.imports.length]? = some f)
    (h : ∀ args (initial : Store α), Pre initial args →
      wp m f.body
        (fun c => match c with
          | .Fallthrough st' s' =>
              Post initial st' (s'.values.take f.results.length ++ args.drop f.numParams)
          | .Return st' vs      =>
              Post initial st' (vs.take f.results.length ++ args.drop f.numParams)
          | _                   => False)
        initial (f.toLocals (args.take f.numParams).reverse) env)
    (hImp : m.imports[id]? = none := by rfl) :
    FuncSpecR env m id Pre Post := by
  intro args initial hPre
  have hwp := h args initial hPre
  unfold wp at hwp
  obtain ⟨N, hN⟩ := hwp
  refine ⟨N, fun fuel hfuel => ?_⟩
  have hQ := hN fuel hfuel
  rw [run_eq hImp]
  simp only [hf]
  cases hexec : exec fuel m initial (f.toLocals (args.take f.numParams).reverse) f.body env with
  | Fallthrough st' s' =>
    rw [hexec] at hQ
    exact ⟨s'.values.take f.results.length ++ args.drop f.numParams, st', rfl, hQ⟩
  | Return st' vs =>
    rw [hexec] at hQ
    exact ⟨vs.take f.results.length ++ args.drop f.numParams, st', rfl, hQ⟩
  | Break n st' s' => rw [hexec] at hQ; exact hQ.elim
  | Trap msg => rw [hexec] at hQ; exact hQ.elim
  | Invalid msg => rw [hexec] at hQ; exact hQ.elim
  | OutOfFuel => rw [hexec] at hQ; exact hQ.elim

theorem wp_call_cons_rel {env : HostEnv α} {m : Module}
    {id : Nat} {Pre : Store α → List Value → Prop} {Post : Store α → Store α → List Value → Prop}
    {st : Store α} {s : Locals} {Q : Assertion α} {rest : Program}
    (spec : FuncSpecR env m id Pre Post)
    (hPre : Pre st s.values)
    (hPost : ∀ st' vs, Post st st' vs → wp m rest Q st' { s with values := vs } env) :
    wp m (.call id :: rest) Q st s env := by
  unfold wp
  unfold FuncSpecR at spec
  obtain ⟨Ns, hNs⟩ := spec s.values st hPre
  obtain ⟨vs, st', hRun, hPost_vs⟩ := hNs Ns le_rfl
  have hRun_ne : run Ns m id st s.values env ≠ .OutOfFuel := by rw [hRun]; intro h; cases h
  have hwp_rest := hPost st' vs hPost_vs
  unfold wp at hwp_rest
  obtain ⟨Nr, hNr⟩ := hwp_rest
  refine ⟨max (Ns + 1) (Nr + 1), fun fuel hfuel => ?_⟩
  obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
  have hRun_f : run f m id st s.values env = .Success vs st' := by
    rw [run_fuel_mono (by omega : f ≥ Ns) hRun_ne]; exact hRun
  rw [exec_call_cons, hRun_f]
  exact hNr (f + 1) (by omega)

/-! ## `reverse_fast` (func0): swap-from-both-ends -/

/-- After `s` swap iterations of the two-pointer reversal of a length-`n`
buffer, cell `i` holds the original cell `mirrorIdx n s i`: the mirror
`n-1-i` once `i` falls into the already-swapped prefix `[0,s)` or suffix
`[n-s, n)`, and its original self in the still-untouched middle. -/
def mirrorIdx (n s i : Nat) : Nat := if i < s ∨ n - s ≤ i then n - 1 - i else i

/-- The `toNat` of an in-buffer pointer `base + 4*k` is exactly
`base.toNat + 4*k` (no `UInt32` wraparound), given the 4-byte cell at
that offset fits in memory and memory fits in `UInt32`. -/
theorem toNat_base_add (base : UInt32) (k pages : Nat)
    (hk : base.toNat + 4 * k + 4 ≤ pages * 65536)
    (hpg : pages * 65536 ≤ 4294967296) :
    (base + 4 * UInt32.ofNat k).toNat = base.toNat + 4 * k := by
  simp [UInt32.toNat_add, UInt32.toNat_mul, UInt32.toNat_ofNat]
  omega

/-- `reverse_fast` (func0) reverses the `count` 32-bit words at `base`
in place: the result cell `i` holds the original cell `count-1-i`. It
touches no globals and no byte outside `[base, base + 4*count)`. The
preconditions (`count ≤ 32`, the buffer fits in memory, and the byte
size fits in `UInt32`) hold at the single call site in `check`. -/
theorem func0_spec (env : HostEnv α) (base count : UInt32)
    (hcount : count.toNat ≤ 32) (tail : List Value) :
    FuncSpecR env «module» 0
      (fun st0 args => args = .i32 count :: .i32 base :: tail ∧
        base.toNat + 128 ≤ st0.mem.pages * 65536 ∧
        st0.mem.pages * 65536 ≤ 4294967296)
      (fun st0 st' vs => vs = tail ∧ st'.globals = st0.globals ∧
        st'.mem.pages = st0.mem.pages ∧
        (∀ j, (j < base.toNat ∨ base.toNat + 4 * count.toNat ≤ j) →
            st'.mem.bytes j = st0.mem.bytes j) ∧
        (∀ i, i < count.toNat →
            st'.mem.read32 (base + 4 * UInt32.ofNat i)
              = st0.mem.read32 (base + 4 * UInt32.ofNat (count.toNat - 1 - i)))) := by
  apply FuncSpecR.of_wp_body (f := ⟨[.i32, .i32], [.i32, .i32, .i32, .i32], func0, []⟩) rfl
  rintro args st0 ⟨rfl, hbound, hpg⟩
  unfold func0
  apply wp_block_cons
  apply wp_block_cons
  wp_run
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
    List.length_cons, List.length_nil, List.getElem?_cons_zero, List.getElem?_cons_succ,
    List.set_cons_zero, List.set_cons_succ, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, reduceIte]
  by_cases hc2 : count < 2
  · -- `count < 2`: the early `br_if 0` exits and the buffer is already its
    -- own reversal (length 0 or 1).
    have hlt : count.toNat < 2 := by
      have := (UInt32.lt_iff_toNat_lt).mp hc2; simpa using this
    simp only [hc2, if_true]
    refine ⟨trivial, trivial, trivial, fun _ _ => trivial, ?_⟩
    intro i hi
    have : count.toNat - 1 - i = i := by omega
    rw [this]
  · -- `count ≥ 2`: run the swap-from-both-ends loop.
    have hge : 2 ≤ count.toNat := by
      have h := UInt32.lt_iff_toNat_lt (a := count) (b := 2)
      simp only [show (2 : UInt32).toNat = 2 from rfl] at h
      exact Nat.le_of_not_lt (fun hh => hc2 (h.mpr hh))
    simp only [hc2, if_false]
    apply wp_loop_cons
      (Inv := fun st' s' => ∃ (t : Nat) (w5 : UInt32),
        t < count.toNat / 2 ∧
        s' = { params := [.i32 (base + 4 * UInt32.ofNat t), .i32 count],
               locals := [.i32 (count - 1 - UInt32.ofNat t),
                          .i32 (base + 4 * UInt32.ofNat (count.toNat - 1 - t)),
                          .i32 (1 + UInt32.ofNat t), .i32 w5],
               values := [] } ∧
        st'.globals = st0.globals ∧ st'.mem.pages = st0.mem.pages ∧
        (∀ j, (j < base.toNat ∨ base.toNat + 4 * count.toNat ≤ j) →
            st'.mem.bytes j = st0.mem.bytes j) ∧
        (∀ i, i < count.toNat → st'.mem.read32 (base + 4 * UInt32.ofNat i)
            = st0.mem.read32 (base + 4 * UInt32.ofNat (mirrorIdx count.toNat t i))))
      (μ := fun _ s' => match s'.locals with
        | (.i32 l2 :: _) => l2.toNat
        | _ => 0)
    · -- Invariant holds on entry (`t = 0`, nothing swapped yet).
      refine ⟨0, 0, by omega, ?_, rfl, rfl, fun j _ => rfl, fun i hi => ?_⟩
      · have eP : base + 4 * UInt32.ofNat 0 = base := by
          simp [show UInt32.ofNat 0 = 0 from rfl]
        have e4 : (1 : UInt32) + UInt32.ofNat 0 = 1 := by
          simp [show UInt32.ofNat 0 = 0 from rfl]
        have e2 : count - 1 - UInt32.ofNat 0 = 4294967295 + count := by
          apply UInt32.toNat.inj
          simp only [show UInt32.ofNat 0 = 0 from rfl, UInt32.toNat_add, UInt32.toNat_sub,
            UInt32.toNat_ofNat]
          omega
        have hB : count <<< (2 % 32) = count * 4 := by
          apply UInt32.toNat.inj
          rw [UInt32.toNat_shiftLeft, UInt32.toNat_mul]
          simp [Nat.shiftLeft_eq]
        have hofn : UInt32.ofNat (count.toNat - 1) = count - 1 := by
          apply UInt32.toNat.inj
          simp [UInt32.toNat_ofNat, UInt32.toNat_sub]
          omega
        have e3 : base + (4 : UInt32) * UInt32.ofNat (count.toNat - 1 - 0)
            = (4294967292 : UInt32) + (base + count <<< (2 % 32)) := by
          rw [Nat.sub_zero, hofn, hB]
          apply UInt32.toNat.inj
          simp only [UInt32.toNat_add, UInt32.toNat_mul, UInt32.toNat_sub,
            show ((4 : UInt32).toNat) = 4 from rfl,
            show ((4294967292 : UInt32).toNat) = 4294967292 from rfl,
            show ((1 : UInt32).toNat) = 1 from rfl]
          omega
        rw [eP, e2, e3, e4]
      · have : mirrorIdx count.toNat 0 i = i := by
          simp only [mirrorIdx]; rw [if_neg (by omega)]
        rw [this]
    · -- One iteration preserves the invariant / establishes the post.
      rintro st s ⟨t, w5, ht, rfl, hg, hp, hframe, hcontent⟩
      have hpages : st.mem.pages = st0.mem.pages := hp
      have hpg' : st.mem.pages * 65536 ≤ 4294967296 := by rw [hpages]; omega
      have hb0 : base.toNat + 4 * t + 4 ≤ st.mem.pages * 65536 := by rw [hpages]; omega
      have hb3 : base.toNat + 4 * (count.toNat - 1 - t) + 4 ≤ st.mem.pages * 65536 := by
        rw [hpages]; omega
      have hl0 : (base + 4 * UInt32.ofNat t).toNat = base.toNat + 4 * t :=
        toNat_base_add _ _ _ hb0 hpg'
      have hl3 : (base + 4 * UInt32.ofNat (count.toNat - 1 - t)).toNat
          = base.toNat + 4 * (count.toNat - 1 - t) := toNat_base_add _ _ _ hb3 hpg'
      have hl2 : (count - 1 - UInt32.ofNat t).toNat = count.toNat - 1 - t := by
        simp [UInt32.toNat_sub, UInt32.toNat_ofNat]; omega
      have hl2ne : ¬ (count - 1 - UInt32.ofNat t = 4294967295) := by
        intro h; have h2 := congrArg UInt32.toNat h; rw [hl2] at h2
        simp only [show ((4294967295 : UInt32).toNat) = 4294967295 from rfl] at h2; omega
      have hmir : t < count.toNat - 1 - t := by omega
      have htlt : t < count.toNat := by omega
      wp_run
      simp only [List.length_cons, List.length_nil, List.getElem?_cons_zero,
        List.getElem?_cons_succ, List.set_cons_zero, List.set_cons_succ, Nat.reduceAdd,
        Nat.reduceLT, Nat.reduceSub, reduceIte, hl2ne, hl0, hl3, write32_pages,
        show ((0 : UInt32).toNat) = 0 from rfl]
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      -- content of every cell after the two swaps = the (t+1)-partial reversal
      have hupd : ∀ i, i < count.toNat →
          ((st.mem.write32 (base + 4 * UInt32.ofNat t)
                    (st.mem.read32 (base + 4 * UInt32.ofNat (count.toNat - 1 - t)))).write32
                (base + 4 * UInt32.ofNat (count.toNat - 1 - t))
                (st.mem.read32 (base + 4 * UInt32.ofNat t))).read32 (base + 4 * UInt32.ofNat i)
            = st0.mem.read32 (base + 4 * UInt32.ofNat (mirrorIdx count.toNat (t + 1) i)) := by
        intro i hi
        have hci : (base + 4 * UInt32.ofNat i).toNat = base.toNat + 4 * i :=
          toNat_base_add base i st.mem.pages (by rw [hpages]; omega) hpg'
        by_cases hit : i = t
        · subst hit
          rw [read32_write32_disjoint _ _ _ _ (by rw [hl0, hl3]; omega), read32_write32_same]
          have hm : mirrorIdx count.toNat (i + 1) i = count.toNat - 1 - i := by
            simp only [mirrorIdx]; rw [if_pos (by omega)]
          rw [hm, hcontent (count.toNat - 1 - i) (by omega)]
          have hm2 : mirrorIdx count.toNat i (count.toNat - 1 - i) = count.toNat - 1 - i := by
            simp only [mirrorIdx]; rw [if_neg (by omega)]
          rw [hm2]
        · by_cases hic : i = count.toNat - 1 - t
          · subst hic
            rw [read32_write32_same]
            have hm : mirrorIdx count.toNat (t + 1) (count.toNat - 1 - t) = t := by
              simp only [mirrorIdx]; rw [if_pos (by omega)]; omega
            rw [hm, hcontent t (by omega)]
            have hm2 : mirrorIdx count.toNat t t = t := by
              simp only [mirrorIdx]; rw [if_neg (by omega)]
            rw [hm2]
          · rw [read32_write32_disjoint _ _ _ _ (by rw [hci, hl3]; omega),
                read32_write32_disjoint _ _ _ _ (by rw [hci, hl0]; omega), hcontent i hi]
            have hm : mirrorIdx count.toNat (t + 1) i = mirrorIdx count.toNat t i := by
              simp only [mirrorIdx]
              by_cases h1 : i < t ∨ count.toNat - t ≤ i
              · rw [if_pos h1, if_pos (by omega)]
              · rw [if_neg h1, if_neg (by omega)]
            rw [hm]
      -- bytes outside the buffer are untouched by the two swaps
      have hframe' : ∀ j, (j < base.toNat ∨ base.toNat + 4 * count.toNat ≤ j) →
          ((st.mem.write32 (base + 4 * UInt32.ofNat t)
                    (st.mem.read32 (base + 4 * UInt32.ofNat (count.toNat - 1 - t)))).write32
                (base + 4 * UInt32.ofNat (count.toNat - 1 - t))
                (st.mem.read32 (base + 4 * UInt32.ofNat t))).bytes j = st0.mem.bytes j := by
        intro j hj
        rw [write32_bytes_of_disjoint _ _ _ _ (by rw [hl3]; omega),
            write32_bytes_of_disjoint _ _ _ _ (by rw [hl0]; omega)]
        exact hframe j hj
      have hz : ∀ a : UInt32, a + 0 = a := fun a => by
        apply UInt32.toNat.inj; simp
      simp only [hz]
      -- the continue test `1+t <U (count-1-t)-1` reduces to a Nat comparison
      have hl1 : (1 + UInt32.ofNat t).toNat = 1 + t := by
        simp [UInt32.toNat_add, UInt32.toNat_ofNat]; omega
      have hl2m1 : (4294967295 + (count - 1 - UInt32.ofNat t)).toNat = count.toNat - 2 - t := by
        rw [UInt32.toNat_add, hl2]
        simp only [show ((4294967295 : UInt32).toNat) = 4294967295 from rfl]; omega
      have hcondN :
          (1 + UInt32.ofNat t < 4294967295 + (count - 1 - UInt32.ofNat t)) ↔ 2 * t + 4 ≤ count.toNat := by
        rw [UInt32.lt_iff_toNat_lt, hl1, hl2m1]; omega
      by_cases hcond : (1 : UInt32) + UInt32.ofNat t < 4294967295 + (count - 1 - UInt32.ofNat t)
      · -- continue: re-establish the invariant at `t + 1`
        have hcN : 2 * t + 4 ≤ count.toNat := hcondN.mp hcond
        simp (config := {decide := true}) only [if_pos hcond]
        refine ⟨⟨t + 1, (1 : UInt32), ?_, ?_, hg, hp, hframe', hupd⟩, ?_⟩
        · -- t + 1 < count.toNat / 2
          omega
        · -- state equality (UInt32 pointer/counter bridging)
          have hp4 : (4 : UInt32) + (base + 4 * UInt32.ofNat t) = base + 4 * UInt32.ofNat (t + 1) := by
            apply UInt32.toNat.inj
            rw [UInt32.toNat_add, hl0,
              toNat_base_add base (t + 1) st.mem.pages (by rw [hpages]; omega) hpg']
            simp only [show ((4 : UInt32).toNat) = 4 from rfl]; omega
          have hp2 : (4294967295 : UInt32) + (count - 1 - UInt32.ofNat t)
              = count - 1 - UInt32.ofNat (t + 1) := by
            apply UInt32.toNat.inj
            rw [hl2m1]
            simp [UInt32.toNat_sub, UInt32.toNat_ofNat]; omega
          have hp3 : (4294967292 : UInt32) + (base + 4 * UInt32.ofNat (count.toNat - 1 - t))
              = base + 4 * UInt32.ofNat (count.toNat - 1 - (t + 1)) := by
            apply UInt32.toNat.inj
            rw [UInt32.toNat_add, hl3,
              toNat_base_add base (count.toNat - 1 - (t + 1)) st.mem.pages (by rw [hpages]; omega) hpg']
            simp only [show ((4294967292 : UInt32).toNat) = 4294967292 from rfl]; omega
          have hp1 : (1 : UInt32) + (1 + UInt32.ofNat t) = 1 + UInt32.ofNat (t + 1) := by
            apply UInt32.toNat.inj
            simp [UInt32.toNat_add, UInt32.toNat_ofNat]; omega
          rw [hp4, hp2, hp3, hp1, List.append_nil]
        · -- measure strictly decreases
          rw [hl2m1, hl2]; omega
      · -- exit: the buffer is now fully reversed
        have hcf : count.toNat ≤ 2 * t + 3 := by
          by_contra h; exact hcond (hcondN.mpr (by omega))
        simp (config := {decide := true}) only [if_neg hcond]
        refine ⟨trivial, hg, hp, hframe', ?_⟩
        intro i hi
        have hmir2 : mirrorIdx count.toNat (t + 1) i = count.toNat - 1 - i := by
          simp only [mirrorIdx]; split
          · rfl
          · omega
        rw [hupd i hi, hmir2]

/-! ## `reverse_naive` (func1): copy-reversed-into-scratch then back -/

set_option maxRecDepth 4000 in
/-- `reverse_naive` (func1) reverses the `count` 32-bit words at `base`
in place by copying them reversed into a 128-byte shadow-stack scratch
buffer at `global0 − 128` and copying back. The result cell `i` holds
the original cell `count-1-i`. It leaves `global0` and every byte
outside the buffer *and* the scratch untouched. The single call site in
`check` supplies a scratch region disjoint from the buffer. -/
theorem func1_spec (env : HostEnv α) (base count sp : UInt32)
    (hcount : count.toNat ≤ 32) (tail : List Value) :
    FuncSpecR env «module» 1
      (fun st0 args => args = .i32 count :: .i32 base :: tail ∧
        st0.globals.globals[0]? = some (.i32 sp) ∧
        128 ≤ sp.toNat ∧ sp.toNat ≤ st0.mem.pages * 65536 ∧
        base.toNat + 128 ≤ st0.mem.pages * 65536 ∧
        st0.mem.pages * 65536 ≤ 4294967296 ∧
        (base.toNat + 128 ≤ sp.toNat - 128 ∨ sp.toNat ≤ base.toNat))
      (fun st0 st' vs => vs = tail ∧ st'.globals = st0.globals ∧
        st'.mem.pages = st0.mem.pages ∧
        (∀ j, (j < sp.toNat - 128 ∨ sp.toNat ≤ j) →
            (j < base.toNat ∨ base.toNat + 4 * count.toNat ≤ j) →
            st'.mem.bytes j = st0.mem.bytes j) ∧
        (∀ i, i < count.toNat →
            st'.mem.read32 (base + 4 * UInt32.ofNat i)
              = st0.mem.read32 (base + 4 * UInt32.ofNat (count.toNat - 1 - i)))) := by
  apply FuncSpecR.of_wp_body (f := ⟨[.i32, .i32], [.i32, .i32, .i32, .i32], func1, []⟩) rfl
  rintro args st0 ⟨rfl, hsp, hsp128, hspb, hbb, hpgb, hdisj⟩
  unfold func1
  wp_run
  rw [hsp]
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
    List.length_cons, List.length_nil, List.getElem?_cons_zero, List.getElem?_cons_succ,
    List.set_cons_zero, List.set_cons_succ, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, reduceIte,
    show ((128 : UInt32).toNat) = 128 from rfl]
  have hsm : (sp - 128).toNat = sp.toNat - 128 := by
    rw [UInt32.toNat_sub]; simp [show ((128 : UInt32).toNat) = 128 from rfl]; omega
  rw [hsm, if_neg (by omega)]
  apply wp_block_cons
  wp_run
  simp only [List.length_cons, List.length_nil, List.getElem?_cons_zero, List.getElem?_cons_succ,
    List.set_cons_zero, List.set_cons_succ, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, reduceIte]
  split
  · -- `count ≥ 1`: copy reversed into scratch (L1), then back (L2).
    rename_i vs heq
    simp only [List.cons.injEq, Value.i32.injEq] at heq
    have hc0 : count ≠ 0 := by
      intro h; rw [if_pos h] at heq; exact absurd heq.1 (by decide)
    have hcpos : 1 ≤ count.toNat := by
      rcases Nat.eq_zero_or_pos count.toNat with h | h
      · exact absurd (UInt32.toNat.inj (by rw [h]; rfl)) hc0
      · exact h
    obtain ⟨-, rfl⟩ := heq
    have hsub0 : ∀ x : UInt32, x - 0 = x := fun x => by
      apply UInt32.toNat.inj; simp
    have hadd0 : ∀ x : UInt32, x + 0 = x := fun x => by
      apply UInt32.toNat.inj; simp
    have hz0 : (4 : UInt32) * UInt32.ofNat 0 = 0 := by decide
    have hb4 : (4294967292 : UInt32) + base = base - 4 := by
      apply UInt32.toNat.inj
      simp [UInt32.toNat_add, UInt32.toNat_sub]
    -- L1: copy reversed into scratch `[sp-128, sp)`.
    apply wp_loop_cons
      (Inv := fun st' s' => ∃ k, k < count.toNat ∧
        s' = { params := [.i32 base, .i32 count],
               locals := [.i32 (sp - 128), .i32 (count <<< (2 % 32) - 4 * UInt32.ofNat k),
                          .i32 (base - 4), .i32 (sp - 128 + 4 * UInt32.ofNat k)],
               values := [] } ∧
          st'.globals = st0.globals ∧ st'.mem.pages = st0.mem.pages ∧
          (∀ j, (j < sp.toNat - 128 ∨ sp.toNat ≤ j) → st'.mem.bytes j = st0.mem.bytes j) ∧
          (∀ jj, jj < k → st'.mem.read32 (sp - 128 + 4 * UInt32.ofNat jj)
              = st0.mem.read32 (base + 4 * UInt32.ofNat (count.toNat - 1 - jj))))
      (μ := fun _ s' => match s'.locals with
        | _ :: .i32 l3 :: _ => l3.toNat
        | _ => 0)
    · -- entry (k = 0): scratch only holds the fill
      refine ⟨0, by omega, ?_, rfl, rfl, ?_, ?_⟩
      · simp only [hz0, hsub0, hadd0, hb4]
      · intro j hj; exact fill_bytes_of_disjoint _ _ _ _ j (by omega)
      · intro jj hjj; omega
    · rintro st s ⟨k, hk, rfl, hg', hp', hframe1, hscr⟩
      have hpg2 : st.mem.pages * 65536 ≤ 4294967296 := by rw [hp']; omega
      have hcw : count <<< (2 % 32) = count * 4 := by
        apply UInt32.toNat.inj
        rw [UInt32.toNat_shiftLeft, UInt32.toNat_mul]; simp [Nat.shiftLeft_eq]
      have haddr : count <<< (2 % 32) - (4 : UInt32) * UInt32.ofNat k + (base - 4)
          = base + (4 : UInt32) * UInt32.ofNat (count.toNat - 1 - k) := by
        apply UInt32.toNat.inj
        rw [hcw, toNat_base_add base (count.toNat - 1 - k) st.mem.pages (by rw [hp']; omega) hpg2]
        simp [UInt32.toNat_add, UInt32.toNat_sub, UInt32.toNat_mul, UInt32.toNat_ofNat]
        omega
      have hl5 : (sp - 128 + 4 * UInt32.ofNat k).toNat = sp.toNat - 128 + 4 * k := by
        rw [UInt32.toNat_add, hsm, UInt32.toNat_mul, UInt32.toNat_ofNat]; simp; omega
      have hbL : base.toNat + 4 * (count.toNat - 1 - k) + 4 ≤ st.mem.pages * 65536 := by
        rw [hp']; omega
      have haddrN : (count <<< (2 % 32) - (4 : UInt32) * UInt32.ofNat k + (base - 4)).toNat
          = base.toNat + 4 * (count.toNat - 1 - k) := by
        rw [haddr, toNat_base_add base (count.toNat - 1 - k) st.mem.pages hbL hpg2]
      wp_run
      simp only [List.length_cons, List.length_nil, List.getElem?_cons_zero,
        List.getElem?_cons_succ, List.set_cons_zero, List.set_cons_succ, Nat.reduceAdd,
        Nat.reduceLT, Nat.reduceSub, reduceIte, show ((0 : UInt32).toNat) = 0 from rfl]
      rw [if_neg (by rw [haddrN]; omega), if_neg (by rw [hl5]; omega)]
      split
      · -- fallthrough: scratch fully written; copy back (L2)
        rename_i vs heq
        simp only [List.cons.injEq, Value.i32.injEq] at heq
        simp only [hadd0]
        have hl3v : (count <<< (2 % 32) - 4 * UInt32.ofNat k).toNat = 4 * (count.toNat - k) := by
          rw [hcw]; simp [UInt32.toNat_sub, UInt32.toNat_mul, UInt32.toNat_ofNat]; omega
        have hkeq : k + 1 = count.toNat := by
          have h2 : ((4294967292 : UInt32) + (count <<< (2 % 32) - (4 : UInt32) * UInt32.ofNat k)).toNat = 0 := by
            rw [heq.1]; rfl
          rw [UInt32.toNat_add, hl3v] at h2
          simp only [show ((4294967292 : UInt32).toNat) = 4294967292 from rfl] at h2
          omega
        have hMpages :
            (st.mem.write32 (sp - 128 + 4 * UInt32.ofNat k)
                (st.mem.read32 (count <<< (2 % 32) - 4 * UInt32.ofNat k + (base - 4)))).pages = st0.mem.pages := by
          rw [write32_pages]; exact hp'
        have hframeM : ∀ j, (j < sp.toNat - 128 ∨ sp.toNat ≤ j) →
            (st.mem.write32 (sp - 128 + 4 * UInt32.ofNat k)
                (st.mem.read32 (count <<< (2 % 32) - 4 * UInt32.ofNat k + (base - 4)))).bytes j
              = st0.mem.bytes j := by
          intro j hj
          rw [write32_bytes_of_disjoint _ _ _ _ (by rw [hl5]; omega)]; exact hframe1 j hj
        have hfull : ∀ jj, jj < count.toNat →
            (st.mem.write32 (sp - 128 + 4 * UInt32.ofNat k)
                (st.mem.read32 (count <<< (2 % 32) - 4 * UInt32.ofNat k + (base - 4)))).read32
                (sp - 128 + 4 * UInt32.ofNat jj)
              = st0.mem.read32 (base + 4 * UInt32.ofNat (count.toNat - 1 - jj)) := by
          intro jj hjj
          rcases Nat.lt_or_ge jj k with hlt | hge
          · have hjjN : (sp - 128 + 4 * UInt32.ofNat jj).toNat = sp.toNat - 128 + 4 * jj := by
              rw [UInt32.toNat_add, hsm, UInt32.toNat_mul, UInt32.toNat_ofNat]; simp; omega
            rw [read32_write32_disjoint _ _ _ _ (by rw [hjjN, hl5]; omega)]
            exact hscr jj hlt
          · have hjk : jj = k := by omega
            subst hjk
            rw [read32_write32_same, haddr]
            have hX : (base + 4 * UInt32.ofNat (count.toNat - 1 - jj)).toNat
                = base.toNat + 4 * (count.toNat - 1 - jj) :=
              toNat_base_add base (count.toNat - 1 - jj) st.mem.pages hbL hpg2
            exact read32_eq_of_bytes st0.mem st.mem _
              (by rw [hX]; exact hframe1 _ (by omega))
              (by rw [hX]; exact hframe1 _ (by omega))
              (by rw [hX]; exact hframe1 _ (by omega))
              (by rw [hX]; exact hframe1 _ (by omega))
        -- L2: copy scratch back to the buffer.
        apply wp_loop_cons
          (Inv := fun st' s' => ∃ m, m ≤ count.toNat ∧
            s' = { params := [.i32 (base + 4 * UInt32.ofNat m), .i32 (count - UInt32.ofNat m)],
                   locals := [.i32 (sp - 128), .i32 (sp - 128 + 4 * UInt32.ofNat m), .i32 (base - 4),
                              .i32 (4 + (sp - 128 + 4 * UInt32.ofNat k))],
                   values := [] } ∧
              st'.globals = st0.globals ∧ st'.mem.pages = st0.mem.pages ∧
              (∀ j, (j < sp.toNat - 128 ∨ sp.toNat ≤ j) →
                  (j < base.toNat ∨ base.toNat + 4 * count.toNat ≤ j) → st'.mem.bytes j = st0.mem.bytes j) ∧
              (∀ jj, jj < count.toNat → st'.mem.read32 (sp - 128 + 4 * UInt32.ofNat jj)
                  = st0.mem.read32 (base + 4 * UInt32.ofNat (count.toNat - 1 - jj))) ∧
              (∀ i, i < m → st'.mem.read32 (base + 4 * UInt32.ofNat i)
                  = st0.mem.read32 (base + 4 * UInt32.ofNat (count.toNat - 1 - i))))
          (μ := fun _ s' => match s'.params with
            | _ :: .i32 l1 :: _ => l1.toNat
            | _ => 0)
        · -- entry (m = 0)
          refine ⟨0, Nat.zero_le _, ?_, hg', hMpages, fun j hj _ => hframeM j hj, hfull, ?_⟩
          · simp only [show UInt32.ofNat 0 = 0 from rfl, show (4 : UInt32) * 0 = 0 from by decide,
              hadd0, hsub0, List.append_nil]
          · intro i hi; omega
        · sorry
      · -- continue: re-establish L1 invariant at `k + 1`
        rename_i n vs hn heq
        simp only [List.cons.injEq, Value.i32.injEq] at heq
        simp only [hadd0]
        have hl3v : (count <<< (2 % 32) - 4 * UInt32.ofNat k).toNat = 4 * (count.toNat - k) := by
          rw [hcw]; simp [UInt32.toNat_sub, UInt32.toNat_mul, UInt32.toNat_ofNat]; omega
        have hkc : k + 1 < count.toNat := by
          by_contra h
          have hkk : count.toNat - k = 1 := by omega
          apply hn; rw [← heq.1]; apply UInt32.toNat.inj
          rw [UInt32.toNat_add, hl3v, hkk]; simp
        have hsl3 : (4294967292 : UInt32) + (count <<< (2 % 32) - (4 : UInt32) * UInt32.ofNat k)
            = count <<< (2 % 32) - (4 : UInt32) * UInt32.ofNat (k + 1) := by
          apply UInt32.toNat.inj
          rw [hcw]; simp [UInt32.toNat_add, UInt32.toNat_sub, UInt32.toNat_mul, UInt32.toNat_ofNat]; omega
        have hsl5 : (4 : UInt32) + (sp - 128 + 4 * UInt32.ofNat k)
            = sp - 128 + 4 * UInt32.ofNat (k + 1) := by
          apply UInt32.toNat.inj
          simp [UInt32.toNat_add, hl5, hsm, UInt32.toNat_mul, UInt32.toNat_ofNat]; omega
        refine ⟨⟨k + 1, hkc, by rw [hsl3, hsl5, List.append_nil], hg',
          by rw [write32_pages]; exact hp', ?_, ?_⟩, ?_⟩
        · -- frame: write at scratch cell k preserves bytes outside scratch
          intro j hj
          rw [write32_bytes_of_disjoint _ _ _ _ (by rw [hl5]; omega)]
          exact hframe1 j hj
        · -- content: scratch[jj] for jj < k+1
          intro jj hjj
          rcases Nat.lt_succ_iff_lt_or_eq.mp hjj with hlt | rfl
          · have hjjN : (sp - 128 + 4 * UInt32.ofNat jj).toNat = sp.toNat - 128 + 4 * jj := by
              rw [UInt32.toNat_add, hsm, UInt32.toNat_mul, UInt32.toNat_ofNat]; simp; omega
            rw [read32_write32_disjoint _ _ _ _ (by rw [hjjN, hl5]; omega)]
            exact hscr jj hlt
          · rw [read32_write32_same, haddr]
            have hX : (base + 4 * UInt32.ofNat (count.toNat - 1 - jj)).toNat
                = base.toNat + 4 * (count.toNat - 1 - jj) :=
              toNat_base_add base (count.toNat - 1 - jj) st.mem.pages hbL hpg2
            exact read32_eq_of_bytes st0.mem st.mem _
              (by rw [hX]; exact hframe1 _ (by omega))
              (by rw [hX]; exact hframe1 _ (by omega))
              (by rw [hX]; exact hframe1 _ (by omega))
              (by rw [hX]; exact hframe1 _ (by omega))
        · -- measure strictly decreases
          rw [hl3v]
          have hm : ((4294967292 : UInt32) + (count <<< (2 % 32) - (4 : UInt32) * UInt32.ofNat k)).toNat
              = 4 * (count.toNat - k) - 4 := by
            rw [hcw]; simp [UInt32.toNat_add, UInt32.toNat_sub, UInt32.toNat_mul, UInt32.toNat_ofNat]; omega
          rw [hm]; omega
      · rename_i hne1 hne2; exact hne2 _ _ rfl
  · -- `count = 0`: nothing to do; only the scratch fill changed memory.
    rename_i n vs hn heq
    simp only [List.cons.injEq, Value.i32.injEq] at heq
    have hc0 : count = 0 := by
      by_contra h; rw [if_neg h] at heq; exact hn heq.1.symm
    rw [hc0]
    refine ⟨trivial, trivial, rfl, ?_, ?_⟩
    · intro j hj _
      exact fill_bytes_of_disjoint _ _ _ _ j (by omega)
    · intro i hi; simp at hi
  · -- impossible: the scrutinee is a singleton cons.
    rename_i hne1 hne2
    exact hne2 _ _ rfl

/-- The exported `check` terminates without trapping (and returns no
values) on every `(seed, len)` input.

Informal spec:
For any `seed len : UInt32`, the wasm export `check`, run on a freshly
instantiated module, terminates and leaves an empty value stack.
Termination-without-trapping is the whole content of the spec — the
body traps via `unreachable` iff the swap-from-both-ends and
copy-reversed reversers disagree, so this property *is* the equivalence
claim between the two implementations.

The store is `Module.initialStore «module»` (a fresh instantiation):
`check` builds its scratch buffers on the shadow stack at
`global0 − 256` and touches `[global0 − 384, global0)`, so it can only
be trap-free given a well-formed stack pointer and enough memory pages.
The fresh instantiation pins `global0 = 1048576` and `pages = 17`,
which is exactly the contract under which the export is called. -/
@[spec_of "rust-exported" "reverse_inplace::check"]
def CheckSpec : Prop :=
  ∀ (env : HostEnv Unit) (seed len : UInt32),
    TerminatesWith env «module» 3 (Module.initialStore «module») [.i32 len, .i32 seed]
      (fun _ rs => rs = [])

end Project.ReverseInplace.Spec
