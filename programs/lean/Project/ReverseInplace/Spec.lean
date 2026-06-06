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
        t ≤ count.toNat / 2 ∧
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
      refine ⟨0, 0, Nat.zero_le _, ?_, rfl, rfl, fun j _ => rfl, fun i hi => ?_⟩
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
      --
      -- Outline (the remaining work for this proof):
      --   rintro st s ⟨t, w5, ht, rfl, hg, hp, hframe, hcontent⟩
      --   * The guard `localGet 2; const -1; eq; br_if 2` never fires: from
      --     `t ≤ count.toNat / 2` and `2 ≤ count.toNat`, `l2 = count-1-t ≠ -1`
      --     (its toNat is `count.toNat - 1 - t ∈ [0, count)`), so the `eq`
      --     yields 0 and control stays in the loop body (no `Break 2` → no
      --     `unreachable`/panic).
      --   * The two `store32`s swap cells `t` and `count-1-t` (distinct since
      --     `t < count-1-t` for `t < count.toNat/2`). Use
      --     `read32_write32_same` / `read32_write32_disjoint` and
      --     `write32_bytes_of_disjoint` to update `hcontent`/`hframe`; the
      --     loads are in bounds via `hbound`/`hpg`. The new content matches
      --     `mirrorIdx count.toNat (t+1)` (case-split each `i` on
      --     `i = t`, `i = count-1-t`, else — exactly the `mirrorIdx` cases).
      --   * The pointer/counter updates give the next state with `t+1`
      --     (UInt32 bridging as in the `init` block).
      --   * The final `localGet 5; br_if 0` branches on `l4 <U l2_new`
      --     (`1+t <U count-2-t`):
      --       - continue (`Break 0`): re-establish `Inv` at `t+1`; the measure
      --         `l2.toNat = count-1-t` strictly decreases.
      --       - fall through (`Fallthrough`): `t+1 = count.toNat/2`, so
      --         `mirrorIdx count.toNat (t+1) i = count-1-i` for all `i`
      --         (middle element maps to itself), establishing the post.
      sorry

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
