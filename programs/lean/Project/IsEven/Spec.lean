import Project.IsEven.Program

/-!
# Specification for `is_even`

The unoptimized (opt-level=0) build exports `is_even` as `func1`
(funcIdx 1): a shadow-stack wrapper that spills its argument to linear
memory, calls the body `func0`, masks the result with `& 1`, restores
the stack pointer and returns. `func0` computes `(n %s 2) == 0`
(signed remainder), guarded by a statically dead overflow check
(`(n == 0x80000000) & 0 & 1`, always `0`).

Because both functions write linear memory (shadow-stack spills), the
spec is pinned to the module's canonical instantiation: under an
adversarial store (e.g. zero pages of memory) the spills would trap.
-/

namespace Project.IsEven.Spec

open Wasm

set_option maxRecDepth 1048576

/-- The exported `is_even` returns `1` for even inputs and `0` otherwise.

Informal spec:
For any input `n : UInt32`, the wasm export `is_even` (funcIdx 1)
terminates and leaves a single i32 on the value stack, equal to `1`
when `n` is even and `0` otherwise, when run from the module's
canonical instantiation. -/
@[spec_of "rust-exported" "is_even::is_even"]
def IsEvenSpec : Prop :=
  ∀ (env : HostEnv Unit) (initial : Store Unit) (n : UInt32),
    initial = «module».initialStore →
    TerminatesWith env «module» 1 initial [.i32 n]
      (fun _ rs => rs = [.i32 (if n.toNat % 2 = 0 then 1 else 0)])

/-! ## Signed-rem parity bridge

`func0` tests evenness with `i32.rem_s` (signed remainder, `Int.tmod`
on the two's-complement reading of `n`). Signed remainder by 2 agrees
with unsigned parity on the zero-test: the two's-complement value
differs from `n.toNat` by `2^32`, which is even. -/

private lemma remS_two_eq_zero_iff (n : UInt32) :
    (Int32.ofInt (Int.tmod n.toInt32.toInt 2)).toUInt32 = 0 ↔ n.toNat % 2 = 0 := by
  have h1 : n.toInt32.toInt = ((n.toNat : Int).bmod (2 ^ 32)) := by
    rw [show n.toInt32.toInt = n.toBitVec.toInt from rfl, BitVec.toInt_eq_toNat_bmod]; rfl
  have h2 : ∀ r : Int, (Int32.ofInt r).toUInt32.toNat = (r % (2 ^ 32 : Int)).toNat := fun r => by
    rw [show (Int32.ofInt r).toUInt32.toNat = (BitVec.ofInt 32 r).toNat from rfl,
        BitVec.toNat_ofInt]
    norm_num
  rw [h1, UInt32.ext_iff, h2, Int.tmod_eq_emod, Int.bmod_def]
  simp only [UInt32.toNat_zero]
  split <;> split <;> constructor <;> intro h <;> omega

/-- The body `func0` (funcIdx 0) terminates with `1` iff `n` is even,
at any store whose stack pointer (global 0) has been set to `1048560`
by the exported wrapper's prologue and whose memory has the canonical
17 pages (so the shadow-stack spill at `global0 - 16 + 12` is in
bounds). The final store keeps a nonempty globals list, which the
wrapper's epilogue `globalSet` needs. -/
theorem func0_terminates (env : HostEnv Unit) (st0 : Store Unit) (n : UInt32)
    (hg : st0.globals.globals[0]? = some (.i32 1048560))
    (hpg : st0.mem.pages = 17) :
    TerminatesWith env «module» 0 st0 [.i32 n]
      (fun st' vs => 0 < st'.globals.globals.length ∧
        vs = [.i32 (if n.toNat % 2 = 0 then 1 else 0)]) := by
  apply TerminatesWith.of_wp_entry_for (f := ⟨[.i32], [.i32, .i32], func0, [.i32]⟩) rfl
  unfold func0
  wp_run
  simp [hg, hpg]
  apply wp_block_cons
  wp_run
  simp
  have hlen : 0 < st0.globals.globals.length := by
    rcases List.getElem?_eq_some_iff.mp hg with ⟨h, _⟩; omega
  simp [hlen]
  simp only [remS_two_eq_zero_iff]
  split <;> decide

@[proves Project.IsEven.Spec.IsEvenSpec]
theorem is_even_correct : IsEvenSpec := by
  intro env initial n hinit
  subst hinit
  apply TerminatesWith.of_wp_entry_for (f := ⟨[.i32], [.i32, .i32], func1, [.i32]⟩) rfl
  unfold func1
  wp_run
  have hg : («module».initialStore : Store Unit).globals.globals[0]? = some (.i32 1048576) := by
    rfl
  have hp : («module».initialStore : Store Unit).mem.pages = 17 := by rfl
  simp [hg, hp]
  -- The wrapper's prologue has set the stack pointer (global 0) to
  -- `1048576 - 16 = 1048560` and spilled the argument; dispatch `.call 0`
  -- against the body's behaviour at this exact store.
  refine wp_call_at (Post := fun st' vs =>
      0 < st'.globals.globals.length ∧
        vs = [.i32 (if n.toNat % 2 = 0 then 1 else 0)])
    (func0_terminates env _ n ?_ ?_) ?_
  · have hlen : 0 < («module».initialStore : Store Unit).globals.globals.length := by
      rcases List.getElem?_eq_some_iff.mp hg with ⟨h, _⟩; omega
    simp [hlen]
  · simp [Mem.write32, hp]
  rintro st' vs ⟨hgl, rfl⟩
  wp_run
  simp [List.getElem?_eq_getElem hgl]
  split <;> decide

end Project.IsEven.Spec
