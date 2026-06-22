import Project.RustU64Tests.Program

/-!
# Reuse tests for the `CodeLib/RustStd/U64` corpus

Two structurally-distinct functions per operator, each using the operator INLINE
the way real client code emits it (no shim, no `.call`). **Every** inlined op is
discharged by rewriting with that op's CodeLib chunk theorem — the op's own
atomic `wp_*` lemma is deliberately NOT in the `simp` set, so the reusable
CodeLib theorem is the only way through (confirm by dropping the chunk lemma: the
proof then fails). This is a CodeLib proof reused on *inlined* client code, which
is the whole point — the same theorem also serves the called export body.

- straight-line + `not`: `add_seq`/`sub_seq`/`mul_seq`/`and_seq`/`or_seq`/
  `xor_seq`/`not_seq`.
- `shl`/`shr`: `shl_seq`/`shr_seq` — the width-specific mask-extend-shift chunk
  (the `b % 64` normalisation is baked into the chunk, so no `bv_decide` here).
- `div`/`rem`: peel the zero-divisor guard `block` (`wp_block_cons`), then reuse
  `div_chunk`/`rem_chunk` for the divide/remainder (`divUI64`/`remUI64` atomics
  excluded). The trailing `+ c` / `* c` reuses `add_seq` / `mul_seq` too.
-/

set_option linter.unusedSimpArgs false

namespace Project.RustU64Tests.Spec

open Wasm Wasm.RustStd Wasm.RustStd.U64

/-! ## add -/
@[spec_of "rust-exported" "rust_u64_tests::add_chain"]
def AddChainSpec : Prop := ∀ (env : HostEnv Unit) (a b c : UInt64),
  TerminatesWith env «module» 0 «module».initialStore [.i64 c, .i64 b, .i64 a]
    (fun _ rs => rs = [.i64 (a + b + c)])
set_option maxRecDepth 4096 in
@[proves Project.RustU64Tests.Spec.AddChainSpec]
theorem add_chain_correct : AddChainSpec := by
  intro env a b c
  apply TerminatesWith.of_wp_entry_for (f := func0Def) rfl
  unfold func0Def func0
  simp only [Function.toLocals, Function.numParams, List.take, List.reverse, List.reverseAux,
    List.map, ValueType.zero, wp_localGet_cons, Locals.get, List.length_cons, List.length_nil,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Nat.reduceAdd, Nat.reduceLT, reduceIte,
    List.drop, add_seq, wp_ret_cons, Continuation.Return.injEq, List.cons.injEq, and_true,
    List.append_nil]

@[spec_of "rust-exported" "rust_u64_tests::add_then_mul"]
def AddThenMulSpec : Prop := ∀ (env : HostEnv Unit) (a b c : UInt64),
  TerminatesWith env «module» 1 «module».initialStore [.i64 c, .i64 b, .i64 a]
    (fun _ rs => rs = [.i64 ((a + b) * c)])
set_option maxRecDepth 4096 in
@[proves Project.RustU64Tests.Spec.AddThenMulSpec]
theorem add_then_mul_correct : AddThenMulSpec := by
  intro env a b c
  apply TerminatesWith.of_wp_entry_for (f := func1Def) rfl
  unfold func1Def func1
  simp only [Function.toLocals, Function.numParams, List.take, List.reverse, List.reverseAux,
    List.map, ValueType.zero, wp_localGet_cons, Locals.get, List.length_cons, List.length_nil,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Nat.reduceAdd, Nat.reduceLT, reduceIte,
    List.drop, add_seq, mul_seq, wp_ret_cons, Continuation.Return.injEq, List.cons.injEq,
    and_true, List.append_nil]

/-! ## sub -/
@[spec_of "rust-exported" "rust_u64_tests::sub_chain"]
def SubChainSpec : Prop := ∀ (env : HostEnv Unit) (a b c : UInt64),
  TerminatesWith env «module» 30 «module».initialStore [.i64 c, .i64 b, .i64 a]
    (fun _ rs => rs = [.i64 (a - b - c)])
set_option maxRecDepth 4096 in
@[proves Project.RustU64Tests.Spec.SubChainSpec]
theorem sub_chain_correct : SubChainSpec := by
  intro env a b c
  apply TerminatesWith.of_wp_entry_for (f := func30Def) rfl
  unfold func30Def func30
  simp only [Function.toLocals, Function.numParams, List.take, List.reverse, List.reverseAux,
    List.map, ValueType.zero, wp_localGet_cons, Locals.get, List.length_cons, List.length_nil,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Nat.reduceAdd, Nat.reduceLT, reduceIte,
    List.drop, sub_seq, wp_ret_cons, Continuation.Return.injEq, List.cons.injEq, and_true,
    List.append_nil]

@[spec_of "rust-exported" "rust_u64_tests::sub_then_add"]
def SubThenAddSpec : Prop := ∀ (env : HostEnv Unit) (a b c : UInt64),
  TerminatesWith env «module» 31 «module».initialStore [.i64 c, .i64 b, .i64 a]
    (fun _ rs => rs = [.i64 ((a - b) + c)])
set_option maxRecDepth 4096 in
@[proves Project.RustU64Tests.Spec.SubThenAddSpec]
theorem sub_then_add_correct : SubThenAddSpec := by
  intro env a b c
  apply TerminatesWith.of_wp_entry_for (f := func31Def) rfl
  unfold func31Def func31
  simp only [Function.toLocals, Function.numParams, List.take, List.reverse, List.reverseAux,
    List.map, ValueType.zero, wp_localGet_cons, Locals.get, List.length_cons, List.length_nil,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Nat.reduceAdd, Nat.reduceLT, reduceIte,
    List.drop, sub_seq, add_seq, wp_ret_cons, Continuation.Return.injEq, List.cons.injEq,
    and_true, List.append_nil]

/-! ## mul -/
@[spec_of "rust-exported" "rust_u64_tests::mul_chain"]
def MulChainSpec : Prop := ∀ (env : HostEnv Unit) (a b c : UInt64),
  TerminatesWith env «module» 16 «module».initialStore [.i64 c, .i64 b, .i64 a]
    (fun _ rs => rs = [.i64 (a * b * c)])
set_option maxRecDepth 4096 in
@[proves Project.RustU64Tests.Spec.MulChainSpec]
theorem mul_chain_correct : MulChainSpec := by
  intro env a b c
  apply TerminatesWith.of_wp_entry_for (f := func16Def) rfl
  unfold func16Def func16
  simp only [Function.toLocals, Function.numParams, List.take, List.reverse, List.reverseAux,
    List.map, ValueType.zero, wp_localGet_cons, Locals.get, List.length_cons, List.length_nil,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Nat.reduceAdd, Nat.reduceLT, reduceIte,
    List.drop, mul_seq, wp_ret_cons, Continuation.Return.injEq, List.cons.injEq, and_true,
    List.append_nil]

@[spec_of "rust-exported" "rust_u64_tests::mul_then_add"]
def MulThenAddSpec : Prop := ∀ (env : HostEnv Unit) (a b c : UInt64),
  TerminatesWith env «module» 17 «module».initialStore [.i64 c, .i64 b, .i64 a]
    (fun _ rs => rs = [.i64 (a * b + c)])
set_option maxRecDepth 4096 in
@[proves Project.RustU64Tests.Spec.MulThenAddSpec]
theorem mul_then_add_correct : MulThenAddSpec := by
  intro env a b c
  apply TerminatesWith.of_wp_entry_for (f := func17Def) rfl
  unfold func17Def func17
  simp only [Function.toLocals, Function.numParams, List.take, List.reverse, List.reverseAux,
    List.map, ValueType.zero, wp_localGet_cons, Locals.get, List.length_cons, List.length_nil,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Nat.reduceAdd, Nat.reduceLT, reduceIte,
    List.drop, mul_seq, add_seq, wp_ret_cons, Continuation.Return.injEq, List.cons.injEq,
    and_true, List.append_nil]

/-! ## bitand -/
@[spec_of "rust-exported" "rust_u64_tests::and_chain"]
def AndChainSpec : Prop := ∀ (env : HostEnv Unit) (a b c : UInt64),
  TerminatesWith env «module» 2 «module».initialStore [.i64 c, .i64 b, .i64 a]
    (fun _ rs => rs = [.i64 (a &&& b &&& c)])
set_option maxRecDepth 4096 in
@[proves Project.RustU64Tests.Spec.AndChainSpec]
theorem and_chain_correct : AndChainSpec := by
  intro env a b c
  apply TerminatesWith.of_wp_entry_for (f := func2Def) rfl
  unfold func2Def func2
  simp only [Function.toLocals, Function.numParams, List.take, List.reverse, List.reverseAux,
    List.map, ValueType.zero, wp_localGet_cons, Locals.get, List.length_cons, List.length_nil,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Nat.reduceAdd, Nat.reduceLT, reduceIte,
    List.drop, and_seq, wp_ret_cons, Continuation.Return.injEq, List.cons.injEq, and_true,
    List.append_nil]

@[spec_of "rust-exported" "rust_u64_tests::and_then_or"]
def AndThenOrSpec : Prop := ∀ (env : HostEnv Unit) (a b c : UInt64),
  TerminatesWith env «module» 3 «module».initialStore [.i64 c, .i64 b, .i64 a]
    (fun _ rs => rs = [.i64 ((a &&& b) ||| c)])
set_option maxRecDepth 4096 in
@[proves Project.RustU64Tests.Spec.AndThenOrSpec]
theorem and_then_or_correct : AndThenOrSpec := by
  intro env a b c
  apply TerminatesWith.of_wp_entry_for (f := func3Def) rfl
  unfold func3Def func3
  simp only [Function.toLocals, Function.numParams, List.take, List.reverse, List.reverseAux,
    List.map, ValueType.zero, wp_localGet_cons, Locals.get, List.length_cons, List.length_nil,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Nat.reduceAdd, Nat.reduceLT, reduceIte,
    List.drop, and_seq, or_seq, wp_ret_cons, Continuation.Return.injEq, List.cons.injEq,
    and_true, List.append_nil]

/-! ## bitor -/
@[spec_of "rust-exported" "rust_u64_tests::or_chain"]
def OrChainSpec : Prop := ∀ (env : HostEnv Unit) (a b c : UInt64),
  TerminatesWith env «module» 22 «module».initialStore [.i64 c, .i64 b, .i64 a]
    (fun _ rs => rs = [.i64 (a ||| b ||| c)])
set_option maxRecDepth 4096 in
@[proves Project.RustU64Tests.Spec.OrChainSpec]
theorem or_chain_correct : OrChainSpec := by
  intro env a b c
  apply TerminatesWith.of_wp_entry_for (f := func22Def) rfl
  unfold func22Def func22
  simp only [Function.toLocals, Function.numParams, List.take, List.reverse, List.reverseAux,
    List.map, ValueType.zero, wp_localGet_cons, Locals.get, List.length_cons, List.length_nil,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Nat.reduceAdd, Nat.reduceLT, reduceIte,
    List.drop, or_seq, wp_ret_cons, Continuation.Return.injEq, List.cons.injEq, and_true,
    List.append_nil]

@[spec_of "rust-exported" "rust_u64_tests::or_then_xor"]
def OrThenXorSpec : Prop := ∀ (env : HostEnv Unit) (a b c : UInt64),
  TerminatesWith env «module» 23 «module».initialStore [.i64 c, .i64 b, .i64 a]
    (fun _ rs => rs = [.i64 ((a ||| b) ^^^ c)])
set_option maxRecDepth 4096 in
@[proves Project.RustU64Tests.Spec.OrThenXorSpec]
theorem or_then_xor_correct : OrThenXorSpec := by
  intro env a b c
  apply TerminatesWith.of_wp_entry_for (f := func23Def) rfl
  unfold func23Def func23
  simp only [Function.toLocals, Function.numParams, List.take, List.reverse, List.reverseAux,
    List.map, ValueType.zero, wp_localGet_cons, Locals.get, List.length_cons, List.length_nil,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Nat.reduceAdd, Nat.reduceLT, reduceIte,
    List.drop, or_seq, xor_seq, wp_ret_cons, Continuation.Return.injEq, List.cons.injEq,
    and_true, List.append_nil]

/-! ## bitxor -/
@[spec_of "rust-exported" "rust_u64_tests::xor_chain"]
def XorChainSpec : Prop := ∀ (env : HostEnv Unit) (a b c : UInt64),
  TerminatesWith env «module» 32 «module».initialStore [.i64 c, .i64 b, .i64 a]
    (fun _ rs => rs = [.i64 (a ^^^ b ^^^ c)])
set_option maxRecDepth 4096 in
@[proves Project.RustU64Tests.Spec.XorChainSpec]
theorem xor_chain_correct : XorChainSpec := by
  intro env a b c
  apply TerminatesWith.of_wp_entry_for (f := func32Def) rfl
  unfold func32Def func32
  simp only [Function.toLocals, Function.numParams, List.take, List.reverse, List.reverseAux,
    List.map, ValueType.zero, wp_localGet_cons, Locals.get, List.length_cons, List.length_nil,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Nat.reduceAdd, Nat.reduceLT, reduceIte,
    List.drop, xor_seq, wp_ret_cons, Continuation.Return.injEq, List.cons.injEq, and_true,
    List.append_nil]

@[spec_of "rust-exported" "rust_u64_tests::xor_then_and"]
def XorThenAndSpec : Prop := ∀ (env : HostEnv Unit) (a b c : UInt64),
  TerminatesWith env «module» 33 «module».initialStore [.i64 c, .i64 b, .i64 a]
    (fun _ rs => rs = [.i64 ((a ^^^ b) &&& c)])
set_option maxRecDepth 4096 in
@[proves Project.RustU64Tests.Spec.XorThenAndSpec]
theorem xor_then_and_correct : XorThenAndSpec := by
  intro env a b c
  apply TerminatesWith.of_wp_entry_for (f := func33Def) rfl
  unfold func33Def func33
  simp only [Function.toLocals, Function.numParams, List.take, List.reverse, List.reverseAux,
    List.map, ValueType.zero, wp_localGet_cons, Locals.get, List.length_cons, List.length_nil,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Nat.reduceAdd, Nat.reduceLT, reduceIte,
    List.drop, xor_seq, and_seq, wp_ret_cons, Continuation.Return.injEq, List.cons.injEq,
    and_true, List.append_nil]

/-! ## not -/
@[spec_of "rust-exported" "rust_u64_tests::not_twice"]
def NotTwiceSpec : Prop := ∀ (env : HostEnv Unit) (a : UInt64),
  TerminatesWith env «module» 21 «module».initialStore [.i64 a]
    (fun _ rs => rs = [.i64 (~~~(~~~a))])
set_option maxRecDepth 4096 in
@[proves Project.RustU64Tests.Spec.NotTwiceSpec]
theorem not_twice_correct : NotTwiceSpec := by
  intro env a
  apply TerminatesWith.of_wp_entry_for (f := func21Def) rfl
  unfold func21Def func21
  simp only [Function.toLocals, Function.numParams, List.take, List.reverse, List.reverseAux,
    List.map, ValueType.zero, wp_localGet_cons, Locals.get, List.length_cons, List.length_nil,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Nat.reduceAdd, Nat.reduceLT, reduceIte,
    List.drop, not_seq, wp_ret_cons, Continuation.Return.injEq, List.cons.injEq, and_true,
    List.append_nil]

@[spec_of "rust-exported" "rust_u64_tests::not_then_xor"]
def NotThenXorSpec : Prop := ∀ (env : HostEnv Unit) (a b : UInt64),
  TerminatesWith env «module» 20 «module».initialStore [.i64 b, .i64 a]
    (fun _ rs => rs = [.i64 ((~~~a) ^^^ b)])
set_option maxRecDepth 4096 in
@[proves Project.RustU64Tests.Spec.NotThenXorSpec]
theorem not_then_xor_correct : NotThenXorSpec := by
  intro env a b
  apply TerminatesWith.of_wp_entry_for (f := func20Def) rfl
  unfold func20Def func20
  simp only [Function.toLocals, Function.numParams, List.take, List.reverse, List.reverseAux,
    List.map, ValueType.zero, wp_localGet_cons, Locals.get, List.length_cons, List.length_nil,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Nat.reduceAdd, Nat.reduceLT, reduceIte,
    List.drop, not_seq, xor_seq, wp_ret_cons, Continuation.Return.injEq, List.cons.injEq,
    and_true, List.append_nil]

/-! ## div (divisor nonzero) — peel the guard, then reuse `div_chunk` -/
@[spec_of "rust-exported" "rust_u64_tests::div_then_add"]
def DivThenAddSpec : Prop := ∀ (env : HostEnv Unit) (a b c : UInt64), b ≠ 0 →
  TerminatesWith env «module» 4 «module».initialStore [.i64 c, .i64 b, .i64 a]
    (fun _ rs => rs = [.i64 (a / b + c)])
set_option maxRecDepth 4096 in
@[proves Project.RustU64Tests.Spec.DivThenAddSpec]
theorem div_then_add_correct : DivThenAddSpec := by
  intro env a b c hb
  apply TerminatesWith.of_wp_entry_for (f := func4Def) rfl
  unfold func4Def func4
  apply wp_block_cons
  have h10 : (1 : UInt32) &&& 0 = 0 := by decide
  simp only [Function.toLocals, Function.numParams, List.take, List.reverse, List.reverseAux,
    List.map, ValueType.zero, wp_localGet_cons, Locals.get, List.length_cons, List.length_nil,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Nat.reduceAdd, Nat.reduceLT, reduceIte,
    List.drop, wp_constI64_cons, wp_eqI64_cons, hb, ↓reduceIte, wp_const_cons, wp_and_cons,
    wp_br_if_cons, h10]
  rw [div_chunk a b _ hb]
  simp only [wp_localGet_cons, Locals.get, List.length_cons, List.length_nil,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Nat.reduceAdd, Nat.reduceLT, reduceIte,
    List.drop, add_seq, wp_ret_cons]
  simp [List.take]

@[spec_of "rust-exported" "rust_u64_tests::div_then_mul"]
def DivThenMulSpec : Prop := ∀ (env : HostEnv Unit) (a b c : UInt64), b ≠ 0 →
  TerminatesWith env «module» 5 «module».initialStore [.i64 c, .i64 b, .i64 a]
    (fun _ rs => rs = [.i64 (a / b * c)])
set_option maxRecDepth 4096 in
@[proves Project.RustU64Tests.Spec.DivThenMulSpec]
theorem div_then_mul_correct : DivThenMulSpec := by
  intro env a b c hb
  apply TerminatesWith.of_wp_entry_for (f := func5Def) rfl
  unfold func5Def func5
  apply wp_block_cons
  have h10 : (1 : UInt32) &&& 0 = 0 := by decide
  simp only [Function.toLocals, Function.numParams, List.take, List.reverse, List.reverseAux,
    List.map, ValueType.zero, wp_localGet_cons, Locals.get, List.length_cons, List.length_nil,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Nat.reduceAdd, Nat.reduceLT, reduceIte,
    List.drop, wp_constI64_cons, wp_eqI64_cons, hb, ↓reduceIte, wp_const_cons, wp_and_cons,
    wp_br_if_cons, h10]
  rw [div_chunk a b _ hb]
  simp only [wp_localGet_cons, Locals.get, List.length_cons, List.length_nil,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Nat.reduceAdd, Nat.reduceLT, reduceIte,
    List.drop, mul_seq, wp_ret_cons]
  simp [List.take]

/-! ## rem (divisor nonzero) -/
@[spec_of "rust-exported" "rust_u64_tests::rem_then_add"]
def RemThenAddSpec : Prop := ∀ (env : HostEnv Unit) (a b c : UInt64), b ≠ 0 →
  TerminatesWith env «module» 24 «module».initialStore [.i64 c, .i64 b, .i64 a]
    (fun _ rs => rs = [.i64 (a % b + c)])
set_option maxRecDepth 4096 in
@[proves Project.RustU64Tests.Spec.RemThenAddSpec]
theorem rem_then_add_correct : RemThenAddSpec := by
  intro env a b c hb
  apply TerminatesWith.of_wp_entry_for (f := func24Def) rfl
  unfold func24Def func24
  apply wp_block_cons
  have h10 : (1 : UInt32) &&& 0 = 0 := by decide
  simp only [Function.toLocals, Function.numParams, List.take, List.reverse, List.reverseAux,
    List.map, ValueType.zero, wp_localGet_cons, Locals.get, List.length_cons, List.length_nil,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Nat.reduceAdd, Nat.reduceLT, reduceIte,
    List.drop, wp_constI64_cons, wp_eqI64_cons, hb, ↓reduceIte, wp_const_cons, wp_and_cons,
    wp_br_if_cons, h10]
  rw [rem_chunk a b _ hb]
  simp only [wp_localGet_cons, Locals.get, List.length_cons, List.length_nil,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Nat.reduceAdd, Nat.reduceLT, reduceIte,
    List.drop, add_seq, wp_ret_cons]
  simp [List.take]

@[spec_of "rust-exported" "rust_u64_tests::rem_then_mul"]
def RemThenMulSpec : Prop := ∀ (env : HostEnv Unit) (a b c : UInt64), b ≠ 0 →
  TerminatesWith env «module» 25 «module».initialStore [.i64 c, .i64 b, .i64 a]
    (fun _ rs => rs = [.i64 (a % b * c)])
set_option maxRecDepth 4096 in
@[proves Project.RustU64Tests.Spec.RemThenMulSpec]
theorem rem_then_mul_correct : RemThenMulSpec := by
  intro env a b c hb
  apply TerminatesWith.of_wp_entry_for (f := func25Def) rfl
  unfold func25Def func25
  apply wp_block_cons
  have h10 : (1 : UInt32) &&& 0 = 0 := by decide
  simp only [Function.toLocals, Function.numParams, List.take, List.reverse, List.reverseAux,
    List.map, ValueType.zero, wp_localGet_cons, Locals.get, List.length_cons, List.length_nil,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Nat.reduceAdd, Nat.reduceLT, reduceIte,
    List.drop, wp_constI64_cons, wp_eqI64_cons, hb, ↓reduceIte, wp_const_cons, wp_and_cons,
    wp_br_if_cons, h10]
  rw [rem_chunk a b _ hb]
  simp only [wp_localGet_cons, Locals.get, List.length_cons, List.length_nil,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Nat.reduceAdd, Nat.reduceLT, reduceIte,
    List.drop, mul_seq, wp_ret_cons]
  simp [List.take]

/-! ## shl / shr — width-specific mask-extend-shift (reusable theorem: `U64.shlBodyWp`) -/
@[spec_of "rust-exported" "rust_u64_tests::shl_then_add"]
def ShlThenAddSpec : Prop := ∀ (env : HostEnv Unit) (a : UInt64) (n : UInt32) (b : UInt64),
  TerminatesWith env «module» 26 «module».initialStore [.i64 b, .i32 n, .i64 a]
    (fun _ rs => rs = [.i64 ((a <<< (n.toUInt64 % 64)) + b)])
set_option maxRecDepth 4096 in
@[proves Project.RustU64Tests.Spec.ShlThenAddSpec]
theorem shl_then_add_correct : ShlThenAddSpec := by
  intro env a n b
  apply TerminatesWith.of_wp_entry_for (f := func26Def) rfl
  unfold func26Def func26
  simp only [Function.toLocals, Function.numParams, List.take, List.reverse, List.reverseAux,
    List.map, ValueType.zero, wp_localGet_cons, Locals.get, List.length_cons, List.length_nil,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Nat.reduceAdd, Nat.reduceLT, reduceIte,
    List.drop, shl_seq, add_seq, wp_ret_cons, Continuation.Return.injEq, List.cons.injEq,
    and_true, List.append_nil]

@[spec_of "rust-exported" "rust_u64_tests::shl_twice"]
def ShlTwiceSpec : Prop := ∀ (env : HostEnv Unit) (a : UInt64) (n m : UInt32),
  TerminatesWith env «module» 27 «module».initialStore [.i32 m, .i32 n, .i64 a]
    (fun _ rs => rs = [.i64 ((a <<< (n.toUInt64 % 64)) <<< (m.toUInt64 % 64))])
set_option maxRecDepth 4096 in
@[proves Project.RustU64Tests.Spec.ShlTwiceSpec]
theorem shl_twice_correct : ShlTwiceSpec := by
  intro env a n m
  apply TerminatesWith.of_wp_entry_for (f := func27Def) rfl
  unfold func27Def func27
  simp only [Function.toLocals, Function.numParams, List.take, List.reverse, List.reverseAux,
    List.map, ValueType.zero, wp_localGet_cons, Locals.get, List.length_cons, List.length_nil,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Nat.reduceAdd, Nat.reduceLT, reduceIte,
    List.drop, shl_seq, wp_ret_cons, Continuation.Return.injEq, List.cons.injEq,
    and_true, List.append_nil]

@[spec_of "rust-exported" "rust_u64_tests::shr_then_sub"]
def ShrThenSubSpec : Prop := ∀ (env : HostEnv Unit) (a : UInt64) (n : UInt32) (b : UInt64),
  TerminatesWith env «module» 28 «module».initialStore [.i64 b, .i32 n, .i64 a]
    (fun _ rs => rs = [.i64 ((a >>> (n.toUInt64 % 64)) - b)])
set_option maxRecDepth 4096 in
@[proves Project.RustU64Tests.Spec.ShrThenSubSpec]
theorem shr_then_sub_correct : ShrThenSubSpec := by
  intro env a n b
  apply TerminatesWith.of_wp_entry_for (f := func28Def) rfl
  unfold func28Def func28
  simp only [Function.toLocals, Function.numParams, List.take, List.reverse, List.reverseAux,
    List.map, ValueType.zero, wp_localGet_cons, Locals.get, List.length_cons, List.length_nil,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Nat.reduceAdd, Nat.reduceLT, reduceIte,
    List.drop, shr_seq, sub_seq, wp_ret_cons, Continuation.Return.injEq, List.cons.injEq,
    and_true, List.append_nil]

@[spec_of "rust-exported" "rust_u64_tests::shr_twice"]
def ShrTwiceSpec : Prop := ∀ (env : HostEnv Unit) (a : UInt64) (n m : UInt32),
  TerminatesWith env «module» 29 «module».initialStore [.i32 m, .i32 n, .i64 a]
    (fun _ rs => rs = [.i64 ((a >>> (n.toUInt64 % 64)) >>> (m.toUInt64 % 64))])
set_option maxRecDepth 4096 in
@[proves Project.RustU64Tests.Spec.ShrTwiceSpec]
theorem shr_twice_correct : ShrTwiceSpec := by
  intro env a n m
  apply TerminatesWith.of_wp_entry_for (f := func29Def) rfl
  unfold func29Def func29
  simp only [Function.toLocals, Function.numParams, List.take, List.reverse, List.reverseAux,
    List.map, ValueType.zero, wp_localGet_cons, Locals.get, List.length_cons, List.length_nil,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Nat.reduceAdd, Nat.reduceLT, reduceIte,
    List.drop, shr_seq, wp_ret_cons, Continuation.Return.injEq, List.cons.injEq,
    and_true, List.append_nil]

/-! ## eq — `(a == b) as u64` reuses the masked chunk `eq_seq` inline (the op's own
atomic `wp_eqI64_cons` is excluded from the `simp` set, so the proof is forced
through `eq_seq`; the trailing arithmetic reuses `add_seq`). -/
@[spec_of "rust-exported" "rust_u64_tests::eq_u64"]
def EqU64Spec : Prop := ∀ (env : HostEnv Unit) (a b c : UInt64),
  TerminatesWith env «module» 7 «module».initialStore [.i64 c, .i64 b, .i64 a]
    (fun _ rs => rs = [.i64 (UInt64.ofNat (if a = b then (1 : UInt32) else 0).toNat + c)])
set_option maxRecDepth 4096 in
@[proves Project.RustU64Tests.Spec.EqU64Spec]
theorem eq_u64_correct : EqU64Spec := by
  intro env a b c
  apply TerminatesWith.of_wp_entry_for (f := func7Def) rfl
  unfold func7Def func7
  simp only [Function.toLocals, Function.numParams, List.take, List.reverse, List.reverseAux,
    List.map, ValueType.zero, wp_localGet_cons, Locals.get, List.length_cons, List.length_nil,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Nat.reduceAdd, Nat.reduceLT, reduceIte,
    List.drop, eq_seq, wp_extendUI32_cons, add_seq, wp_ret_cons, Continuation.Return.injEq,
    List.cons.injEq, and_true, List.append_nil]

@[spec_of "rust-exported" "rust_u64_tests::eq_two"]
def EqTwoSpec : Prop := ∀ (env : HostEnv Unit) (a b c d : UInt64),
  TerminatesWith env «module» 6 «module».initialStore [.i64 d, .i64 c, .i64 b, .i64 a]
    (fun _ rs => rs = [.i64 (UInt64.ofNat (if a = b then (1 : UInt32) else 0).toNat
                          + UInt64.ofNat (if c = d then (1 : UInt32) else 0).toNat)])
set_option maxRecDepth 4096 in
@[proves Project.RustU64Tests.Spec.EqTwoSpec]
theorem eq_two_correct : EqTwoSpec := by
  intro env a b c d
  apply TerminatesWith.of_wp_entry_for (f := func6Def) rfl
  unfold func6Def func6
  simp only [Function.toLocals, Function.numParams, List.take, List.reverse, List.reverseAux,
    List.map, ValueType.zero, wp_localGet_cons, Locals.get, List.length_cons, List.length_nil,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Nat.reduceAdd, Nat.reduceLT, reduceIte,
    List.drop, eq_seq, wp_extendUI32_cons, add_seq, wp_ret_cons, Continuation.Return.injEq,
    List.cons.injEq, and_true, List.append_nil]

end Project.RustU64Tests.Spec
