import Project.RustU64Tests.Program
import Interpreter.Wasm.Wp.Call

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
  TerminatesWith env «module» 4 «module».initialStore [.i64 c, .i64 b, .i64 a]
    (fun _ rs => rs = [.i64 (a + b + c)])
set_option maxRecDepth 4096 in
@[proves Project.RustU64Tests.Spec.AddChainSpec]
theorem add_chain_correct : AddChainSpec := by
  intro env a b c
  apply TerminatesWith.of_wp_entry_for (f := func4Def) rfl
  unfold func4Def func4
  simp only [Function.toLocals, Function.numParams, List.take, List.reverse, List.reverseAux,
    List.map, ValueType.zero, wp_localGet_cons, Locals.get, List.length_cons, List.length_nil,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Nat.reduceAdd, Nat.reduceLT, reduceIte,
    List.drop, add_seq, wp_ret_cons, Continuation.Return.injEq, List.cons.injEq, and_true,
    List.append_nil]

@[spec_of "rust-exported" "rust_u64_tests::add_then_mul"]
def AddThenMulSpec : Prop := ∀ (env : HostEnv Unit) (a b c : UInt64),
  TerminatesWith env «module» 5 «module».initialStore [.i64 c, .i64 b, .i64 a]
    (fun _ rs => rs = [.i64 ((a + b) * c)])
set_option maxRecDepth 4096 in
@[proves Project.RustU64Tests.Spec.AddThenMulSpec]
theorem add_then_mul_correct : AddThenMulSpec := by
  intro env a b c
  apply TerminatesWith.of_wp_entry_for (f := func5Def) rfl
  unfold func5Def func5
  simp only [Function.toLocals, Function.numParams, List.take, List.reverse, List.reverseAux,
    List.map, ValueType.zero, wp_localGet_cons, Locals.get, List.length_cons, List.length_nil,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Nat.reduceAdd, Nat.reduceLT, reduceIte,
    List.drop, add_seq, mul_seq, wp_ret_cons, Continuation.Return.injEq, List.cons.injEq,
    and_true, List.append_nil]

/-! ## sub -/
@[spec_of "rust-exported" "rust_u64_tests::sub_chain"]
def SubChainSpec : Prop := ∀ (env : HostEnv Unit) (a b c : UInt64),
  TerminatesWith env «module» 40 «module».initialStore [.i64 c, .i64 b, .i64 a]
    (fun _ rs => rs = [.i64 (a - b - c)])
set_option maxRecDepth 4096 in
@[proves Project.RustU64Tests.Spec.SubChainSpec]
theorem sub_chain_correct : SubChainSpec := by
  intro env a b c
  apply TerminatesWith.of_wp_entry_for (f := func40Def) rfl
  unfold func40Def func40
  simp only [Function.toLocals, Function.numParams, List.take, List.reverse, List.reverseAux,
    List.map, ValueType.zero, wp_localGet_cons, Locals.get, List.length_cons, List.length_nil,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Nat.reduceAdd, Nat.reduceLT, reduceIte,
    List.drop, sub_seq, wp_ret_cons, Continuation.Return.injEq, List.cons.injEq, and_true,
    List.append_nil]

@[spec_of "rust-exported" "rust_u64_tests::sub_then_add"]
def SubThenAddSpec : Prop := ∀ (env : HostEnv Unit) (a b c : UInt64),
  TerminatesWith env «module» 41 «module».initialStore [.i64 c, .i64 b, .i64 a]
    (fun _ rs => rs = [.i64 ((a - b) + c)])
set_option maxRecDepth 4096 in
@[proves Project.RustU64Tests.Spec.SubThenAddSpec]
theorem sub_then_add_correct : SubThenAddSpec := by
  intro env a b c
  apply TerminatesWith.of_wp_entry_for (f := func41Def) rfl
  unfold func41Def func41
  simp only [Function.toLocals, Function.numParams, List.take, List.reverse, List.reverseAux,
    List.map, ValueType.zero, wp_localGet_cons, Locals.get, List.length_cons, List.length_nil,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Nat.reduceAdd, Nat.reduceLT, reduceIte,
    List.drop, sub_seq, add_seq, wp_ret_cons, Continuation.Return.injEq, List.cons.injEq,
    and_true, List.append_nil]

/-! ## mul -/
@[spec_of "rust-exported" "rust_u64_tests::mul_chain"]
def MulChainSpec : Prop := ∀ (env : HostEnv Unit) (a b c : UInt64),
  TerminatesWith env «module» 26 «module».initialStore [.i64 c, .i64 b, .i64 a]
    (fun _ rs => rs = [.i64 (a * b * c)])
set_option maxRecDepth 4096 in
@[proves Project.RustU64Tests.Spec.MulChainSpec]
theorem mul_chain_correct : MulChainSpec := by
  intro env a b c
  apply TerminatesWith.of_wp_entry_for (f := func26Def) rfl
  unfold func26Def func26
  simp only [Function.toLocals, Function.numParams, List.take, List.reverse, List.reverseAux,
    List.map, ValueType.zero, wp_localGet_cons, Locals.get, List.length_cons, List.length_nil,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Nat.reduceAdd, Nat.reduceLT, reduceIte,
    List.drop, mul_seq, wp_ret_cons, Continuation.Return.injEq, List.cons.injEq, and_true,
    List.append_nil]

@[spec_of "rust-exported" "rust_u64_tests::mul_then_add"]
def MulThenAddSpec : Prop := ∀ (env : HostEnv Unit) (a b c : UInt64),
  TerminatesWith env «module» 27 «module».initialStore [.i64 c, .i64 b, .i64 a]
    (fun _ rs => rs = [.i64 (a * b + c)])
set_option maxRecDepth 4096 in
@[proves Project.RustU64Tests.Spec.MulThenAddSpec]
theorem mul_then_add_correct : MulThenAddSpec := by
  intro env a b c
  apply TerminatesWith.of_wp_entry_for (f := func27Def) rfl
  unfold func27Def func27
  simp only [Function.toLocals, Function.numParams, List.take, List.reverse, List.reverseAux,
    List.map, ValueType.zero, wp_localGet_cons, Locals.get, List.length_cons, List.length_nil,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Nat.reduceAdd, Nat.reduceLT, reduceIte,
    List.drop, mul_seq, add_seq, wp_ret_cons, Continuation.Return.injEq, List.cons.injEq,
    and_true, List.append_nil]

/-! ## bitand -/
@[spec_of "rust-exported" "rust_u64_tests::and_chain"]
def AndChainSpec : Prop := ∀ (env : HostEnv Unit) (a b c : UInt64),
  TerminatesWith env «module» 6 «module».initialStore [.i64 c, .i64 b, .i64 a]
    (fun _ rs => rs = [.i64 (a &&& b &&& c)])
set_option maxRecDepth 4096 in
@[proves Project.RustU64Tests.Spec.AndChainSpec]
theorem and_chain_correct : AndChainSpec := by
  intro env a b c
  apply TerminatesWith.of_wp_entry_for (f := func6Def) rfl
  unfold func6Def func6
  simp only [Function.toLocals, Function.numParams, List.take, List.reverse, List.reverseAux,
    List.map, ValueType.zero, wp_localGet_cons, Locals.get, List.length_cons, List.length_nil,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Nat.reduceAdd, Nat.reduceLT, reduceIte,
    List.drop, and_seq, wp_ret_cons, Continuation.Return.injEq, List.cons.injEq, and_true,
    List.append_nil]

@[spec_of "rust-exported" "rust_u64_tests::and_then_or"]
def AndThenOrSpec : Prop := ∀ (env : HostEnv Unit) (a b c : UInt64),
  TerminatesWith env «module» 7 «module».initialStore [.i64 c, .i64 b, .i64 a]
    (fun _ rs => rs = [.i64 ((a &&& b) ||| c)])
set_option maxRecDepth 4096 in
@[proves Project.RustU64Tests.Spec.AndThenOrSpec]
theorem and_then_or_correct : AndThenOrSpec := by
  intro env a b c
  apply TerminatesWith.of_wp_entry_for (f := func7Def) rfl
  unfold func7Def func7
  simp only [Function.toLocals, Function.numParams, List.take, List.reverse, List.reverseAux,
    List.map, ValueType.zero, wp_localGet_cons, Locals.get, List.length_cons, List.length_nil,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Nat.reduceAdd, Nat.reduceLT, reduceIte,
    List.drop, and_seq, or_seq, wp_ret_cons, Continuation.Return.injEq, List.cons.injEq,
    and_true, List.append_nil]

/-! ## bitor -/
@[spec_of "rust-exported" "rust_u64_tests::or_chain"]
def OrChainSpec : Prop := ∀ (env : HostEnv Unit) (a b c : UInt64),
  TerminatesWith env «module» 32 «module».initialStore [.i64 c, .i64 b, .i64 a]
    (fun _ rs => rs = [.i64 (a ||| b ||| c)])
set_option maxRecDepth 4096 in
@[proves Project.RustU64Tests.Spec.OrChainSpec]
theorem or_chain_correct : OrChainSpec := by
  intro env a b c
  apply TerminatesWith.of_wp_entry_for (f := func32Def) rfl
  unfold func32Def func32
  simp only [Function.toLocals, Function.numParams, List.take, List.reverse, List.reverseAux,
    List.map, ValueType.zero, wp_localGet_cons, Locals.get, List.length_cons, List.length_nil,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Nat.reduceAdd, Nat.reduceLT, reduceIte,
    List.drop, or_seq, wp_ret_cons, Continuation.Return.injEq, List.cons.injEq, and_true,
    List.append_nil]

@[spec_of "rust-exported" "rust_u64_tests::or_then_xor"]
def OrThenXorSpec : Prop := ∀ (env : HostEnv Unit) (a b c : UInt64),
  TerminatesWith env «module» 33 «module».initialStore [.i64 c, .i64 b, .i64 a]
    (fun _ rs => rs = [.i64 ((a ||| b) ^^^ c)])
set_option maxRecDepth 4096 in
@[proves Project.RustU64Tests.Spec.OrThenXorSpec]
theorem or_then_xor_correct : OrThenXorSpec := by
  intro env a b c
  apply TerminatesWith.of_wp_entry_for (f := func33Def) rfl
  unfold func33Def func33
  simp only [Function.toLocals, Function.numParams, List.take, List.reverse, List.reverseAux,
    List.map, ValueType.zero, wp_localGet_cons, Locals.get, List.length_cons, List.length_nil,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Nat.reduceAdd, Nat.reduceLT, reduceIte,
    List.drop, or_seq, xor_seq, wp_ret_cons, Continuation.Return.injEq, List.cons.injEq,
    and_true, List.append_nil]

/-! ## bitxor -/
@[spec_of "rust-exported" "rust_u64_tests::xor_chain"]
def XorChainSpec : Prop := ∀ (env : HostEnv Unit) (a b c : UInt64),
  TerminatesWith env «module» 42 «module».initialStore [.i64 c, .i64 b, .i64 a]
    (fun _ rs => rs = [.i64 (a ^^^ b ^^^ c)])
set_option maxRecDepth 4096 in
@[proves Project.RustU64Tests.Spec.XorChainSpec]
theorem xor_chain_correct : XorChainSpec := by
  intro env a b c
  apply TerminatesWith.of_wp_entry_for (f := func42Def) rfl
  unfold func42Def func42
  simp only [Function.toLocals, Function.numParams, List.take, List.reverse, List.reverseAux,
    List.map, ValueType.zero, wp_localGet_cons, Locals.get, List.length_cons, List.length_nil,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Nat.reduceAdd, Nat.reduceLT, reduceIte,
    List.drop, xor_seq, wp_ret_cons, Continuation.Return.injEq, List.cons.injEq, and_true,
    List.append_nil]

@[spec_of "rust-exported" "rust_u64_tests::xor_then_and"]
def XorThenAndSpec : Prop := ∀ (env : HostEnv Unit) (a b c : UInt64),
  TerminatesWith env «module» 43 «module».initialStore [.i64 c, .i64 b, .i64 a]
    (fun _ rs => rs = [.i64 ((a ^^^ b) &&& c)])
set_option maxRecDepth 4096 in
@[proves Project.RustU64Tests.Spec.XorThenAndSpec]
theorem xor_then_and_correct : XorThenAndSpec := by
  intro env a b c
  apply TerminatesWith.of_wp_entry_for (f := func43Def) rfl
  unfold func43Def func43
  simp only [Function.toLocals, Function.numParams, List.take, List.reverse, List.reverseAux,
    List.map, ValueType.zero, wp_localGet_cons, Locals.get, List.length_cons, List.length_nil,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Nat.reduceAdd, Nat.reduceLT, reduceIte,
    List.drop, xor_seq, and_seq, wp_ret_cons, Continuation.Return.injEq, List.cons.injEq,
    and_true, List.append_nil]

/-! ## not -/
@[spec_of "rust-exported" "rust_u64_tests::not_twice"]
def NotTwiceSpec : Prop := ∀ (env : HostEnv Unit) (a : UInt64),
  TerminatesWith env «module» 31 «module».initialStore [.i64 a]
    (fun _ rs => rs = [.i64 (~~~(~~~a))])
set_option maxRecDepth 4096 in
@[proves Project.RustU64Tests.Spec.NotTwiceSpec]
theorem not_twice_correct : NotTwiceSpec := by
  intro env a
  apply TerminatesWith.of_wp_entry_for (f := func31Def) rfl
  unfold func31Def func31
  simp only [Function.toLocals, Function.numParams, List.take, List.reverse, List.reverseAux,
    List.map, ValueType.zero, wp_localGet_cons, Locals.get, List.length_cons, List.length_nil,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Nat.reduceAdd, Nat.reduceLT, reduceIte,
    List.drop, not_seq, wp_ret_cons, Continuation.Return.injEq, List.cons.injEq, and_true,
    List.append_nil]

@[spec_of "rust-exported" "rust_u64_tests::not_then_xor"]
def NotThenXorSpec : Prop := ∀ (env : HostEnv Unit) (a b : UInt64),
  TerminatesWith env «module» 30 «module».initialStore [.i64 b, .i64 a]
    (fun _ rs => rs = [.i64 ((~~~a) ^^^ b)])
set_option maxRecDepth 4096 in
@[proves Project.RustU64Tests.Spec.NotThenXorSpec]
theorem not_then_xor_correct : NotThenXorSpec := by
  intro env a b
  apply TerminatesWith.of_wp_entry_for (f := func30Def) rfl
  unfold func30Def func30
  simp only [Function.toLocals, Function.numParams, List.take, List.reverse, List.reverseAux,
    List.map, ValueType.zero, wp_localGet_cons, Locals.get, List.length_cons, List.length_nil,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Nat.reduceAdd, Nat.reduceLT, reduceIte,
    List.drop, not_seq, xor_seq, wp_ret_cons, Continuation.Return.injEq, List.cons.injEq,
    and_true, List.append_nil]

/-! ## div (divisor nonzero) — peel the guard, then reuse `div_chunk` -/
@[spec_of "rust-exported" "rust_u64_tests::div_then_add"]
def DivThenAddSpec : Prop := ∀ (env : HostEnv Unit) (a b c : UInt64), b ≠ 0 →
  TerminatesWith env «module» 10 «module».initialStore [.i64 c, .i64 b, .i64 a]
    (fun _ rs => rs = [.i64 (a / b + c)])
set_option maxRecDepth 4096 in
@[proves Project.RustU64Tests.Spec.DivThenAddSpec]
theorem div_then_add_correct : DivThenAddSpec := by
  intro env a b c hb
  apply TerminatesWith.of_wp_entry_for (f := func10Def) rfl
  unfold func10Def func10
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
  TerminatesWith env «module» 11 «module».initialStore [.i64 c, .i64 b, .i64 a]
    (fun _ rs => rs = [.i64 (a / b * c)])
set_option maxRecDepth 4096 in
@[proves Project.RustU64Tests.Spec.DivThenMulSpec]
theorem div_then_mul_correct : DivThenMulSpec := by
  intro env a b c hb
  apply TerminatesWith.of_wp_entry_for (f := func11Def) rfl
  unfold func11Def func11
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
  TerminatesWith env «module» 34 «module».initialStore [.i64 c, .i64 b, .i64 a]
    (fun _ rs => rs = [.i64 (a % b + c)])
set_option maxRecDepth 4096 in
@[proves Project.RustU64Tests.Spec.RemThenAddSpec]
theorem rem_then_add_correct : RemThenAddSpec := by
  intro env a b c hb
  apply TerminatesWith.of_wp_entry_for (f := func34Def) rfl
  unfold func34Def func34
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
  TerminatesWith env «module» 35 «module».initialStore [.i64 c, .i64 b, .i64 a]
    (fun _ rs => rs = [.i64 (a % b * c)])
set_option maxRecDepth 4096 in
@[proves Project.RustU64Tests.Spec.RemThenMulSpec]
theorem rem_then_mul_correct : RemThenMulSpec := by
  intro env a b c hb
  apply TerminatesWith.of_wp_entry_for (f := func35Def) rfl
  unfold func35Def func35
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
  TerminatesWith env «module» 36 «module».initialStore [.i64 b, .i32 n, .i64 a]
    (fun _ rs => rs = [.i64 ((a <<< (n.toUInt64 % 64)) + b)])
set_option maxRecDepth 4096 in
@[proves Project.RustU64Tests.Spec.ShlThenAddSpec]
theorem shl_then_add_correct : ShlThenAddSpec := by
  intro env a n b
  apply TerminatesWith.of_wp_entry_for (f := func36Def) rfl
  unfold func36Def func36
  simp only [Function.toLocals, Function.numParams, List.take, List.reverse, List.reverseAux,
    List.map, ValueType.zero, wp_localGet_cons, Locals.get, List.length_cons, List.length_nil,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Nat.reduceAdd, Nat.reduceLT, reduceIte,
    List.drop, shl_seq, add_seq, wp_ret_cons, Continuation.Return.injEq, List.cons.injEq,
    and_true, List.append_nil]

@[spec_of "rust-exported" "rust_u64_tests::shl_twice"]
def ShlTwiceSpec : Prop := ∀ (env : HostEnv Unit) (a : UInt64) (n m : UInt32),
  TerminatesWith env «module» 37 «module».initialStore [.i32 m, .i32 n, .i64 a]
    (fun _ rs => rs = [.i64 ((a <<< (n.toUInt64 % 64)) <<< (m.toUInt64 % 64))])
set_option maxRecDepth 4096 in
@[proves Project.RustU64Tests.Spec.ShlTwiceSpec]
theorem shl_twice_correct : ShlTwiceSpec := by
  intro env a n m
  apply TerminatesWith.of_wp_entry_for (f := func37Def) rfl
  unfold func37Def func37
  simp only [Function.toLocals, Function.numParams, List.take, List.reverse, List.reverseAux,
    List.map, ValueType.zero, wp_localGet_cons, Locals.get, List.length_cons, List.length_nil,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Nat.reduceAdd, Nat.reduceLT, reduceIte,
    List.drop, shl_seq, wp_ret_cons, Continuation.Return.injEq, List.cons.injEq,
    and_true, List.append_nil]

@[spec_of "rust-exported" "rust_u64_tests::shr_then_sub"]
def ShrThenSubSpec : Prop := ∀ (env : HostEnv Unit) (a : UInt64) (n : UInt32) (b : UInt64),
  TerminatesWith env «module» 38 «module».initialStore [.i64 b, .i32 n, .i64 a]
    (fun _ rs => rs = [.i64 ((a >>> (n.toUInt64 % 64)) - b)])
set_option maxRecDepth 4096 in
@[proves Project.RustU64Tests.Spec.ShrThenSubSpec]
theorem shr_then_sub_correct : ShrThenSubSpec := by
  intro env a n b
  apply TerminatesWith.of_wp_entry_for (f := func38Def) rfl
  unfold func38Def func38
  simp only [Function.toLocals, Function.numParams, List.take, List.reverse, List.reverseAux,
    List.map, ValueType.zero, wp_localGet_cons, Locals.get, List.length_cons, List.length_nil,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Nat.reduceAdd, Nat.reduceLT, reduceIte,
    List.drop, shr_seq, sub_seq, wp_ret_cons, Continuation.Return.injEq, List.cons.injEq,
    and_true, List.append_nil]

@[spec_of "rust-exported" "rust_u64_tests::shr_twice"]
def ShrTwiceSpec : Prop := ∀ (env : HostEnv Unit) (a : UInt64) (n m : UInt32),
  TerminatesWith env «module» 39 «module».initialStore [.i32 m, .i32 n, .i64 a]
    (fun _ rs => rs = [.i64 ((a >>> (n.toUInt64 % 64)) >>> (m.toUInt64 % 64))])
set_option maxRecDepth 4096 in
@[proves Project.RustU64Tests.Spec.ShrTwiceSpec]
theorem shr_twice_correct : ShrTwiceSpec := by
  intro env a n m
  apply TerminatesWith.of_wp_entry_for (f := func39Def) rfl
  unfold func39Def func39
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
  TerminatesWith env «module» 13 «module».initialStore [.i64 c, .i64 b, .i64 a]
    (fun _ rs => rs = [.i64 (UInt64.ofNat (if a = b then (1 : UInt32) else 0).toNat + c)])
set_option maxRecDepth 4096 in
@[proves Project.RustU64Tests.Spec.EqU64Spec]
theorem eq_u64_correct : EqU64Spec := by
  intro env a b c
  apply TerminatesWith.of_wp_entry_for (f := func13Def) rfl
  unfold func13Def func13
  simp only [Function.toLocals, Function.numParams, List.take, List.reverse, List.reverseAux,
    List.map, ValueType.zero, wp_localGet_cons, Locals.get, List.length_cons, List.length_nil,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Nat.reduceAdd, Nat.reduceLT, reduceIte,
    List.drop, eq_seq, wp_extendUI32_cons, add_seq, wp_ret_cons, Continuation.Return.injEq,
    List.cons.injEq, and_true, List.append_nil]

@[spec_of "rust-exported" "rust_u64_tests::eq_two"]
def EqTwoSpec : Prop := ∀ (env : HostEnv Unit) (a b c d : UInt64),
  TerminatesWith env «module» 12 «module».initialStore [.i64 d, .i64 c, .i64 b, .i64 a]
    (fun _ rs => rs = [.i64 (UInt64.ofNat (if a = b then (1 : UInt32) else 0).toNat
                          + UInt64.ofNat (if c = d then (1 : UInt32) else 0).toNat)])
set_option maxRecDepth 4096 in
@[proves Project.RustU64Tests.Spec.EqTwoSpec]
theorem eq_two_correct : EqTwoSpec := by
  intro env a b c d
  apply TerminatesWith.of_wp_entry_for (f := func12Def) rfl
  unfold func12Def func12
  simp only [Function.toLocals, Function.numParams, List.take, List.reverse, List.reverseAux,
    List.map, ValueType.zero, wp_localGet_cons, Locals.get, List.length_cons, List.length_nil,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Nat.reduceAdd, Nat.reduceLT, reduceIte,
    List.drop, eq_seq, wp_extendUI32_cons, add_seq, wp_ret_cons, Continuation.Return.injEq,
    List.cons.injEq, and_true, List.append_nil]

/-! ## ne — `(a != b) as u64` reuses `ne_seq` inline (`wp_neI64_cons` excluded). -/
@[spec_of "rust-exported" "rust_u64_tests::ne_u64"]
def NeU64Spec : Prop := ∀ (env : HostEnv Unit) (a b c : UInt64),
  TerminatesWith env «module» 29 «module».initialStore [.i64 c, .i64 b, .i64 a]
    (fun _ rs => rs = [.i64 (UInt64.ofNat (if a ≠ b then (1 : UInt32) else 0).toNat + c)])
set_option maxRecDepth 4096 in
@[proves Project.RustU64Tests.Spec.NeU64Spec]
theorem ne_u64_correct : NeU64Spec := by
  intro env a b c
  apply TerminatesWith.of_wp_entry_for (f := func29Def) rfl
  unfold func29Def func29
  simp only [Function.toLocals, Function.numParams, List.take, List.reverse, List.reverseAux,
    List.map, ValueType.zero, wp_localGet_cons, Locals.get, List.length_cons, List.length_nil,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Nat.reduceAdd, Nat.reduceLT, reduceIte,
    List.drop, ne_seq, wp_extendUI32_cons, add_seq, wp_ret_cons, Continuation.Return.injEq,
    List.cons.injEq, and_true, List.append_nil]

@[spec_of "rust-exported" "rust_u64_tests::ne_two"]
def NeTwoSpec : Prop := ∀ (env : HostEnv Unit) (a b c d : UInt64),
  TerminatesWith env «module» 28 «module».initialStore [.i64 d, .i64 c, .i64 b, .i64 a]
    (fun _ rs => rs = [.i64 (UInt64.ofNat (if a ≠ b then (1 : UInt32) else 0).toNat
                          + UInt64.ofNat (if c ≠ d then (1 : UInt32) else 0).toNat)])
set_option maxRecDepth 4096 in
@[proves Project.RustU64Tests.Spec.NeTwoSpec]
theorem ne_two_correct : NeTwoSpec := by
  intro env a b c d
  apply TerminatesWith.of_wp_entry_for (f := func28Def) rfl
  unfold func28Def func28
  simp only [Function.toLocals, Function.numParams, List.take, List.reverse, List.reverseAux,
    List.map, ValueType.zero, wp_localGet_cons, Locals.get, List.length_cons, List.length_nil,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Nat.reduceAdd, Nat.reduceLT, reduceIte,
    List.drop, ne_seq, wp_extendUI32_cons, add_seq, wp_ret_cons, Continuation.Return.injEq,
    List.cons.injEq, and_true, List.append_nil]

/-! ## lt — `(a < b) as u64` reuses `lt_seq` inline (`wp_ltUI64_cons` excluded). -/
@[spec_of "rust-exported" "rust_u64_tests::lt_u64"]
def LtU64Spec : Prop := ∀ (env : HostEnv Unit) (a b c : UInt64),
  TerminatesWith env «module» 21 «module».initialStore [.i64 c, .i64 b, .i64 a]
    (fun _ rs => rs = [.i64 (UInt64.ofNat (if a < b then (1 : UInt32) else 0).toNat + c)])
set_option maxRecDepth 4096 in
@[proves Project.RustU64Tests.Spec.LtU64Spec]
theorem lt_u64_correct : LtU64Spec := by
  intro env a b c
  apply TerminatesWith.of_wp_entry_for (f := func21Def) rfl
  unfold func21Def func21
  simp only [Function.toLocals, Function.numParams, List.take, List.reverse, List.reverseAux,
    List.map, ValueType.zero, wp_localGet_cons, Locals.get, List.length_cons, List.length_nil,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Nat.reduceAdd, Nat.reduceLT, reduceIte,
    List.drop, lt_seq, wp_extendUI32_cons, add_seq, wp_ret_cons, Continuation.Return.injEq,
    List.cons.injEq, and_true, List.append_nil]

@[spec_of "rust-exported" "rust_u64_tests::lt_two"]
def LtTwoSpec : Prop := ∀ (env : HostEnv Unit) (a b c d : UInt64),
  TerminatesWith env «module» 20 «module».initialStore [.i64 d, .i64 c, .i64 b, .i64 a]
    (fun _ rs => rs = [.i64 (UInt64.ofNat (if a < b then (1 : UInt32) else 0).toNat
                          + UInt64.ofNat (if c < d then (1 : UInt32) else 0).toNat)])
set_option maxRecDepth 4096 in
@[proves Project.RustU64Tests.Spec.LtTwoSpec]
theorem lt_two_correct : LtTwoSpec := by
  intro env a b c d
  apply TerminatesWith.of_wp_entry_for (f := func20Def) rfl
  unfold func20Def func20
  simp only [Function.toLocals, Function.numParams, List.take, List.reverse, List.reverseAux,
    List.map, ValueType.zero, wp_localGet_cons, Locals.get, List.length_cons, List.length_nil,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Nat.reduceAdd, Nat.reduceLT, reduceIte,
    List.drop, lt_seq, wp_extendUI32_cons, add_seq, wp_ret_cons, Continuation.Return.injEq,
    List.cons.injEq, and_true, List.append_nil]

/-! ## le — `(a <= b) as u64` reuses `le_seq` inline (`wp_leUI64_cons` excluded). -/
@[spec_of "rust-exported" "rust_u64_tests::le_u64"]
def LeU64Spec : Prop := ∀ (env : HostEnv Unit) (a b c : UInt64),
  TerminatesWith env «module» 19 «module».initialStore [.i64 c, .i64 b, .i64 a]
    (fun _ rs => rs = [.i64 (UInt64.ofNat (if a ≤ b then (1 : UInt32) else 0).toNat + c)])
set_option maxRecDepth 4096 in
@[proves Project.RustU64Tests.Spec.LeU64Spec]
theorem le_u64_correct : LeU64Spec := by
  intro env a b c
  apply TerminatesWith.of_wp_entry_for (f := func19Def) rfl
  unfold func19Def func19
  simp only [Function.toLocals, Function.numParams, List.take, List.reverse, List.reverseAux,
    List.map, ValueType.zero, wp_localGet_cons, Locals.get, List.length_cons, List.length_nil,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Nat.reduceAdd, Nat.reduceLT, reduceIte,
    List.drop, le_seq, wp_extendUI32_cons, add_seq, wp_ret_cons, Continuation.Return.injEq,
    List.cons.injEq, and_true, List.append_nil]

@[spec_of "rust-exported" "rust_u64_tests::le_two"]
def LeTwoSpec : Prop := ∀ (env : HostEnv Unit) (a b c d : UInt64),
  TerminatesWith env «module» 18 «module».initialStore [.i64 d, .i64 c, .i64 b, .i64 a]
    (fun _ rs => rs = [.i64 (UInt64.ofNat (if a ≤ b then (1 : UInt32) else 0).toNat
                          + UInt64.ofNat (if c ≤ d then (1 : UInt32) else 0).toNat)])
set_option maxRecDepth 4096 in
@[proves Project.RustU64Tests.Spec.LeTwoSpec]
theorem le_two_correct : LeTwoSpec := by
  intro env a b c d
  apply TerminatesWith.of_wp_entry_for (f := func18Def) rfl
  unfold func18Def func18
  simp only [Function.toLocals, Function.numParams, List.take, List.reverse, List.reverseAux,
    List.map, ValueType.zero, wp_localGet_cons, Locals.get, List.length_cons, List.length_nil,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Nat.reduceAdd, Nat.reduceLT, reduceIte,
    List.drop, le_seq, wp_extendUI32_cons, add_seq, wp_ret_cons, Continuation.Return.injEq,
    List.cons.injEq, and_true, List.append_nil]

/-! ## gt — `(a > b) as u64` reuses `gt_seq` inline (`wp_gtUI64_cons` excluded). -/
@[spec_of "rust-exported" "rust_u64_tests::gt_u64"]
def GtU64Spec : Prop := ∀ (env : HostEnv Unit) (a b c : UInt64),
  TerminatesWith env «module» 17 «module».initialStore [.i64 c, .i64 b, .i64 a]
    (fun _ rs => rs = [.i64 (UInt64.ofNat (if a > b then (1 : UInt32) else 0).toNat + c)])
set_option maxRecDepth 4096 in
@[proves Project.RustU64Tests.Spec.GtU64Spec]
theorem gt_u64_correct : GtU64Spec := by
  intro env a b c
  apply TerminatesWith.of_wp_entry_for (f := func17Def) rfl
  unfold func17Def func17
  simp only [Function.toLocals, Function.numParams, List.take, List.reverse, List.reverseAux,
    List.map, ValueType.zero, wp_localGet_cons, Locals.get, List.length_cons, List.length_nil,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Nat.reduceAdd, Nat.reduceLT, reduceIte,
    List.drop, gt_seq, wp_extendUI32_cons, add_seq, wp_ret_cons, Continuation.Return.injEq,
    List.cons.injEq, and_true, List.append_nil]

@[spec_of "rust-exported" "rust_u64_tests::gt_two"]
def GtTwoSpec : Prop := ∀ (env : HostEnv Unit) (a b c d : UInt64),
  TerminatesWith env «module» 16 «module».initialStore [.i64 d, .i64 c, .i64 b, .i64 a]
    (fun _ rs => rs = [.i64 (UInt64.ofNat (if a > b then (1 : UInt32) else 0).toNat
                          + UInt64.ofNat (if c > d then (1 : UInt32) else 0).toNat)])
set_option maxRecDepth 4096 in
@[proves Project.RustU64Tests.Spec.GtTwoSpec]
theorem gt_two_correct : GtTwoSpec := by
  intro env a b c d
  apply TerminatesWith.of_wp_entry_for (f := func16Def) rfl
  unfold func16Def func16
  simp only [Function.toLocals, Function.numParams, List.take, List.reverse, List.reverseAux,
    List.map, ValueType.zero, wp_localGet_cons, Locals.get, List.length_cons, List.length_nil,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Nat.reduceAdd, Nat.reduceLT, reduceIte,
    List.drop, gt_seq, wp_extendUI32_cons, add_seq, wp_ret_cons, Continuation.Return.injEq,
    List.cons.injEq, and_true, List.append_nil]

/-! ## ge — `(a >= b) as u64` reuses `ge_seq` inline (`wp_geUI64_cons` excluded). -/
@[spec_of "rust-exported" "rust_u64_tests::ge_u64"]
def GeU64Spec : Prop := ∀ (env : HostEnv Unit) (a b c : UInt64),
  TerminatesWith env «module» 15 «module».initialStore [.i64 c, .i64 b, .i64 a]
    (fun _ rs => rs = [.i64 (UInt64.ofNat (if a ≥ b then (1 : UInt32) else 0).toNat + c)])
set_option maxRecDepth 4096 in
@[proves Project.RustU64Tests.Spec.GeU64Spec]
theorem ge_u64_correct : GeU64Spec := by
  intro env a b c
  apply TerminatesWith.of_wp_entry_for (f := func15Def) rfl
  unfold func15Def func15
  simp only [Function.toLocals, Function.numParams, List.take, List.reverse, List.reverseAux,
    List.map, ValueType.zero, wp_localGet_cons, Locals.get, List.length_cons, List.length_nil,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Nat.reduceAdd, Nat.reduceLT, reduceIte,
    List.drop, ge_seq, wp_extendUI32_cons, add_seq, wp_ret_cons, Continuation.Return.injEq,
    List.cons.injEq, and_true, List.append_nil]

@[spec_of "rust-exported" "rust_u64_tests::ge_two"]
def GeTwoSpec : Prop := ∀ (env : HostEnv Unit) (a b c d : UInt64),
  TerminatesWith env «module» 14 «module».initialStore [.i64 d, .i64 c, .i64 b, .i64 a]
    (fun _ rs => rs = [.i64 (UInt64.ofNat (if a ≥ b then (1 : UInt32) else 0).toNat
                          + UInt64.ofNat (if c ≥ d then (1 : UInt32) else 0).toNat)])
set_option maxRecDepth 4096 in
@[proves Project.RustU64Tests.Spec.GeTwoSpec]
theorem ge_two_correct : GeTwoSpec := by
  intro env a b c d
  apply TerminatesWith.of_wp_entry_for (f := func14Def) rfl
  unfold func14Def func14
  simp only [Function.toLocals, Function.numParams, List.take, List.reverse, List.reverseAux,
    List.map, ValueType.zero, wp_localGet_cons, Locals.get, List.length_cons, List.length_nil,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Nat.reduceAdd, Nat.reduceLT, reduceIte,
    List.drop, ge_seq, wp_extendUI32_cons, add_seq, wp_ret_cons, Continuation.Return.injEq,
    List.cons.injEq, and_true, List.append_nil]

/-! ## Ord: min / max / clamp — call-reuse tests. `a.min/max/clamp(..)` compiles to
a `call` to the framed inner fn, so each test reuses the CodeLib body theorem
(`max_wp`/`min_wp`/`clamp_wp`) across the `call` via `wp_call_tw` — exactly like
`total_variation` reuses `absDiff_wp`. The inner fns sit at test-`«module»` 0/1/2. -/

private theorem tmax_call {env : HostEnv Unit} (st : Store Unit) (a b : UInt64) (rest : List Value)
    (hsp : st.globals.globals[0]? = some (.i32 1048576)) (hhi : 1048576 ≤ st.mem.pages * 65536) :
    TerminatesWith env «module» 0 st (.i64 b :: .i64 a :: rest)
      (fun st' vs => vs = .i64 (if b < a then a else b) :: rest
        ∧ st'.globals = st.globals ∧ st'.mem.pages = st.mem.pages) :=
  TerminatesWith.of_returns_wp (f := maxFunc)
    (rs := [.i64 (if b < a then a else b)]) rfl rfl
    (max_wp st 1048576 a b [] hsp (by decide) hhi) rfl

private theorem tmin_call {env : HostEnv Unit} (st : Store Unit) (a b : UInt64) (rest : List Value)
    (hsp : st.globals.globals[0]? = some (.i32 1048576)) (hhi : 1048576 ≤ st.mem.pages * 65536) :
    TerminatesWith env «module» 1 st (.i64 b :: .i64 a :: rest)
      (fun st' vs => vs = .i64 (if b < a then b else a) :: rest
        ∧ st'.globals = st.globals ∧ st'.mem.pages = st.mem.pages) :=
  TerminatesWith.of_returns_wp (f := minFunc)
    (rs := [.i64 (if b < a then b else a)]) rfl rfl
    (min_wp st 1048576 a b [] hsp (by decide) hhi) rfl

private theorem tclamp_call {env : HostEnv Unit} (st : Store Unit) (a lo hi : UInt64) (loc : UInt32)
    (rest : List Value) (hsp : st.globals.globals[0]? = some (.i32 1048576))
    (hhi : 1048576 ≤ st.mem.pages * 65536) (hlohi : lo ≤ hi) :
    TerminatesWith env «module» 2 st (.i32 loc :: .i64 hi :: .i64 lo :: .i64 a :: rest)
      (fun st' vs => vs = .i64 (if a < lo then lo else if a > hi then hi else a) :: rest
        ∧ st'.mem.pages = st.mem.pages) :=
  TerminatesWith.of_returns_wp (f := clampFunc 93)
    (rs := [.i64 (if a < lo then lo else if a > hi then hi else a)]) rfl rfl
    (clamp_wp st 93 1048576 a lo hi loc [] hsp (by decide) hhi hlohi) rfl

/-! ## max -/
@[spec_of "rust-exported" "rust_u64_tests::max_add"]
def MaxAddSpec : Prop := ∀ (env : HostEnv Unit) (a b c : UInt64),
  TerminatesWith env «module» 22 «module».initialStore [.i64 c, .i64 b, .i64 a]
    (fun _ rs => rs = [.i64 ((if b < a then a else b) + c)])
set_option maxRecDepth 4096 in
@[proves Project.RustU64Tests.Spec.MaxAddSpec]
theorem max_add_correct : MaxAddSpec := by
  intro env a b c
  apply TerminatesWith.of_wp_entry_for (f := func22Def) rfl
  unfold func22Def func22
  wp_run
  apply wp_call_tw (tmax_call «module».initialStore a b [] rfl (by decide))
  intro st1 vs1 h1
  obtain ⟨hvs1, _, _⟩ := h1
  subst hvs1
  wp_run
  simp

@[spec_of "rust-exported" "rust_u64_tests::max_chain"]
def MaxChainSpec : Prop := ∀ (env : HostEnv Unit) (a b c : UInt64),
  TerminatesWith env «module» 23 «module».initialStore [.i64 c, .i64 b, .i64 a]
    (fun _ rs => rs = [.i64 (if c < (if b < a then a else b) then (if b < a then a else b) else c)])
set_option maxRecDepth 4096 in
@[proves Project.RustU64Tests.Spec.MaxChainSpec]
theorem max_chain_correct : MaxChainSpec := by
  intro env a b c
  apply TerminatesWith.of_wp_entry_for (f := func23Def) rfl
  unfold func23Def func23
  wp_run
  apply wp_call_tw (tmax_call «module».initialStore a b [] rfl (by decide))
  intro st1 vs1 h1
  obtain ⟨hvs1, hg1, hp1⟩ := h1
  subst hvs1
  wp_run
  apply wp_call_tw (tmax_call st1 (if b < a then a else b) c [] (by rw [hg1]; rfl) (by rw [hp1]; decide))
  intro st2 vs2 h2
  obtain ⟨hvs2, _, _⟩ := h2
  subst hvs2
  wp_run
  simp

/-! ## min -/
@[spec_of "rust-exported" "rust_u64_tests::min_add"]
def MinAddSpec : Prop := ∀ (env : HostEnv Unit) (a b c : UInt64),
  TerminatesWith env «module» 24 «module».initialStore [.i64 c, .i64 b, .i64 a]
    (fun _ rs => rs = [.i64 ((if b < a then b else a) + c)])
set_option maxRecDepth 4096 in
@[proves Project.RustU64Tests.Spec.MinAddSpec]
theorem min_add_correct : MinAddSpec := by
  intro env a b c
  apply TerminatesWith.of_wp_entry_for (f := func24Def) rfl
  unfold func24Def func24
  wp_run
  apply wp_call_tw (tmin_call «module».initialStore a b [] rfl (by decide))
  intro st1 vs1 h1
  obtain ⟨hvs1, _, _⟩ := h1
  subst hvs1
  wp_run
  simp

@[spec_of "rust-exported" "rust_u64_tests::min_chain"]
def MinChainSpec : Prop := ∀ (env : HostEnv Unit) (a b c : UInt64),
  TerminatesWith env «module» 25 «module».initialStore [.i64 c, .i64 b, .i64 a]
    (fun _ rs => rs = [.i64 (if c < (if b < a then b else a) then c else (if b < a then b else a))])
set_option maxRecDepth 4096 in
@[proves Project.RustU64Tests.Spec.MinChainSpec]
theorem min_chain_correct : MinChainSpec := by
  intro env a b c
  apply TerminatesWith.of_wp_entry_for (f := func25Def) rfl
  unfold func25Def func25
  wp_run
  apply wp_call_tw (tmin_call «module».initialStore a b [] rfl (by decide))
  intro st1 vs1 h1
  obtain ⟨hvs1, hg1, hp1⟩ := h1
  subst hvs1
  wp_run
  apply wp_call_tw (tmin_call st1 (if b < a then b else a) c [] (by rw [hg1]; rfl) (by rw [hp1]; decide))
  intro st2 vs2 h2
  obtain ⟨hvs2, _, _⟩ := h2
  subst hvs2
  wp_run
  simp

/-! ## clamp (precondition `lo ≤ hi`) -/
@[spec_of "rust-exported" "rust_u64_tests::clamp_add"]
def ClampAddSpec : Prop := ∀ (env : HostEnv Unit) (a lo hi c : UInt64), lo ≤ hi →
  TerminatesWith env «module» 8 «module».initialStore [.i64 c, .i64 hi, .i64 lo, .i64 a]
    (fun _ rs => rs = [.i64 ((if a < lo then lo else if a > hi then hi else a) + c)])
set_option maxRecDepth 4096 in
@[proves Project.RustU64Tests.Spec.ClampAddSpec]
theorem clamp_add_correct : ClampAddSpec := by
  intro env a lo hi c hlohi
  apply TerminatesWith.of_wp_entry_for (f := func8Def) rfl
  unfold func8Def func8
  wp_run
  apply wp_call_tw (tclamp_call «module».initialStore a lo hi 1048636 [] rfl (by decide) hlohi)
  intro st1 vs1 h1
  obtain ⟨hvs1, _⟩ := h1
  subst hvs1
  wp_run
  simp

@[spec_of "rust-exported" "rust_u64_tests::clamp_mul"]
def ClampMulSpec : Prop := ∀ (env : HostEnv Unit) (a lo hi c : UInt64), lo ≤ hi →
  TerminatesWith env «module» 9 «module».initialStore [.i64 c, .i64 hi, .i64 lo, .i64 a]
    (fun _ rs => rs = [.i64 ((if a < lo then lo else if a > hi then hi else a) * c)])
set_option maxRecDepth 4096 in
@[proves Project.RustU64Tests.Spec.ClampMulSpec]
theorem clamp_mul_correct : ClampMulSpec := by
  intro env a lo hi c hlohi
  apply TerminatesWith.of_wp_entry_for (f := func9Def) rfl
  unfold func9Def func9
  wp_run
  apply wp_call_tw (tclamp_call «module».initialStore a lo hi 1048652 [] rfl (by decide) hlohi)
  intro st1 vs1 h1
  obtain ⟨hvs1, _⟩ := h1
  subst hvs1
  wp_run
  simp

end Project.RustU64Tests.Spec
