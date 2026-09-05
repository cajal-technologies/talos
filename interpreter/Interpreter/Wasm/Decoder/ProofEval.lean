import Interpreter.Wasm.Decoder.Wat
import Interpreter.Wasm.Validate
import Lean

/-!
Kernel-checked evaluation support for WAT proofs.

The ordinary `cbv` equations for the decoder's large string matches repeat
expensive reduction of unsuccessful pattern tests. Cache their specializations
for the supported opcode spellings. Every generated declaration is a theorem:
its proof is either reflexivity or an application of the parser's own checked
fixed-point equation. `addDecl` checks it in Lean's kernel before it becomes a
`cbv` rewrite rule. Lexical candidates are computed separately and certified by kernel reduction;
no native-evaluation proof axiom is introduced.
The runtime decoder does not import this module.
-/

open Lean Meta Elab Command
namespace Wasm.Decoder.Wat.ProofEval

/-- Keep Boolean conditions out of the generic decidable-`ite` evaluator.
Its instance normalization can repeat the full decoder computation. Boolean
case analysis proves the replacement for every result type and instance. -/
private theorem boolIte_eq_cond {α : Sort u} (b : Bool) (inst : Decidable (b = true)) (t f : α) :
    @ite α (b = true) inst t f = (bif b then t else f) := by
  cases b <;> simp
local macro "originalBoolIte" : term => pure <| mkIdent <| mkPrivateNameCore `Lean.Meta.Tactic.Cbv.ControlFlow `Lean.Meta.Sym.Simp.simpIteCbv
/-- Enable the decoder's kernel-checked Boolean rewrite in this file.
Lean does not export attribute erasures through imports, so consumers invoke
this command after importing the proof support. Other conditions retain the
standard evaluator. -/
macro "kernel_decoder" : command =>
  `(attribute [-cbvSimprocAttr] $(mkIdent <| mkPrivateNameCore
    `Lean.Meta.Tactic.Cbv.ControlFlow `Lean.Meta.Sym.Simp.simpIteCbv))
kernel_decoder
cbv_simproc ↓ boolIteChecked (@ite _ _ _ _ _) := fun e => do
  let_expr ite α c inst t f := e | return .rfl
  let some (ty, b, value) := c.eq? | return ← originalBoolIte e
  unless ty.isConstOf ``Bool && value.isConstOf ``Bool.true do
    return ← originalBoolIte e
  let levels := e.getAppFn.constLevels!
  let proof := mkAppN (mkConst ``boolIte_eq_cond levels) #[α, b, inst, t, f]
  let result ← Sym.share <| mkAppN (mkConst ``cond levels) #[α, b, t, f]
  -- A pre-simproc result proceeds to application simplification; it does not
  -- revisit the pre-simprocs. Select the branch here so that the unchosen
  -- parser branch is never evaluated as an ordinary application argument.
  match ← Sym.Simp.simpCond result with
  | .step out h done cd =>
    let combined := mkAppN (mkConst ``Eq.trans levels) #[α, e, result, out, proof, h]
    return .step out combined done cd
  | .rfl done cd => return .step result proof done cd

/-- Quote a computed lexical candidate, then prove the original lexical
call equals it by reflexivity. `addDecl` checks that equality in the kernel
before `cbv` may use it; a wrong evaluator result cannot produce a theorem.
Use the checked string encoding and round-trip theorem to obtain the character
list; reducing UTF-8 decoding directly would create enormous kernel terms. -/
private def sexprListExpr (xs : List Expr) : Expr :=
  xs.foldr (fun x acc => mkApp3 (mkConst ``List.cons [.zero]) (mkConst ``Wasm.Decoder.Wat.Sexpr) x acc)
    (mkApp (mkConst ``List.nil [.zero]) (mkConst ``Wasm.Decoder.Wat.Sexpr))
private partial def quoteSexpr : Wasm.Decoder.Wat.Sexpr → Expr
  | .atom a => mkApp (mkConst ``Wasm.Decoder.Wat.Sexpr.atom) (toExpr a)
  | .list xs => mkApp (mkConst ``Wasm.Decoder.Wat.Sexpr.list)
      (sexprListExpr (xs.map quoteSexpr))
private def quoteResult (r : Except String (List Wasm.Decoder.Wat.Sexpr)) : Expr :=
  let ty := mkApp (mkConst ``List [.zero]) (mkConst ``Wasm.Decoder.Wat.Sexpr)
  match r with
  | .ok xs => mkApp3 (mkConst ``Except.ok [.zero,.zero]) (mkConst ``String) ty
      (sexprListExpr (xs.map quoteSexpr))
  | .error err => mkApp3 (mkConst ``Except.error [.zero,.zero]) (mkConst ``String) ty (toExpr err)


local macro "proofStrip" : term => pure <| mkIdent <| mkPrivateNameCore `Interpreter.Wasm.Decoder.Wat `Wasm.Decoder.Wat.stripCommentsAux
local macro "proofTokenize" : term => pure <| mkIdent <| mkPrivateNameCore `Interpreter.Wasm.Decoder.Wat `Wasm.Decoder.Wat.tokenizeAux
private def parseChars (cs : List Char) : Except String (List Wasm.Decoder.Wat.Sexpr) := do
  let (xs, rest) ← Wasm.Decoder.Wat.parseSexprs (proofTokenize (proofStrip cs []) [])
  match rest with
  | [] => .ok xs
  | _ => .error "unexpected ')'"
private theorem parseAll_eq_parseChars (s : String) :
    Wasm.Decoder.Wat.parseAll s = parseChars s.toList := by rfl
private def checkedProof (e result : Expr) : MetaM Expr := do
  let name ← mkAuxDeclName `kernel_lexical_reduction
  let type ← mkEq e result
  let value ← mkEqRefl e
  addDecl (.thmDecl {name, levelParams := [], type, value})
  return mkConst name
cbv_simproc cbv_eval lexChecked (Wasm.Decoder.Wat.parseAll _) := fun e => do
  let some s := Sym.getStringValue? e.appArg! | return .rfl
  let chars := toExpr s.toList
  let encoded := mkApp (mkConst ``String.ofList) chars
  let encodingProof ← checkedProof e.appArg! encoded
  let listProof ← mkAppM ``congrArg #[mkConst ``String.toList, encodingProof]
  let charsProof ← mkAppM ``Eq.trans #[listProof, mkApp (mkConst ``String.toList_ofList) chars]
  let reductionProof ← mkAppM ``congrArg #[mkConst ``parseChars, charsProof]
  let result := quoteResult (Wasm.Decoder.Wat.parseAll s)
  let parsedProof ← checkedProof (mkApp (mkConst ``parseChars) chars) result
  let restProof ← mkAppM ``Eq.trans #[reductionProof, parsedProof]
  let proof ← mkAppM ``Eq.trans #[mkApp (mkConst ``parseAll_eq_parseChars) e.appArg!, restProof]
  return .step (← Sym.share result) proof


private def decoderDecl (name : Name) : Name :=
  mkPrivateNameCore `Interpreter.Wasm.Decoder.Wat (`Wasm.Decoder.Wat ++ name)

private def cacheOpcode (opcode : String) : CommandElabM Unit := do
  for (parser, category) in [(`parseInstr, `instruction), (`parseFolded, `folded)] do
    let declName := Name.str (`Wasm.Decoder.Wat.ProofEval ++ category) opcode
    liftTermElabM do
      let parserName := decoderDecl parser
      let some equation ← getUnfoldEqnFor? parserName
        | throwError "missing checked instruction-parser equation"
      withLocalDeclD `ctx (mkConst ``Ctx) fun ctx =>
        withLocalDeclD `rest (mkApp (mkConst ``List [.zero]) (mkConst ``Sexpr)) fun rest => do
          let atom := mkApp (mkConst ``Sexpr.atom) (toExpr opcode)
          let tokens := mkApp3 (mkConst ``List.cons [.zero]) (mkConst ``Sexpr) atom rest
          let proof := mkApp2 (mkConst equation) ctx tokens
          let some (_, lhs, rhs) := (← inferType proof).eq?
            | throwError "instruction-parser unfolding is not an equality"
          let rhs ← whnf rhs
          let type ← mkForallFVars #[ctx, rest] (← mkEq lhs rhs)
          let proof ← mkLambdaFVars #[ctx, rest] proof
          addDecl (.thmDecl { name := declName, levelParams := [], type, value := proof })
    elabCommand (← `(attribute [cbv_eval] $(mkIdent declName)))
  -- Block headers also inspect an opcode as a possible bare value type.
  -- These closed helper applications can be checked directly by reduction.
  for helper in [`atomToValueType?, `isMemOp, `simdOp?, `simdLaneOp?] do
    let declName := Name.str (`Wasm.Decoder.Wat.ProofEval ++ helper) opcode
    liftTermElabM do
      let lhs := mkApp (mkConst (decoderDecl helper)) (toExpr opcode)
      let rhs ← whnf lhs
      let type ← mkEq lhs rhs
      let proof ← mkEqRefl lhs
      addDecl (.thmDecl { name := declName, levelParams := [], type, value := proof })
    elabCommand (← `(attribute [cbv_eval] $(mkIdent declName)))

set_option maxHeartbeats 4000000 in
run_cmd do
  for opcode in [
      "i32", "i64", "f32", "f64", "v128", "funcref", "externref",
      "func", "nofunc", "extern", "noextern", "ref", "null", "mut",
      "any.convert_extern", "array.copy", "array.fill", "array.get", "array.get_s",
      "array.get_u", "array.init_data", "array.init_elem", "array.len", "array.new",
      "array.new_data", "array.new_default", "array.new_elem", "array.new_fixed", "array.set",
      "block", "br", "br_if", "br_on_cast", "br_on_cast_fail",
      "br_on_non_null", "br_on_null", "br_table", "call", "call_indirect",
      "call_ref", "data.drop", "drop", "elem.drop", "else",
      "end", "extern.convert_any", "f32.abs", "f32.add", "f32.ceil",
      "f32.const", "f32.convert_i32_s", "f32.convert_i32_u", "f32.convert_i64_s", "f32.convert_i64_u",
      "f32.copysign", "f32.demote_f64", "f32.div", "f32.eq", "f32.floor",
      "f32.ge", "f32.gt", "f32.le", "f32.load", "f32.lt",
      "f32.max", "f32.min", "f32.mul", "f32.ne", "f32.nearest",
      "f32.neg", "f32.reinterpret_i32", "f32.sqrt", "f32.store", "f32.sub",
      "f32.trunc", "f64.abs", "f64.add", "f64.ceil", "f64.const",
      "f64.convert_i32_s", "f64.convert_i32_u", "f64.convert_i64_s", "f64.convert_i64_u", "f64.copysign",
      "f64.div", "f64.eq", "f64.floor", "f64.ge", "f64.gt",
      "f64.le", "f64.load", "f64.lt", "f64.max", "f64.min",
      "f64.mul", "f64.ne", "f64.nearest", "f64.neg", "f64.promote_f32",
      "f64.reinterpret_i64", "f64.sqrt", "f64.store", "f64.sub", "f64.trunc",
      "global.get", "global.set", "i31.get_s", "i31.get_u", "i32.add",
      "i32.and", "i32.clz", "i32.const", "i32.ctz", "i32.div_s",
      "i32.div_u", "i32.eq", "i32.eqz", "i32.extend16_s", "i32.extend8_s",
      "i32.ge_s", "i32.ge_u", "i32.gt_s", "i32.gt_u", "i32.le_s",
      "i32.le_u", "i32.load", "i32.load16_s", "i32.load16_u", "i32.load8_s",
      "i32.load8_u", "i32.lt_s", "i32.lt_u", "i32.mul", "i32.ne",
      "i32.or", "i32.popcnt", "i32.reinterpret_f32", "i32.rem_s", "i32.rem_u",
      "i32.rotl", "i32.rotr", "i32.shl", "i32.shr_s", "i32.shr_u",
      "i32.store", "i32.store16", "i32.store8", "i32.sub", "i32.trunc_f32_s",
      "i32.trunc_f32_u", "i32.trunc_f64_s", "i32.trunc_f64_u", "i32.trunc_sat_f32_s", "i32.trunc_sat_f32_u",
      "i32.trunc_sat_f64_s", "i32.trunc_sat_f64_u", "i32.wrap_i64", "i32.xor", "i64.add",
      "i64.and", "i64.clz", "i64.const", "i64.ctz", "i64.div_s",
      "i64.div_u", "i64.eq", "i64.eqz", "i64.extend16_s", "i64.extend32_s",
      "i64.extend8_s", "i64.extend_i32_s", "i64.extend_i32_u", "i64.ge_s", "i64.ge_u",
      "i64.gt_s", "i64.gt_u", "i64.le_s", "i64.le_u", "i64.load",
      "i64.load16_s", "i64.load16_u", "i64.load32_s", "i64.load32_u", "i64.load8_s",
      "i64.load8_u", "i64.lt_s", "i64.lt_u", "i64.mul", "i64.ne",
      "i64.or", "i64.popcnt", "i64.reinterpret_f64", "i64.rem_s", "i64.rem_u",
      "i64.rotl", "i64.rotr", "i64.shl", "i64.shr_s", "i64.shr_u",
      "i64.store", "i64.store16", "i64.store32", "i64.store8", "i64.sub",
      "i64.trunc_f32_s", "i64.trunc_f32_u", "i64.trunc_f64_s", "i64.trunc_f64_u", "i64.trunc_sat_f32_s",
      "i64.trunc_sat_f32_u", "i64.trunc_sat_f64_s", "i64.trunc_sat_f64_u", "i64.xor", "i8x16.shuffle",
      "if", "local.get", "local.set", "local.tee", "loop",
      "memory.copy", "memory.fill", "memory.grow", "memory.init", "memory.size",
      "nop", "ref.as_non_null", "ref.cast", "ref.eq", "ref.func",
      "ref.i31", "ref.is_null", "ref.null", "ref.test", "return",
      "return_call", "return_call_indirect", "return_call_ref", "select", "struct.get",
      "struct.get_s", "struct.get_u", "struct.new", "struct.new_default", "struct.set",
      "table.copy", "table.fill", "table.get", "table.grow", "table.init",
      "table.set", "table.size", "throw", "throw_ref", "try_table",
      "unreachable", "v128.const", "v128.load", "v128.load16_lane", "v128.load16_splat",
      "v128.load16x4_s", "v128.load16x4_u", "v128.load32_lane", "v128.load32_splat", "v128.load32_zero",
      "v128.load32x2_s", "v128.load32x2_u", "v128.load64_lane", "v128.load64_splat", "v128.load64_zero",
      "v128.load8_lane", "v128.load8_splat", "v128.load8x8_s", "v128.load8x8_u", "v128.store",
      "v128.store16_lane", "v128.store32_lane", "v128.store64_lane", "v128.store8_lane" ] do
    cacheOpcode opcode

/-- Specializing the validator's signature match also avoids generating a
large unused generic splitter when evaluating a concrete instruction. -/
private def cacheSignature (ctor : Name) : CommandElabM Unit := do
  let name := `Wasm.Decoder.Wat.ProofEval.signature ++ ctor
  liftTermElabM do
    let sig ← getConstInfoDefn ``Wasm.Instruction.straightSig
    let ci ← getConstInfoCtor ctor
    forallBoundedTelescope sig.type (some 2) fun ctx _ =>
      forallTelescope ci.type fun args _ => do
        let lhs := mkApp3 (mkConst sig.name) ctx[0]! ctx[1]! (mkAppN (mkConst ctor) args)
        let rhs ← whnf lhs
        let params := ctx ++ args
        let type ← mkForallFVars params (← mkEq lhs rhs)
        let value ← mkLambdaFVars params (← mkEqRefl lhs)
        addDecl (.thmDecl {name, levelParams := [], type, value})
  elabCommand (← `(attribute [cbv_eval] $(mkIdent name)))

set_option maxHeartbeats 4000000 in
run_cmd do
  let info ← liftTermElabM <| getConstInfoInduct ``Wasm.Instruction
  for ctor in info.ctors do cacheSignature ctor

end Wasm.Decoder.Wat.ProofEval
