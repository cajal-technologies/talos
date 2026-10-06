import Lean

open Lean

namespace CodeLib.Tactics

/-- Extra data for a memory/global step rule registered via `@[wasm_rule … mem …]`. -/
structure WasmMemRuleInfo where
  predWidth     : String  -- "u32" | "u64" | "byte" | "global"
  addrVariantThm : Name   -- offset-zero `_addr` theorem, or .anonymous
  deriving Inhabited

/-- Kind tag distinguishing pure-step rules from memory/global rules. -/
inductive WasmRuleKind
  | pure (needsRfl : Bool)
  | mem  (info : WasmMemRuleInfo)
  deriving Inhabited

/-- Data stored for each registered TWP/WP rule. -/
structure WasmRuleEntry where
  thmName : Name
  kind    : WasmRuleKind
  deriving Inhabited

-- NameMap is core Lean (RBMap Name α Name.lt); no extra import needed.
-- Key combines modality and ctor into one Name: e.g. twp ++ const = `twp.const`.
-- Each key holds an ordered array; entries are appended in registration order,
-- so the first entry registered is tried first by wasm_pure / wasm_mem.
abbrev WasmRuleMap := NameMap (Array WasmRuleEntry)

-- Flat tuple encoding:
-- (modality, ctor, thm, needsRfl, isMem, predWidth, addrVariant)
-- Pure rules: (mod, ctor, thm, needsRfl, false, "", .anonymous)
-- Mem rules:  (mod, ctor, thm, false,    true,  width, addrVariant)
private def wasmRuleAddEntry (m : WasmRuleMap)
    (entry : Name × Name × Name × Bool × Bool × String × Name) : WasmRuleMap :=
  let (mod, ctor, thm, needsRfl, isMem, predWidth, addrVariant) := entry
  let kind : WasmRuleKind :=
    if isMem then .mem { predWidth, addrVariantThm := addrVariant }
    else .pure needsRfl
  let key := mod ++ ctor
  m.insert key ((m.find? key |>.getD #[]).push { thmName := thm, kind })

initialize wasmRuleExt : SimplePersistentEnvExtension
    (Name × Name × Name × Bool × Bool × String × Name) WasmRuleMap ←
  registerSimplePersistentEnvExtension {
    addEntryFn    := wasmRuleAddEntry
    addImportedFn := fun nss =>
      nss.foldl (fun (m : WasmRuleMap) ns =>
        ns.foldl wasmRuleAddEntry m) (∅ : WasmRuleMap)
  }

/-- Look up all registered rules for a given modality and instruction constructor,
    in registration order (first registered = first tried). -/
def getWasmRule (env : Environment) (modality : Name) (ctor : Name) :
    Option (Array WasmRuleEntry) :=
  (wasmRuleExt.getState env).find? (modality ++ ctor)

-- Pure form: `@[wasm_rule <modality> <head>]` or `@[wasm_rule <modality> <head> rfl]`
syntax (name := wasm_rule)     "wasm_rule"     ident ident (&"rfl")? : attr
-- Mem form:  `@[wasm_mem_rule <modality> <head> <width> [<addrVariantThm>]?]`
-- Note: we avoid using "mem" as a keyword atom here because Lean 4 registers it
-- globally, which would break uses of `mem` as a field name elsewhere.
syntax (name := wasm_mem_rule) "wasm_mem_rule" ident ident  ident   (ident)? : attr

private def wasmRuleAddHandler (thmName : Name) (stx : Syntax) (_ : AttributeKind) : AttrM Unit := do
  let modality := stx[1].getId
  let head     := stx[2].getId
  -- Pure form: stx[3] is optional (&"rfl")
  let needsRfl := !stx[3].isNone
  modifyEnv (wasmRuleExt.addEntry · (modality, head, thmName, needsRfl, false, "", .anonymous))

private def wasmMemRuleAddHandler (thmName : Name) (stx : Syntax) (_ : AttributeKind) : AttrM Unit := do
  -- Mem form: stx[1]=modality, stx[2]=head, stx[3]=predWidth, stx[4]=optional addrVariant
  let modality  := stx[1].getId
  let head      := stx[2].getId
  let predWidth := stx[3].getId.getString!
  let addrVariant : Name :=
    if stx[4].isNone then .anonymous
    else
      let inner := stx[4].getArgs
      if inner.size > 0 then inner[0]!.getId else .anonymous
  modifyEnv (wasmRuleExt.addEntry · (modality, head, thmName, false, true, predWidth, addrVariant))

/-- `attribute [-wasm_rule]` is not supported: the registry is append-only and
an erased entry would silently survive in every module that imported it. -/
private def wasmRuleEraseUnsupported (attr : Name) : Name → AttrM Unit := fun decl =>
  throwError "attribute [-{attr}] is not supported (tried to erase it from {decl}); \
    the Wasm rule registry is append-only"

initialize registerBuiltinAttribute {
  name            := `wasm_rule
  descr           := "Register a TWP/WP pure-step rule for an instruction constructor."
  applicationTime := .afterCompilation
  add             := wasmRuleAddHandler
  erase           := wasmRuleEraseUnsupported `wasm_rule
}

initialize registerBuiltinAttribute {
  name            := `wasm_mem_rule
  descr           := "Register a TWP/WP memory/global step rule for an instruction constructor."
  applicationTime := .afterCompilation
  add             := wasmMemRuleAddHandler
  erase           := wasmRuleEraseUnsupported `wasm_mem_rule
}

/-! ## Definition-site registration for generated pure rules

`wasm_wp_pure_rule` / `wasm_twp_pure_rule` (in `SmallStepLifting` /
`SmallStepTotalLifting`) already name the instruction the rule retires, so they
register the generated theorem themselves: the registry is derived from the
rule definitions instead of being a hand-maintained copy of them.
-/

/-- The `@[wasm_rule]` registration a generated pure rule should carry, or
`none` when the instruction is not a literal constructor (e.g. the generic
`scalarFloat*` rules, whose instruction is a variable; those are registered
by hand next to their definitions).

* The key is the constructor in `instruction`: `.add` or `.const value`.
* The `rfl` flag is set when the first side condition is an equation
  (`result = if … then 1 else 0`, `selected = …`, `… = some bits`): `rfl`
  both proves it and fixes the result value. Other side conditions
  (`divisor ≠ 0`, …) are left to `wasm_pure`'s `rfl`/`decide` discharger. -/
def wasmPureRuleAttr? (modality : Name) (thm : Ident) (instruction : Term)
    (sideConditions : Array (TSyntax ``Lean.Parser.Term.bracketedBinder)) :
    MacroM (Option Command) := do
  let raw := instruction.raw
  let head := if raw.getKind == ``Lean.Parser.Term.app then raw[0] else raw
  unless head.getKind == ``Lean.Parser.Term.dotIdent do return none
  let ctor := mkIdent head[1].getId
  let modId := mkIdent modality
  -- explicitBinder: `(` ids (`:` type)? … `)`
  let isEq (b : TSyntax ``Lean.Parser.Term.bracketedBinder) : Bool :=
    b.raw[2][1].getKind == ``«term_=_»
  if (sideConditions[0]?.map isEq).getD false then
    return some (← `(command| attribute [wasm_rule $modId $ctor rfl] $thm))
  else
    return some (← `(command| attribute [wasm_rule $modId $ctor] $thm))

end CodeLib.Tactics
