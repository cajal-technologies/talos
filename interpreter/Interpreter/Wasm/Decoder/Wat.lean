import Interpreter.Wasm.Syntax
import Std.Data.HashMap

/-!
# WAT decoder

A small parser for the WebAssembly text format, targeting Wasm's AST.

Supported:
* `(module ...)` with any number of `(func ...)` definitions.
* `(type ...)`, `(export ...)`, `(import ...)`, `(table ...)`, `(memory ...)`,
  `(global ...)`, `(elem ...)`, `(data ...)`, `(tag ...)`, `(start ...)` —
  recognized at the module level and fully parsed into the resulting
  `Wasm.Module`. Non-func imports (`(import … (memory|global|table …))`)
  are parsed too: each becomes a placeholder decl at the low end of its
  index space and is recorded in `importedGlobals`/`importedTables`/
  `importedMemories` for later host substitution.
* Func headers may include `(type N)`, `(param ...)*`, `(result ...)*`,
  `(local ...)*` in any order, with grouped or singleton declarations.
* Linear instruction stream and folded operand expressions
  (`(i32.add (i32.const 1) (i32.const 2))`).
* Structured forms `block ... end`, `loop ... end`, `if ... else? ... end`,
  plus folded `(block …)`, `(loop …)`, `(if …)` forms.
* `br N`, `br_if N`, `br_table … N`, `call N`, `return`, `drop`, `select`,
  i32 / i64 numeric/comparison/bitwise/shift/rotate/conversion ops.
* Signed integer literals (`-`, `+`), hex (`0x…`/`0X…`) with mixed case, and
  underscore separators (`1_000_000`, `0xa_0f_00_99`).
* Numeric indices and symbolic identifiers (`$L`).
* `(;0;)` block comments and `;;` line comments are stripped during tokenization.

Memory loads/stores, `memory.*`, globals, `call_indirect`, tables,
floats, and SIMD are all modelled and decode to real instructions.
Instructions from proposals the interpreter still doesn't model (e.g.
atomics/threads) are accepted lexically but lowered to
`Wasm.Instruction.unreachable` so the surrounding function still
type-checks. `local.tee i` is desugared to `[local.set i; local.get i]`. -/

namespace Wasm.Decoder.Wat

inductive Sexpr where
  | atom (s : String)
  | list (xs : List Sexpr)
deriving Inhabited, Repr

abbrev Err := String

private def isWatSpace (c : Char) : Bool :=
  c = ' ' || c = '\t' || c = '\n' || c = '\r'

private def isAtomChar (c : Char) : Bool :=
  ¬ (isWatSpace c || c = '(' || c = ')')

private partial def dropLine : List Char → List Char
  | [] => []
  | '\n' :: r => '\n' :: r
  | _ :: r => dropLine r

private partial def dropBlock : Nat → List Char → List Char
  | _,         [] => []
  | depth,     '(' :: ';' :: r => dropBlock (depth + 1) r
  | 0,         ';' :: ')' :: r => r
  | depth + 1, ';' :: ')' :: r => dropBlock depth r
  | depth,     _ :: r => dropBlock depth r

private partial def copyString (cs : List Char) (acc : List Char) : List Char × List Char :=
  match cs with
  | [] => ([], acc)
  | '"' :: rest => (rest, '"' :: acc)
  | '\\' :: c :: rest => copyString rest (c :: '\\' :: acc)
  | c :: rest => copyString rest (c :: acc)

private partial def stripCommentsAux (cs : List Char) (acc : List Char) : List Char :=
  match cs with
  | ';' :: ';' :: rest => stripCommentsAux (dropLine rest) acc
  | '(' :: ';' :: rest => stripCommentsAux (dropBlock 0 rest) acc
  | '"' :: rest =>
    let (rest', acc') := copyString rest ('"' :: acc)
    stripCommentsAux rest' acc'
  | c :: rest => stripCommentsAux rest (c :: acc)
  | [] => acc.reverse

private def stripComments (s : String) : String :=
  String.ofList (stripCommentsAux s.toList [])

private partial def tokenizeAux (cs : List Char) (acc : List String) : List String :=
  match cs with
  | [] => acc.reverse
  | c :: rest =>
    if isWatSpace c then
      tokenizeAux rest acc
    else if c = '(' then
      tokenizeAux rest ("(" :: acc)
    else if c = ')' then
      tokenizeAux rest (")" :: acc)
    else if c = '"' then
      let (body, rest') := readString rest []
      tokenizeAux rest' (body :: acc)
    else
      let (atomChars, rest') := rest.span isAtomChar
      let atom := String.ofList (c :: atomChars)
      tokenizeAux rest' (atom :: acc)
where
  readString : List Char → List Char → String × List Char
    | [], acc => (String.ofList ('"' :: acc.reverse), [])
    | '"' :: rest, acc =>
      (String.ofList ('"' :: (acc.reverse ++ ['"'])), rest)
    | '\\' :: c :: rest, acc => readString rest (c :: '\\' :: acc)
    | c :: rest, acc => readString rest (c :: acc)

private def tokenize (s : String) : List String :=
  tokenizeAux (stripComments s).toList []

partial def parseSexprs : List String → Except Err (List Sexpr × List String)
  | [] => .ok ([], [])
  | ")" :: rest => .ok ([], ")" :: rest)
  | "(" :: rest => do
    let (children, rest1) ← parseSexprs rest
    match rest1 with
    | ")" :: rest2 =>
      let (siblings, rest3) ← parseSexprs rest2
      .ok (Sexpr.list children :: siblings, rest3)
    | _ => .error "unbalanced parens: missing ')'"
  | tok :: rest => do
    let (siblings, rest1) ← parseSexprs rest
    .ok (Sexpr.atom tok :: siblings, rest1)

def parseAll (s : String) : Except Err (List Sexpr) := do
  let (xs, rest) ← parseSexprs (tokenize s)
  match rest with
  | [] => .ok xs
  | _ => .error "unexpected ')'"

private def fromHexString? (s : String) : Option Nat := Id.run do
  if s.isEmpty then return none
  let mut acc := 0
  for c in s.toList do
    let d := if c.isDigit then some (c.toNat - '0'.toNat)
             else if 'a' ≤ c ∧ c ≤ 'f' then some (10 + c.toNat - 'a'.toNat)
             else if 'A' ≤ c ∧ c ≤ 'F' then some (10 + c.toNat - 'A'.toNat)
             else none
    match d with
    | none => return none
    | some d => acc := acc * 16 + d
  return some acc

private def stripUnderscores (s : String) : String :=
  String.ofList (s.toList.filter (· ≠ '_'))

private def parseUnsignedNat (s : String) : Except Err Nat :=
  if s.isEmpty then .error "empty integer literal"
  else if s.startsWith "0x" || s.startsWith "0X" then
    match fromHexString? (s.drop 2).toString with
    | some n => .ok n
    | none => .error s!"bad integer literal: {s}"
  else
    match s.toNat? with
    | some n => .ok n
    | none => .error s!"bad integer literal: {s}"

def parseU32 (s : String) : Except Err UInt32 := do
  let n ← parseUnsignedNat s
  if n ≥ 2 ^ 32 then .error s!"integer out of range: {s}"
  else .ok (UInt32.ofNat n)

private def parseNat (s : String) : Except Err Nat := do
  let v ← parseU32 s
  .ok v.toNat

private def parseIntLiteral (s : String) (bits : Nat) : Except Err Nat := do
  let (neg, body0) :=
    if s.startsWith "-" then (true, (s.drop 1).toString)
    else if s.startsWith "+" then (false, (s.drop 1).toString)
    else (false, s)
  let body := stripUnderscores body0
  let n ← parseUnsignedNat body
  let bound := 2 ^ bits
  let halfBound := 2 ^ (bits - 1)
  if neg then
    if n > halfBound then .error s!"integer out of range: {s}"
    else .ok ((bound - n) % bound)
  else
    if n ≥ bound then .error s!"integer out of range: {s}"
    else .ok n

def parseI32 (s : String) : Except Err UInt32 := do
  let n ← parseIntLiteral s 32
  .ok (UInt32.ofNat n)

def parseI64 (s : String) : Except Err UInt64 := do
  let n ← parseIntLiteral s 64
  .ok (UInt64.ofNat n)

/-! ## Float literal parsing

`wasm-tools print` emits float constants as hex floats (`0x1.91eb86p+1`),
`inf`, `nan`, or `nan:0x…`; raw `.wat` may also use decimal (`3.14`, `1e10`).
A hex float is `mantissa · 2^exp`, which native `Float` reproduces exactly;
decimal goes through `Float.ofScientific` (correctly rounded). The `f32`
encoder rounds the `f64` magnitude to single precision — exact for every
value `wasm-tools` prints, since those round-trip. -/

private def floatMulPow2 : Float → Nat → Float
  | x, 0 => x
  | x, n + 1 => floatMulPow2 (x * 2.0) n
private def floatDivPow2 : Float → Nat → Float
  | x, 0 => x
  | x, n + 1 => floatDivPow2 (x / 2.0) n
private def floatScalePow2 (x : Float) (e : Int) : Float :=
  if e ≥ 0 then floatMulPow2 x e.toNat else floatDivPow2 x (-e).toNat

private def parseDecExp (s : String) : Except Err Int :=
  if s.isEmpty then .ok 0
  else
    let (neg, body) :=
      if s.startsWith "-" then (true, (s.drop 1).toString)
      else if s.startsWith "+" then (false, (s.drop 1).toString)
      else (false, s)
    match body.toNat? with
    | some n => .ok (if neg then -(Int.ofNat n) else Int.ofNat n)
    | none   => .error s!"bad float exponent: {s}"

/-- Magnitude of a hex float `INT[.FRAC][p±EXP]` (no `0x`, no sign). -/
private def parseHexFloatMag (body : String) : Except Err Float := do
  let (mant, expS) := match (body.replace "P" "p").splitOn "p" with
    | [m]          => (m, "")
    | m :: e :: _  => (m, e)
    | []           => ("", "")
  let (intH, fracH) := match mant.splitOn "." with
    | [i]          => (i, "")
    | i :: f :: _  => (i, f)
    | []           => ("", "")
  let m := (fromHexString? (intH ++ fracH)).getD 0
  let e ← parseDecExp expS
  .ok (floatScalePow2 (Float.ofNat m) (e - 4 * Int.ofNat fracH.length))

/-- Magnitude of a decimal float `INT[.FRAC][e±EXP]` (no sign). -/
private def parseDecFloatMag (body : String) : Except Err Float := do
  let (mant, expS) := match (body.replace "E" "e").splitOn "e" with
    | [m]          => (m, "")
    | m :: e :: _  => (m, e)
    | []           => ("", "")
  let (intP, fracP) := match mant.splitOn "." with
    | [i]          => (i, "")
    | i :: f :: _  => (i, f)
    | []           => ("", "")
  let m := ((intP ++ fracP).toNat?).getD 0
  let de ← parseDecExp expS
  let exp := de - Int.ofNat fracP.length
  .ok (Float.ofScientific m (exp < 0) exp.natAbs)

/-- Sign and width-independent body of a float literal. -/
private inductive FloatLitBody where
  | finite (mag : Float)
  | inf
  | nan (payload : Option Nat)

private def classifyFloatLit (s : String) : Except Err (Bool × FloatLitBody) := do
  let (neg, r0) :=
    if s.startsWith "-" then (true, (s.drop 1).toString)
    else if s.startsWith "+" then (false, (s.drop 1).toString)
    else (false, s)
  let r := stripUnderscores r0
  if r == "inf" then .ok (neg, .inf)
  else if r == "nan" || r == "nan:canonical" || r == "nan:arithmetic" then
    .ok (neg, .nan none)
  else if r.startsWith "nan:0x" then
    match fromHexString? (r.drop 6).toString with
    | some p => .ok (neg, .nan (some p))
    | none   => .error s!"bad nan payload: {s}"
  else if r.startsWith "0x" || r.startsWith "0X" then
    .ok (neg, .finite (← parseHexFloatMag (r.drop 2).toString))
  else
    .ok (neg, .finite (← parseDecFloatMag r))

/-- Parse a WAT `f64` literal into its 64-bit IEEE-754 encoding. -/
def parseF64Lit (s : String) : Except Err UInt64 := do
  match (← classifyFloatLit s) with
  | (neg, .finite mag) => .ok (if neg then (-mag).toBits else mag.toBits)
  | (neg, .inf)        => .ok (if neg then 0xFFF0000000000000 else 0x7FF0000000000000)
  | (neg, .nan none)   => .ok (if neg then 0xFFF8000000000000 else 0x7FF8000000000000)
  | (neg, .nan (some p)) =>
    let base : UInt64 := 0x7FF0000000000000 ||| UInt64.ofNat (p % 0x10000000000000)
    .ok (if neg then base ||| 0x8000000000000000 else base)

/-- Parse a WAT `f32` literal into its 32-bit IEEE-754 encoding. -/
def parseF32Lit (s : String) : Except Err UInt32 := do
  match (← classifyFloatLit s) with
  | (neg, .finite mag) => .ok (if neg then (-mag).toFloat32.toBits else mag.toFloat32.toBits)
  | (neg, .inf)        => .ok (if neg then 0xFF800000 else 0x7F800000)
  | (neg, .nan none)   => .ok (if neg then 0xFFC00000 else 0x7FC00000)
  | (neg, .nan (some p)) =>
    let base : UInt32 := 0x7F800000 ||| UInt32.ofNat (p % 0x800000)
    .ok (if neg then base ||| 0x80000000 else base)

/-- Decode a value-type atom. Numeric types and the two reference types
of wasm 2.0 (`funcref`, `externref`) are modelled directly. Types from
proposals the interpreter doesn't yet model (SIMD, GC) are accepted at
the decoder level — silently normalised to `i32` — so that modules
which include such types in *signatures* still decode. Functions whose
bodies actually touch those types will hit `unreachable` (because the
corresponding instructions are also lowered to `unreachable`), giving
the testsuite runner a chance to run any supported exports declared in
the same module. -/
private def atomToValueType? : String → Option Wasm.ValueType
  | "i32"       => some .i32
  | "i64"       => some .i64
  | "f32"       => some .f32
  | "f64"       => some .f64
  | "funcref"   => some .funcref
  | "externref" => some .externref
  | "exnref"    => some .exnref
  | "v128"      => some .v128
  -- GC managed reference types (GC proposal) collapse to the `anyref` slot.
  | "anyref"    => some .anyref
  | "eqref"     => some .anyref
  | "i31ref"    => some .anyref
  | "structref" => some .anyref
  | "arrayref"  => some .anyref
  | "nullref"   => some .anyref
  | "nullfuncref"   => some .funcref
  | "nullexternref" => some .externref
  | _     => none

private def isNullFuncrefHeapType (ht : String) : Bool :=
  ht == "func" || ht == "nofunc"

private def isNullExternrefHeapType (ht : String) : Bool :=
  ht == "extern" || ht == "noextern"

/-- Decode a reference value-type written in list form, e.g.
`(ref func)`, `(ref null extern)`, `(ref $t)`. Symbolic and numeric heap
types refer to the type table — pre-GC those are function types, so they
map to `funcref`; GC heap types keep the `i32` placeholder used for
unmodelled proposals. -/
private def listToValueType (xs : List Sexpr) : Wasm.ValueType :=
  match xs with
  | [.atom "ref", .atom ht] | [.atom "ref", .atom "null", .atom ht] =>
    if isNullFuncrefHeapType ht then .funcref
    else if isNullExternrefHeapType ht then .externref
    -- GC abstract heap types (GC proposal): a managed reference type, so its
    -- zero is the managed null `anyref`.
    else if ht == "any" || ht == "eq" || ht == "i31"
         || ht == "struct" || ht == "array" || ht == "none" then .anyref
    -- A concrete `(ref $t)` / `(ref N)` in GC modules is overwhelmingly a
    -- struct/array type; treat it as a managed reference so its zero is the
    -- managed null. (Typed-funcref locals are set before use, so only the
    -- unused zero-init differs.)
    else if ht.startsWith "$" || ht.all Char.isDigit then .anyref
    else .i32
  | _ => .i32

/-- Resolve a `(type N)` reference on a block/loop/if to the signature
declared in the module's type table. Returns `none` if the index/id is
unknown or the entry's signature is outside our supported integer
subset; callers fall back to whatever inline `(param ...)` /
`(result ...)` annotations follow. Constructed by `parseFunc` and
threaded through `Ctx` so block/loop/if parsing can see the type table. -/
abbrev BlockTypeResolver :=
  String → Option (List Wasm.ValueType × List Wasm.ValueType)

/-- Skip block/loop/if type annotations and collect explicit param/result
types. The block constructors `Wasm.Instruction.block` / `loop` / `iff`
carry only arities (`paramArity`, `resultArity`), so we throw away the
element types after counting them — but we *do* honour `(type N)`
references by consulting the module's type table via `resolveType`, so
a `block (type $sig)` whose entry declares non-zero arities is parsed
with the correct arities instead of silently degenerating to `0 0`. -/
private partial def skipBlockType (resolveType : BlockTypeResolver) :
    List Wasm.ValueType → List Wasm.ValueType → List Sexpr →
    List Wasm.ValueType × List Wasm.ValueType × List Sexpr
  | ps, rs, .list (.atom "result" :: ts) :: r =>
    let extra := ts.filterMap fun
      | .atom a => atomToValueType? a
      | .list l => some (listToValueType l)
    skipBlockType resolveType ps (rs ++ extra) r
  | ps, rs, .list (.atom "param" :: ts) :: r =>
    let extra := ts.filterMap fun
      | .atom a => atomToValueType? a
      | .list l => some (listToValueType l)
    skipBlockType resolveType (ps ++ extra) rs r
  | ps, rs, .list (.atom "type" :: .atom ref :: _) :: r =>
    -- A `(type N)` annotation adopts the type-table entry's signature as
    -- the block's arity. wasm-tools commonly emits a redundant
    -- `(type N) (param …) (result …)` triple where the inline forms
    -- restate the resolved signature, so we also consume any trailing
    -- `(param …)` / `(result …)` siblings to avoid double-counting.
    -- If resolution fails, fall through to the inline accumulators.
    match resolveType ref with
    | some (resolvedPs, resolvedRs) =>
      let r' := r.dropWhile fun
        | .list (.atom "param" :: _)  => true
        | .list (.atom "result" :: _) => true
        | _ => false
      (resolvedPs, resolvedRs, r')
    | none => skipBlockType resolveType ps rs r
  | ps, rs, .list (.atom "type" :: _) :: r =>
    -- Malformed `(type …)` form (no atom reference) — preserve the old
    -- behaviour of silently advancing the token stream.
    skipBlockType resolveType ps rs r
  | ps, rs, .atom a :: r =>
    match atomToValueType? a with
    | some t => (ps, rs ++ [t], r)
    | none   => (ps, rs, .atom a :: r)
  | ps, rs, xs => (ps, rs, xs)

/-- Pull an optional `$label` and any `(type N)` / `(param T*)` /
`(result T*)` annotations off the front of a block/loop/if's tokens.
Returns the label (if any), parameter arity, result arity, and the
remaining tokens. `resolveType` looks up `(type N)` references against
the module's type table; pass `fun _ => none` (or `Ctx.empty`'s default)
when no type table is available. -/
private def parseBlockHeader (resolveType : BlockTypeResolver) (xs : List Sexpr)
    : Option String × Nat × Nat × List Sexpr :=
  match xs with
  | .atom a :: r =>
    if a.startsWith "$" then
      let (ps, rs, r') := skipBlockType resolveType [] [] r
      (some (a.drop 1).toString, ps.length, rs.length, r')
    else
      let (ps, rs, r') := skipBlockType resolveType [] [] xs
      (none, ps.length, rs.length, r')
  | _ =>
    let (ps, rs, r') := skipBlockType resolveType [] [] xs
    (none, ps.length, rs.length, r')

/-- A module-level `(type (func …))` declaration: optional symbolic id and
the signature, if it has one we can model. Pulled up before `Ctx` so the
ctx can carry the collected type table for `call_indirect (type N)`
resolution. -/
private structure TypeEntry where
  symId : Option String
  sig   : Option (List Wasm.ValueType × List Wasm.ValueType)
  /-- GC composite type (struct/array/func) for this entry, if recognised
  (GC proposal). Filled alongside `sig`. -/
  comp     : Option Wasm.CompositeType := none
  /-- Unresolved `sub $super` reference, resolved to an index in
  `parseModule` once the whole type table is known. -/
  superRef : Option String := none
  /-- For a struct type, the field names (`(field $x …)`), positionally;
  `none` for anonymous fields. Used to resolve `struct.get $t $field`. -/
  fieldNames : List (Option String) := []
  /-- `false` when declared `(sub …)` without `final` (open for subtyping). -/
  isFinal : Bool := true
  /-- Recursion-group marker for members of a multi-member `(rec …)` group
  (the group's first type index); `none` for singleton groups. Threaded
  into `GcTypeDef.recGroup` for iso-recursive type equivalence. -/
  recGroup : Option Nat := none
deriving Inhabited

structure Ctx where
  funcIds          : Std.HashMap String Nat
  localIds         : Std.HashMap String Nat
  globalIds        : Std.HashMap String Nat := {}
  labelNames       : List (Option String) := []
  /-- All `(type (func …))` declarations collected at module level, in
  source order. Carries the symbolic id (if any) and signature so
  `call_indirect (type $T)` can resolve to a numeric type index. -/
  types            : Array TypeEntry := #[]
  /-- `$name → table index` for `(table $name ...)` declarations. The
  testsuite almost always uses table 0 implicitly, but the form is
  legal. -/
  tableNames       : Std.HashMap String Nat := {}
  /-- `$name → element segment index` for `(elem $name ...)` declarations,
  so `table.init` / `elem.drop` can resolve symbolic segment refs. -/
  elemNames        : Std.HashMap String Nat := {}
  /-- `$name → memory index` for `(memory $name ...)` declarations
  (multi-memory). -/
  memNames         : Std.HashMap String Nat := {}
  /-- `$name → tag index` for `(tag $name ...)` declarations
  (exception handling). -/
  tagNames         : Std.HashMap String Nat := {}
  /-- Resolves `(type N)` / `(type $sig)` references on `block`/`loop`/`if`
  to the parsed signature, so multi-value block-types declared via the
  type table are decoded with their correct arity. Defaults to "always
  none" — callers without a type table behave exactly as before. -/
  resolveBlockType : BlockTypeResolver := fun _ => none

def Ctx.empty : Ctx := { funcIds := {}, localIds := {} }

def Ctx.pushLabel (ctx : Ctx) (name : Option String) : Ctx :=
  { ctx with labelNames := name :: ctx.labelNames }

private def resolveNamed (table : Std.HashMap String Nat) (kind : String)
    (s : String) : Except Err Nat :=
  if s.startsWith "$" then
    match table[(s.drop 1).toString]? with
    | some i => .ok i
    | none => .error s!"unknown {kind} id: {s}"
  else parseNat s

/-- Decode a `ref.null ht` heap-type immediate into the matching null-ref
push. Heap types from proposals we don't model decode to `unreachable`
(consistent with their other instructions). -/
private def refNullInstr (types : Array TypeEntry) (ht : String) : Wasm.Instruction :=
  if isNullFuncrefHeapType ht then .refNull
  else if isNullExternrefHeapType ht then .refNullExtern
  -- GC abstract heap types (GC proposal): the null they denote is the
  -- shared managed null `anyref`.
  else if ht == "any" || ht == "eq" || ht == "i31"
       || ht == "struct" || ht == "array" || ht == "none" then .gc .refNullAny
  -- Exception heap types (exception-handling proposal): the null they denote
  -- is the null `exnref`.
  else if ht == "exn" || ht == "noexn" then .refNullExn
  -- Concrete heap types (`$t` / numeric): a struct/array type denotes the
  -- managed null; a function type denotes the null funcref.
  else if ht.startsWith "$" || ht.all Char.isDigit then
    let idx? := if ht.startsWith "$" then
        types.findIdx? (·.symId = some (ht.drop 1).toString)
      else ht.toNat?
    match idx?.bind (fun i => (types[i]?).bind (·.comp)) with
    | some (.struct _) | some (.array _) => .gc .refNullAny
    | _ => .refNull
  else .unreachable

private def dropTrailingLabel : List Sexpr → List Sexpr
  | .atom a :: r => if a.startsWith "$" then r else .atom a :: r
  | xs => xs

private def resolveLabel (ctx : Ctx) (s : String) : Except Err Nat :=
  if s.startsWith "$" then
    let name := (s.drop 1).toString
    match ctx.labelNames.findIdx? (fun n => n = some name) with
    | some i => .ok i
    | none => .error s!"unknown label id: {s}"
  else parseNat s

/-- Parse a single bare-op atom (no immediate, no folded operands). -/
private def parsePlainOp : String → Except Err Wasm.Instruction
  | "i32.add"   => .ok .add
  | "i32.sub"   => .ok .sub
  | "i32.mul"   => .ok .mul
  | "i32.div_u" => .ok .divU
  | "i32.div_s" => .ok .divS
  | "i32.rem_u" => .ok .remU
  | "i32.rem_s" => .ok .remS
  | "i32.eqz"   => .ok .eqz
  | "i32.eq"    => .ok .eq
  | "i32.ne"    => .ok .ne
  | "i32.lt_u"  => .ok .ltU
  | "i32.lt_s"  => .ok .ltS
  | "i32.gt_u"  => .ok .gtU
  | "i32.gt_s"  => .ok .gtS
  | "i32.le_u"  => .ok .leU
  | "i32.le_s"  => .ok .leS
  | "i32.ge_u"  => .ok .geU
  | "i32.ge_s"  => .ok .geS
  | "i32.and"   => .ok .and
  | "i32.or"    => .ok .or
  | "i32.xor"   => .ok .xor
  | "i32.shl"   => .ok .shl
  | "i32.shr_u" => .ok .shrU
  | "i32.shr_s" => .ok .shrS
  | "i32.rotl"  => .ok .rotl
  | "i32.rotr"  => .ok .rotr
  | "i32.clz"   => .ok .clz
  | "i32.ctz"   => .ok .ctz
  | "i32.popcnt" => .ok .popcnt
  | "i64.add"   => .ok .addI64
  | "i64.sub"   => .ok .subI64
  | "i64.mul"   => .ok .mulI64
  | "i64.eq"    => .ok .eqI64
  | "i64.lt_s"  => .ok .ltSI64
  | "i64.gt_s"  => .ok .gtSI64
  | "i64.gt_u"  => .ok .gtUI64
  | "i64.lt_u"  => .ok .ltUI64
  | "i64.le_u"  => .ok .leUI64
  | "i64.le_s"  => .ok .leSI64
  | "i64.ge_u"  => .ok .geUI64
  | "i64.ge_s"  => .ok .geSI64
  | "i64.ne"    => .ok .neI64
  | "i64.eqz"   => .ok .eqzI64
  | "i64.div_u" => .ok .divUI64
  | "i64.div_s" => .ok .divSI64
  | "i64.rem_u" => .ok .remUI64
  | "i64.rem_s" => .ok .remSI64
  | "i64.and"   => .ok .andI64
  | "i64.or"    => .ok .orI64
  | "i64.xor"   => .ok .xorI64
  | "i64.shl"   => .ok .shlI64
  | "i64.shr_u" => .ok .shrUI64
  | "i64.shr_s" => .ok .shrSI64
  | "i64.rotl"  => .ok .rotlI64
  | "i64.rotr"  => .ok .rotrI64
  | "i64.clz"   => .ok .clzI64
  | "i64.ctz"   => .ok .ctzI64
  | "i64.popcnt" => .ok .popcntI64
  | "i32.wrap_i64"     => .ok .wrapI64
  | "i64.extend_i32_s" => .ok .extendSI32
  | "i64.extend_i32_u" => .ok .extendUI32
  | "i32.extend8_s"    => .ok .extend8S
  | "i32.extend16_s"   => .ok .extend16S
  | "i64.extend8_s"    => .ok .extend8SI64
  | "i64.extend16_s"   => .ok .extend16SI64
  | "i64.extend32_s"   => .ok .extend32SI64
  | "drop"      => .ok .drop
  | "return"    => .ok .ret
  | "select"    => .ok .select
  | "nop"       => .ok .nop
  | "unreachable" => .ok .unreachable
  -- f32 arithmetic / unary / comparison
  | "f32.add" => .ok .f32Add
  | "f32.sub" => .ok .f32Sub
  | "f32.mul" => .ok .f32Mul
  | "f32.div" => .ok .f32Div
  | "f32.min" => .ok .f32Min
  | "f32.max" => .ok .f32Max
  | "f32.copysign" => .ok .f32Copysign
  | "f32.abs" => .ok .f32Abs
  | "f32.neg" => .ok .f32Neg
  | "f32.sqrt" => .ok .f32Sqrt
  | "f32.ceil" => .ok .f32Ceil
  | "f32.floor" => .ok .f32Floor
  | "f32.trunc" => .ok .f32Trunc
  | "f32.nearest" => .ok .f32Nearest
  | "f32.eq" => .ok .f32Eq
  | "f32.ne" => .ok .f32Ne
  | "f32.lt" => .ok .f32Lt
  | "f32.gt" => .ok .f32Gt
  | "f32.le" => .ok .f32Le
  | "f32.ge" => .ok .f32Ge
  -- f64 arithmetic / unary / comparison
  | "f64.add" => .ok .f64Add
  | "f64.sub" => .ok .f64Sub
  | "f64.mul" => .ok .f64Mul
  | "f64.div" => .ok .f64Div
  | "f64.min" => .ok .f64Min
  | "f64.max" => .ok .f64Max
  | "f64.copysign" => .ok .f64Copysign
  | "f64.abs" => .ok .f64Abs
  | "f64.neg" => .ok .f64Neg
  | "f64.sqrt" => .ok .f64Sqrt
  | "f64.ceil" => .ok .f64Ceil
  | "f64.floor" => .ok .f64Floor
  | "f64.trunc" => .ok .f64Trunc
  | "f64.nearest" => .ok .f64Nearest
  | "f64.eq" => .ok .f64Eq
  | "f64.ne" => .ok .f64Ne
  | "f64.lt" => .ok .f64Lt
  | "f64.gt" => .ok .f64Gt
  | "f64.le" => .ok .f64Le
  | "f64.ge" => .ok .f64Ge
  -- integer → float
  | "f32.convert_i32_s" => .ok .f32ConvertI32S
  | "f32.convert_i32_u" => .ok .f32ConvertI32U
  | "f32.convert_i64_s" => .ok .f32ConvertI64S
  | "f32.convert_i64_u" => .ok .f32ConvertI64U
  | "f64.convert_i32_s" => .ok .f64ConvertI32S
  | "f64.convert_i32_u" => .ok .f64ConvertI32U
  | "f64.convert_i64_s" => .ok .f64ConvertI64S
  | "f64.convert_i64_u" => .ok .f64ConvertI64U
  -- float → integer (trapping)
  | "i32.trunc_f32_s" => .ok .i32TruncF32S
  | "i32.trunc_f32_u" => .ok .i32TruncF32U
  | "i32.trunc_f64_s" => .ok .i32TruncF64S
  | "i32.trunc_f64_u" => .ok .i32TruncF64U
  | "i64.trunc_f32_s" => .ok .i64TruncF32S
  | "i64.trunc_f32_u" => .ok .i64TruncF32U
  | "i64.trunc_f64_s" => .ok .i64TruncF64S
  | "i64.trunc_f64_u" => .ok .i64TruncF64U
  -- float → integer (saturating)
  | "i32.trunc_sat_f32_s" => .ok .i32TruncSatF32S
  | "i32.trunc_sat_f32_u" => .ok .i32TruncSatF32U
  | "i32.trunc_sat_f64_s" => .ok .i32TruncSatF64S
  | "i32.trunc_sat_f64_u" => .ok .i32TruncSatF64U
  | "i64.trunc_sat_f32_s" => .ok .i64TruncSatF32S
  | "i64.trunc_sat_f32_u" => .ok .i64TruncSatF32U
  | "i64.trunc_sat_f64_s" => .ok .i64TruncSatF64S
  | "i64.trunc_sat_f64_u" => .ok .i64TruncSatF64U
  -- float ↔ float and bitwise reinterpret
  | "f32.demote_f64"      => .ok .f32DemoteF64
  | "f64.promote_f32"     => .ok .f64PromoteF32
  | "i32.reinterpret_f32" => .ok .i32ReinterpretF32
  | "i64.reinterpret_f64" => .ok .i64ReinterpretF64
  | "f32.reinterpret_i32" => .ok .f32ReinterpretI32
  | "f64.reinterpret_i64" => .ok .f64ReinterpretI64
  | "ref.is_null"  => .ok .refIsNull
  -- GC reference instructions (GC proposal).
  | "ref.i31"      => .ok (.gc .refI31)
  | "i31.get_s"    => .ok (.gc .i31GetS)
  | "i31.get_u"    => .ok (.gc .i31GetU)
  | "ref.eq"       => .ok (.gc .refEq)
  | op          =>
    -- Fallback for mnemonics not matched above (and not caught by
    -- `simdOp?`): still-unmodelled proposals such as atomics/threads and
    -- relaxed SIMD, plus stray leftovers from partly-modelled proposals
    -- (reference types, tables, GC, exceptions, tail calls). Lower them to
    -- `unreachable` so modules whose *signatures* or unrelated functions
    -- touch these features still decode; a function that actually executes
    -- such an instruction traps with "unreachable" instead of failing to
    -- decode at all, which would cascade to every assert in the file.
    if op.startsWith "f32." || op.startsWith "f64." || op.startsWith "v128."
       || op.startsWith "i8x16." || op.startsWith "i16x8." || op.startsWith "i32x4."
       || op.startsWith "i64x2." || op.startsWith "f32x4." || op.startsWith "f64x2."
       || op.startsWith "ref." || op.startsWith "table." || op.startsWith "elem."
       || op.startsWith "struct." || op.startsWith "array." || op.startsWith "i31."
       || op.startsWith "br_on_" || op.startsWith "extern."
       || op == "throw" || op == "throw_ref" || op == "rethrow" || op == "try"
       || op == "try_table" || op == "catch" || op == "catch_all" || op == "delegate"
       || op == "return_call" || op == "return_call_indirect" || op == "return_call_ref"
       || op == "call_ref" || op == "any.convert_extern"
       || op == "memory.atomic.notify" || op.startsWith "memory.atomic."
       || op.startsWith "atomic." then
      .ok .unreachable
    else
      .error s!"unsupported instruction: {op}"

/-- Memory ops that take an offset immediate, mapped to their natural
alignment (byte width). `offset=`/`align=` attributes are parsed off the
token stream; `memOpToInstruction` then emits the real load/store. -/
private def isMemOp (op : String) : Option Nat :=
  match op with
  | "i32.load"     => some 4
  | "i32.load8_u"  | "i32.load8_s"  => some 1
  | "i32.load16_u" | "i32.load16_s" => some 2
  | "i32.store"    => some 4
  | "i32.store8"   => some 1
  | "i32.store16"  => some 2
  | "i64.load"     => some 8
  | "i64.load8_u"  | "i64.load8_s"  => some 1
  | "i64.load16_u" | "i64.load16_s" => some 2
  | "i64.load32_u" | "i64.load32_s" => some 4
  | "i64.store"    => some 8
  | "i64.store8"   => some 1
  | "i64.store16"  => some 2
  | "i64.store32"  => some 4
  -- Float and SIMD memory ops (their offset=/align= attributes parsed the
  -- same way); `memOpToInstruction` emits the matching real load/store.
  | "f32.load" | "f32.store" => some 4
  | "f64.load" | "f64.store" => some 8
  | "v128.load" | "v128.store" => some 16
  | "v128.load8x8_u" | "v128.load8x8_s" => some 8
  | "v128.load16x4_u" | "v128.load16x4_s" => some 8
  | "v128.load32x2_u" | "v128.load32x2_s" => some 8
  | "v128.load8_splat" => some 1
  | "v128.load16_splat" => some 2
  | "v128.load32_splat" | "v128.load32_zero" => some 4
  | "v128.load64_splat" | "v128.load64_zero" => some 8
  | "v128.load8_lane" | "v128.store8_lane" => some 1
  | "v128.load16_lane" | "v128.store16_lane" => some 2
  | "v128.load32_lane" | "v128.store32_lane" => some 4
  | "v128.load64_lane" | "v128.store64_lane" => some 8
  | _              => none

private def parseEqImmediate (pref : String) (s : String) : Option Nat :=
  if s.startsWith pref then
    let body := stripUnderscores (s.drop pref.length).toString
    match parseUnsignedNat body with
    | .ok n => some n
    | .error _ => none
  else none

private def isPowerOfTwo (n : Nat) : Bool :=
  n ≠ 0 && n &&& (n - 1) = 0

/-- Pull optional `offset=N` and `align=N` atoms off the front of `toks`.
Returns the parsed byte offset (default 0) and the remaining tokens. -/
private def consumeMemAttrs (natAlign : Nat) (toks : List Sexpr)
    : Except Err (UInt32 × List Sexpr) :=
  let rec loop (offset : UInt32) (toks : List Sexpr) : Except Err (UInt32 × List Sexpr) :=
    match toks with
    | .atom a :: r =>
      match parseEqImmediate "offset=" a with
      | some n => loop (UInt32.ofNat n) r
      | none =>
        match parseEqImmediate "align=" a with
        | some n =>
          if !isPowerOfTwo n then
            .error s!"alignment must be a positive power of two: {a}"
          else if n > natAlign then
            .error s!"alignment must not exceed natural ({natAlign}): {a}"
          else loop offset r
        | none => .ok (offset, .atom a :: r)
    | xs => .ok (offset, xs)
  loop 0 toks

/-! ## SIMD mnemonic table

Shape-prefixed mnemonics (`i8x16.add`, `f64x2.pmin`, …) decode through
`simdOp?`; the per-shape availability of an op (e.g. `mul` only on
i16x8/i32x4/i64x2) is validation's concern, not the decoder's. -/

private def simdShapeOfPrefix? : String → Option Wasm.Simd.Shape
  | "i8x16" => some .i8x16
  | "i16x8" => some .i16x8
  | "i32x4" => some .i32x4
  | "i64x2" => some .i64x2
  | "f32x4" => some .f32x4
  | "f64x2" => some .f64x2
  | _ => none

private def simdShapeIsFloat : Wasm.Simd.Shape → Bool
  | .f32x4 | .f64x2 => true
  | _ => false

private def simdICmp? : String → Option Wasm.Simd.ICmp
  | "eq" => some .eq | "ne" => some .ne
  | "lt_s" => some .ltS | "lt_u" => some .ltU
  | "gt_s" => some .gtS | "gt_u" => some .gtU
  | "le_s" => some .leS | "le_u" => some .leU
  | "ge_s" => some .geS | "ge_u" => some .geU
  | _ => none

private def simdFCmp? : String → Option Wasm.Simd.FCmp
  | "eq" => some .eq | "ne" => some .ne
  | "lt" => some .lt | "gt" => some .gt
  | "le" => some .le | "ge" => some .ge
  | _ => none

/-- Decode a no-immediate SIMD mnemonic. -/
private def simdOp? (op : String) : Option Wasm.Instruction :=
  match op with
  | "v128.not"       => some (.vUnOp .not)
  | "v128.and"       => some (.vBinOp .and)
  | "v128.andnot"    => some (.vBinOp .andnot)
  | "v128.or"        => some (.vBinOp .or)
  | "v128.xor"       => some (.vBinOp .xor)
  | "v128.bitselect" => some .vBitselect
  | "v128.any_true"  => some (.vTestOp .anyTrue)
  | _ =>
    match op.splitOn "." with
    | [pre, name] =>
      match simdShapeOfPrefix? pre with
      | none => none
      | some sh =>
        let flt := simdShapeIsFloat sh
        match name with
        | "splat"    => some (.vSplat sh)
        | "all_true" => some (.vTestOp (.allTrue sh))
        | "bitmask"  => some (.vTestOp (.bitmask sh))
        | "shl"      => some (.vShiftOp (.shl sh))
        | "shr_s"    => some (.vShiftOp (.shrS sh))
        | "shr_u"    => some (.vShiftOp (.shrU sh))
        | "neg"      => some (.vUnOp (if flt then .fNeg sh else .intNeg sh))
        | "abs"      => some (.vUnOp (if flt then .fAbs sh else .intAbs sh))
        | "popcnt"   => some (.vUnOp .popcnt)
        | "sqrt"     => some (.vUnOp (.fSqrt sh))
        | "ceil"     => some (.vUnOp (.fCeil sh))
        | "floor"    => some (.vUnOp (.fFloor sh))
        | "trunc"    => some (.vUnOp (.fTrunc sh))
        | "nearest"  => some (.vUnOp (.fNearest sh))
        | "add"      => some (.vBinOp (if flt then .fAdd sh else .add sh))
        | "sub"      => some (.vBinOp (if flt then .fSub sh else .sub sh))
        | "mul"      => some (.vBinOp (if flt then .fMul sh else .mul sh))
        | "div"      => some (.vBinOp (.fDiv sh))
        | "min"      => some (.vBinOp (.fMin sh))
        | "max"      => some (.vBinOp (.fMax sh))
        | "pmin"     => some (.vBinOp (.fPmin sh))
        | "pmax"     => some (.vBinOp (.fPmax sh))
        | "min_s"    => some (.vBinOp (.minI sh true))
        | "min_u"    => some (.vBinOp (.minI sh false))
        | "max_s"    => some (.vBinOp (.maxI sh true))
        | "max_u"    => some (.vBinOp (.maxI sh false))
        | "add_sat_s" => some (.vBinOp (.addSat sh true))
        | "add_sat_u" => some (.vBinOp (.addSat sh false))
        | "sub_sat_s" => some (.vBinOp (.subSat sh true))
        | "sub_sat_u" => some (.vBinOp (.subSat sh false))
        | "avgr_u"   => some (.vBinOp (.avgrU sh))
        | "swizzle"  => some (.vBinOp .swizzle)
        | "q15mulr_sat_s" => some (.vBinOp .q15mulrSatS)
        | "dot_i16x8_s"   => some (.vBinOp .dot)
        | "demote_f64x2_zero" => some (.vUnOp .f32x4DemoteF64x2Zero)
        | "promote_low_f32x4" => some (.vUnOp .f64x2PromoteLowF32x4)
        | "trunc_sat_f32x4_s" => some (.vUnOp (.i32x4TruncSatF32x4 true))
        | "trunc_sat_f32x4_u" => some (.vUnOp (.i32x4TruncSatF32x4 false))
        | "trunc_sat_f64x2_s_zero" => some (.vUnOp (.i32x4TruncSatF64x2Zero true))
        | "trunc_sat_f64x2_u_zero" => some (.vUnOp (.i32x4TruncSatF64x2Zero false))
        | "convert_i32x4_s" => some (.vUnOp (.f32x4ConvertI32x4 true))
        | "convert_i32x4_u" => some (.vUnOp (.f32x4ConvertI32x4 false))
        | "convert_low_i32x4_s" => some (.vUnOp (.f64x2ConvertLowI32x4 true))
        | "convert_low_i32x4_u" => some (.vUnOp (.f64x2ConvertLowI32x4 false))
        -- Relaxed SIMD: deterministic choices coinciding with (or built
        -- from) the non-relaxed semantics.
        | "relaxed_swizzle" => some (.vBinOp .swizzle)
        | "relaxed_min" => some (.vBinOp (.fMin sh))
        | "relaxed_max" => some (.vBinOp (.fMax sh))
        | "relaxed_q15mulr_s" => some (.vBinOp .q15mulrSatS)
        | "relaxed_madd"  => some (.vFma sh false)
        | "relaxed_nmadd" => some (.vFma sh true)
        | "relaxed_laneselect" => some .vBitselect
        | "relaxed_trunc_f32x4_s" => some (.vUnOp (.i32x4TruncSatF32x4 true))
        | "relaxed_trunc_f32x4_u" => some (.vUnOp (.i32x4TruncSatF32x4 false))
        | "relaxed_trunc_f64x2_s_zero" => some (.vUnOp (.i32x4TruncSatF64x2Zero true))
        | "relaxed_trunc_f64x2_u_zero" => some (.vUnOp (.i32x4TruncSatF64x2Zero false))
        | "relaxed_dot_i8x16_i7x16_s" => some (.vBinOp .dotI8)
        | "relaxed_dot_i8x16_i7x16_add_s" => some .vDotAdd
        | _ =>
          -- Suffix families: extend / extadd_pairwise / extmul / narrow /
          -- comparisons. All encode signedness as a trailing `_s`/`_u`.
          let signed := name.endsWith "_s"
          if name.startsWith "extend_low_" || name.startsWith "extend_high_" then
            some (.vUnOp (.extend sh (name.startsWith "extend_high_") signed))
          else if name.startsWith "extadd_pairwise_" then
            some (.vUnOp (.extaddPairwise sh signed))
          else if name.startsWith "extmul_low_" || name.startsWith "extmul_high_" then
            some (.vBinOp (.extmul sh (name.startsWith "extmul_high_") signed))
          else if name.startsWith "narrow_" then
            some (.vBinOp (.narrow sh signed))
          else if flt then
            (simdFCmp? name).map fun c => .vBinOp (.fcmp sh c)
          else
            (simdICmp? name).map fun c => .vBinOp (.cmp sh c)
    | _ => none

/-- Parse the immediates of a `v128.const`: a shape atom followed by the
shape's lane count of literals. -/
private def parseV128Const (toks : List Sexpr)
    : Except Err (BitVec 128 × List Sexpr) := do
  match toks with
  | .atom shapeName :: r =>
    let sh ← match simdShapeOfPrefix? shapeName with
      | some sh => .ok sh
      | none    => .error s!"v128.const: unknown shape `{shapeName}`"
    let cnt := sh.laneCount
    let mut lanes : List Nat := []
    let mut rest := r
    for _ in [0:cnt] do
      match rest with
      | .atom lit :: r' =>
        let n : Nat ← match sh with
          | .i8x16 => parseIntLiteral lit 8
          | .i16x8 => parseIntLiteral lit 16
          | .i32x4 => (·.toNat) <$> parseI32 lit
          | .i64x2 => (·.toNat) <$> parseI64 lit
          | .f32x4 => (·.toNat) <$> parseF32Lit lit
          | .f64x2 => (·.toNat) <$> parseF64Lit lit
        lanes := lanes ++ [n]
        rest := r'
      | _ => .error "v128.const: missing lane literal"
    .ok (Wasm.Simd.ofLanes sh.laneBits lanes, rest)
  | _ => .error "v128.const expects a shape immediate"

/-- Decode the lane-immediate SIMD ops (`extract_lane`, `replace_lane`):
returns the constructor to apply to the parsed lane index. -/
private def simdLaneOp? (op : String) : Option (Nat → Wasm.Instruction) :=
  match op.splitOn "." with
  | [pre, name] =>
    match simdShapeOfPrefix? pre with
    | none => none
    | some sh =>
      match name with
      | "extract_lane"   => some (.vExtractLane sh false)
      | "extract_lane_s" => some (.vExtractLane sh true)
      | "extract_lane_u" => some (.vExtractLane sh false)
      | "replace_lane"   => some (.vReplaceLane sh)
      | _ => none
  | _ => none

/-- Map a memory op name and byte offset to the appropriate instruction. -/
private def memOpToInstruction (op : String) (offset : UInt32) : Wasm.Instruction :=
  match op with
  | "i32.load"     => .load32  offset
  | "i32.load8_u"  => .load8U  offset
  | "i32.load8_s"  => .load8S  offset
  | "i32.load16_u" => .load16U offset
  | "i32.load16_s" => .load16S offset
  | "i32.store"    => .store32 offset
  | "i32.store8"   => .store8  offset
  | "i32.store16"  => .store16 offset
  | "i64.load"     => .load64  offset
  | "i64.store"    => .store64 offset
  | "i64.load8_u"  => .load8UI64  offset
  | "i64.load8_s"  => .load8SI64  offset
  | "i64.load16_u" => .load16UI64 offset
  | "i64.load16_s" => .load16SI64 offset
  | "i64.load32_u" => .load32UI64 offset
  | "i64.load32_s" => .load32SI64 offset
  | "i64.store8"   => .store8I64  offset
  | "i64.store16"  => .store16I64 offset
  | "i64.store32"  => .store32I64 offset
  | "f32.load"     => .f32Load  offset
  | "f64.load"     => .f64Load  offset
  | "f32.store"    => .f32Store offset
  | "f64.store"    => .f64Store offset
  | "v128.load"    => .v128Load  offset
  | "v128.store"   => .v128Store offset
  | "v128.load8x8_s"   => .v128LoadExt 8  true  offset
  | "v128.load8x8_u"   => .v128LoadExt 8  false offset
  | "v128.load16x4_s"  => .v128LoadExt 16 true  offset
  | "v128.load16x4_u"  => .v128LoadExt 16 false offset
  | "v128.load32x2_s"  => .v128LoadExt 32 true  offset
  | "v128.load32x2_u"  => .v128LoadExt 32 false offset
  | "v128.load8_splat"  => .v128LoadSplat 8  offset
  | "v128.load16_splat" => .v128LoadSplat 16 offset
  | "v128.load32_splat" => .v128LoadSplat 32 offset
  | "v128.load64_splat" => .v128LoadSplat 64 offset
  | "v128.load32_zero"  => .v128LoadZero 32 offset
  | "v128.load64_zero"  => .v128LoadZero 64 offset
  | _              => .unreachable

/-- Map a lane-indexed v128 memory op (`v128.load8_lane` …) to its
instruction. Returns `none` for non-lane ops. -/
private def memLaneOpToInstruction (op : String) (offset : UInt32) (lane : Nat)
    : Option Wasm.Instruction :=
  match op with
  | "v128.load8_lane"   => some (.v128LoadLane  8  lane offset)
  | "v128.load16_lane"  => some (.v128LoadLane  16 lane offset)
  | "v128.load32_lane"  => some (.v128LoadLane  32 lane offset)
  | "v128.load64_lane"  => some (.v128LoadLane  64 lane offset)
  | "v128.store8_lane"  => some (.v128StoreLane 8  lane offset)
  | "v128.store16_lane" => some (.v128StoreLane 16 lane offset)
  | "v128.store32_lane" => some (.v128StoreLane 32 lane offset)
  | "v128.store64_lane" => some (.v128StoreLane 64 lane offset)
  | _ => none

private def looksLikeLabel (s : String) : Bool :=
  if s.startsWith "$" then true
  else if s.isEmpty then false
  else if s.startsWith "0x" || s.startsWith "0X" then
    (s.drop 2).toString.toList.all fun c =>
      c.isDigit || ('a' ≤ c ∧ c ≤ 'f') || ('A' ≤ c ∧ c ≤ 'F') || c = '_'
  else
    s.toList.all (fun c => c.isDigit || c = '_')

/-- Parse the *optional* table-index immediate carried by `table.get` /
`table.size` in flat (post-`wasm-tools print`) form. The index is `$name`
or a numeric literal when present and defaults to table `0` when omitted;
we only consume a leading atom that `looksLikeLabel` (so an immediately
following bare instruction op is left for the next parse step). -/
private def parseOptTableIdx (ctx : Ctx) (mk : Nat → Wasm.Instruction)
    : List Sexpr → Except Err (List Wasm.Instruction × List Sexpr)
  | .atom a :: rest' =>
    if looksLikeLabel a then do
      .ok ([mk (← resolveNamed ctx.tableNames "table" a)], rest')
    else .ok ([mk 0], .atom a :: rest')
  | rest' => .ok ([mk 0], rest')

/-- `table.copy` carries 0 or 2 table-index immediates: none for the
default `(0, 0)` pair, or `dst src` when either table is non-default. -/
private def parseTableCopy (ctx : Ctx)
    : List Sexpr → Except Err (List Wasm.Instruction × List Sexpr)
  | .atom a :: .atom b :: rest' =>
    if looksLikeLabel a && looksLikeLabel b then do
      let d ← resolveNamed ctx.tableNames "table" a
      let s ← resolveNamed ctx.tableNames "table" b
      .ok ([.tableCopy d s], rest')
    else .ok ([.tableCopy 0 0], .atom a :: .atom b :: rest')
  | rest' => .ok ([.tableCopy 0 0], rest')

/-- `table.init` carries 1 or 2 immediates: `elemIdx` alone for the
default table, or `tableIdx elemIdx` when the table is non-default. -/
private def parseTableInit (ctx : Ctx)
    : List Sexpr → Except Err (List Wasm.Instruction × List Sexpr)
  | .atom a :: .atom b :: rest' =>
    if looksLikeLabel a && looksLikeLabel b then do
      let t ← resolveNamed ctx.tableNames "table" a
      let e ← resolveNamed ctx.elemNames "elem" b
      .ok ([.tableInit t e], rest')
    else if looksLikeLabel a then do
      .ok ([.tableInit 0 (← resolveNamed ctx.elemNames "elem" a)], .atom b :: rest')
    else .error "table.init expects an element-segment immediate"
  | .atom a :: rest' =>
    if looksLikeLabel a then do
      .ok ([.tableInit 0 (← resolveNamed ctx.elemNames "elem" a)], rest')
    else .error "table.init expects an element-segment immediate"
  | _ => .error "table.init expects an element-segment immediate"

/-- Resolve a type-index immediate (`$t` or numeric) against the
module's type table. Used by `call_ref` / `return_call_ref`. -/
private def resolveTypeIdx (ctx : Ctx) (n : String) : Except Err Nat :=
  if n.startsWith "$" then
    let name := (n.drop 1).toString
    match ctx.types.findIdx? (fun te => te.symId = some name) with
    | some i => .ok i
    | none   => .error s!"unknown type id: {n}"
  else parseNat n

/-- Resolve a heap-type token (`any`/`eq`/`i31`/`struct`/`array`/`none`,
the `func`/`extern` families, or a concrete `$t`/index) to a
`GcHeapType`. -/
private def heapTypeOfAtom (ctx : Ctx) (a : String) : Except Err Wasm.GcHeapType :=
  match a with
  | "any"      => .ok .any
  | "eq"       => .ok .eq
  | "i31"      => .ok .i31
  | "struct"   => .ok .structT
  | "array"    => .ok .arrayT
  | "none"     => .ok .noneT
  | "func"     => .ok .func
  | "nofunc"   => .ok .noFunc
  | "extern"   => .ok .extern
  | "noextern" => .ok .noExtern
  | _          => Wasm.GcHeapType.concrete <$> resolveTypeIdx ctx a

/-- Parse a `ref.test`/`ref.cast` target reference-type immediate into its
nullability and heap type. Accepts the `…ref` abbreviations (all nullable),
the explicit `(ref ht)` (non-nullable), and `(ref null ht)` (nullable). -/
private def parseRefTypeImmediate (ctx : Ctx) : Sexpr → Except Err (Bool × Wasm.GcHeapType)
  | .atom "anyref"        => .ok (true, .any)
  | .atom "eqref"         => .ok (true, .eq)
  | .atom "i31ref"        => .ok (true, .i31)
  | .atom "structref"     => .ok (true, .structT)
  | .atom "arrayref"      => .ok (true, .arrayT)
  | .atom "nullref"       => .ok (true, .noneT)
  | .atom "funcref"       => .ok (true, .func)
  | .atom "nullfuncref"   => .ok (true, .noFunc)
  | .atom "externref"     => .ok (true, .extern)
  | .atom "nullexternref" => .ok (true, .noExtern)
  | .list [.atom "ref", .atom "null", .atom ht] => (fun h => (true, h)) <$> heapTypeOfAtom ctx ht
  | .list [.atom "ref", .atom ht]               => (fun h => (false, h)) <$> heapTypeOfAtom ctx ht
  | _ => .error "unsupported ref-type immediate"

/-- Wrap a memory instruction for a non-default memory (multi-memory). -/
private def wrapMem (k : Nat) (i : Wasm.Instruction) : Wasm.Instruction :=
  if k = 0 then i else .memOp k i

/-- Parse the optional memory-index immediate of `memory.size` /
`memory.grow` / `memory.fill` (default 0), wrapping for non-default
memories. -/
private def parseOptMemIdx (ctx : Ctx) (i : Wasm.Instruction)
    : List Sexpr → Except Err (List Wasm.Instruction × List Sexpr)
  | .atom a :: rest' =>
    if looksLikeLabel a then do
      .ok ([wrapMem (← resolveNamed ctx.memNames "memory" a) i], rest')
    else .ok ([i], .atom a :: rest')
  | rest' => .ok ([i], rest')

/-- `memory.copy` carries 0 or 2 memory-index immediates. Distinct (or
non-default) memories decode to the cross-memory instruction. -/
private def parseMemCopy (ctx : Ctx)
    : List Sexpr → Except Err (List Wasm.Instruction × List Sexpr)
  | .atom a :: .atom b :: rest' =>
    if looksLikeLabel a && looksLikeLabel b then do
      let d ← resolveNamed ctx.memNames "memory" a
      let sM ← resolveNamed ctx.memNames "memory" b
      if d = 0 && sM = 0 then .ok ([.memoryCopy], rest')
      else .ok ([.memoryCopyBetween d sM], rest')
    else .ok ([.memoryCopy], .atom a :: .atom b :: rest')
  | rest' => .ok ([.memoryCopy], rest')

/-- `memory.init` carries 1 or 2 immediates: `dataIdx` alone for the
default memory, or `memIdx dataIdx`. -/
private def parseMemInit (ctx : Ctx)
    : List Sexpr → Except Err (List Wasm.Instruction × List Sexpr)
  | .atom a :: .atom b :: rest' =>
    if looksLikeLabel a && looksLikeLabel b then do
      let k ← resolveNamed ctx.memNames "memory" a
      let d ← parseNat b
      .ok ([wrapMem k (.memoryInit d)], rest')
    else if looksLikeLabel a then do
      .ok ([.memoryInit (← parseNat a)], .atom b :: rest')
    else .error "memory.init expects a data-segment immediate"
  | .atom a :: rest' =>
    if looksLikeLabel a then do
      .ok ([.memoryInit (← parseNat a)], rest')
    else .error "memory.init expects a data-segment immediate"
  | _ => .error "memory.init expects a data-segment immediate"

mutual

private partial def parseInstr (ctx : Ctx) (toks : List Sexpr)
    : Except Err (List Wasm.Instruction × List Sexpr) :=
  match toks with
  | [] => .error "unexpected end of instruction stream"
  | .list ls :: rest => do
    let xs ← parseFolded ctx ls
    .ok (xs, rest)
  | .atom op :: rest =>
    match op with
    | "i32.const" => parseImmediateConst .const parseI32 op rest
    | "i64.const" => parseImmediateConst .constI64 parseI64 op rest
    | "f32.const" => parseImmediateConst .f32Const parseF32Lit op rest
    | "f64.const" => parseImmediateConst .f64Const parseF64Lit op rest
    | "local.get" => parseImmediateNat (resolveNamed ctx.localIds "local") .localGet op rest
    | "local.set" => parseImmediateNat (resolveNamed ctx.localIds "local") .localSet op rest
    | "local.tee" => parseLocalTee ctx rest
    | "global.get" => parseImmediateNat (resolveNamed ctx.globalIds "global") .globalGet op rest
    | "global.set" => parseImmediateNat (resolveNamed ctx.globalIds "global") .globalSet op rest
    | "br"        => parseImmediateNat (resolveLabel ctx) .br op rest
    | "br_if"     => parseImmediateNat (resolveLabel ctx) .br_if op rest
    | "br_table"  => parseBrTable ctx rest
    | "call"      => parseImmediateNat (resolveNamed ctx.funcIds "function") .call op rest
    | "throw" => parseImmediateNat (resolveNamed ctx.tagNames "tag") .throwI op rest
    | "throw_ref" => .ok ([.throwRef], rest)
    | "try_table" => parseTryTable ctx rest
    | "call_ref" => parseImmediateNat (resolveTypeIdx ctx) .callRef op rest
    | "return_call_ref" => parseImmediateNat (resolveTypeIdx ctx) .returnCallRef op rest
    | "ref.as_non_null" => .ok ([.refAsNonNull], rest)
    | "ref.test" => match rest with
      | t :: rest' => do
        let (n, ht) ← parseRefTypeImmediate ctx t
        .ok ([.gc (.refTest n ht)], rest')
      | _ => .error "ref.test expects a reference-type immediate"
    | "ref.cast" => match rest with
      | t :: rest' => do
        let (n, ht) ← parseRefTypeImmediate ctx t
        .ok ([.gc (.refCast n ht)], rest')
      | _ => .error "ref.cast expects a reference-type immediate"
    | "br_on_cast" | "br_on_cast_fail" => match rest with
      | .atom lbl :: _t1 :: t2 :: rest' => do
        let label ← resolveLabel ctx lbl
        let (n2, ht2) ← parseRefTypeImmediate ctx t2
        let instr := if op == "br_on_cast" then Wasm.GcOp.brOnCast label n2 ht2
                     else Wasm.GcOp.brOnCastFail label n2 ht2
        .ok ([.gc instr], rest')
      | _ => .error s!"{op} expects label + 2 type immediates"
    -- Struct / array instructions (GC proposal). Type immediates resolve
    -- against the GC type table; field/length immediates are numeric.
    | "struct.new"         => parseImmediateNat (resolveTypeIdx ctx) (fun i => .gc (.structNew i)) op rest
    | "struct.new_default" => parseImmediateNat (resolveTypeIdx ctx) (fun i => .gc (.structNewDefault i)) op rest
    | "struct.get" | "struct.get_s" | "struct.get_u" | "struct.set" => match rest with
      | .atom t :: .atom f :: rest' => do
        let ti ← resolveTypeIdx ctx t
        let fi ← if f.startsWith "$" then
            let name := (f.drop 1).toString
            match (ctx.types[ti]?).bind (·.fieldNames.findIdx? (· = some name)) with
            | some i => .ok i
            | none   => .error s!"unknown struct field: {f}"
          else parseNat f
        let mk : Nat → Nat → Wasm.GcOp := match op with
          | "struct.get"   => Wasm.GcOp.structGet
          | "struct.get_s" => Wasm.GcOp.structGetS
          | "struct.get_u" => Wasm.GcOp.structGetU
          | _              => Wasm.GcOp.structSet
        .ok ([.gc (mk ti fi)], rest')
      | _ => .error s!"{op} expects type and field immediates"
    | "array.new"         => parseImmediateNat (resolveTypeIdx ctx) (fun i => .gc (.arrayNew i)) op rest
    | "array.new_default" => parseImmediateNat (resolveTypeIdx ctx) (fun i => .gc (.arrayNewDefault i)) op rest
    | "array.new_fixed" => match rest with
      | .atom t :: .atom n :: rest' => do
        let ti ← resolveTypeIdx ctx t
        let nn ← parseNat n
        .ok ([.gc (.arrayNewFixed ti nn)], rest')
      | _ => .error "array.new_fixed expects type and length immediates"
    | "array.get"   => parseImmediateNat (resolveTypeIdx ctx) (fun i => .gc (.arrayGet i)) op rest
    | "array.get_s" => parseImmediateNat (resolveTypeIdx ctx) (fun i => .gc (.arrayGetS i)) op rest
    | "array.get_u" => parseImmediateNat (resolveTypeIdx ctx) (fun i => .gc (.arrayGetU i)) op rest
    | "array.set"   => parseImmediateNat (resolveTypeIdx ctx) (fun i => .gc (.arraySet i)) op rest
    | "array.len"   => .ok ([.gc .arrayLen], rest)
    | "array.fill"  => parseImmediateNat (resolveTypeIdx ctx) (fun i => .gc (.arrayFill i)) op rest
    | "array.copy" => match rest with
      | .atom dt :: .atom st :: rest' => do
        .ok ([.gc (.arrayCopy (← resolveTypeIdx ctx dt) (← resolveTypeIdx ctx st))], rest')
      | _ => .error "array.copy expects two type immediates"
    | "array.new_data" => match rest with
      | .atom t :: .atom d :: rest' => do
        .ok ([.gc (.arrayNewData (← resolveTypeIdx ctx t) (← parseNat d))], rest')
      | _ => .error "array.new_data expects type and data immediates"
    | "array.init_data" => match rest with
      | .atom t :: .atom d :: rest' => do
        .ok ([.gc (.arrayInitData (← resolveTypeIdx ctx t) (← parseNat d))], rest')
      | _ => .error "array.init_data expects type and data immediates"
    | "array.new_elem" => match rest with
      | .atom t :: .atom e :: rest' => do
        .ok ([.gc (.arrayNewElem (← resolveTypeIdx ctx t) (← resolveNamed ctx.elemNames "elem" e))], rest')
      | _ => .error "array.new_elem expects type and elem immediates"
    | "array.init_elem" => match rest with
      | .atom t :: .atom e :: rest' => do
        .ok ([.gc (.arrayInitElem (← resolveTypeIdx ctx t) (← resolveNamed ctx.elemNames "elem" e))], rest')
      | _ => .error "array.init_elem expects type and elem immediates"
    | "br_on_null" => parseImmediateNat (resolveLabel ctx) .brOnNull op rest
    | "br_on_non_null" => parseImmediateNat (resolveLabel ctx) .brOnNonNull op rest
    | "call_indirect" => parseCallIndirect ctx .callIndirect rest
    | "return_call_indirect" => parseCallIndirect ctx .returnCallIndirect rest
    | "return_call" =>
      parseImmediateNat (resolveNamed ctx.funcIds "function") .returnCall op rest
    | "memory.size" => parseOptMemIdx ctx .memorySize rest
    | "memory.grow" => parseOptMemIdx ctx .memoryGrow rest
    | "memory.fill" => parseOptMemIdx ctx .memoryFill rest
    | "memory.copy" => parseMemCopy ctx rest
    | "memory.init" => parseMemInit ctx rest
    | "data.drop"   => parseImmediateNat parseNat .dataDrop   op rest
    | "ref.func"    => parseImmediateNat (resolveNamed ctx.funcIds "function") .refFunc op rest
    -- `ref.null ht` carries a heap-type immediate. `func`-like heap types
    -- become the null funcref, `extern`-like ones the null externref; heap
    -- types from unmodelled proposals keep the decode-but-trap behaviour.
    | "ref.null"    => match rest with
      | .atom ht :: rest' => .ok ([refNullInstr ctx.types ht], rest')
      | _ => .error "ref.null expects a heap-type immediate"
    -- Table ops carry an *optional* table-index immediate (default 0);
    -- see `parseOptTableIdx`.
    | "table.get"   => parseOptTableIdx ctx .tableGet rest
    | "table.size"  => parseOptTableIdx ctx .tableSize rest
    | "table.set"   => parseOptTableIdx ctx .tableSet rest
    | "table.grow"  => parseOptTableIdx ctx .tableGrow rest
    | "table.fill"  => parseOptTableIdx ctx .tableFill rest
    | "table.copy"  => parseTableCopy ctx rest
    | "table.init"  => parseTableInit ctx rest
    | "elem.drop"   => parseImmediateNat (resolveNamed ctx.elemNames "elem") .elemDrop op rest
    | "select"    =>
      let rec dropResults : List Sexpr → List Sexpr
        | .list (.atom "result" :: _) :: r => dropResults r
        | xs => xs
      .ok ([.select], dropResults rest)
    | "block"     => parseStructured ctx .block #["end"] rest
    | "loop"      => parseStructured ctx .loop  #["end"] rest
    | "if"        => parseIf ctx rest
    | "end"       => .error "stray 'end'"
    | "else"      => .error "stray 'else'"
    | "v128.const" => do
      let (bits, rest') ← parseV128Const rest
      .ok ([.vConst bits], rest')
    | "i8x16.shuffle" => do
      let mut lanes : List Nat := []
      let mut r := rest
      for _ in [0:16] do
        match r with
        | .atom n :: r' => lanes := lanes ++ [(← parseNat n)]; r := r'
        | _ => .error "i8x16.shuffle expects 16 lane immediates"
      .ok ([.vShuffle lanes], r)
    | _ =>
      match simdLaneOp? op with
      | some mk => match rest with
        | .atom n :: rest' => do .ok ([mk (← parseNat n)], rest')
        | _ => .error s!"{op} expects a lane immediate"
      | none =>
      match isMemOp op with
      | some na => do
        -- Optional memory-index immediate (multi-memory) before the
        -- offset/align attributes: `i32.load $mem1 offset=1`.
        let (lead?, rest0) : Option String × List Sexpr := match rest with
          | .atom a :: r => if looksLikeLabel a then (some a, r) else (none, rest)
          | r => (none, r)
        let (offset, rest') ← consumeMemAttrs na rest0
        -- v128 lane-load/store ops carry an additional lane-index atom
        -- after the offset/align attrs. The grammar is
        -- `memidx? memarg laneidx`, so for lane ops two bare atoms mean
        -- memidx-then-lane and a single bare atom is just the lane.
        if op.endsWith "_lane" && op.startsWith "v128." then
          -- Grammar `memidx? memarg laneidx`. With no attrs the leading
          -- atom(s) are ambiguous; the lane is mandatory and is the LAST
          -- immediate, so a second leading atom is the lane only when it
          -- *itself* looks like a label (otherwise it's the next
          -- instruction, e.g. a bare `local.get` sibling in flat form).
          match lead?, rest' with
          | some a, .atom n :: rest'' =>
            if looksLikeLabel n then do
              let memIdx ← resolveNamed ctx.memNames "memory" a
              match memLaneOpToInstruction op offset (← parseNat n) with
              | some i => .ok ([wrapMem memIdx i], rest'')
              | none   => .error s!"unknown lane memory op: {op}"
            else
              match memLaneOpToInstruction op offset (← parseNat a) with
              | some i => .ok ([i], .atom n :: rest'')
              | none   => .error s!"unknown lane memory op: {op}"
          | some a, rest'' =>
            match memLaneOpToInstruction op offset (← parseNat a) with
            | some i => .ok ([i], rest'')
            | none   => .error s!"unknown lane memory op: {op}"
          | none, .atom n :: rest'' =>
            match memLaneOpToInstruction op offset (← parseNat n) with
            | some i => .ok ([i], rest'')
            | none   => .error s!"unknown lane memory op: {op}"
          | none, _ => .error s!"{op} expects a lane immediate"
        else do
          let memIdx ← match lead? with
            | some a => resolveNamed ctx.memNames "memory" a
            | none   => pure 0
          .ok ([wrapMem memIdx (memOpToInstruction op offset)], rest')
      | none =>
        match simdOp? op with
        | some i => .ok ([i], rest)
        | none =>
        match parsePlainOp op with
        | .error e => .error e
        -- Ops reaching this fallback are lowered to `unreachable` and carry
        -- no immediates we track, so the token stream stays aligned with
        -- `rest` untouched. (Ops that *do* carry immediates — including
        -- `br_on_cast`/`br_on_cast_fail` — are handled by explicit arms above
        -- and never fall through here.)
        | .ok i => .ok ([i], rest)

private partial def parseFolded (ctx : Ctx) (xs : List Sexpr)
    : Except Err (List Wasm.Instruction) :=
  match xs with
  | [] => .error "empty folded form"
  | .atom op :: rest =>
    match op with
    | "i32.const" =>
      match rest with
      | [.atom n] => do .ok [.const (← parseI32 n)]
      | _ => .error "folded i32.const expects exactly one immediate atom"
    | "i64.const" =>
      match rest with
      | [.atom n] => do .ok [.constI64 (← parseI64 n)]
      | _ => .error "folded i64.const expects exactly one immediate atom"
    | "f32.const" =>
      match rest with
      | [.atom n] => do .ok [.f32Const (← parseF32Lit n)]
      | _ => .error "folded f32.const expects exactly one immediate atom"
    | "f64.const" =>
      match rest with
      | [.atom n] => do .ok [.f64Const (← parseF64Lit n)]
      | _ => .error "folded f64.const expects exactly one immediate atom"
    | "local.get" =>
      match rest with
      | [.atom n] => do .ok [.localGet (← resolveNamed ctx.localIds "local" n)]
      | _ => .error "folded local.get expects exactly one immediate atom"
    | "local.set" =>
      foldedWithImmediate ctx (resolveNamed ctx.localIds "local") (fun i => [.localSet i]) rest
    | "local.tee" =>
      -- Desugar: `local.tee i` ≡ `local.set i; local.get i`.
      foldedWithImmediate ctx (resolveNamed ctx.localIds "local")
        (fun i => [.localSet i, .localGet i]) rest
    | "global.get" =>
      match rest with
      | [.atom n] => do .ok [.globalGet (← resolveNamed ctx.globalIds "global" n)]
      | _ => .error "folded global.get expects exactly one immediate atom"
    | "global.set" =>
      foldedWithImmediate ctx (resolveNamed ctx.globalIds "global") (fun i => [.globalSet i]) rest
    | "br"    => foldedWithImmediate ctx (resolveLabel ctx) (fun n => [.br n]) rest
    | "br_if" => foldedWithImmediate ctx (resolveLabel ctx) (fun n => [.br_if n]) rest
    | "br_table" => foldedBrTable ctx rest
    | "select" => foldedSelect ctx rest
    | "call"  => foldedWithImmediate ctx (resolveNamed ctx.funcIds "function") (fun i => [.call i]) rest
    | "data.drop"   => foldedWithImmediate ctx parseNat (fun i => [.dataDrop i])   rest
    | "ref.func"    =>
      foldedWithImmediate ctx (resolveNamed ctx.funcIds "function") (fun i => [.refFunc i]) rest
    | "ref.null"    =>
      match rest with
      | [.atom ht] => .ok [refNullInstr ctx.types ht]
      | _ => .error "folded ref.null expects exactly one heap-type immediate"
    | "table.get"   => foldedOptTableIdx ctx .tableGet rest
    | "table.size"  => foldedOptTableIdx ctx .tableSize rest
    | "table.set"   => foldedOptTableIdx ctx .tableSet rest
    | "table.grow"  => foldedOptTableIdx ctx .tableGrow rest
    | "table.fill"  => foldedOptTableIdx ctx .tableFill rest
    | "table.copy" | "table.init" | "elem.drop" => do
      -- Reuse the linear parsers for the immediates, then treat the
      -- remaining forms as folded operand sub-expressions.
      let (instr, leftover) ← parseInstr ctx (.atom op :: rest)
      let mut acc : List Wasm.Instruction := []
      for s in leftover do
        match s with
        | .list ys =>
          let sub ← parseFolded ctx ys
          acc := acc ++ sub
        | .atom a => .error s!"folded {op}: unexpected atom operand '{a}'"
      .ok (acc ++ instr)
    | "call_indirect" | "return_call_indirect" => do
      let mk : Nat → Nat → Wasm.Instruction :=
        if op == "call_indirect" then .callIndirect else .returnCallIndirect
      let (instr, leftover) ← parseCallIndirect ctx mk rest
      let mut acc : List Wasm.Instruction := []
      for sx in leftover do
        match sx with
        | .list ys =>
          let sub ← parseFolded ctx ys
          acc := acc ++ sub
        | .atom a => .error s!"folded {op}: unexpected atom operand '{a}'"
      .ok (acc ++ instr)
    | "return_call" =>
      foldedWithImmediate ctx (resolveNamed ctx.funcIds "function")
        (fun i => [.returnCall i]) rest
    | "throw" =>
      foldedWithImmediate ctx (resolveNamed ctx.tagNames "tag") (fun i => [.throwI i]) rest
    | "try_table" => foldedTryTable ctx rest
    | "call_ref" =>
      foldedWithImmediate ctx (resolveTypeIdx ctx) (fun i => [.callRef i]) rest
    | "return_call_ref" =>
      foldedWithImmediate ctx (resolveTypeIdx ctx) (fun i => [.returnCallRef i]) rest
    | "br_on_null" =>
      foldedWithImmediate ctx (resolveLabel ctx) (fun n => [.brOnNull n]) rest
    | "br_on_non_null" =>
      foldedWithImmediate ctx (resolveLabel ctx) (fun n => [.brOnNonNull n]) rest
    | "block" => foldedStructured ctx .block rest
    | "loop"  => foldedStructured ctx .loop  rest
    | "if"    => foldedIf ctx rest
    | _ => do
      -- Plain op, SIMD op, or memory op with optional `offset=`/`align=`
      -- attrs (plus lane/shape immediates for SIMD). Delegate the head +
      -- immediate parsing to the linear parser, then treat the remaining
      -- `(...)` forms as folded operand sub-expressions.
      let (heads, rest') ← parseInstr ctx (.atom op :: rest)
      let mut acc : List Wasm.Instruction := []
      for s in rest' do
        match s with
        | .list ys =>
          let sub ← parseFolded ctx ys
          acc := acc ++ sub
        | .atom a => .error s!"folded {op}: unexpected atom operand '{a}'"
      .ok (acc ++ heads)
  | _ => .error "malformed folded form"

private partial def foldedStructured (ctx : Ctx)
    (mk : Nat → Nat → List Wasm.Instruction → Wasm.Instruction)
    (xs : List Sexpr) : Except Err (List Wasm.Instruction) := do
  let (label, ps, rs, xs') := parseBlockHeader ctx.resolveBlockType xs
  let body ← parseInstrSeq (ctx.pushLabel label) xs'
  .ok [mk ps rs body]

private partial def foldedIf (ctx : Ctx) (xs : List Sexpr)
    : Except Err (List Wasm.Instruction) := do
  let (label, ps, rs, xs') := parseBlockHeader ctx.resolveBlockType xs
  let bodyCtx := ctx.pushLabel label
  let mut condInstrs : List Wasm.Instruction := []
  let mut cur := xs'
  let mut stop := false
  while !stop do
    match cur with
    | .list (.atom "then" :: _) :: _ => stop := true
    | .list ys :: r =>
      let sub ← parseFolded ctx ys
      condInstrs := condInstrs ++ sub
      cur := r
    | [] => stop := true
    | .atom a :: _ =>
      throw s!"folded if: unexpected atom '{a}' before (then …)"
  match cur with
  | .list (.atom "then" :: thenBody) :: rest2 => do
    let thn ← parseInstrSeq bodyCtx thenBody
    match rest2 with
    | .list (.atom "else" :: elseBody) :: [] => do
      let els ← parseInstrSeq bodyCtx elseBody
      .ok (condInstrs ++ [.iff ps rs thn els])
    | [] => .ok (condInstrs ++ [.iff ps rs thn []])
    | _ => .error "folded if: trailing forms after (else …)"
  | _ => .error "folded if: missing (then …)"

private partial def foldedWithImmediate (ctx : Ctx)
    (resolve : String → Except Err Nat)
    (mkInstrs : Nat → List Wasm.Instruction)
    : List Sexpr → Except Err (List Wasm.Instruction)
  | .atom n :: ops => do
    let mut acc : List Wasm.Instruction := []
    for s in ops do
      match s with
      | .list ys =>
        let sub ← parseFolded ctx ys
        acc := acc ++ sub
      | .atom a => .error s!"folded form: unexpected atom operand '{a}'"
    .ok (acc ++ mkInstrs (← resolve n))
  | _ => .error "folded form: missing immediate"

/-- Folded form of `table.get` / `table.size`. The table-index immediate is
optional (a leading `$name`/numeric atom, default 0); everything after it
is the folded index-operand sub-expression(s). -/
private partial def foldedOptTableIdx (ctx : Ctx) (mk : Nat → Wasm.Instruction)
    : List Sexpr → Except Err (List Wasm.Instruction)
  | xs => do
    let (tableIdx, ops) ← match xs with
      | .atom a :: rest =>
        if looksLikeLabel a then
          pure ((← resolveNamed ctx.tableNames "table" a), rest)
        else .error s!"folded table op: unexpected atom operand '{a}'"
      | _ => pure (0, xs)
    let mut acc : List Wasm.Instruction := []
    for s in ops do
      match s with
      | .list ys =>
        let sub ← parseFolded ctx ys
        acc := acc ++ sub
      | .atom a => .error s!"folded table op: unexpected atom operand '{a}'"
    .ok (acc ++ [mk tableIdx])

private partial def parseBrTable (ctx : Ctx) (toks : List Sexpr)
    : Except Err (List Wasm.Instruction × List Sexpr) := do
  let mut labels : List Nat := []
  let mut cur := toks
  let mut stop := false
  while !stop do
    match cur with
    | .atom a :: r =>
      if looksLikeLabel a then
        labels := labels ++ [(← resolveLabel ctx a)]
        cur := r
      else stop := true
    | _ => stop := true
  match labels.reverse with
  | [] => .error "br_table requires at least one label"
  | dflt :: revRest => .ok ([.brTable revRest.reverse dflt], cur)

private partial def foldedBrTable (ctx : Ctx) (xs : List Sexpr)
    : Except Err (List Wasm.Instruction) := do
  let mut labels : List Nat := []
  let mut cur := xs
  let mut stop := false
  while !stop do
    match cur with
    | .atom a :: r =>
      if looksLikeLabel a then
        labels := labels ++ [(← resolveLabel ctx a)]
        cur := r
      else stop := true
    | _ => stop := true
  let dflt ← match labels.reverse with
    | [] => .error "br_table requires at least one label"
    | x :: _ => .ok x
  let revLabels := labels.reverse
  let targets := match revLabels with
    | _ :: rest => rest.reverse
    | [] => []
  let mut acc : List Wasm.Instruction := []
  for s in cur do
    match s with
    | .list ys =>
      let sub ← parseFolded ctx ys
      acc := acc ++ sub
    | .atom a => .error s!"folded br_table: unexpected atom operand '{a}'"
  .ok (acc ++ [.brTable targets dflt])

private partial def foldedSelect (ctx : Ctx) (xs : List Sexpr)
    : Except Err (List Wasm.Instruction) := do
  let xs' := xs.filter fun
    | .list (.atom "result" :: _) => false
    | _ => true
  let mut acc : List Wasm.Instruction := []
  for s in xs' do
    match s with
    | .list ys =>
      let sub ← parseFolded ctx ys
      acc := acc ++ sub
    | .atom a => .error s!"folded select: unexpected atom operand '{a}'"
  .ok (acc ++ [.select])

private partial def parseLocalTee (ctx : Ctx) (toks : List Sexpr)
    : Except Err (List Wasm.Instruction × List Sexpr) := do
  match toks with
  | .atom n :: rest => do
    let i ← resolveNamed ctx.localIds "local" n
    .ok ([.localSet i, .localGet i], rest)
  | _ => .error "local.tee expects an immediate"

private partial def parseImmediateConst {α} (mk : α → Wasm.Instruction)
    (parseV : String → Except Err α) (op : String)
    : List Sexpr → Except Err (List Wasm.Instruction × List Sexpr)
  | .atom n :: rest' => do .ok ([mk (← parseV n)], rest')
  | _ => .error s!"{op} expects an immediate"

private partial def parseImmediateNat (resolve : String → Except Err Nat)
    (mk : Nat → Wasm.Instruction) (op : String)
    : List Sexpr → Except Err (List Wasm.Instruction × List Sexpr)
  | .atom n :: rest' => do .ok ([mk (← resolve n)], rest')
  | _ => .error s!"{op} expects an immediate"

/-- Parse a `call_indirect` instruction. The wasm-tools-canonical forms
are `call_indirect [$t | (table T)] (type N)`; raw `.wat` may instead
carry an inline `(param …)* (result …)*` signature, which we resolve to
the first matching entry of the module's type table (wasm-tools'
canonical encoding always materialises such an entry). -/
private partial def parseCallIndirect (ctx : Ctx)
    (mk : Nat → Nat → Wasm.Instruction) (toks : List Sexpr)
    : Except Err (List Wasm.Instruction × List Sexpr) := do
  let mut rest := toks
  let mut tableIdx : Nat := 0
  -- Optional table immediate: a bare `$t`/numeric atom (canonical print)
  -- or a `(table T)` list (raw wast).
  match rest with
  | .list [.atom "table", .atom t] :: r =>
    tableIdx := (← resolveNamed ctx.tableNames "table" t)
    rest := r
  | .atom a :: r =>
    if looksLikeLabel a then
      tableIdx := (← resolveNamed ctx.tableNames "table" a)
      rest := r
  | _ => pure ()
  match rest with
  | .list [.atom "type", .atom n] :: r =>
    let typeIdx ←
      if n.startsWith "$" then
        let name := (n.drop 1).toString
        match ctx.types.findIdx? (fun te => te.symId = some name) with
        | some i => .ok i
        | none   => .error s!"unknown type id: {n}"
      else parseNat n
    -- A redundant inline `(param …)/(result …)` restating the resolved
    -- signature may follow; consume it.
    let r := r.dropWhile fun
      | .list (.atom "param" :: _)  => true
      | .list (.atom "result" :: _) => true
      | _ => false
    .ok ([mk typeIdx tableIdx], r)
  | _ =>
    -- Inline signature without `(type N)`: collect `(param …)*
    -- (result …)*` and resolve against the type table.
    let mut ps : List Wasm.ValueType := []
    let mut rs : List Wasm.ValueType := []
    let mut r := rest
    let mut stop := false
    while !stop do
      match r with
      | .list (.atom "param" :: tail) :: r' =>
        for t in tail do
          match t with
          | .atom a =>
            if a.startsWith "$" then pure ()
            else match atomToValueType? a with
              | some vt => ps := ps ++ [vt]
              | none    => .error s!"call_indirect: unsupported param type {a}"
          | .list l => ps := ps ++ [listToValueType l]
        r := r'
      | .list (.atom "result" :: tail) :: r' =>
        for t in tail do
          match t with
          | .atom a =>
            match atomToValueType? a with
            | some vt => rs := rs ++ [vt]
            | none    => .error s!"call_indirect: unsupported result type {a}"
          | .list l => rs := rs ++ [listToValueType l]
        r := r'
      | _ => stop := true
    -- With no inline forms at all this is the bare `call_indirect`,
    -- whose type is the empty signature `[] → []`.
    match ctx.types.findIdx? (fun te => te.sig = some (ps, rs)) with
    | some i => .ok ([mk i tableIdx], r)
    | none   => .error "call_indirect: inline signature has no matching type entry"

/-- Parse the catch clauses of a `try_table`. Clause labels are branch
depths relative to the scope *enclosing* the `try_table` (label 0 is the
construct surrounding it), matching the binary format: a caught
exception behaves like a branch executed at the position of the
`try_table` instruction itself. -/
private partial def parseCatchClauses (ctx bodyCtx : Ctx)
    : List Sexpr → Except Err (List Wasm.CatchClause × List Sexpr)
  | .list (.atom "catch" :: .atom t :: .atom l :: _) :: r => do
    let tag ← resolveNamed ctx.tagNames "tag" t
    let lbl ← resolveLabel ctx l
    let (rest, r') ← parseCatchClauses ctx bodyCtx r
    .ok (.catch tag lbl :: rest, r')
  | .list (.atom "catch_ref" :: .atom t :: .atom l :: _) :: r => do
    let tag ← resolveNamed ctx.tagNames "tag" t
    let lbl ← resolveLabel ctx l
    let (rest, r') ← parseCatchClauses ctx bodyCtx r
    .ok (.catchRef tag lbl :: rest, r')
  | .list (.atom "catch_all" :: .atom l :: _) :: r => do
    let lbl ← resolveLabel ctx l
    let (rest, r') ← parseCatchClauses ctx bodyCtx r
    .ok (.catchAll lbl :: rest, r')
  | .list (.atom "catch_all_ref" :: .atom l :: _) :: r => do
    let lbl ← resolveLabel ctx l
    let (rest, r') ← parseCatchClauses ctx bodyCtx r
    .ok (.catchAllRef lbl :: rest, r')
  | r => .ok ([], r)

private partial def parseTryTable (ctx : Ctx) (toks : List Sexpr)
    : Except Err (List Wasm.Instruction × List Sexpr) := do
  let (label, ps, rs, toks') := parseBlockHeader ctx.resolveBlockType toks
  let bodyCtx := ctx.pushLabel label
  let (clauses, toks'') ← parseCatchClauses ctx bodyCtx toks'
  let (body, after) ← parseInstrsUntil bodyCtx toks'' #["end"]
  match after with
  | _ :: aft => .ok ([.tryTable ps rs clauses body], dropTrailingLabel aft)
  | [] => .error "unterminated try_table"

private partial def foldedTryTable (ctx : Ctx) (xs : List Sexpr)
    : Except Err (List Wasm.Instruction) := do
  let (label, ps, rs, xs') := parseBlockHeader ctx.resolveBlockType xs
  let bodyCtx := ctx.pushLabel label
  let (clauses, xs'') ← parseCatchClauses ctx bodyCtx xs'
  let body ← parseInstrSeq bodyCtx xs''
  .ok [.tryTable ps rs clauses body]

private partial def parseStructured (ctx : Ctx)
    (mk : Nat → Nat → List Wasm.Instruction → Wasm.Instruction)
    (stops : Array String) (toks : List Sexpr)
    : Except Err (List Wasm.Instruction × List Sexpr) := do
  let (label, ps, rs, toks') := parseBlockHeader ctx.resolveBlockType toks
  let (body, after) ← parseInstrsUntil (ctx.pushLabel label) toks' stops
  match after with
  | _ :: aft => .ok ([mk ps rs body], dropTrailingLabel aft)
  | [] => .error "unterminated structured instruction"

private partial def parseIf (ctx : Ctx) (toks : List Sexpr)
    : Except Err (List Wasm.Instruction × List Sexpr) := do
  let (label, ps, rs, toks') := parseBlockHeader ctx.resolveBlockType toks
  let bodyCtx := ctx.pushLabel label
  let (thn, after) ← parseInstrsUntil bodyCtx toks' #["else", "end"]
  match after with
  | .atom "else" :: aft1 =>
    let aft1' := dropTrailingLabel aft1
    let (els, aft2) ← parseInstrsUntil bodyCtx aft1' #["end"]
    match aft2 with
    | _ :: aft3 => .ok ([.iff ps rs thn els], dropTrailingLabel aft3)
    | [] => .error "if: missing 'end' after 'else'"
  | .atom "end" :: aft1 =>
    .ok ([.iff ps rs thn []], dropTrailingLabel aft1)
  | _ => .error "if without else/end"

private partial def parseInstrsUntil (ctx : Ctx) (toks : List Sexpr)
    (stops : Array String)
    : Except Err (List Wasm.Instruction × List Sexpr) := do
  let mut acc : List Wasm.Instruction := []
  let mut s := toks
  while true do
    match s with
    | [] => throw "unterminated structured instruction"
    | .atom a :: _ =>
      if stops.contains a then return (acc, s)
      else
        let (is, s') ← parseInstr ctx s
        acc := acc ++ is
        s := s'
    | _ =>
      let (is, s') ← parseInstr ctx s
      acc := acc ++ is
      s := s'
  return (acc, s)  -- unreachable

private partial def parseInstrSeq (ctx : Ctx) (toks : List Sexpr)
    : Except Err (List Wasm.Instruction) := do
  let mut acc : List Wasm.Instruction := []
  let mut s := toks
  while !s.isEmpty do
    let (is, s') ← parseInstr ctx s
    acc := acc ++ is
    s := s'
  return acc

end

private structure FuncDecl where
  symId         : Option String
  inlineExports : List String
  func          : Wasm.Function

/-- Resolve a `(type N)` / `(type $sig)` reference to its type-table
index. -/
private def resolveTypeIdxRef (types : Array TypeEntry) (s : String)
    : Except Err Nat :=
  if s.startsWith "$" then
    let name := (s.drop 1).toString
    match types.findIdx? (fun t => t.symId = some name) with
    | some i => .ok i
    | none => .error s!"unknown type id: {s}"
  else
    parseNat s

private def resolveTypeRef (types : Array TypeEntry) (s : String)
    : Except Err (List Wasm.ValueType × List Wasm.ValueType) := do
  let idx ← resolveTypeIdxRef types s
  match types[idx]? with
  | some { sig := some sig, .. } => .ok sig
  | some { sig := none, .. } =>
    .error s!"(type {s}) is not a supported (func ...) signature"
  | none => .error s!"type index out of range: {idx}"

/-- Parse a storage type (`i8`/`i16` packed, a numeric/value type, or a
reference type) for a struct field or array element (GC proposal). -/
private def parseStorageType : Sexpr → Wasm.StorageType
  | .atom "i8"  => .packed 8
  | .atom "i16" => .packed 16
  | .atom a     => match atomToValueType? a with
    | some vt => .val vt
    | none    => .val .anyref
  | .list (.atom "ref" :: _) => .val .anyref
  | .list l                  => .val (listToValueType l)

/-- Parse a field type `st` or `(mut st)` into a `FieldType`. -/
private def parseFieldType : Sexpr → Wasm.FieldType
  | .list [.atom "mut", st] => { storage := parseStorageType st, isMut := true }
  | st                      => { storage := parseStorageType st, isMut := false }

/-- Parse a `(field …)` form into its declared fields, each paired with its
optional name. A `(field $x st)` is one named field; `(field st …)` is one
anonymous field per storage type. -/
private def parseFieldDecl : Sexpr → List (Option String × Wasm.FieldType)
  | .list (.atom "field" :: .atom name :: [ft]) =>
    if name.startsWith "$" then [(some (name.drop 1).toString, parseFieldType ft)]
    else [(none, parseFieldType (.atom name)), (none, parseFieldType ft)]
  | .list (.atom "field" :: fs) => fs.map (fun ft => (none, parseFieldType ft))
  | _                           => []

private def parseFields (s : Sexpr) : List Wasm.FieldType :=
  (parseFieldDecl s).map (·.2)

/-- Recognise the GC composite type `(struct …)` / `(array …)` / `(func …)`
and, for `(sub $super …)`, peel the supertype reference. Returns the
composite together with the unresolved super name. -/
private partial def parseComposite : Sexpr → Option Wasm.CompositeType × Option String
  | .list (.atom "struct" :: fieldForms) =>
    (some (.struct (fieldForms.flatMap parseFields)), none)
  | .list [.atom "array", ft] =>
    (some (.array (parseFieldType ft)), none)
  | .list (.atom "sub" :: rest) =>
    -- `(sub $super comp)` or `(sub final $super comp)`; the comp is the
    -- last element, the super reference (if any) the preceding `$id`.
    let rest := match rest with | .atom "final" :: r => r | r => r
    match rest with
    | [.atom sup, comp] => let (c, _) := parseComposite comp; (c, some sup)
    | [comp]            => let (c, _) := parseComposite comp; (c, none)
    | _                 => (none, none)
  | _ => (none, none)

/-- The `(func …)` signature forms of a type body, peeling a `(sub …)`
wrapper. In GC modules `wasm-tools print` wraps function types as
`(sub final (func …))`, so a bare-`(func …)` match alone misses them. -/
private partial def funcSigForms? : Sexpr → Option (List Sexpr)
  | .list (.atom "func" :: sigForms) => some sigForms
  | .list (.atom "sub" :: rest) =>
    let rest := match rest with | .atom "final" :: r => r | r => r
    match rest with
    | [_, comp] => funcSigForms? comp
    | [comp]    => funcSigForms? comp
    | _         => none
  | _ => none

/-- Positional field names of a struct composite (peeling any `(sub …)`). -/
private partial def compositeFieldNames : Sexpr → List (Option String)
  | .list (.atom "struct" :: fieldForms) =>
    fieldForms.flatMap (fun f => (parseFieldDecl f).map (·.1))
  | .list (.atom "sub" :: rest) =>
    let rest := match rest with | .atom "final" :: r => r | r => r
    match rest with
    | [_, comp] => compositeFieldNames comp
    | [comp]    => compositeFieldNames comp
    | _         => []
  | _ => []

private def parseTypeField (xs : List Sexpr) : TypeEntry := Id.run do
  let mut symId : Option String := none
  let mut rest := xs
  match rest with
  | .atom a :: r =>
    if a.startsWith "$" then
      symId := some (a.drop 1).toString
      rest := r
  | _ => pure ()
  -- GC composite types (struct/array, possibly under `(sub …)`).
  let (comp, superRef) : Option Wasm.CompositeType × Option String :=
    match rest with
    | [single] => parseComposite single
    | _        => (none, none)
  let fieldNames : List (Option String) :=
    match rest with
    | [single] => compositeFieldNames single
    | _        => []
  -- `(sub …)` without `final` declares the type open for subtyping.
  let isFinal : Bool :=
    match rest with
    | [.list (.atom "sub" :: .atom "final" :: _)] => true
    | [.list (.atom "sub" :: _)]                  => false
    | _                                           => true
  let sig : Option (List Wasm.ValueType × List Wasm.ValueType) :=
    match (match rest with | [single] => funcSigForms? single | _ => none) with
    | some sigForms => Id.run do
      let mut paramTypes : List Wasm.ValueType := []
      let mut resultTypes : List Wasm.ValueType := []
      let mut ok := true
      for f in sigForms do
        match f with
        | .list (.atom "param" :: tail) =>
          for t in tail do
            match t with
            | .atom a =>
              if a.startsWith "$" then pure ()
              else match atomToValueType? a with
                | some vt => paramTypes := paramTypes ++ [vt]
                | none    => ok := false
            -- Reference-type forms like `(ref null T)` are lowered to
            -- the i32 placeholder so the function still type-checks
            -- against our reduced value type set.
            | .list l => paramTypes := paramTypes ++ [listToValueType l]
        | .list (.atom "result" :: tail) =>
          for t in tail do
            match t with
            | .atom a =>
              match atomToValueType? a with
              | some vt => resultTypes := resultTypes ++ [vt]
              | none    => ok := false
            | .list l => resultTypes := resultTypes ++ [listToValueType l]
        | _ => ok := false
      if ok then return some (paramTypes, resultTypes) else return none
    | none => none
  return { symId, sig, comp, superRef, fieldNames, isFinal }

private def stripQuotes (s : String) : String :=
  if s.length ≥ 2 && s.startsWith "\"" && s.endsWith "\"" then
    ((s.drop 1).dropEnd 1).toString
  else s

private def hexDigitVal (c : Char) : Option Nat :=
  if c.isDigit then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (10 + c.toNat - 'a'.toNat)
  else if 'A' ≤ c && c ≤ 'F' then some (10 + c.toNat - 'A'.toNat)
  else none

-- decode WAT string escapes to a String (for export/import names)
private partial def decodeWatStringChars : List Char → String
  | []                       => ""
  | '\\' :: 'n'  :: r       => "\n" ++ decodeWatStringChars r
  | '\\' :: 't'  :: r       => "\t" ++ decodeWatStringChars r
  | '\\' :: 'r'  :: r       => "\r" ++ decodeWatStringChars r
  | '\\' :: '"'  :: r       => "\"" ++ decodeWatStringChars r
  | '\\' :: '\\' :: r       => "\\" ++ decodeWatStringChars r
  | '\\' :: 'u'  :: '{' :: r =>
    let (hex, rest) := r.span (· != '}')
    match rest with
    | '}' :: r' =>
      if !hex.isEmpty && hex.all (fun c => (hexDigitVal c).isSome) then
        let n := hex.foldl (fun acc c => acc * 16 + (hexDigitVal c).getD 0) 0
        String.singleton (Char.ofNat n) ++ decodeWatStringChars r'
      else "\\u{" ++ decodeWatStringChars (hex ++ rest)
    | _ => "\\u{" ++ decodeWatStringChars (hex ++ rest)
  | '\\' :: h1 :: h2 :: r   =>
    match hexDigitVal h1, hexDigitVal h2 with
    | some d1, some d2 =>
      String.singleton (Char.ofNat (d1 * 16 + d2)) ++ decodeWatStringChars r
    | _, _ => "\\" ++ decodeWatStringChars (h1 :: h2 :: r)
  | '\\' :: c :: r           => "\\" ++ String.singleton c ++ decodeWatStringChars r
  | c :: r                   => String.singleton c ++ decodeWatStringChars r

private def decodeWatString (s : String) : String :=
  if s.length ≥ 2 && s.startsWith "\"" && s.endsWith "\"" then
    decodeWatStringChars ((s.drop 1).dropEnd 1).toString.toList
  else s

private def parseFunc (funcIds : Std.HashMap String Nat)
    (globalIds : Std.HashMap String Nat)
    (tableNames : Std.HashMap String Nat)
    (elemNames : Std.HashMap String Nat)
    (memNames : Std.HashMap String Nat)
    (tagNames : Std.HashMap String Nat)
    (types : Array TypeEntry) (xs : List Sexpr)
    : Except Err FuncDecl := do
  let mut paramTypes : List Wasm.ValueType := []
  let mut resultTypes : List Wasm.ValueType := []
  let mut localTypes : List Wasm.ValueType := []
  let mut symId : Option String := none
  let mut inlineExports : List String := []
  let mut localIds : Std.HashMap String Nat := {}
  let mut typeApplied : Bool := false
  -- Declared `(type N)` index, recorded on the function so the runtime
  -- nominal type checks (`(return_)call_indirect`, `ref.test`/`ref.cast`
  -- against a concrete function type) can consult the `rec`/`sub`
  -- hierarchy (issues #95/#96).
  let mut declaredTypeIdx : Option Nat := none
  let mut rest := xs
  match rest with
  | .atom a :: r =>
    if a.startsWith "$" then
      symId := some (a.drop 1).toString
      rest := r
  | _ => pure ()
  let mut headerDone := false
  while !rest.isEmpty && !headerDone do
    match rest with
    | .list (.atom h :: tail) :: r =>
      match h with
      | "param" =>
        if !typeApplied then
          let named := tail.any fun
            | .atom a => a.startsWith "$"
            | _ => false
          if named then
            for t in tail do
              match t with
              | .atom a =>
                if a.startsWith "$" then
                  localIds := localIds.insert (a.drop 1).toString paramTypes.length
                else match atomToValueType? a with
                  | some vt => paramTypes := paramTypes ++ [vt]
                  | none    => throw s!"unsupported param type: {a}"
              -- Reference-type forms like `(ref null T)` → i32 placeholder.
              | .list l => paramTypes := paramTypes ++ [listToValueType l]
          else
            for t in tail do
              match t with
              | .atom a =>
                match atomToValueType? a with
                | some vt => paramTypes := paramTypes ++ [vt]
                | none    => throw s!"unsupported param type: {a}"
              | .list l => paramTypes := paramTypes ++ [listToValueType l]
        rest := r
      | "local" =>
        let named := tail.any fun
          | .atom a => a.startsWith "$"
          | _ => false
        if named then
          for t in tail do
            match t with
            | .atom a =>
              if a.startsWith "$" then
                localIds := localIds.insert (a.drop 1).toString
                  (paramTypes.length + localTypes.length)
              else match atomToValueType? a with
                | some vt => localTypes := localTypes ++ [vt]
                | none    => throw s!"unsupported local type: {a}"
            -- Reference-type forms like `(ref null T)` → i32 placeholder.
            | .list l => localTypes := localTypes ++ [listToValueType l]
        else
          for t in tail do
            match t with
            | .atom a =>
              match atomToValueType? a with
              | some vt => localTypes := localTypes ++ [vt]
              | none    => throw s!"unsupported local type: {a}"
            | .list l => localTypes := localTypes ++ [listToValueType l]
        rest := r
      | "result" =>
        -- wasm-tools commonly emits `(type N) (param …) (result …)` where
        -- the explicit (param/result …) merely re-state what (type N)
        -- resolved to; appending in that case would double the results.
        if !typeApplied then
          for t in tail do
            match t with
            | .atom a =>
              match atomToValueType? a with
              | some vt => resultTypes := resultTypes ++ [vt]
              | none    => throw s!"unsupported result type: {a}"
            -- Reference-type forms like `(ref null T)` → i32 placeholder.
            | .list l => resultTypes := resultTypes ++ [listToValueType l]
        rest := r
      | "type" =>
        match tail with
        | [.atom ref] =>
          if !paramTypes.isEmpty then
            throw "(type ...) after explicit (param/result ...) is not supported"
          let (ps, rs) ← resolveTypeRef types ref
          paramTypes := ps
          resultTypes := rs
          typeApplied := true
          declaredTypeIdx := some (← resolveTypeIdxRef types ref)
        | _ => throw "malformed (type ...) reference"
        rest := r
      | "export" =>
        match tail with
        | [.atom s] =>
          inlineExports := inlineExports ++ [decodeWatString s]
        | _ => throw "malformed inline (export ...)"
        rest := r
      | "import" =>
        throw "inline (import ...) on a func is not supported"
      | _ =>
        headerDone := true
    | _ => headerDone := true
  let resolveBlockType : BlockTypeResolver := fun ref =>
    match resolveTypeRef types ref with
    | .ok sig  => some sig
    | .error _ => none
  let ctx : Ctx := { funcIds, localIds, globalIds, types, tableNames, elemNames,
                     memNames, tagNames, resolveBlockType }
  let instrs ← parseInstrSeq ctx rest
  return { symId, inlineExports,
           func := {
             params  := paramTypes
             locals  := localTypes
             body    := instrs
             results := resultTypes
             typeIdx := declaredTypeIdx
           } }

private def resolveFuncRef (idOf : Std.HashMap String Nat) (s : String)
    : Except Err Nat := do
  if s.startsWith "$" then
    match idOf[(s.drop 1).toString]? with
    | some i => .ok i
    | none => .error s!"unknown function id: {s}"
  else
    parseNat s

private def collectFuncNames (fields : List Sexpr)
    : Except Err (Std.HashMap String Nat) := do
  let mut idOf : Std.HashMap String Nat := {}
  let mut i := 0
  for f in fields do
    match f with
    | .list (.atom "func" :: body) =>
      match body with
      | .atom a :: _ =>
        if a.startsWith "$" then
          idOf := idOf.insert (a.drop 1).toString i
      | _ => pure ()
      i := i + 1
    | _ => pure ()
  return idOf

private def collectGlobalNames (fields : List Sexpr)
    : Except Err (Std.HashMap String Nat) := do
  let mut idOf : Std.HashMap String Nat := {}
  let mut i := 0
  -- Imported globals occupy the low indices, in import order.
  for f in fields do
    match f with
    | .list [.atom "import", .atom _, .atom _, .list (.atom "global" :: body)] =>
      match body with
      | .atom a :: _ =>
        if a.startsWith "$" then
          idOf := idOf.insert (a.drop 1).toString i
      | _ => pure ()
      i := i + 1
    | _ => pure ()
  for f in fields do
    match f with
    | .list (.atom "global" :: body) =>
      match body with
      | .atom a :: _ =>
        if a.startsWith "$" then
          idOf := idOf.insert (a.drop 1).toString i
      | _ => pure ()
      i := i + 1
    | _ => pure ()
  return idOf

private partial def decodeWatBytes : List Char → Except Err (List UInt8)
  | []                   => .ok []
  | '\\' :: 'n'  :: r   => (0x0A :: ·) <$> decodeWatBytes r
  | '\\' :: 't'  :: r   => (0x09 :: ·) <$> decodeWatBytes r
  | '\\' :: 'r'  :: r   => (0x0D :: ·) <$> decodeWatBytes r
  | '\\' :: '"'  :: r   => (0x22 :: ·) <$> decodeWatBytes r
  | '\\' :: '\'' :: r   => (0x27 :: ·) <$> decodeWatBytes r
  | '\\' :: '\\' :: r   => (0x5C :: ·) <$> decodeWatBytes r
  | '\\' :: h1 :: h2 :: r =>
    match hexDigitVal h1, hexDigitVal h2 with
    | some d1, some d2 => (UInt8.ofNat (d1 * 16 + d2) :: ·) <$> decodeWatBytes r
    | _, _ => .error s!"invalid hex escape \\{h1}{h2} in data string"
  | '\\' :: c :: _ => .error s!"invalid escape '\\{c}' in data string"
  | c :: r               => (c.toNat.toUInt8 :: ·) <$> decodeWatBytes r

private def parseWatString (s : String) : Except Err (List UInt8) :=
  if !s.startsWith "\"" then .error s!"expected string literal, got: {s}"
  else decodeWatBytes (stripQuotes s).toList

/- Whether a global-initializer sexpr mentions an instruction whose value
depends on the store and so cannot be folded to a literal at decode time:
`global.get` of an imported global (wasm 1.0), or the extended-const
arithmetic ops (`i32.add`/`i32.sub`/`i32.mul`, i64 ditto). Recurses into
folded operand forms (the flat form emitted by `wasm-tools print` is
handled by the list case). -/
mutual
  /-- Scan a single sexpr for an atom satisfying `p`; recurse into a `(…)`
  list via the list helper (covers both the folded operand form and the flat
  form emitted by `wasm-tools print`). -/
  def initExprMentions (p : String → Bool) : Sexpr → Bool
    | .atom a => p a
    | .list ys => initExprMentionsList p ys
  /-- Scan a sequence of sexprs (the operands of a folded instruction). -/
  def initExprMentionsList (p : String → Bool) : List Sexpr → Bool
    | [] => false
    | y :: ys => initExprMentions p y || initExprMentionsList p ys
end

/-- Scan a single sexpr; recurse into a `(…)` list via the list helper. -/
def initExprNeedsEval : Sexpr → Bool :=
  initExprMentions fun a =>
    a == "global.get"
      || a ∈ #["i32.add", "i32.sub", "i32.mul", "i64.add", "i64.sub", "i64.mul"]

/-- Whether a global-initializer sexpr mentions a GC heap-allocating constant
instruction (`struct.new`/`array.new*`), in either the flat or the folded
form. Such initializers cannot be folded to a literal at decode time. -/
def initExprAllocates : Sexpr → Bool :=
  initExprMentions fun a =>
    a ∈ #["struct.new", "struct.new_default",
          "array.new", "array.new_default", "array.new_fixed",
          "array.new_data", "array.new_elem"]

private def parseGlobalDecl (ctx : Ctx) (xs : List Sexpr) :
    Except Err Wasm.GlobalDecl := do
  let xs := match xs with
    | .atom a :: r => if a.startsWith "$" then r else xs
    | _ => xs
  -- Skip inline `(export "n")` annotations (captured by `parseModule`).
  let xs := xs.dropWhile fun
    | .list (.atom "export" :: _) => true
    | _ => false
  let (_vt, xs) ← match xs with
    | .list (.atom "mut" :: .atom t :: _) :: r =>
      match atomToValueType? t with
      | some vt => .ok (vt, r)
      | none    => .error s!"unsupported global type: {t}"
    -- `(mut (ref null T))` and similar reference-type syntaxes from
    -- proposals we don't model — accept as i32 placeholder.
    | .list (.atom "mut" :: .list _ :: _) :: r => .ok (.i32, r)
    | .atom t :: r =>
      match atomToValueType? t with
      | some vt => .ok (vt, r)
      | none    => .error s!"unsupported global type: {t}"
    -- `(ref null T)` form (immutable ref type).
    | .list (.atom "ref" :: _) :: r => .ok (.i32, r)
    | _ => .error "malformed (global ...): missing type"
  -- GC heap-allocating initializers (`struct.new`/`array.new*`) cannot be
  -- folded to a single value at decode time; keep the const-expr program so
  -- `Module.runConstGlobals` can evaluate it at instantiation.
  if xs.any initExprAllocates then
    let prog ← parseInstrSeq ctx xs
    -- The value can't be folded at decode time; stash a placeholder `init`
    -- and let `Module.runConstGlobals` evaluate `initExpr` at instantiation.
    return { init := .anyref none, initExpr := prog }
  -- `global.get` of an imported global is a wasm 1.0 constant expression,
  -- and `i32.add`/`i32.sub`/`i32.mul` (i64 ditto) are the extended-const
  -- proposal. Neither can be folded to a single value at decode time — the
  -- value depends on the store — so, like the GC allocator case above, keep
  -- the const-expr program and let `Module.runConstGlobals` evaluate it at
  -- instantiation once the imported globals are in place. The placeholder
  -- `init` carries the declared value type for static type-checking.
  --
  -- `wasm-tools print` emits these as a *flat* instruction sequence
  -- (`i32.const 20 i32.const 2 i32.mul …`), so detect by scanning every
  -- atom (recursing into folded forms) for a `global.get` or arithmetic
  -- op rather than looking only at the head. Plain const / ref / v128
  -- initializers contain none of these and keep folding to a literal below.
  if xs.any initExprNeedsEval then
    let prog ← parseInstrSeq ctx xs
    return { init := _vt.zero, initExpr := prog }
  -- The init expression is either wrapped in a `(...)` list or — in
  -- wasm-tools' canonical print — emitted as a bare sequence of atoms
  -- (for v128.const this is `v128.const <shape> <lanes...>`, six tokens).
  -- Normalise to "head op atom + tail" for the shape match below.
  let (head?, tail) : Option String × List Sexpr := match xs with
    | [.list (.atom h :: rest)] => (some h, rest)
    | .atom h :: rest           => (some h, rest)
    | _                         => (none, [])
  let init : Wasm.Value ← match head?, tail with
    -- GC constant init `i32.const N ref.i31` (flat form emitted by
    -- `wasm-tools print`): box the low 31 bits as an i31 reference.
    | some "i32.const", [.atom n, .atom "ref.i31"] =>
      .ok (.anyref (some (.i31 ((← parseI32 n) &&& 0x7fffffff))))
    | some "i32.const", .atom n :: _ => .ok (.i32 (← parseI32 n))
    | some "i64.const", .atom n :: _ => .ok (.i64 (← parseI64 n))
    | some "f32.const", .atom n :: _ => .ok (.f32 (← parseF32Lit n))
    | some "f64.const", .atom n :: _ => .ok (.f64 (← parseF64Lit n))
    | some "ref.null", .atom ht :: _ =>
      -- Reuse `refNullInstr`'s heap-type resolution (incl. concrete `$t`
      -- types, where a struct/array denotes the managed null and a function
      -- type the null funcref); map the resulting null to its init value.
      match refNullInstr ctx.types ht with
      | .refNullExtern  => .ok (.externref none)
      | .gc .refNullAny => .ok (.anyref none)
      | .refNull        => .ok (.funcref none)
      | _               => .ok (.i32 0)
    -- `(ref.i31 (i32.const N))` constant init (GC proposal).
    | some "ref.i31", [.list [.atom "i32.const", .atom n]] =>
      .ok (.anyref (some (.i31 ((← parseI32 n) &&& 0x7fffffff))))
    | some "ref.func", .atom ref :: _ => .ok (.funcref (some (← resolveFuncRef ctx.funcIds ref)))
    | some "ref.func", _ => .error "global ref.func init expects a function immediate"
    | some "ref.null", _ => .error "global ref.null init expects a heap-type immediate"
    -- Init expressions from proposals we don't model are accepted by
    -- the decoder; the *value* is replaced with a zero placeholder
    -- since none of them feed an `i32`/`i64` computation. Function
    -- bodies that would read the global hit `unreachable` anyway.
    | some "v128.const", _ =>
      match parseV128Const tail with
      | .ok (bits, _) => .ok (.v128 bits)
      | .error e      => .error e
    | _, _ => .error "global init expression must be i32.const or i64.const"
  .ok { init }

private def parseMemDecl (xs : List Sexpr) : Except Err Wasm.MemDecl := do
  let xs := match xs with
    | .atom a :: r => if a.startsWith "$" then r else xs
    | _ => xs
  -- Skip inline `(export "n")` annotations and an `(import "m" "n")`
  -- form (an imported memory decodes as a fresh local memory with the
  -- declared bounds until cross-module linking is supported).
  let xs := xs.dropWhile fun
    | .list (.atom "export" :: _) => true
    | .list (.atom "import" :: _) => true
    | _ => false
  -- Optional explicit address type: `i64` selects a 64-bit (memory64)
  -- memory; `i32` is accepted for symmetry and means the default.
  let (is64, xs) : Bool × List Sexpr := match xs with
    | .atom "i64" :: r => (true, r)
    | .atom "i32" :: r => (false, r)
    | _ => (false, xs)
  -- 64-bit memories may declare page bounds past 2^32; clamp them into
  -- the UInt32 fields. The effective grow ceiling (`Module.memoryCap`,
  -- 65536 pages) sits far below the clamp, so semantics are unaffected.
  let parsePages (s : String) : Except Err UInt32 :=
    if is64 then do
      let n ← parseUnsignedNat (stripUnderscores s)
      .ok (UInt32.ofNat (Nat.min n 0xFFFFFFFF))
    else parseU32 s
  match xs with
  | [.atom min] =>
    .ok { pagesMin := ← parsePages min, is64 }
  | [.atom min, .atom max] =>
    .ok { pagesMin := ← parsePages min, pagesMax := some (← parsePages max), is64 }
  | _ => .error "malformed (memory ...): expected (memory min) or (memory min max)"

/-- Parse a `(data ...)` body. Active segments produce `offset := some n`;
passive segments (no offset expression) produce `offset := none`. -/
private def parseDataSegment (ctx : Ctx)
    (xs : List Sexpr) : Except Err Wasm.DataSegment := do
  let memNames := ctx.memNames
  -- Strip an optional segment id ($name).
  let xs := match xs with
    | .atom a :: r => if a.startsWith "$" then r else xs
    | _ => xs
  -- Optional target memory (multi-memory): a bare index or an explicit
  -- `(memory N|$name)` form.
  let (memIdx, xs) ← match xs with
    | .atom a :: r =>
      if a.all Char.isDigit then do pure ((← parseNat a), r)
      else pure ((0 : Nat), .atom a :: r)
    | .list [.atom "memory", .atom mref] :: r => do
      pure ((← resolveNamed memNames "memory" mref), r)
    | r => pure ((0 : Nat), r)
  -- Extract the offset constant; passive segments have no offset form.
  -- Non-literal offset expressions (`global.get`, extended-const
  -- arithmetic) cannot be folded at decode time — the value depends on
  -- the store — so they are kept as a const-expr program in
  -- `offsetExpr` (with a `some 0` active-marker placeholder in
  -- `offset`) and evaluated at instantiation by
  -- `Module.runActiveSegments`.
  let parsed ← match xs with
    | .list [.atom "offset", .list [.atom "i32.const", .atom n]] :: r =>
      do .ok ((some (← parseU32 n) : Option UInt32), ([] : Wasm.Program), r)
    | .list [.atom "i32.const", .atom n] :: r =>
      do .ok ((some (← parseU32 n) : Option UInt32), ([] : Wasm.Program), r)
    -- memory64: active offsets in a 64-bit memory are i64 constants. The
    -- segment offset field is 32 bits; active 64-bit segments in practice
    -- are tiny, so a genuinely huge offset is a decode error.
    | .list [.atom "offset", .list [.atom "i64.const", .atom n]] :: r =>
      do
        let v ← parseI64 n
        if v.toNat ≥ 2 ^ 32 then .error "data offset out of range"
        else .ok ((some v.toUInt32 : Option UInt32), ([] : Wasm.Program), r)
    | .list [.atom "i64.const", .atom n] :: r =>
      do
        let v ← parseI64 n
        if v.toNat ≥ 2 ^ 32 then .error "data offset out of range"
        else .ok ((some v.toUInt32 : Option UInt32), ([] : Wasm.Program), r)
    -- Non-literal offset expressions (`global.get`, extended-const
    -- arithmetic): keep the const-expr program for evaluation at
    -- instantiation; `some 0` marks the segment active.
    | .list (.atom "offset" :: es) :: r =>
      do .ok ((some (0 : UInt32) : Option UInt32), (← parseInstrSeq ctx es), r)
    -- Bare (unwrapped) non-literal offset expression, e.g.
    -- `(data (global.get $o) "…")`.
    | e :: r =>
      if initExprNeedsEval e then
        do .ok ((some (0 : UInt32) : Option UInt32), (← parseInstrSeq ctx [e]), r)
      else .ok ((none : Option UInt32), ([] : Wasm.Program), xs)
    | _ => .ok ((none : Option UInt32), ([] : Wasm.Program), xs)
  let (offset, offsetExpr, rest) := parsed
  let mut bytes : List UInt8 := []
  for tok in rest do
    match tok with
    | .atom s => bytes := bytes ++ (← parseWatString s)
    | _ => .error "data segment: expected string literal(s)"
  .ok { offset, bytes, memIdx, offsetExpr }

/-- Collect names declared by `(table $name ...)` forms in source order.
Same pattern as `collectFuncNames` / `collectGlobalNames`. -/
private def collectTableNames (fields : List Sexpr) : Std.HashMap String Nat := Id.run do
  let mut idOf : Std.HashMap String Nat := {}
  let mut i := 0
  -- Imported tables occupy the low indices, in import order.
  for f in fields do
    match f with
    | .list [.atom "import", .atom _, .atom _, .list (.atom "table" :: body)] =>
      match body with
      | .atom a :: _ =>
        if a.startsWith "$" then
          idOf := idOf.insert (a.drop 1).toString i
      | _ => pure ()
      i := i + 1
    | _ => pure ()
  for f in fields do
    match f with
    | .list (.atom "table" :: body) =>
      match body with
      | .atom a :: _ =>
        if a.startsWith "$" then
          idOf := idOf.insert (a.drop 1).toString i
      | _ => pure ()
      i := i + 1
    | _ => pure ()
  return idOf

/-- Collect names declared by `(memory $name ...)` forms in source order
(multi-memory). -/
private def collectMemNames (fields : List Sexpr) : Std.HashMap String Nat := Id.run do
  let mut idOf : Std.HashMap String Nat := {}
  let mut i := 0
  -- Imported memorys occupy the low indices, in import order.
  for f in fields do
    match f with
    | .list [.atom "import", .atom _, .atom _, .list (.atom "memory" :: body)] =>
      match body with
      | .atom a :: _ =>
        if a.startsWith "$" then
          idOf := idOf.insert (a.drop 1).toString i
      | _ => pure ()
      i := i + 1
    | _ => pure ()
  for f in fields do
    match f with
    | .list (.atom "memory" :: body) =>
      match body with
      | .atom a :: _ =>
        if a.startsWith "$" then
          idOf := idOf.insert (a.drop 1).toString i
      | _ => pure ()
      i := i + 1
    | _ => pure ()
  return idOf

/-- Collect names declared by `(elem $name ...)` forms, numbering them the
way `parseModule` numbers element segments: an inline `(table … (elem …))`
initializer occupies one (anonymous) slot in the element index space at
the table's source position, exactly as the spec's inline-elem
abbreviation expands to a leading active segment. -/
private def collectElemNames (fields : List Sexpr) : Std.HashMap String Nat := Id.run do
  let mut idOf : Std.HashMap String Nat := {}
  let mut i := 0
  for f in fields do
    match f with
    | .list (.atom "elem" :: body) =>
      match body with
      | .atom "declare" :: .atom a :: _
      | .atom a :: _ =>
        if a.startsWith "$" then
          idOf := idOf.insert (a.drop 1).toString i
      | _ => pure ()
      i := i + 1
    | .list (.atom "table" :: body) =>
      -- Inline `(elem …)` initializer inside a table declaration.
      if body.any (fun s => match s with
          | .list (.atom "elem" :: _) => true
          | _ => false) then
        i := i + 1
    | _ => pure ()
  return idOf

/-- Parse the body of one `(table ...)` form. We accept the canonical
post-`wasm-tools print` shapes:

* `(table $name? min funcref)`
* `(table $name? min max funcref)`
* `(table $name? funcref (elem $f0 $f1 …))` — inline initializer; the
  table is sized to exactly the number of refs.

The second value returned is an inline element segment (for the third
form) or `none`. Non-funcref element types are accepted lexically with
a zero-size declaration so unrelated modules still decode; nothing
references those tables. -/
private def parseTableDecl (funcIds : Std.HashMap String Nat) (tableIdx : Nat)
    (xs : List Sexpr) : Except Err (Wasm.TableDecl × Option Wasm.ElementSegment) := do
  let xs := match xs with
    | .atom a :: r => if a.startsWith "$" then r else xs
    | _ => xs
  -- Optional explicit address type: `i64` selects a 64-bit (table64)
  -- table; `i32` is accepted for symmetry and means the default.
  let (is64, xs) : Bool × List Sexpr := match xs with
    | .atom "i64" :: r => (true, r)
    | .atom "i32" :: r => (false, r)
    | _ => (false, xs)
  -- 64-bit tables may declare bounds past 2^32; parse them in full and
  -- clamp at the implementation growth ceiling (`Module.tableCap` would
  -- intersect with it anyway, and tables are materialised as lists).
  let parseBound (s : String) : Except Err Nat :=
    if is64 then do
      let n ← parseUnsignedNat (stripUnderscores s)
      .ok (Nat.min n Wasm.Module.tableHardCap)
    else parseNat s
  match xs with
  | [.atom "funcref", .list (.atom "elem" :: items)] =>
    let items := match items with
      | .atom "func" :: rest => rest
      | _ => items
    let mut funcs : List (Option Nat) := []
    for it in items do
      match it with
      | .atom s =>
        let i ← resolveFuncRef funcIds s
        funcs := funcs ++ [some i]
      | .list [.atom "ref.func", .atom s] =>
        let i ← resolveFuncRef funcIds s
        funcs := funcs ++ [some i]
      | .list [.atom "ref.null", _] => funcs := funcs ++ [none]
      | _ => .error "(table funcref (elem ...)): expected func reference"
    let n := funcs.length
    .ok ({ min := n, max := some n, elemType := .funcref, is64 },
         some { tableIdx := some tableIdx, offset := some 0, funcs })
  | [.atom min, .atom elemTy] =>
    -- Single-bound declaration. `funcref`/`externref` are modelled;
    -- element types from unmodelled proposals fall back to `funcref` so
    -- the index space stays aligned (nothing references those tables).
    let n ← parseBound min
    .ok ({ min := n, elemType := (atomToValueType? elemTy).getD .funcref, is64 }, none)
  | [.atom min, .atom max, .atom elemTy] =>
    let nMin ← parseBound min
    let nMax ← parseBound max
    .ok ({ min := nMin, max := some nMax,
           elemType := (atomToValueType? elemTy).getD .funcref, is64 }, none)
  -- List element types, e.g. `(table $t 1 1 (ref null $t))`. `listToValueType`
  -- maps GC heap references to the `anyref` slot (so the table fills with the
  -- managed null) and other ref types to funcref/externref.
  | [.atom min, .list l] =>
    let n ← parseBound min
    .ok ({ min := n, elemType := listToValueType l, is64 }, none)
  | [.atom min, .atom max, .list l] =>
    let nMin ← parseBound min
    let nMax ← parseBound max
    .ok ({ min := nMin, max := some nMax, elemType := listToValueType l, is64 }, none)
  | [.atom _other] => .ok ({ min := 0, elemType := .funcref, is64 }, none)
  | _ => .error "malformed (table ...) declaration"

/-- Whether a `(ref null? ht)` element type uses the constant-expression
item form rather than the bare funcref list. Abstract `func`/`extern`
element types keep the funcref/externref `funcs` path; every other ref
type (GC abstract heap types and concrete `$t` typed references) takes the
const-expr path, whose evaluator handles `ref.func`/`ref.i31`/`struct.new`
uniformly. -/
private def elemRefIsGc (inner : List Sexpr) : Bool :=
  match inner with
  | [.atom ht] | [.atom "null", .atom ht] =>
    !(isNullFuncrefHeapType ht || isNullExternrefHeapType ht)
  | _ => false

/-- Parse one `(elem ...)` declaration. Handles every shape produced by
`wasm-tools print`: active w/ default or explicit table, passive with
the `func` or `funcref` keyword, and declarative (`elem declare`).
Inside the function-ref list each entry is one of:

* `$name` / `N` — bare function ref atom
* `(ref.func $name)` — explicit constant
* `(ref.null func)` — null entry
* `(item …)` — canonical wrapper; we look one level inside
-/
private def parseElemSegment (ctx : Ctx)
    (xs : List Sexpr) : Except Err Wasm.ElementSegment := do
  let funcIds := ctx.funcIds
  let tableNames := ctx.tableNames
  let mut rest := xs
  let mut isDeclarative := false
  let mut isGc := false
  match rest with
  | .atom "declare" :: r => isDeclarative := true; rest := r
  | _ => pure ()
  match rest with
  | .atom a :: r =>
    if a.startsWith "$" then rest := r
  | _ => pure ()
  let mut tableIdx : Option Nat := if isDeclarative then none else some 0
  match rest with
  | .list [.atom "table", .atom t] :: r =>
    let idx ←
      if t.startsWith "$" then
        match tableNames[(t.drop 1).toString]? with
        | some i => .ok i
        | none   => .error s!"unknown table id: {t}"
      else parseNat t
    tableIdx := some idx; rest := r
  | _ => pure ()
  let mut offset : Option Nat := none
  let mut offsetExpr : Wasm.Program := []
  match rest with
  | .list [.atom "offset", .list [.atom "i32.const", .atom n]] :: r =>
    let v ← parseNat n; offset := some v; rest := r
  | .list [.atom "offset", .list [.atom "i64.const", .atom n]] :: r =>
    -- table64: active offsets in a 64-bit table are i64 constants.
    let v ← parseI64 n; offset := some v.toNat; rest := r
  | .list (.atom "offset" :: es) :: r =>
    -- Non-literal offset expressions (`global.get`, extended-const
    -- arithmetic): keep the const-expr program for evaluation at
    -- instantiation by `Module.runActiveSegments`; `some 0` marks the
    -- segment active.
    offset := some 0; offsetExpr := (← parseInstrSeq ctx es); rest := r
  | .list [.atom "i32.const", .atom n] :: r =>
    let v ← parseNat n; offset := some v; rest := r
  | .list [.atom "i64.const", .atom n] :: r =>
    let v ← parseI64 n; offset := some v.toNat; rest := r
  -- Bare (unwrapped) non-literal offset expression, e.g.
  -- `(elem (global.get $o) $f)`. Guard against `(item …)` heads so a
  -- passive segment's first const-expr item is never taken for an offset.
  | e :: r =>
    match e with
    | .list (.atom "item" :: _) => pure ()
    | _ =>
      if initExprNeedsEval e then
        offset := some 0; offsetExpr := (← parseInstrSeq ctx [e]); rest := r
  | _ => pure ()
  match rest with
  | .atom "func"      :: r => rest := r
  | .atom "funcref"   :: r => rest := r
  | .atom "externref" :: r => rest := r
  -- GC managed-reference element-type keyword (GC proposal): the items are
  -- constant expressions. Only consume `rest` when this atom really is such
  -- a keyword — otherwise it is the first funcref item (e.g. `$f0`), which
  -- the item loop below must still see.
  | .atom t :: r =>
    if t == "i31ref" || t == "anyref" || t == "eqref"
       || t == "structref" || t == "arrayref" || t == "nullref" then
      isGc := true; rest := r
  -- List type form `(ref null? ht)`: GC when `ht` is a managed heap type.
  | .list (.atom "ref" :: inner) :: r =>
    if elemRefIsGc inner then isGc := true
    rest := r
  | _ => pure ()
  if isDeclarative then offset := none; offsetExpr := []
  if isGc then
    -- Each item is a `(item <const-expr>)` (or a bare const-expr) producing
    -- one reference value; keep the program for `runConstElems`.
    let mut exprs : List Wasm.Program := []
    for it in rest do
      match it with
      | .list (.atom "item" :: inner) => exprs := exprs ++ [← parseInstrSeq ctx inner]
      | other                         => exprs := exprs ++ [← parseInstrSeq ctx [other]]
    return { tableIdx, offset, exprs, offsetExpr }
  let mut funcs : List (Option Nat) := []
  for it in rest do
    match it with
    | .atom s =>
      let i ← resolveFuncRef funcIds s
      funcs := funcs ++ [some i]
    | .list [.atom "ref.func", .atom s] =>
      let i ← resolveFuncRef funcIds s
      funcs := funcs ++ [some i]
    | .list [.atom "ref.null", _] => funcs := funcs ++ [none]
    | .list (.atom "item" :: inner) =>
      match inner with
      | [.atom "ref.func", .atom s]
      | [.list [.atom "ref.func", .atom s]] =>
        let i ← resolveFuncRef funcIds s
        funcs := funcs ++ [some i]
      | [.atom "ref.null", _]
      | [.list [.atom "ref.null", _]] => funcs := funcs ++ [none]
      | _ => .error "elem: unsupported (item ...) form"
    | _ => .error "elem: unsupported entry"
  .ok { tableIdx, offset, funcs, offsetExpr }

/-- Parse the `(param …)` / `(result …)` / `(type N)` forms inside the
`(func …)` of an `(import …)` declaration, returning `(params, results)`.

Two equivalent surface forms are accepted:
* inline `(param T) … (result T)` — directly populate the signature;
* `(type N)` or `(type $sig)` — look up `N` in the module's type table.

`wasm-tools print` emits the `(type N)` form for every Rust-compiled
import, so resolving it here is the difference between a typed import
and a `params := [], results := []` stub. Named param/local ids inside
an import are ignored (they're never referenced by id from the wasm
body — imports have no body). -/
private def parseImportSig (types : Array TypeEntry) (xs : List Sexpr)
    : Except Err (List Wasm.ValueType × List Wasm.ValueType) := do
  let mut params : List Wasm.ValueType := []
  let mut results : List Wasm.ValueType := []
  for x in xs do
    match x with
    | .list (.atom "param" :: tail) =>
      for t in tail do
        match t with
        | .atom a =>
          if a.startsWith "$" then pure ()
          else match atomToValueType? a with
            | some vt => params := params ++ [vt]
            | none    => throw s!"unsupported import param type: {a}"
        | _ => throw "malformed (param ...) in import"
    | .list (.atom "result" :: tail) =>
      for t in tail do
        match t with
        | .atom a =>
          match atomToValueType? a with
          | some vt => results := results ++ [vt]
          | none    => throw s!"unsupported import result type: {a}"
        | _ => throw "malformed (result ...) in import"
    | .list [.atom "type", .atom ref] =>
      -- `(type N)` / `(type $sig)` — resolve against the module's type
      -- table. Overwrites any previously accumulated `(param …)` /
      -- `(result …)`, matching the wasm convention that a referenced
      -- type fully specifies the signature.
      let (ps, rs) ← resolveTypeRef types ref
      params := ps
      results := rs
    | _ => pure ()
  return (params, results)

/-- Collect `$name → tag index` (imports first, then declarations). -/
private def collectTagNames (fields : List Sexpr) : Std.HashMap String Nat := Id.run do
  let mut idOf : Std.HashMap String Nat := {}
  let mut i := 0
  for f in fields do
    match f with
    | .list [.atom "import", .atom _, .atom _, .list (.atom "tag" :: body)] =>
      match body with
      | .atom a :: _ =>
        if a.startsWith "$" then idOf := idOf.insert (a.drop 1).toString i
      | _ => pure ()
      i := i + 1
    | _ => pure ()
  for f in fields do
    match f with
    | .list (.atom "tag" :: body) =>
      match body with
      | .atom a :: _ =>
        if a.startsWith "$" then idOf := idOf.insert (a.drop 1).toString i
      | _ => pure ()
      i := i + 1
    | _ => pure ()
  return idOf

/-- Parse a tag's signature: `(tag $id? (type N))` or inline
`(param …)*` forms (tags have no results). -/
private def parseTagSig (types : Array TypeEntry) (xs : List Sexpr)
    : Except Err Wasm.FuncType := do
  let xs := match xs with
    | .atom a :: r => if a.startsWith "$" then r else xs
    | _ => xs
  let xs := xs.dropWhile fun
    | .list (.atom "export" :: _) => true
    | _ => false
  match xs with
  | .list [.atom "type", .atom ref] :: _ =>
    let (ps, _) ← resolveTypeRef types ref
    .ok { params := ps }
  | _ =>
    let mut ps : List Wasm.ValueType := []
    for x in xs do
      match x with
      | .list (.atom "param" :: tail) =>
        for t in tail do
          match t with
          | .atom a =>
            if a.startsWith "$" then pure ()
            else ps := ps ++ [(atomToValueType? a).getD .i32]
          | .list l => ps := ps ++ [listToValueType l]
      | _ => pure ()
    .ok { params := ps }

/-- Parse the type body of an imported global (`(global $id? <gt>)`) into
a zero-initialised `GlobalDecl`. -/
private def parseImportedGlobal (xs : List Sexpr) : Wasm.GlobalDecl :=
  let xs := match xs with
    | .atom a :: r => if a.startsWith "$" then r else xs
    | _ => xs
  let vt : Wasm.ValueType := match xs with
    | .list (.atom "mut" :: .atom t :: _) :: _ => (atomToValueType? t).getD .i32
    | .list (.atom "mut" :: .list l :: _) :: _ => listToValueType l
    | .atom t :: _ => (atomToValueType? t).getD .i32
    | .list l :: _ => listToValueType l
    | _ => .i32
  { init := vt.zero }

/-- Collect imported non-function entities, in import order: zero-content
decl slots for the low indices of each index space, plus the
(module, name) pairs the harness uses to substitute real values. -/
private def collectEntityImports (funcIds : Std.HashMap String Nat)
    (fields : List Sexpr)
    : Except Err (List ((String × String) × Wasm.GlobalDecl)
                × List ((String × String) × Wasm.TableDecl)
                × List ((String × String) × Wasm.MemDecl)) := do
  let mut globs : List ((String × String) × Wasm.GlobalDecl) := []
  let mut tbls  : List ((String × String) × Wasm.TableDecl) := []
  let mut mems  : List ((String × String) × Wasm.MemDecl) := []
  for f in fields do
    match f with
    | .list [.atom "import", .atom modName, .atom impName, .list (.atom kind :: body)] =>
      let key := (decodeWatString modName, decodeWatString impName)
      match kind with
      | "global" => globs := globs ++ [(key, parseImportedGlobal body)]
      | "table"  =>
        let (td, _) ← parseTableDecl funcIds 0 body
        tbls := tbls ++ [(key, td)]
      | "memory" => mems := mems ++ [(key, ← parseMemDecl body)]
      | _ => pure ()
    | _ => pure ()
  return (globs, tbls, mems)

/-- Walk the module's fields collecting `(import "mod" "name" (func …))`
forms. Each function import gets a positional unified-index `0 … N-1`
and is recorded in `idOf` if it carries a `$name`. Imports of memory,
global, and table are silently dropped (unsupported). -/
private def collectImports (types : Array TypeEntry) (fields : List Sexpr)
    : Except Err (List Wasm.ImportDecl × Std.HashMap String Nat) := do
  let mut imports : List Wasm.ImportDecl := []
  let mut idOf : Std.HashMap String Nat := {}
  let mut i := 0
  for f in fields do
    match f with
    | .list (.atom "import" :: tail) =>
      match tail with
      | [.atom modName, .atom importName, .list (.atom "func" :: funcBody)] =>
        let modName' := decodeWatString modName
        let importName' := decodeWatString importName
        let funcBodyAfterId : List Sexpr :=
          match funcBody with
          | .atom a :: rest => if a.startsWith "$" then rest else funcBody
          | _ => funcBody
        match funcBody with
        | .atom a :: _ =>
          if a.startsWith "$" then
            idOf := idOf.insert (a.drop 1).toString i
        | _ => pure ()
        let (params, results) ← parseImportSig types funcBodyAfterId
        imports := imports ++ [{ «module» := modName',
                                  name := importName',
                                  params, results }]
        i := i + 1
      | _ => pure ()  -- (import … (memory|global|table …)) — drop silently
    | _ => pure ()
  return (imports, idOf)

/-- Walk a `(module ...)` form. `(type …)`, `(func …)`, `(export …)`,
`(global …)`, `(table …)`, `(memory …)`, `(elem …)`, `(data …)`,
`(tag …)`, `(start …)`, and `(import "mod" "name" (…))` — for func and
non-func imports alike — all contribute to the resulting `Wasm.Module`.
Function imports occupy the low end of the unified function index space
(indices `0 … N-1`); in-module function indices are shifted up by
`imports.length`. Non-func imports (`(import … (memory|global|table …))`)
are collected by `collectEntityImports` into placeholder decls at the low
end of the global/table/memory index spaces and recorded in
`importedGlobals`/`importedTables`/`importedMemories`. -/
def parseModule (xs : List Sexpr) : Except Err Wasm.Module := do
  let mut rest := xs
  match rest with
  | .atom a :: r =>
    if a.startsWith "$" then rest := r
  | _ => pure ()
  -- Collect `(type ...)` declarations first so import-signature
  -- resolution (`(type N)` form) can look them up. The type table is
  -- module-level and visible to every other field.
  let mut types : Array TypeEntry := #[]
  for f in rest do
    match f with
    | .list (.atom "type" :: body) =>
      types := types.push (parseTypeField body)
    -- Recursive type groups (`(rec (type …) …)`, GC proposal): the inner
    -- types occupy consecutive indices, flattened into the table here.
    -- Multi-member groups are tagged with a shared recursion-group marker
    -- (the first member's index) so iso-recursive type equivalence can
    -- compare whole groups; singleton groups stay untagged.
    | .list (.atom "rec" :: inner) =>
      let groupStart := types.size
      let groupSize := inner.countP fun
        | .list (.atom "type" :: _) => true
        | _ => false
      let marker := if groupSize > 1 then some groupStart else none
      for t in inner do
        match t with
        | .list (.atom "type" :: body) =>
          types := types.push { parseTypeField body with recGroup := marker }
        | _ => pure ()
    | _ => pure ()
  let (imports, importFuncIds) ← collectImports types rest
  let (globImps, tblImps, memImps) ← collectEntityImports importFuncIds rest
  let inModuleFuncIds ← collectFuncNames rest
  -- Unified function index space: imports occupy `0 … imports.length - 1`,
  -- in-module functions are shifted up by `imports.length`.
  let mut funcIds : Std.HashMap String Nat := importFuncIds
  for (name, idx) in inModuleFuncIds.toList do
    funcIds := funcIds.insert name (idx + imports.length)
  let globalIds ← collectGlobalNames rest
  let tableNames := collectTableNames rest
  let elemNames := collectElemNames rest
  let memNames := collectMemNames rest
  let tagNames := collectTagNames rest
  -- Tag index space: imported tags first, then declarations.
  let mut tags : Array Wasm.FuncType := #[]
  for f in rest do
    match f with
    | .list [.atom "import", .atom _, .atom _, .list (.atom "tag" :: body)] =>
      tags := tags.push (← parseTagSig types body)
    | _ => pure ()
  for f in rest do
    match f with
    | .list (.atom "tag" :: body) =>
      tags := tags.push (← parseTagSig types body)
    | _ => pure ()
  let inlineExportsOf : List Sexpr → List String := fun body =>
    (body.filterMap fun
      | .list [.atom "export", .atom n] => some (decodeWatString n)
      | _ => none)
  let mut decls : Array FuncDecl := #[]
  let mut topExports : Array (String × String) := #[]
  let mut globalExports : Array (String × Nat) := #[]
  let mut tableExports  : Array (String × Nat) := #[]
  let mut memoryExports : Array (String × Nat) := #[]
  let mut globalDecls : Array Wasm.GlobalDecl := #[]
  let mut memDecl : Option Wasm.MemDecl := none
  let mut extraMemDecls : Array Wasm.MemDecl := #[]
  let mut dataSegs : Array Wasm.DataSegment := #[]
  let mut tableDecls : Array Wasm.TableDecl := #[]
  let mut elemSegs   : Array Wasm.ElementSegment := #[]
  let mut startFunc : Option Nat := none
  for f in rest do
    match f with
    | .list (.atom "func" :: body) =>
      decls := decls.push
        (← parseFunc funcIds globalIds tableNames elemNames memNames tagNames types body)
    | .list (.atom "export" :: tail) =>
      match tail with
      | [.atom name, .list [.atom "func", .atom ref]] =>
        topExports := topExports.push (decodeWatString name, ref)
      | [.atom _, .list (.atom "func" :: _)] =>
        throw "malformed top-level (export … (func …))"
      | [.atom name, .list [.atom "global", .atom ref]] =>
        globalExports := globalExports.push
          (decodeWatString name, ← resolveNamed globalIds "global" ref)
      | [.atom name, .list [.atom "table", .atom ref]] =>
        tableExports := tableExports.push
          (decodeWatString name, ← resolveNamed tableNames "table" ref)
      | [.atom name, .list [.atom "memory", .atom ref]] =>
        memoryExports := memoryExports.push
          (decodeWatString name, ← resolveNamed memNames "memory" ref)
      | _ =>
        continue
    | .list (.atom "global" :: body) =>
      for n in inlineExportsOf body do
        globalExports := globalExports.push (n, globImps.length + globalDecls.size)
      let gResolveBlockType : BlockTypeResolver := fun ref =>
        (match resolveTypeRef types ref with | .ok sig => some sig | .error _ => none)
      let gctx : Ctx := { Ctx.empty with funcIds := funcIds, globalIds := globalIds, types := types, tableNames := tableNames, elemNames := elemNames, memNames := memNames, tagNames := tagNames, resolveBlockType := gResolveBlockType }
      globalDecls := globalDecls.push (← parseGlobalDecl gctx body)
    | .list (.atom "memory" :: body) =>
      -- Multi-memory: declared memories follow the imported ones in the
      -- index space; the combined list is split into the default memory
      -- and `extraMemories` below.
      let declared := (if memDecl.isSome then 1 else 0) + extraMemDecls.size
      for n in inlineExportsOf body do
        memoryExports := memoryExports.push (n, memImps.length + declared)
      match memDecl with
      | none   => memDecl := some (← parseMemDecl body)
      | some _ => extraMemDecls := extraMemDecls.push (← parseMemDecl body)
    | .list (.atom "data" :: body) =>
      let dctx : Ctx := { Ctx.empty with funcIds := funcIds, globalIds := globalIds, types := types, tableNames := tableNames, elemNames := elemNames, memNames := memNames, tagNames := tagNames }
      dataSegs := dataSegs.push (← parseDataSegment dctx body)
    | .list (.atom "table" :: body) =>
      for n in inlineExportsOf body do
        tableExports := tableExports.push (n, tblImps.length + tableDecls.size)
      let (td, inlineSeg?) ← parseTableDecl funcIds (tblImps.length + tableDecls.size) body
      tableDecls := tableDecls.push td
      match inlineSeg? with
      | some seg => elemSegs := elemSegs.push seg
      | none     => pure ()
    | .list (.atom "elem" :: body) =>
      let eResolveBlockType : BlockTypeResolver := fun ref =>
        (match resolveTypeRef types ref with | .ok sig => some sig | .error _ => none)
      let ectx : Ctx := { Ctx.empty with funcIds := funcIds, globalIds := globalIds, types := types, tableNames := tableNames, elemNames := elemNames, memNames := memNames, tagNames := tagNames, resolveBlockType := eResolveBlockType }
      elemSegs := elemSegs.push (← parseElemSegment ectx body)
    | .list [.atom "start", .atom ref] =>
      if startFunc.isSome then throw "duplicate (start ...) declaration"
      startFunc := some (← resolveFuncRef funcIds ref)
    | .list (.atom "import" :: _) =>
      -- Already collected by `collectImports` above; function imports get
      -- recorded in `imports` and contribute their low-end function
      -- indices, non-func imports (memory, global, table) are dropped.
      pure ()
    | _ =>
      -- type / table / elem / stray atoms: skipped at module level.
      continue
  let mut exports : Array Wasm.Export := #[]
  -- Inline exports' `funcIdx` is in the unified index space: imports
  -- occupy `0 … imports.length - 1`, so in-module function `k` is at
  -- unified index `imports.length + k`.
  let mut i := imports.length
  for d in decls do
    for n in d.inlineExports do
      exports := exports.push { name := n, funcIdx := i }
    i := i + 1
  for (name, ref) in topExports do
    let idx ← resolveFuncRef funcIds ref
    exports := exports.push { name, funcIdx := idx }
  -- Memory index space: imported memories first, then declarations. The
  -- combined head is the default memory and carries the (global,
  -- source-ordered) data segment list.
  let allMemDecls : List Wasm.MemDecl :=
    memImps.map (·.2)
      ++ (match memDecl with | some d => [d] | none => [])
      ++ extraMemDecls.toList
  let (finalMem, finalExtraMems) : Option Wasm.MemDecl × List Wasm.MemDecl :=
    match allMemDecls with
    | [] =>
      (if dataSegs.isEmpty then none
       else some { pagesMin := 0, data := dataSegs.toList }, [])
    | d0 :: rest' => (some { d0 with data := d0.data ++ dataSegs.toList }, rest')
  -- Project the parsed `TypeEntry` array down to `Wasm.FuncType`. Entries
  -- whose signature we couldn't model (e.g. SIMD/reference proposals) get
  -- a placeholder empty signature so type-index positions stay aligned;
  -- `call_indirect (type N)` against those would never succeed type-check
  -- but the test runner wraps them in cascade failures anyway.
  let moduleTypes : List Wasm.FuncType := types.toList.map fun te =>
    match te.sig with
    | some (ps, rs) => { params := ps, results := rs }
    | none          => {}
  -- GC type table (GC proposal), parallel-indexed to `moduleTypes`. Each
  -- entry carries its composite type (struct/array, or the func signature)
  -- and resolved `sub` supertype index.
  let resolveSuper : String → Option Nat := fun s =>
    let name := if s.startsWith "$" then (s.drop 1).toString else s
    match types.findIdx? (fun t => t.symId = some name) with
    | some i => some i
    | none   => s.toNat?
  let gcTypes : List Wasm.GcTypeDef := types.toList.map fun te =>
    let comp : Wasm.CompositeType := match te.comp with
      | some c => c
      | none   => match te.sig with
        | some (ps, rs) => .func { params := ps, results := rs }
        | none          => .func {}
    { comp, super := te.superRef.bind resolveSuper, «final» := te.isFinal,
      recGroup := te.recGroup }
  return { funcs    := decls.toList.map (·.func)
           exports  := exports.toList
           globals  := globImps.map (·.2) ++ globalDecls.toList
           memory   := finalMem
           extraMemories := finalExtraMems
           imports
           startFunc
           types    := moduleTypes
           gcTypes
           tables   := tblImps.map (·.2) ++ tableDecls.toList
           elements := elemSegs.toList
           importedGlobals  := globImps.map (·.1)
           importedTables   := tblImps.map (·.1)
           importedMemories := memImps.map (·.1)
           globalExports := globalExports.toList
           tableExports  := tableExports.toList
           memoryExports := memoryExports.toList
           tags := tags.toList }

/-- Public entry point. Parses one top-level `(module …)` form. -/
def decode (s : String) : Except Err Wasm.Module := do
  let xs ← parseAll s
  match xs with
  | [.list (.atom "module" :: body)] => parseModule body
  | [_] => .error "top-level form is not (module ...)"
  | [] => .error "empty input"
  | _ => .error "expected exactly one top-level (module ...) form"

end Wasm.Decoder.Wat
