import Interpreter.Wasm.Syntax
import Std.Data.HashMap

/-!
# WAT decoder

A small parser for the WebAssembly text format, targeting Wasm's AST.

Supported:
* `(module ...)` with any number of `(func ...)` definitions.
* `(type ...)`, `(export ...)`, `(import ...)`, `(table ...)`, `(memory ...)`,
  `(global ...)`, `(elem ...)`, `(data ...)`, `(start ...)` — recognized at the
  module level. Only `func` and `export` contribute to the resulting
  `Wasm.Module`; the rest are accepted to allow round-tripping the spec
  testsuite, but their content is discarded.
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

Features Wasm does not model (memory loads/stores, `memory.*`, globals,
`call_indirect`, tables) are accepted lexically but lowered to
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

/-- Decode a value-type atom. The interpreter only models i32/i64; types
from other proposals (floats, SIMD, reference types) are accepted at
the decoder level — silently normalised to `i32` — so that modules
which include such types in *signatures* still decode. Functions whose
bodies actually touch those types will hit `unreachable` (because the
corresponding instructions are also lowered to `unreachable`), giving
the testsuite runner a chance to run any i32-only exports declared in
the same module. -/
private def atomToValueType? : String → Option Wasm.ValueType
  | "i32"       => some .i32
  | "i64"       => some .i64
  | "f32"       => some .i32  -- placeholder, see comment
  | "f64"       => some .i32  -- placeholder
  | "v128"      => some .i32  -- placeholder
  | "funcref"   => some .i32  -- placeholder
  | "externref" => some .i32  -- placeholder
  | "anyref"    => some .i32  -- placeholder
  | "eqref"     => some .i32  -- placeholder
  | "i31ref"    => some .i32  -- placeholder
  | "structref" => some .i32  -- placeholder
  | "arrayref"  => some .i32  -- placeholder
  | "nullref"   => some .i32  -- placeholder
  | "nullfuncref"   => some .i32
  | "nullexternref" => some .i32
  | _     => none

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
      | _       => none
    skipBlockType resolveType ps (rs ++ extra) r
  | ps, rs, .list (.atom "param" :: ts) :: r =>
    let extra := ts.filterMap fun
      | .atom a => atomToValueType? a
      | _       => none
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
  | "memory.size"  => .ok .memorySize
  | "memory.grow"  => .ok .memoryGrow
  | "memory.fill"  => .ok .memoryFill
  | "memory.copy"  => .ok .memoryCopy
  | op          =>
    -- Accept instructions from proposals the interpreter doesn't model
    -- (floats, SIMD, reference types, tables, GC, exceptions, tail calls)
    -- by lowering them to `unreachable`. This lets modules whose
    -- *signatures* or unrelated functions touch these features still
    -- decode; any function that actually executes such an instruction
    -- traps with "unreachable" instead of failing to decode at all,
    -- which would cascade to every assert in the file.
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
       || op.startsWith "atomic."
       -- int-from-float conversions: the operand is a float we don't
       -- model, so we can't produce a real result; lower to unreachable
       -- alongside the float-producing ops so mixed-signature modules
       -- still decode.
       || op == "i32.trunc_f32_s" || op == "i32.trunc_f32_u"
       || op == "i32.trunc_f64_s" || op == "i32.trunc_f64_u"
       || op == "i64.trunc_f32_s" || op == "i64.trunc_f32_u"
       || op == "i64.trunc_f64_s" || op == "i64.trunc_f64_u"
       || op == "i32.trunc_sat_f32_s" || op == "i32.trunc_sat_f32_u"
       || op == "i32.trunc_sat_f64_s" || op == "i32.trunc_sat_f64_u"
       || op == "i64.trunc_sat_f32_s" || op == "i64.trunc_sat_f32_u"
       || op == "i64.trunc_sat_f64_s" || op == "i64.trunc_sat_f64_u"
       || op == "i32.reinterpret_f32" || op == "i64.reinterpret_f64" then
      .ok .unreachable
    else
      .error s!"unsupported instruction: {op}"

/-- Memory ops that take an offset immediate. We accept them lexically
(`offset=`/`align=` attributes parsed and discarded) but emit
`unreachable` for the instruction itself. -/
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
  -- Float and SIMD memory ops are lexically accepted (their offset=/
  -- align= attributes parsed and discarded), but `memOpToInstruction`
  -- lowers them to `unreachable` since the interpreter doesn't model
  -- those value types.
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

/-- Number of atom immediates a *lowered* (treated-as-`unreachable`) op
consumes. Used to keep the linear/folded parsers in sync with the token
stream when we accept-and-stub instructions from proposals the
interpreter doesn't model. Returns `none` for ops we don't pretend to
support. -/
private def stubImmediateCount (op : String) : Option Nat :=
  if op == "f32.const" || op == "f64.const"
     || op == "ref.null" || op == "ref.func"
     || op == "ref.test" || op == "ref.cast"
     || op == "br_on_null" || op == "br_on_non_null"
     || op == "return_call" || op == "return_call_ref" || op == "call_ref"
     || op == "elem.drop" || op == "throw" || op == "tag"
     || op == "table.get" || op == "table.set" || op == "table.size"
     || op == "table.grow" || op == "table.fill"
     || op == "struct.new" || op == "struct.new_default"
     || op == "array.new" || op == "array.new_default" || op == "array.new_fixed"
     -- array element accessors take 1 atom (the array type ref) only;
     -- struct accessors take 2 (type + field), see below.
     || op == "array.get" || op == "array.get_u" || op == "array.get_s"
     || op == "array.set" || op == "array.fill"
     -- SIMD lane-index ops: one lane-index atom.
     || op.endsWith ".extract_lane" || op.endsWith ".extract_lane_s"
     || op.endsWith ".extract_lane_u" || op.endsWith ".replace_lane"
  then some 1
  -- `i8x16.shuffle` has 16 lane-index immediates.
  else if op == "i8x16.shuffle" then some 16
  -- `br_on_cast`/`br_on_cast_fail` take label + from_type + to_type,
  -- where the type immediates can be atoms (`anyref`) or lists
  -- (`(ref $t)`); they are handled separately by
  -- `consumeBrOnCastImmediates`.
  else if op == "br_on_cast" || op == "br_on_cast_fail" then none
  else if op == "struct.get" || op == "struct.get_u" || op == "struct.get_s"
     || op == "struct.set"
     || op == "array.new_elem" || op == "array.new_data"
     || op == "array.copy"
     || op == "array.init_data" || op == "array.init_elem"
  then some 2
  -- `table.init` and `table.copy` are handled separately by
  -- `consumeTableBulkAtoms` (0..2 label-looking atoms — wasm-tools'
  -- canonical print emits 0/1 when default tables are used and 2
  -- when both tables are named).
  else none

/-- Drop the first `n` atom tokens from `toks`. Errors if a non-atom is
encountered or the stream is too short. -/
private partial def consumeStubAtoms (op : String) : Nat → List Sexpr → Except Err (List Sexpr)
  | 0, ts => .ok ts
  | k+1, .atom _ :: ts => consumeStubAtoms op k ts
  | _+1, _ => .error s!"{op}: expected immediate atom"

/-- v128.const has a shape-dependent number of immediates. -/
private def consumeV128ConstImmediates (rest : List Sexpr) : Except Err (List Sexpr) :=
  match rest with
  | .atom shape :: r =>
    let count : Nat := match shape with
      | "i8x16" => 16
      | "i16x8" => 8
      | "i32x4" => 4
      | "i64x2" => 2
      | "f32x4" => 4
      | "f64x2" => 2
      | _      => 0
    consumeStubAtoms "v128.const" count r
  | _ => .ok rest

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
  | _              => .unreachable

private def looksLikeLabel (s : String) : Bool :=
  if s.startsWith "$" then true
  else if s.isEmpty then false
  else if s.startsWith "0x" || s.startsWith "0X" then
    (s.drop 2).toString.toList.all fun c =>
      c.isDigit || ('a' ≤ c ∧ c ≤ 'f') || ('A' ≤ c ∧ c ≤ 'F') || c = '_'
  else
    s.toList.all (fun c => c.isDigit || c = '_')

/-- Consume up to `k` label-looking atoms immediately following
`table.copy` / `table.init`. wasm-tools' canonical print emits 0 or 2
atoms for `table.copy` (depending on whether named tables are involved)
and 1 or 2 atoms for `table.init` (the element segment index is always
emitted, the destination table index only when non-default), so we stop
once we've consumed `k` atoms or hit a non-label token. -/
private partial def consumeTableBulkAtoms : Nat → List Sexpr → List Sexpr
  | 0, ts => ts
  | k+1, .atom a :: ts =>
    if looksLikeLabel a then consumeTableBulkAtoms k ts
    else .atom a :: ts
  | _+1, ts => ts

/-- Consume the label immediate and the two type-immediates of a
`br_on_cast` / `br_on_cast_fail`. The label is a single atom; each type
is either an atom (e.g. `anyref`) or a `(ref …)` list. -/
private def consumeBrOnCastImmediates (op : String)
    : List Sexpr → Except Err (List Sexpr)
  | .atom _ :: t1 :: t2 :: rest =>
    match t1, t2 with
    | .atom _, .atom _ | .atom _, .list _
    | .list _, .atom _ | .list _, .list _ => .ok rest
  | _ => .error s!"{op}: expected label + 2 type immediates"

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
    | "local.get" => parseImmediateNat (resolveNamed ctx.localIds "local") .localGet op rest
    | "local.set" => parseImmediateNat (resolveNamed ctx.localIds "local") .localSet op rest
    | "local.tee" => parseLocalTee ctx rest
    | "global.get" => parseImmediateNat (resolveNamed ctx.globalIds "global") .globalGet op rest
    | "global.set" => parseImmediateNat (resolveNamed ctx.globalIds "global") .globalSet op rest
    | "br"        => parseImmediateNat (resolveLabel ctx) .br op rest
    | "br_if"     => parseImmediateNat (resolveLabel ctx) .br_if op rest
    | "br_table"  => parseBrTable ctx rest
    | "call"      => parseImmediateNat (resolveNamed ctx.funcIds "function") .call op rest
    | "call_indirect" | "return_call_indirect" => parseCallIndirect ctx rest
    | "memory.init" => parseImmediateNat parseNat .memoryInit op rest
    | "data.drop"   => parseImmediateNat parseNat .dataDrop   op rest
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
    | _ =>
      match isMemOp op with
      | some na => do
        let (offset, rest') ← consumeMemAttrs na rest
        -- v128 lane-load/store ops carry an additional lane-index atom
        -- after the offset/align attrs. We discard it since the
        -- instruction is lowered to `unreachable` anyway.
        let rest'' ← if op.endsWith "_lane" && op.startsWith "v128." then
          consumeStubAtoms op 1 rest'
        else .ok rest'
        .ok ([memOpToInstruction op offset], rest'')
      | none =>
        match parsePlainOp op with
        | .error e => .error e
        | .ok i => do
          -- For ops we lowered to `unreachable`, consume any textual
          -- immediates so the token stream stays aligned.
          let rest' ← if op == "v128.const" then
            consumeV128ConstImmediates rest
          else if op == "table.copy" || op == "table.init" then
            .ok (consumeTableBulkAtoms 2 rest)
          else if op == "br_on_cast" || op == "br_on_cast_fail" then
            consumeBrOnCastImmediates op rest
          else match stubImmediateCount op with
            | some n => consumeStubAtoms op n rest
            | none   => .ok rest
          .ok ([i], rest')

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
    | "memory.init" => foldedWithImmediate ctx parseNat (fun i => [.memoryInit i]) rest
    | "data.drop"   => foldedWithImmediate ctx parseNat (fun i => [.dataDrop i])   rest
    | "call_indirect" | "return_call_indirect" => do
      let (instr, leftover) ← parseCallIndirect ctx rest
      unless leftover.isEmpty do
        .error "folded call_indirect: trailing tokens"
      .ok instr
    | "block" => foldedStructured ctx .block rest
    | "loop"  => foldedStructured ctx .loop  rest
    | "if"    => foldedIf ctx rest
    | _ => do
      -- Plain op or memory op with optional `offset=`/`align=` attrs.
      let (head, rest') ← match isMemOp op with
        | some na => do
          let (offset, rest'') ← consumeMemAttrs na rest
          let rest''' ← if op.endsWith "_lane" && op.startsWith "v128." then
            consumeStubAtoms op 1 rest''
          else .ok rest''
          .ok (memOpToInstruction op offset, rest''')
        | none => do
          let head ← parsePlainOp op
          -- For ops we lowered to `unreachable`, consume any textual
          -- immediates so the remaining tokens are valid operand
          -- expressions (`(...)` forms).
          let rest' ← if op == "v128.const" then
            consumeV128ConstImmediates rest
          else match stubImmediateCount op with
            | some n => consumeStubAtoms op n rest
            | none   => .ok rest
          .ok (head, rest')
      let mut acc : List Wasm.Instruction := []
      for s in rest' do
        match s with
        | .list ys =>
          let sub ← parseFolded ctx ys
          acc := acc ++ sub
        | .atom a => .error s!"folded {op}: unexpected atom operand '{a}'"
      .ok (acc ++ [head])
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

/-- Parse a `call_indirect` instruction. The wasm-tools-canonical form is
`call_indirect [(table T)] (type N)`. We resolve both into numeric
indices using the surrounding `ctx`. The `(param …)/(result …)` inline-
signature form (legal in raw `.wast`) does not appear in our input after
`wasm-tools print`, so we don't try to handle it. -/
private partial def parseCallIndirect (ctx : Ctx) (toks : List Sexpr)
    : Except Err (List Wasm.Instruction × List Sexpr) := do
  let mut rest := toks
  let mut tableIdx : Nat := 0
  match rest with
  | .list [.atom "table", .atom t] :: r =>
    let idx ←
      if t.startsWith "$" then
        match ctx.tableNames[(t.drop 1).toString]? with
        | some i => .ok i
        | none   => .error s!"unknown table id: {t}"
      else parseNat t
    tableIdx := idx
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
    .ok ([.callIndirect typeIdx tableIdx], r)
  | _ => .error "call_indirect expects a (type N) annotation"

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

private def resolveTypeRef (types : Array TypeEntry) (s : String)
    : Except Err (List Wasm.ValueType × List Wasm.ValueType) := do
  let idx ← if s.startsWith "$" then
    let name := (s.drop 1).toString
    match types.findIdx? (fun t => t.symId = some name) with
    | some i => .ok i
    | none => .error s!"unknown type id: {s}"
  else
    parseNat s
  match types[idx]? with
  | some { sig := some sig, .. } => .ok sig
  | some { sig := none, .. } =>
    .error s!"(type {s}) is not a supported (func ...) signature"
  | none => .error s!"type index out of range: {idx}"

private def parseTypeField (xs : List Sexpr) : TypeEntry := Id.run do
  let mut symId : Option String := none
  let mut rest := xs
  match rest with
  | .atom a :: r =>
    if a.startsWith "$" then
      symId := some (a.drop 1).toString
      rest := r
  | _ => pure ()
  let sig : Option (List Wasm.ValueType × List Wasm.ValueType) :=
    match rest with
    | [.list (.atom "func" :: sigForms)] => Id.run do
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
            | .list _ => paramTypes := paramTypes ++ [.i32]
        | .list (.atom "result" :: tail) =>
          for t in tail do
            match t with
            | .atom a =>
              match atomToValueType? a with
              | some vt => resultTypes := resultTypes ++ [vt]
              | none    => ok := false
            | .list _ => resultTypes := resultTypes ++ [.i32]
        | _ => ok := false
      if ok then return some (paramTypes, resultTypes) else return none
    | _ => none
  return { symId, sig }

private def stripQuotes (s : String) : String :=
  if s.length ≥ 2 && s.startsWith "\"" && s.endsWith "\"" then
    ((s.drop 1).dropEnd 1).toString
  else s

private def parseFunc (funcIds : Std.HashMap String Nat)
    (globalIds : Std.HashMap String Nat)
    (tableNames : Std.HashMap String Nat)
    (types : Array TypeEntry) (xs : List Sexpr)
    : Except Err FuncDecl := do
  let mut paramTypes : List Wasm.ValueType := []
  let mut resultTypes : List Wasm.ValueType := []
  let mut localTypes : List Wasm.ValueType := []
  let mut symId : Option String := none
  let mut inlineExports : List String := []
  let mut localIds : Std.HashMap String Nat := {}
  let mut typeApplied : Bool := false
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
              | .list _ => paramTypes := paramTypes ++ [.i32]
          else
            for t in tail do
              match t with
              | .atom a =>
                match atomToValueType? a with
                | some vt => paramTypes := paramTypes ++ [vt]
                | none    => throw s!"unsupported param type: {a}"
              | .list _ => paramTypes := paramTypes ++ [.i32]
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
            | .list _ => localTypes := localTypes ++ [.i32]
        else
          for t in tail do
            match t with
            | .atom a =>
              match atomToValueType? a with
              | some vt => localTypes := localTypes ++ [vt]
              | none    => throw s!"unsupported local type: {a}"
            | .list _ => localTypes := localTypes ++ [.i32]
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
            | .list _ => resultTypes := resultTypes ++ [.i32]
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
        | _ => throw "malformed (type ...) reference"
        rest := r
      | "export" =>
        match tail with
        | [.atom s] =>
          inlineExports := inlineExports ++ [stripQuotes s]
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
  let ctx : Ctx := { funcIds, localIds, globalIds, types, tableNames, resolveBlockType }
  let instrs ← parseInstrSeq ctx rest
  return { symId, inlineExports,
           func := {
             params  := paramTypes
             locals  := localTypes
             body    := instrs
             results := resultTypes
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

-- TODO: imported globals are not counted here, so the index space is wrong
-- when imports are present. Wasm places imported globals first (indices
-- 0 … N-1) and declared globals after (indices N … N+M-1). This function
-- assigns 0 … M-1 to declared globals, so any `global.get`/`global.set`
-- that references a declared global will be off by N and will likely trap
-- at runtime. The fix is to count the `(import … (global …))` forms first
-- and start `i` at that offset. Rust's wasm32-unknown-unknown target never
-- imports globals, so the corpus is unaffected for now.
private def collectGlobalNames (fields : List Sexpr)
    : Except Err (Std.HashMap String Nat) := do
  let mut idOf : Std.HashMap String Nat := {}
  let mut i := 0
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

private def hexDigitVal (c : Char) : Option Nat :=
  if c.isDigit then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (10 + c.toNat - 'a'.toNat)
  else if 'A' ≤ c && c ≤ 'F' then some (10 + c.toNat - 'A'.toNat)
  else none

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

private def parseGlobalDecl (xs : List Sexpr) : Except Err Wasm.GlobalDecl := do
  let xs := match xs with
    | .atom a :: r => if a.startsWith "$" then r else xs
    | _ => xs
  let (vt, xs) ← match xs with
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
  -- The init expression is either wrapped in a `(...)` list or — in
  -- wasm-tools' canonical print — emitted as a bare sequence of atoms
  -- (for v128.const this is `v128.const <shape> <lanes...>`, six tokens).
  -- Normalise to "head op atom + tail" for the shape match below.
  let (head?, tail) : Option String × List Sexpr := match xs with
    | [.list (.atom h :: rest)] => (some h, rest)
    | .atom h :: rest           => (some h, rest)
    | _                         => (none, [])
  let init : Wasm.Value ← match head?, tail with
    | some "i32.const", .atom n :: _ => .ok (.i32 (← parseI32 n))
    | some "i64.const", .atom n :: _ => .ok (.i64 (← parseI64 n))
    -- Init expressions from proposals we don't model are accepted by
    -- the decoder; the *value* is replaced with a zero placeholder
    -- since none of them feed an `i32`/`i64` computation. Function
    -- bodies that would read the global hit `unreachable` anyway.
    | some "f32.const", _ | some "f64.const", _
    | some "v128.const", _
    | some "ref.null",  _ | some "ref.func",  _
    | some "global.get", _ => .ok (.i32 0)
    | _, _ => .error "global init expression must be i32.const or i64.const"
  .ok { type := vt, init }

private def parseMemDecl (xs : List Sexpr) : Except Err Wasm.MemDecl := do
  let xs := match xs with
    | .atom a :: r => if a.startsWith "$" then r else xs
    | _ => xs
  match xs with
  | [.atom min] =>
    .ok { pagesMin := ← parseU32 min }
  | [.atom min, .atom max] =>
    .ok { pagesMin := ← parseU32 min, pagesMax := some (← parseU32 max) }
  | _ => .error "malformed (memory ...): expected (memory min) or (memory min max)"

/-- Parse a `(data ...)` body. Active segments produce `offset := some n`;
passive segments (no offset expression) produce `offset := none`. -/
private def parseDataSegment (xs : List Sexpr) : Except Err Wasm.DataSegment := do
  -- Strip optional segment id ($name) or memory index (bare number).
  let xs := match xs with
    | .atom a :: r => if a.startsWith "$" || a.all Char.isDigit then r else xs
    | _ => xs
  -- Strip optional explicit `(memory N)` reference.
  let xs := match xs with
    | .list (.atom "memory" :: _) :: r => r
    | _ => xs
  -- Extract the offset constant; passive segments have no offset form.
  -- Non-`i32.const` offset expressions (e.g. `(global.get N)` pointing
  -- at an imported global) are accepted with a 0 placeholder so the
  -- module still decodes; tests that depend on the actual offset will
  -- fail at runtime rather than at decode time.
  let parsed ← match xs with
    | .list [.atom "offset", .list [.atom "i32.const", .atom n]] :: r =>
      do .ok ((some (← parseU32 n) : Option UInt32), r)
    | .list [.atom "i32.const", .atom n] :: r =>
      do .ok ((some (← parseU32 n) : Option UInt32), r)
    | .list [.atom "offset", .list (.atom "global.get" :: _)] :: r
    | .list (.atom "global.get" :: _) :: r =>
      .ok ((some (0 : UInt32) : Option UInt32), r)
    | _ => .ok ((none : Option UInt32), xs)
  let (offset, rest) := parsed
  let mut bytes : List UInt8 := []
  for tok in rest do
    match tok with
    | .atom s => bytes := bytes ++ (← parseWatString s)
    | _ => .error "data segment: expected string literal(s)"
  .ok { offset, bytes }

/-- Collect names declared by `(table $name ...)` forms in source order.
Same pattern as `collectFuncNames` / `collectGlobalNames`. -/
private def collectTableNames (fields : List Sexpr) : Std.HashMap String Nat := Id.run do
  let mut idOf : Std.HashMap String Nat := {}
  let mut i := 0
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
    .ok ({ min := n, max := some n, elemType := .funcref },
         some { tableIdx := some tableIdx, offset := some 0, funcs })
  | [.atom min, .atom "funcref"] =>
    let n ← parseNat min
    .ok ({ min := n, elemType := .funcref }, none)
  | [.atom min, .atom max, .atom "funcref"] =>
    let nMin ← parseNat min
    let nMax ← parseNat max
    .ok ({ min := nMin, max := some nMax, elemType := .funcref }, none)
  | [.atom min, .atom _other] =>
    -- Non-funcref single-bound: accept with the declared minimum so
    -- index space stays aligned; we never inspect its element type.
    let n ← parseNat min
    .ok ({ min := n, elemType := .funcref }, none)
  | [.atom min, .atom max, .atom _other] =>
    let nMin ← parseNat min
    let nMax ← parseNat max
    .ok ({ min := nMin, max := some nMax, elemType := .funcref }, none)
  | [.atom _other] => .ok ({ min := 0, elemType := .funcref }, none)
  | _ => .error "malformed (table ...) declaration"

/-- Parse one `(elem ...)` declaration. Handles every shape produced by
`wasm-tools print`: active w/ default or explicit table, passive with
the `func` or `funcref` keyword, and declarative (`elem declare`).
Inside the function-ref list each entry is one of:

* `$name` / `N` — bare function ref atom
* `(ref.func $name)` — explicit constant
* `(ref.null func)` — null entry
* `(item …)` — canonical wrapper; we look one level inside
-/
private def parseElemSegment
    (funcIds : Std.HashMap String Nat) (tableNames : Std.HashMap String Nat)
    (xs : List Sexpr) : Except Err Wasm.ElementSegment := do
  let mut rest := xs
  let mut isDeclarative := false
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
  match rest with
  | .list [.atom "offset", .list [.atom "i32.const", .atom n]] :: r =>
    let v ← parseNat n; offset := some v; rest := r
  | .list (.atom "offset" :: _) :: r =>
    -- Other offset expressions (constant globals etc.) — not modelled.
    offset := some 0; rest := r
  | .list [.atom "i32.const", .atom n] :: r =>
    let v ← parseNat n; offset := some v; rest := r
  | _ => pure ()
  match rest with
  | .atom "func"    :: r => rest := r
  | .atom "funcref" :: r => rest := r
  | _ => pure ()
  if isDeclarative then offset := none
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
  .ok { tableIdx, offset, funcs }

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
        let modName' := stripQuotes modName
        let importName' := stripQuotes importName
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

/-- Walk a `(module ...)` form. `(func …)`, `(export …)`, `(global …)`,
`(memory …)`, `(data …)`, `(start …)`, and `(import "mod" "name"
(func …))` all contribute to the resulting `Wasm.Module`. Function
imports occupy the low end of the unified function index space (indices
`0 … N-1`); in-module function indices are shifted up by
`imports.length`. Other recognised fields (`type`, `table`, `elem`, non-
func imports) are accepted lexically so the spec testsuite still loads,
but their content is discarded. -/
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
    | _ => pure ()
  let (imports, importFuncIds) ← collectImports types rest
  let inModuleFuncIds ← collectFuncNames rest
  -- Unified function index space: imports occupy `0 … imports.length - 1`,
  -- in-module functions are shifted up by `imports.length`.
  let mut funcIds : Std.HashMap String Nat := importFuncIds
  for (name, idx) in inModuleFuncIds.toList do
    funcIds := funcIds.insert name (idx + imports.length)
  let globalIds ← collectGlobalNames rest
  let tableNames := collectTableNames rest
  let mut decls : Array FuncDecl := #[]
  let mut topExports : Array (String × String) := #[]
  let mut globalDecls : Array Wasm.GlobalDecl := #[]
  let mut memDecl : Option Wasm.MemDecl := none
  let mut dataSegs : Array Wasm.DataSegment := #[]
  let mut tableDecls : Array Wasm.TableDecl := #[]
  let mut elemSegs   : Array Wasm.ElementSegment := #[]
  let mut startFunc : Option Nat := none
  for f in rest do
    match f with
    | .list (.atom "func" :: body) =>
      decls := decls.push (← parseFunc funcIds globalIds tableNames types body)
    | .list (.atom "export" :: tail) =>
      match tail with
      | [.atom name, .list [.atom "func", .atom ref]] =>
        topExports := topExports.push (stripQuotes name, ref)
      | [.atom _, .list (.atom "func" :: _)] =>
        throw "malformed top-level (export … (func …))"
      | _ =>
        -- Export of a non-func item (memory, global, table) — drop silently.
        continue
    | .list (.atom "global" :: body) =>
      globalDecls := globalDecls.push (← parseGlobalDecl body)
    | .list (.atom "memory" :: body) =>
      if memDecl.isSome then throw "duplicate (memory ...) declaration"
      memDecl := some (← parseMemDecl body)
    | .list (.atom "data" :: body) =>
      dataSegs := dataSegs.push (← parseDataSegment body)
    | .list (.atom "table" :: body) =>
      let (td, inlineSeg?) ← parseTableDecl funcIds tableDecls.size body
      tableDecls := tableDecls.push td
      match inlineSeg? with
      | some seg => elemSegs := elemSegs.push seg
      | none     => pure ()
    | .list (.atom "elem" :: body) =>
      elemSegs := elemSegs.push (← parseElemSegment funcIds tableNames body)
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
  let finalMem : Option Wasm.MemDecl := match memDecl with
    | some decl => some { decl with data := decl.data ++ dataSegs.toList }
    | none      =>
      if dataSegs.isEmpty then none
      else some { pagesMin := 0, data := dataSegs.toList }
  -- Project the parsed `TypeEntry` array down to `Wasm.FuncType`. Entries
  -- whose signature we couldn't model (e.g. SIMD/reference proposals) get
  -- a placeholder empty signature so type-index positions stay aligned;
  -- `call_indirect (type N)` against those would never succeed type-check
  -- but the test runner wraps them in cascade failures anyway.
  let moduleTypes : List Wasm.FuncType := types.toList.map fun te =>
    match te.sig with
    | some (ps, rs) => { params := ps, results := rs }
    | none          => {}
  return { funcs    := decls.toList.map (·.func)
           exports  := exports.toList
           globals  := globalDecls.toList
           memory   := finalMem
           imports
           startFunc
           types    := moduleTypes
           tables   := tableDecls.toList
           elements := elemSegs.toList }

/-- Public entry point. Parses one top-level `(module …)` form. -/
def decode (s : String) : Except Err Wasm.Module := do
  let xs ← parseAll s
  match xs with
  | [.list (.atom "module" :: body)] => parseModule body
  | [_] => .error "top-level form is not (module ...)"
  | [] => .error "empty input"
  | _ => .error "expected exactly one top-level (module ...) form"

end Wasm.Decoder.Wat
