import Interpreter.Wasm.LeanSyntax

/-!
# Emit Wasm AST as literal Lean source

Serialises a `Wasm.Module` to a Lean source expression that re-elaborates
to the same value. Per-function bodies are extracted as standalone `def`s
(`func0`, `func1`, …) so the emitted `module` record stays small.

Output uses anonymous-constructor dot notation (`.localGet 0`, `.i32`, …)
since the surrounding type ascriptions (`Wasm.Program`, `List Wasm.ValueType`,
record field types) make the namespace unambiguous. Programs are pretty-
printed across multiple lines with two-space indentation for nested
structured-control bodies.
-/

namespace Verifier.Emit

open Wasm

/- Keep the top-level list contents at two spaces, then add only one space per
nesting level. Bracketed Lean syntax does not need two-space indentation, and
large compiler-generated functions otherwise spend a surprising amount of
their source size on whitespace alone. -/
private def indent (n : Nat) : String := "".pushn ' ' (n + 1)

private def list (xs : List String) : String :=
  "[" ++ String.intercalate ", " xs ++ "]"

private def field (name value : String) : String := s!"{name} := {value}"

private def fieldIf (keep : Bool) (name value : String) : List String :=
  if keep then [field name value] else []

private def record (fields : List String) : String :=
  match fields with
  | [] => "{}"
  | _ => "{ " ++ String.intercalate ", " fields ++ " }"

/-- Pretty-print pre-rendered records as a multi-line list at depth `ind`. -/
private def recordListAt (ind : Nat) (items : List String) : String :=
  match items with
  | [] => "[]"
  | _  => "[\n" ++ indent (ind + 1) ++
      String.intercalate (",\n" ++ indent (ind + 1)) items ++
      "\n" ++ indent ind ++ "]"

private def recordList (items : List String) : String := recordListAt 1 items

private def emitNat (n : Nat) : String := toString n

private def emitNatList (ns : List Nat) : String :=
  list (ns.map emitNat)

private def emitOptionNat : Option Nat → String
  | none   => "none"
  | some n => s!"some {emitNat n}"

private def emitUnsignedShortest (n modulus : Nat) : String :=
  let unsigned := toString n
  let signed := if modulus / 2 ≤ n then s!"(-{modulus - n})" else unsigned
  if signed.length < unsigned.length then signed else unsigned

/- Constructor and record-field types determine the numeral type, so explicit
`UInt32`/`UInt64` ascriptions are redundant. For high bit-patterns, use the
shorter signed spelling when it saves bytes (`4294967295` becomes `(-1)`). -/
private def emitU32 (n : UInt32) : String :=
  emitUnsignedShortest n.toNat 4294967296

private def emitU64 (n : UInt64) : String :=
  emitUnsignedShortest n.toNat 18446744073709551616

private def emitHeapType : Wasm.GcHeapType → String
  | .any => ".any"
  | .eq => ".eq"
  | .i31 => ".i31"
  | .structT => ".structT"
  | .arrayT => ".arrayT"
  | .noneT => ".noneT"
  | .func => ".func"
  | .noFunc => ".noFunc"
  | .extern => ".extern"
  | .noExtern => ".noExtern"
  | .exn => ".exn"
  | .noExn => ".noExn"
  | .concrete typeIdx => s!".concrete {emitNat typeIdx}"
  | .named name => s!".named {repr name}"

private def emitValueType : Wasm.ValueType → String
  | .i32       => ".i32"
  | .i64       => ".i64"
  | .f32       => ".f32"
  | .f64       => ".f64"
  | .funcref   => ".funcref"
  | .externref => ".externref"
  | .v128      => ".v128"
  | .exnref    => ".exnref"
  | .anyref    => ".anyref"
  | .ref nullable heap =>
      s!".ref {repr nullable} ({emitHeapType heap})"

private def emitValueTypes (xs : List Wasm.ValueType) : String :=
  list (xs.map emitValueType)

private def emitControlTypes (paramTypes resultTypes : List Wasm.ValueType) : String :=
  if paramTypes.isEmpty && resultTypes.isEmpty then ""
  else s!" {emitValueTypes paramTypes} {emitValueTypes resultTypes}"

private def emitOptionValueType : Option Wasm.ValueType → String
  | none => "none"
  | some valueType => s!"some ({emitValueType valueType})"

/-- One-line rendering for a non-structured-control instruction. Structured
control (`block`, `loop`, `iff`) is handled by `emitInstr`/`emitInstrList`
because its body is pretty-printed on multiple lines. -/
private def emitInstrShort : Wasm.Instruction → String
  -- Constants / locals
  | .const v        => ".const " ++ emitU32 v
  | .constI64 v     => ".constI64 " ++ emitU64 v
  | .localGet i     => s!".localGet {emitNat i}"
  | .localSet i     => s!".localSet {emitNat i}"
  | .localTee i     => s!".localTee {emitNat i}"
  -- i32 arithmetic
  | .add            => ".add"
  | .sub            => ".sub"
  | .mul            => ".mul"
  | .divU           => ".divU"
  | .divS           => ".divS"
  | .remU           => ".remU"
  | .remS           => ".remS"
  -- i32 comparison
  | .eqz            => ".eqz"
  | .eq             => ".eq"
  | .ne             => ".ne"
  | .ltU            => ".ltU"
  | .ltS            => ".ltS"
  | .gtU            => ".gtU"
  | .gtS            => ".gtS"
  | .leU            => ".leU"
  | .leS            => ".leS"
  | .geU            => ".geU"
  | .geS            => ".geS"
  -- i32 bitwise / shift / counting
  | .and            => ".and"
  | .or             => ".or"
  | .xor            => ".xor"
  | .shl            => ".shl"
  | .shrU           => ".shrU"
  | .shrS           => ".shrS"
  | .rotl           => ".rotl"
  | .rotr           => ".rotr"
  | .clz            => ".clz"
  | .ctz            => ".ctz"
  | .popcnt         => ".popcnt"
  -- i64 arithmetic
  | .addI64         => ".addI64"
  | .subI64         => ".subI64"
  | .mulI64         => ".mulI64"
  | .divUI64        => ".divUI64"
  | .divSI64        => ".divSI64"
  | .remUI64        => ".remUI64"
  | .remSI64        => ".remSI64"
  -- i64 comparison
  | .eqzI64         => ".eqzI64"
  | .eqI64          => ".eqI64"
  | .neI64          => ".neI64"
  | .ltUI64         => ".ltUI64"
  | .ltSI64         => ".ltSI64"
  | .gtUI64         => ".gtUI64"
  | .gtSI64         => ".gtSI64"
  | .leUI64         => ".leUI64"
  | .leSI64         => ".leSI64"
  | .geUI64         => ".geUI64"
  | .geSI64         => ".geSI64"
  -- i64 bitwise / shift / counting
  | .andI64         => ".andI64"
  | .orI64          => ".orI64"
  | .xorI64         => ".xorI64"
  | .shlI64         => ".shlI64"
  | .shrUI64        => ".shrUI64"
  | .shrSI64        => ".shrSI64"
  | .rotlI64        => ".rotlI64"
  | .rotrI64        => ".rotrI64"
  | .clzI64         => ".clzI64"
  | .ctzI64         => ".ctzI64"
  | .popcntI64      => ".popcntI64"
  -- Conversions
  | .wrapI64        => ".wrapI64"
  | .extendUI32     => ".extendUI32"
  | .extendSI32     => ".extendSI32"
  | .extend8S       => ".extend8S"
  | .extend16S      => ".extend16S"
  | .extend8SI64    => ".extend8SI64"
  | .extend16SI64   => ".extend16SI64"
  | .extend32SI64   => ".extend32SI64"
  -- Float constants
  | .f32Const v     => ".f32Const " ++ emitU32 v
  | .f64Const v     => ".f64Const " ++ emitU64 v
  -- Float arithmetic
  | .f32Add         => ".f32Add"
  | .f32Sub         => ".f32Sub"
  | .f32Mul         => ".f32Mul"
  | .f32Div         => ".f32Div"
  | .f32Min         => ".f32Min"
  | .f32Max         => ".f32Max"
  | .f32Copysign    => ".f32Copysign"
  | .f64Add         => ".f64Add"
  | .f64Sub         => ".f64Sub"
  | .f64Mul         => ".f64Mul"
  | .f64Div         => ".f64Div"
  | .f64Min         => ".f64Min"
  | .f64Max         => ".f64Max"
  | .f64Copysign    => ".f64Copysign"
  -- Float unary
  | .f32Abs         => ".f32Abs"
  | .f32Neg         => ".f32Neg"
  | .f32Sqrt        => ".f32Sqrt"
  | .f32Ceil        => ".f32Ceil"
  | .f32Floor       => ".f32Floor"
  | .f32Trunc       => ".f32Trunc"
  | .f32Nearest     => ".f32Nearest"
  | .f64Abs         => ".f64Abs"
  | .f64Neg         => ".f64Neg"
  | .f64Sqrt        => ".f64Sqrt"
  | .f64Ceil        => ".f64Ceil"
  | .f64Floor       => ".f64Floor"
  | .f64Trunc       => ".f64Trunc"
  | .f64Nearest     => ".f64Nearest"
  -- Float comparison
  | .f32Eq          => ".f32Eq"
  | .f32Ne          => ".f32Ne"
  | .f32Lt          => ".f32Lt"
  | .f32Gt          => ".f32Gt"
  | .f32Le          => ".f32Le"
  | .f32Ge          => ".f32Ge"
  | .f64Eq          => ".f64Eq"
  | .f64Ne          => ".f64Ne"
  | .f64Lt          => ".f64Lt"
  | .f64Gt          => ".f64Gt"
  | .f64Le          => ".f64Le"
  | .f64Ge          => ".f64Ge"
  -- Float memory loads/stores
  | .f32Load off    => s!".f32Load {emitU32 off}"
  | .f64Load off    => s!".f64Load {emitU32 off}"
  | .f32Store off   => s!".f32Store {emitU32 off}"
  | .f64Store off   => s!".f64Store {emitU32 off}"
  -- Integer → float conversions
  | .f32ConvertI32S => ".f32ConvertI32S"
  | .f32ConvertI32U => ".f32ConvertI32U"
  | .f32ConvertI64S => ".f32ConvertI64S"
  | .f32ConvertI64U => ".f32ConvertI64U"
  | .f64ConvertI32S => ".f64ConvertI32S"
  | .f64ConvertI32U => ".f64ConvertI32U"
  | .f64ConvertI64S => ".f64ConvertI64S"
  | .f64ConvertI64U => ".f64ConvertI64U"
  -- Float → integer conversions (trapping)
  | .i32TruncF32S   => ".i32TruncF32S"
  | .i32TruncF32U   => ".i32TruncF32U"
  | .i32TruncF64S   => ".i32TruncF64S"
  | .i32TruncF64U   => ".i32TruncF64U"
  | .i64TruncF32S   => ".i64TruncF32S"
  | .i64TruncF32U   => ".i64TruncF32U"
  | .i64TruncF64S   => ".i64TruncF64S"
  | .i64TruncF64U   => ".i64TruncF64U"
  -- Float → integer conversions (saturating)
  | .i32TruncSatF32S => ".i32TruncSatF32S"
  | .i32TruncSatF32U => ".i32TruncSatF32U"
  | .i32TruncSatF64S => ".i32TruncSatF64S"
  | .i32TruncSatF64U => ".i32TruncSatF64U"
  | .i64TruncSatF32S => ".i64TruncSatF32S"
  | .i64TruncSatF32U => ".i64TruncSatF32U"
  | .i64TruncSatF64S => ".i64TruncSatF64S"
  | .i64TruncSatF64U => ".i64TruncSatF64U"
  -- Float ↔ float and bitwise reinterpret
  | .f32DemoteF64       => ".f32DemoteF64"
  | .f64PromoteF32      => ".f64PromoteF32"
  | .i32ReinterpretF32  => ".i32ReinterpretF32"
  | .i64ReinterpretF64  => ".i64ReinterpretF64"
  | .f32ReinterpretI32  => ".f32ReinterpretI32"
  | .f64ReinterpretI64  => ".f64ReinterpretI64"
  -- Branching
  | .br n           => s!".br {emitNat n}"
  | .br_if n        => s!".br_if {emitNat n}"
  | .brTable ts d   => s!".brTable {emitNatList ts} {emitNat d}"
  -- Calls / returns
  | .call idx                  => s!".call {emitNat idx}"
  | .callIndirect ti tj        => s!".callIndirect {emitNat ti} {emitNat tj}"
  | .ret                       => ".ret"
  -- References
  | .refNull staticType => s!".refNull ({emitValueType staticType})"
  | .refFunc i      => s!".refFunc {emitNat i}"
  | .refIsNull      => ".refIsNull"
  -- Tables
  | .tableGet t     => s!".tableGet {emitNat t}"
  | .tableSize t    => s!".tableSize {emitNat t}"
  -- Globals
  | .globalGet i    => s!".globalGet {emitNat i}"
  | .globalSet i    => s!".globalSet {emitNat i}"
  -- i32 memory loads/stores
  | .load8U off     => s!".load8U {emitU32 off}"
  | .load8S off     => s!".load8S {emitU32 off}"
  | .load16U off    => s!".load16U {emitU32 off}"
  | .load16S off    => s!".load16S {emitU32 off}"
  | .load32 off     => s!".load32 {emitU32 off}"
  | .store8 off     => s!".store8 {emitU32 off}"
  | .store16 off    => s!".store16 {emitU32 off}"
  | .store32 off    => s!".store32 {emitU32 off}"
  -- i64 memory loads/stores
  | .load64 off     => s!".load64 {emitU32 off}"
  | .store64 off    => s!".store64 {emitU32 off}"
  | .load8UI64 off  => s!".load8UI64 {emitU32 off}"
  | .load8SI64 off  => s!".load8SI64 {emitU32 off}"
  | .load16UI64 off => s!".load16UI64 {emitU32 off}"
  | .load16SI64 off => s!".load16SI64 {emitU32 off}"
  | .load32UI64 off => s!".load32UI64 {emitU32 off}"
  | .load32SI64 off => s!".load32SI64 {emitU32 off}"
  | .store8I64 off  => s!".store8I64 {emitU32 off}"
  | .store16I64 off => s!".store16I64 {emitU32 off}"
  | .store32I64 off => s!".store32I64 {emitU32 off}"
  -- Memory management
  | .memorySize     => ".memorySize"
  | .memoryGrow     => ".memoryGrow"
  | .memoryFill     => ".memoryFill"
  | .memoryCopy     => ".memoryCopy"
  | .memoryInit i   => s!".memoryInit {emitNat i}"
  | .dataDrop i     => s!".dataDrop {emitNat i}"
  -- Parametric / nullary
  | .drop           => ".drop"
  | .select         => ".select"
  | .nop            => ".nop"
  | .unreachable    => ".unreachable"
  -- Structured control: should be handled by emitInstr; fall back to a flat
  -- one-line form so this function remains total.
  | .block pa ra body paramTypes resultTypes =>
      s!".block {emitNat pa} {emitNat ra} " ++ list (body.map emitInstrShort) ++
        emitControlTypes paramTypes resultTypes
  | .loop pa ra body paramTypes resultTypes  =>
      s!".loop {emitNat pa} {emitNat ra} " ++ list (body.map emitInstrShort) ++
        emitControlTypes paramTypes resultTypes
  | .iff pa ra thn els paramTypes resultTypes =>
      s!".iff {emitNat pa} {emitNat ra} " ++
        list (thn.map emitInstrShort) ++ " " ++ list (els.map emitInstrShort) ++
        emitControlTypes paramTypes resultTypes
  -- Reference / table (wasm 2.0+)
  | .refNullExtern staticType => s!".refNullExtern ({emitValueType staticType})"
  | .refNullExn staticType    => s!".refNullExn ({emitValueType staticType})"
  | .tableSet t           => s!".tableSet {emitNat t}"
  | .tableGrow t          => s!".tableGrow {emitNat t}"
  | .tableFill t          => s!".tableFill {emitNat t}"
  | .tableCopy d s        => s!".tableCopy {emitNat d} {emitNat s}"
  | .tableInit t e        => s!".tableInit {emitNat t} {emitNat e}"
  | .elemDrop e           => s!".elemDrop {emitNat e}"
  -- Tail calls
  | .returnCall i         => s!".returnCall {emitNat i}"
  | .returnCallIndirect ti tj => s!".returnCallIndirect {emitNat ti} {emitNat tj}"
  -- Typed function references
  | .callRef t            => s!".callRef {emitNat t}"
  | .returnCallRef t      => s!".returnCallRef {emitNat t}"
  | .refAsNonNull         => ".refAsNonNull"
  | .brOnNull l           => s!".brOnNull {emitNat l}"
  | .brOnNonNull l        => s!".brOnNonNull {emitNat l}"
  -- Exception handling
  | .throwI t             => s!".throwI {emitNat t}"
  | .throwRef             => ".throwRef"
  | .tryTable pa ra cs body paramTypes resultTypes =>
      s!".tryTable {emitNat pa} {emitNat ra} {reprStr cs} " ++
        list (body.map emitInstrShort) ++
        emitControlTypes paramTypes resultTypes
  -- Multi-memory
  | .memOp k i            => s!".memOp {emitNat k} (" ++ emitInstrShort i ++ ")"
  | .memoryCopyBetween d s => s!".memoryCopyBetween {emitNat d} {emitNat s}"
  -- SIMD (v128). Lane semantics carry `Simd.*` immediates, rendered via
  -- their `Repr`. The Rust-compiled corpus never emits these.
  | .vConst bits          => s!".vConst (BitVec.ofNat 128 {bits.toNat})"
  | .vUnOp op             => s!".vUnOp {reprStr op}"
  | .vBinOp op            => s!".vBinOp {reprStr op}"
  | .vBitselect           => ".vBitselect"
  | .vTestOp op           => s!".vTestOp {reprStr op}"
  | .vShiftOp op          => s!".vShiftOp {reprStr op}"
  | .vSplat sh            => s!".vSplat {reprStr sh}"
  | .vExtractLane sh signed lane =>
      s!".vExtractLane {reprStr sh} {reprStr signed} {emitNat lane}"
  | .vReplaceLane sh lane => s!".vReplaceLane {reprStr sh} {emitNat lane}"
  | .vShuffle ls          => s!".vShuffle {emitNatList ls}"
  | .vFma sh neg          => s!".vFma {reprStr sh} {reprStr neg}"
  | .vDotAdd              => ".vDotAdd"
  | .v128Load off         => s!".v128Load {emitU32 off}"
  | .v128Store off        => s!".v128Store {emitU32 off}"
  | .v128LoadExt sb signed off => s!".v128LoadExt {emitNat sb} {reprStr signed} {emitU32 off}"
  | .v128LoadSplat b off  => s!".v128LoadSplat {emitNat b} {emitU32 off}"
  | .v128LoadZero b off   => s!".v128LoadZero {emitNat b} {emitU32 off}"
  | .v128LoadLane b l off => s!".v128LoadLane {emitNat b} {emitNat l} {emitU32 off}"
  | .v128StoreLane b l off => s!".v128StoreLane {emitNat b} {emitNat l} {emitU32 off}"
  -- GC ops (GC proposal). Rendered via `GcOp`'s `Repr`; the Rust-compiled
  -- corpus this emitter targets never produces them.
  | .gc op                => s!".gc ({reprStr op})"

mutual
  /-- Render an instruction prefixed with `indent ind`. Structured-control
  bodies are recursively broken across lines; leaf instructions stay on the
  caller's line. -/
  private partial def emitInstr (ind : Nat) : Wasm.Instruction → String
    | .block pa ra body paramTypes resultTypes =>
        indent ind ++ s!".block {emitNat pa} {emitNat ra} " ++ emitInstrList ind body ++
          emitControlTypes paramTypes resultTypes
    | .loop pa ra body paramTypes resultTypes =>
        indent ind ++ s!".loop {emitNat pa} {emitNat ra} " ++ emitInstrList ind body ++
          emitControlTypes paramTypes resultTypes
    | .iff pa ra thn els paramTypes resultTypes =>
        indent ind ++ s!".iff {emitNat pa} {emitNat ra} " ++
          emitInstrList ind thn ++ " " ++ emitInstrList ind els ++
          emitControlTypes paramTypes resultTypes
    | .tryTable pa ra cs body paramTypes resultTypes =>
        indent ind ++ s!".tryTable {emitNat pa} {emitNat ra} {reprStr cs} " ++
          emitInstrList ind body ++
          emitControlTypes paramTypes resultTypes
    | other =>
        indent ind ++ emitInstrShort other

  /-- Render a `[...]` instruction list. Empty lists collapse to `[]`; non-
  empty lists break across lines with each entry on its own line, indented
  one level deeper than the opener, with a comma after every entry except
  the last. The closing `]` sits at column `ind`. -/
  private partial def emitInstrList (ind : Nat) : List Wasm.Instruction → String
    | [] => "[]"
    | xs =>
        let n := xs.length
        let lines := xs.mapIdx fun i instr =>
          let l := emitInstr (ind + 1) instr
          if i + 1 < n then l ++ "," else l
        "[\n" ++ String.intercalate "\n" lines ++ "\n" ++ indent ind ++ "]"
end

/-- The set of export names pointing at the given function index. -/
private def exportsForIdx (es : List Wasm.Export) (idx : Nat) : List String :=
  es.filterMap (fun e => if e.funcIdx = idx then some e.name else none)

private def exportDocComment (es : List Wasm.Export) (idx : Nat) : String :=
  if (exportsForIdx es idx).isEmpty then "" else "/-- Exported function. -/\n"

private def funcBodyName (idx : Nat) : String := s!"func{idx}"
private def funcDefName (idx : Nat) : String := s!"func{idx}Def"

private def emitFuncBodyDef (es : List Wasm.Export) (importCount idx : Nat)
    (f : Wasm.Function) : String :=
  let body := emitInstrList 0 f.body
  s!"{exportDocComment es (importCount + idx)}def {funcBodyName idx} : Wasm.Program :=\n  {body}"

private def emitFunc (idx : Nat) (f : Wasm.Function) : String :=
  record <|
    fieldIf (!f.params.isEmpty) "params" (emitValueTypes f.params) ++
    fieldIf (!f.locals.isEmpty) "locals" (emitValueTypes f.locals) ++
    [field "body" (funcBodyName idx)] ++
    fieldIf (!f.results.isEmpty) "results" (emitValueTypes f.results) ++
    fieldIf f.typeIdx.isSome "typeIdx" (emitOptionNat f.typeIdx)

/-- Render one named function record, referring to the corresponding `funcN`
body definition. Used by both expanded and compact generated files. -/
def funcDef (idx : Nat) (f : Wasm.Function) : String :=
  s!"def {funcDefName idx} : Wasm.Function :=\n  {emitFunc idx f}"

private def emitExport (e : Wasm.Export) : String :=
  s!"\{ name := {repr e.name}, funcIdx := {emitNat e.funcIdx} }"

private def emitImport (i : Wasm.ImportDecl) : String :=
  record <|
    [field "«module»" (reprStr i.«module»), field "name" (reprStr i.name)] ++
    fieldIf (!i.params.isEmpty) "params" (emitValueTypes i.params) ++
    fieldIf (!i.results.isEmpty) "results" (emitValueTypes i.results)

private def emitValue : Wasm.Value → String
  | .i32 n              => s!".i32 {emitU32 n}"
  | .i64 n              => s!".i64 {emitU64 n}"
  | .f32 bits           => s!".f32 {emitU32 bits}"
  | .f64 bits           => s!".f64 {emitU64 bits}"
  | .funcref none       => ".funcref none"
  | .funcref (some i)   => s!".funcref (some {emitNat i})"
  | .externref none     => ".externref none"
  | .externref (some i) => s!".externref (some {emitNat i})"
  | .v128 bits          => s!".v128 (BitVec.ofNat 128 {bits.toNat})"
  | .exnref none        => ".exnref none"
  | .exnref (some i)    => s!".exnref (some {emitNat i})"
  | .anyref none        => ".anyref none"
  | .anyref (some r)    => s!".anyref (some ({reprStr r}))"

private def emitGlobalDecl (g : Wasm.GlobalDecl) : String :=
  let declaredType := emitOptionValueType g.declaredType
  let sourceInit := match g.sourceInit with
    | none => "none"
    | some program => "some (" ++ emitInstrList 3 program ++ ")"
  record <|
    [field "init" (emitValue g.init)] ++
    fieldIf g.declaredType.isSome "declaredType" declaredType ++
    fieldIf (!g.isMut) "isMut" (reprStr g.isMut) ++
    fieldIf g.sourceInit.isSome "sourceInit" sourceInit ++
    fieldIf (!g.initExpr.isEmpty) "initExpr" (emitInstrList 3 g.initExpr)

private def emitByte (b : UInt8) : String := toString b.toNat

private def emitHexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat ('0'.toNat + n)
  else Char.ofNat ('a'.toNat + n - 10)

private def emitHexByte (b : UInt8) : String :=
  let n := b.toNat
  String.ofList [emitHexDigit (n / 16), emitHexDigit (n % 16)]

private def emitByteList (bs : List UInt8) : String :=
  let decimal := list (bs.map emitByte)
  let hex := s!"hexBytes% {repr (String.join (bs.map emitHexByte))}"
  if hex.length < decimal.length then hex else decimal

private def emitOptionU32 : Option UInt32 → String
  | none   => "none"
  | some n => s!"some {emitU32 n}"

private def emitDataSegment (d : Wasm.DataSegment) : String :=
  record <|
    [field "offset" (emitOptionU32 d.offset), field "bytes" (emitByteList d.bytes)] ++
    fieldIf (d.memIdx != 0) "memIdx" (emitNat d.memIdx) ++
    fieldIf d.offsetType.isSome "offsetType" (emitOptionValueType d.offsetType) ++
    fieldIf d.offsetExprPresent "offsetExprPresent" (reprStr d.offsetExprPresent) ++
    fieldIf (!d.offsetExpr.isEmpty) "offsetExpr" (emitInstrList 4 d.offsetExpr)

private def emitMemDecl (m : Wasm.MemDecl) : String :=
  record <|
    [field "pagesMin" (emitU32 m.pagesMin)] ++
    fieldIf m.pagesMax.isSome "pagesMax" (emitOptionU32 m.pagesMax) ++
    fieldIf (!m.data.isEmpty) "data" (recordListAt 2 (m.data.map emitDataSegment)) ++
    fieldIf m.is64 "is64" (reprStr m.is64)

private def emitOptionMem : Option Wasm.MemDecl → String
  | none   => "none"
  | some m => s!"some ({emitMemDecl m})"

private def emitFuncType (t : Wasm.FuncType) : String :=
  record <|
    fieldIf (!t.params.isEmpty) "params" (emitValueTypes t.params) ++
    fieldIf (!t.results.isEmpty) "results" (emitValueTypes t.results)

private def emitStorageType : Wasm.StorageType → String
  | .val valueType => s!".val ({emitValueType valueType})"
  | .packed bits => s!".packed {emitNat bits}"

private def emitFieldType (field : Wasm.FieldType) : String :=
  s!"\{ storage := {emitStorageType field.storage}, isMut := {repr field.isMut} }"

private def emitCompositeType : Wasm.CompositeType → String
  | .func signature => s!".func ({emitFuncType signature})"
  | .struct fields => s!".struct {list (fields.map emitFieldType)}"
  | .array elem => s!".array ({emitFieldType elem})"

private def emitOptionString : Option String → String
  | none => "none"
  | some value => s!"some {repr value}"

private def emitGcTypeDef (typeDef : Wasm.GcTypeDef) : String :=
  record <|
    [field "comp" (emitCompositeType typeDef.comp)] ++
    fieldIf typeDef.sourceName.isSome "sourceName" (emitOptionString typeDef.sourceName) ++
    fieldIf typeDef.super.isSome "super" (emitOptionNat typeDef.super) ++
    fieldIf (!typeDef.final) "«final»" (reprStr typeDef.final) ++
    fieldIf typeDef.recGroup.isSome "recGroup" (emitOptionNat typeDef.recGroup)

private def emitTableDecl (t : Wasm.TableDecl) : String :=
  record <|
    [field "min" (emitNat t.min)] ++
    fieldIf t.max.isSome "max" (emitOptionNat t.max) ++
    fieldIf (t.elemType != .funcref) "elemType" (emitValueType t.elemType) ++
    fieldIf t.is64 "is64" (reprStr t.is64)

private def emitFuncrefSlot : Option Nat → String
  | none   => "none"
  | some i => s!"some {emitNat i}"

private def emitElementSegment (e : Wasm.ElementSegment) : String :=
  record <|
    fieldIf e.tableIdx.isSome "tableIdx" (emitOptionNat e.tableIdx) ++
    fieldIf e.offset.isSome "offset" (emitOptionNat e.offset) ++
    fieldIf e.offsetType.isSome "offsetType" (emitOptionValueType e.offsetType) ++
    fieldIf e.offsetExprPresent "offsetExprPresent" (reprStr e.offsetExprPresent) ++
    fieldIf e.elemType.isSome "elemType" (emitOptionValueType e.elemType) ++
    fieldIf e.declarative "declarative" (reprStr e.declarative) ++
    fieldIf (!e.funcs.isEmpty) "funcs" (list (e.funcs.map emitFuncrefSlot)) ++
    fieldIf (!e.exprs.isEmpty) "exprs" (recordListAt 3 (e.exprs.map (emitInstrList 4))) ++
    fieldIf (!e.offsetExpr.isEmpty) "offsetExpr" (emitInstrList 3 e.offsetExpr)

private def emitStringPair (entry : String × String) : String :=
  s!"({repr entry.1}, {repr entry.2})"

private def emitStringNatPair (entry : String × Nat) : String :=
  s!"({repr entry.1}, {emitNat entry.2})"

/-- All function-body and named `Function` `def`s, joined by blank lines. -/
def funcBodies (m : Wasm.Module) : String :=
  String.intercalate "\n\n" <|
    m.funcs.mapIdx (fun i f =>
      emitFuncBodyDef m.exports m.imports.length i f ++ "\n\n" ++ funcDef i f)

/-- The module record, pretty-printed across multiple lines. -/
def «module» (m : Wasm.Module) : String :=
  let imports := recordList (m.imports.map emitImport)
  let funcs := recordList (m.funcs.mapIdx (fun i _ => funcDefName i))
  let exports := recordList (m.exports.map emitExport)
  let memory := emitOptionMem m.memory
  let extraMemories := recordList (m.extraMemories.map emitMemDecl)
  let globals := recordList (m.globals.map emitGlobalDecl)
  let types    := recordList (m.types.map emitFuncType)
  let gcTypes  := recordList (m.gcTypes.map emitGcTypeDef)
  let tables   := recordList (m.tables.map emitTableDecl)
  let elements := recordList (m.elements.map emitElementSegment)
  let importedGlobals := recordList (m.importedGlobals.map emitStringPair)
  let importedTables := recordList (m.importedTables.map emitStringPair)
  let importedMemories := recordList (m.importedMemories.map emitStringPair)
  let importedTags := recordList (m.importedTags.map emitStringPair)
  let globalExports := recordList (m.globalExports.map emitStringNatPair)
  let tableExports := recordList (m.tableExports.map emitStringNatPair)
  let memoryExports := recordList (m.memoryExports.map emitStringNatPair)
  let tagExports := recordList (m.tagExports.map emitStringNatPair)
  let tags := recordList (m.tags.map emitFuncType)
  let fields :=
    fieldIf (!m.imports.isEmpty) "imports" imports ++
    [field "funcs" funcs] ++
    fieldIf (!m.exports.isEmpty) "exports" exports ++
    fieldIf m.memory.isSome "memory" memory ++
    fieldIf (!m.extraMemories.isEmpty) "extraMemories" extraMemories ++
    fieldIf m.dataWithoutMemory "dataWithoutMemory" (reprStr m.dataWithoutMemory) ++
    fieldIf (!m.globals.isEmpty) "globals" globals ++
    fieldIf m.startFunc.isSome "startFunc" (emitOptionNat m.startFunc) ++
    fieldIf (!m.types.isEmpty) "types" types ++
    fieldIf (!m.gcTypes.isEmpty) "gcTypes" gcTypes ++
    fieldIf (!m.tables.isEmpty) "tables" tables ++
    fieldIf (!m.elements.isEmpty) "elements" elements ++
    fieldIf (!m.importedGlobals.isEmpty) "importedGlobals" importedGlobals ++
    fieldIf (!m.importedTables.isEmpty) "importedTables" importedTables ++
    fieldIf (!m.importedMemories.isEmpty) "importedMemories" importedMemories ++
    fieldIf (!m.importedTags.isEmpty) "importedTags" importedTags ++
    fieldIf (!m.globalExports.isEmpty) "globalExports" globalExports ++
    fieldIf (!m.tableExports.isEmpty) "tableExports" tableExports ++
    fieldIf (!m.memoryExports.isEmpty) "memoryExports" memoryExports ++
    fieldIf (!m.tagExports.isEmpty) "tagExports" tagExports ++
    fieldIf (!m.tags.isEmpty) "tags" tags
  "{\n  " ++ String.intercalate ",\n  " fields ++ "\n}"

/-- Emit a fail-closed structural fidelity check. The generated `#eval`
re-decodes the current WAT and compares the complete module AST with the Lean
literal, so an edited instruction on either side is detected without embedding
a second full copy of the WAT source. -/
def driftCheck (relWatPath : String) : String :=
  String.intercalate "\n" [
    "-- Compile-time fidelity check: errors if WAT and generated Lean AST differ.",
    "#guard_msgs (drop info) in",
    s!"#eval Wasm.checkWatFidelity {repr relWatPath} «module»"
  ]

/-! ## CodeLib scaffolding (`lift`)

Render a single function body as a ready-to-prove `CodeLib/RustStd/<Type>/`
file: the verbatim body + `Function` record (so it matches the emitted module
exactly — checked by `rfl` in the per-crate spec), plus a wp-form theorem stub
in the house style. The post-condition (`Returns …`) and the proof are left as
`sorry` for the human to fill, mirroring `AbsDiff`. -/

private def valLeanType : Wasm.ValueType → String
  | .i64 => "UInt64"
  | .i32 => "UInt32"
  | _    => "UInt32 /- TODO: unsupported value type -/"

private def valCtor : Wasm.ValueType → String
  | .i64 => ".i64"
  | _    => ".i32"

private def valZero : Wasm.ValueType → String
  | .i64 => ".i64 0"
  | _    => ".i32 0"

/-- Single-letter binder name `a`, `b`, … for the `i`-th parameter. Only valid
for `i < 12`: it must stay clear of the theorem's `m : Module` binder (offset 12)
and the printable-letter range (offset 26). Callers (`cmdLift`) guard the arity. -/
private def paramName (i : Nat) : String := String.singleton (Char.ofNat (97 + i))

/-- Full CodeLib scaffold file for function `f`, named `<funcName>`/`<bodyName>`
under `namespace Wasm.RustStd.<typeNs>`. -/
def codeLibScaffold (typeNs fnName bodyName funcName : String)
    (f : Wasm.Function) : String :=
  let binders := String.intercalate " "
    (f.params.mapIdx fun i t => s!"({paramName i} : {valLeanType t})")
  let paramLocals := "[" ++ String.intercalate ", "
    (f.params.mapIdx fun i t => s!"{valCtor t} {paramName i}") ++ "]"
  let zeroLocals := "[" ++ String.intercalate ", " (f.locals.map valZero) ++ "]"
  let body := emitInstrList 0 f.body
  String.intercalate "\n" [
    "import CodeLib.RustStd.Frame",
    "import Interpreter.Wasm.Wp.Tactic",
    "import Interpreter.Wasm.Wp.Block",
    "import CodeLib.Entry",
    "",
    s!"/-! AUTO-SCAFFOLDED by `verifier lift`. Fill in the `Returns` result and",
    s!"the proof (see `AbsDiff` for a template), then delete this note.",
    s!"The `sp`/`hsp`/`hlo`/`hhi` hypotheses and the frame post-condition follow the",
    s!"shadow-stack (global 0 = SP) convention; drop them for a function that uses",
    s!"neither the shadow stack nor memory. -/",
    "",
    s!"namespace Wasm.RustStd.{typeNs}",
    "",
    "open Wasm",
    "",
    s!"/-- Verbatim opt-0 body of `{fnName}`. -/",
    s!"def {bodyName} : Program :=\n  {body}",
    "",
    s!"def {funcName} : Function :=",
    s!"  \{ params := {emitValueTypes f.params}, locals := {emitValueTypes f.locals}" ++
      s!", body := {bodyName}, results := {emitValueTypes f.results} }",
    "",
    "set_option maxRecDepth 4096 in",
    s!"/-- TODO: state what `{fnName}` returns, then prove it. -/",
    s!"theorem {fnName}_wp \{α} \{m : Module} \{env : HostEnv α} (st : Store α)",
    s!"    (sp : UInt32) {binders} (vs : List Value)",
    s!"    (hsp : st.globals.globals[0]? = some (.i32 sp))",
    s!"    (hlo : 16 ≤ sp.toNat) (hhi : sp.toNat ≤ st.mem.pages * 65536) :",
    s!"    wp m {bodyName}",
    s!"      (Returns ((sorry : Value) :: vs)",
    s!"        (fun st' => st'.globals = st.globals ∧ st'.mem.pages = st.mem.pages))",
    s!"      st ⟨{paramLocals}, {zeroLocals}, vs⟩ env := by",
    s!"  sorry",
    "",
    s!"end Wasm.RustStd.{typeNs}",
    ""
  ]

end Verifier.Emit
