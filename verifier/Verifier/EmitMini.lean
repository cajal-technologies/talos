import Interpreter.Wasm.Syntax

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

namespace Verifier.EmitMini

open Wasm

private def indent (n : Nat) : String := "".pushn ' ' (n * 2)

private def parens (s : String) : String := "(" ++ s ++ ")"

private def list (xs : List String) : String :=
  "[" ++ String.intercalate ", " xs ++ "]"

/-- Pretty-print a list of pre-rendered record strings as a multi-line
literal, two-space indented under the field. Empty lists collapse to `[]`. -/
private def recordList (items : List String) : String :=
  match items with
  | [] => "[]"
  | _  => "[\n    " ++ String.intercalate ",\n    " items ++ "\n  ]"

private def emitNat (n : Nat) : String := toString n

private def emitNatList (ns : List Nat) : String :=
  list (ns.map emitNat)

private def emitU32 (n : UInt32) : String :=
  parens s!"{n.toNat} : UInt32"

private def emitU64 (n : UInt64) : String :=
  parens s!"{n.toNat} : UInt64"

private def emitValueType : Wasm.ValueType → String
  | .i32 => ".i32"
  | .i64 => ".i64"

private def emitValueTypes (xs : List Wasm.ValueType) : String :=
  list (xs.map emitValueType)

/-- One-line rendering for a non-structured-control instruction. Structured
control (`block`, `loop`, `iff`) is handled by `emitInstr`/`emitInstrList`
because its body is pretty-printed on multiple lines. -/
private def emitInstrShort : Wasm.Instruction → String
  -- Constants / locals
  | .const v        => ".const " ++ emitU32 v
  | .constI64 v     => ".constI64 " ++ emitU64 v
  | .localGet i     => s!".localGet {emitNat i}"
  | .localSet i     => s!".localSet {emitNat i}"
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
  -- Branching
  | .br n           => s!".br {emitNat n}"
  | .br_if n        => s!".br_if {emitNat n}"
  | .brTable ts d   => s!".brTable {emitNatList ts} {emitNat d}"
  -- Calls / returns
  | .call idx       => s!".call {emitNat idx}"
  | .ret            => ".ret"
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
  | .block body     => ".block " ++ list (body.map emitInstrShort)
  | .loop body      => ".loop " ++ list (body.map emitInstrShort)
  | .iff thn els    =>
      ".iff " ++ list (thn.map emitInstrShort) ++ " " ++ list (els.map emitInstrShort)

mutual
  /-- Render an instruction prefixed with `indent ind`. Structured-control
  bodies are recursively broken across lines; leaf instructions stay on the
  caller's line. -/
  private partial def emitInstr (ind : Nat) : Wasm.Instruction → String
    | .block body =>
        indent ind ++ ".block " ++ emitInstrList ind body
    | .loop body =>
        indent ind ++ ".loop " ++ emitInstrList ind body
    | .iff thn els =>
        indent ind ++ ".iff " ++ emitInstrList ind thn ++ " " ++ emitInstrList ind els
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
  match exportsForIdx es idx with
  | []   => ""
  | [n]  => s!"/-- export: {n} -/\n"
  | ns   => s!"/-- exports: {String.intercalate ", " ns} -/\n"

private def funcBodyName (idx : Nat) : String := s!"func{idx}"

private def emitFuncBodyDef (es : List Wasm.Export) (idx : Nat) (f : Wasm.Function) : String :=
  let body := emitInstrList 0 f.body
  s!"{exportDocComment es idx}def {funcBodyName idx} : Wasm.Program :=\n  {body}"

private def emitFunc (idx : Nat) (f : Wasm.Function) : String :=
  s!"\{ params := {emitValueTypes f.params}, locals := {emitValueTypes f.locals}" ++
  s!", body := {funcBodyName idx}, results := {emitValueTypes f.results} }"

private def emitExport (e : Wasm.Export) : String :=
  s!"\{ name := {repr e.name}, funcIdx := {emitNat e.funcIdx} }"

private def emitValue : Wasm.Value → String
  | .i32 n => s!".i32 {emitU32 n}"
  | .i64 n => s!".i64 {emitU64 n}"

private def emitGlobalDecl (g : Wasm.GlobalDecl) : String :=
  s!"\{ type := {emitValueType g.type}, init := {emitValue g.init} }"

private def emitByte (b : UInt8) : String := s!"({b.toNat} : UInt8)"

private def emitByteList (bs : List UInt8) : String :=
  list (bs.map emitByte)

private def emitOptionU32 : Option UInt32 → String
  | none   => "none"
  | some n => s!"some {emitU32 n}"

private def emitDataSegment (d : Wasm.DataSegment) : String :=
  s!"\{ offset := {emitOptionU32 d.offset}, bytes := {emitByteList d.bytes} }"

private def emitMemDecl (m : Wasm.MemDecl) : String :=
  let pagesMin := emitU32 m.pagesMin
  let pagesMax := emitOptionU32 m.pagesMax
  let data := recordList (m.data.map emitDataSegment)
  s!"\{ pagesMin := {pagesMin}, pagesMax := {pagesMax}, data := {data} }"

private def emitOptionMem : Option Wasm.MemDecl → String
  | none   => "none"
  | some m => s!"some {emitMemDecl m}"

/-- All function-body `def`s, joined by blank lines. -/
def funcBodies (m : Wasm.Module) : String :=
  String.intercalate "\n\n" <|
    m.funcs.mapIdx (fun i f => emitFuncBodyDef m.exports i f)

/-- The module record, pretty-printed across multiple lines. -/
def «module» (m : Wasm.Module) : String :=
  let funcs := recordList (m.funcs.mapIdx (fun i f => emitFunc i f))
  let exports := recordList (m.exports.map emitExport)
  let memory := emitOptionMem m.memory
  let globals := recordList (m.globals.map emitGlobalDecl)
  s!"\{\n  funcs := {funcs},\n  exports := {exports}" ++
  s!",\n  memory := {memory},\n  globals := {globals}\n}"

/-- Emit the drift-check block: a `UInt64` hash constant pinned to the
`module.wat` content at emit time, plus a `#eval` that re-reads the sibling
file at elaboration time and `throw`s if the hash disagrees. The path is
resolved relative to the lake-project root (lake's elaboration cwd). The
`#guard_msgs (drop info) in` wrapper silences the success-case `()` info
message; if the hash disagrees, `#eval` emits an `error` which still
surfaces. -/
def driftCheck (relWatPath : String) (watHash : UInt64) : String :=
  String.intercalate "\n" [
    "/-- Hash of the source `module.wat` captured when `verifier check` last ran. -/",
    s!"private def expectedWatHash : UInt64 := {watHash.toNat}",
    "",
    "-- Compile-time drift check: errors if `module.wat` has changed without a corresponding re-emit.",
    "#guard_msgs (drop info) in",
    "#eval show IO Unit from do",
    s!"  let path : System.FilePath := {repr relWatPath}",
    "  unless ← path.pathExists do return",
    "  let actual ← IO.FS.readFile path",
    "  if actual.hash ≠ expectedWatHash then",
    "    throw <| IO.userError",
    s!"      s!\"\{path} has drifted from Program.lean; re-run `lake exe verifier check`.\""
  ]

end Verifier.EmitMini
