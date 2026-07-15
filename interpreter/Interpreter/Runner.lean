import Interpreter.Wasm.Semantics
import Interpreter.Wasm.Decoder.Wat

/-!
# `runner` — CLI front-end for the Lean Wasm interpreter

Loads a `.wat` (read directly) or `.wasm` (decoded by shelling out to
`wasm-tools print`) module, invokes one of its functions, and prints
the results. See the README for the CLI contract.
-/

namespace Wasm.Runner

open Wasm Wasm.Decoder.Wat

/-! ## CLI parsing -/

structure Args where
  file   : String
  method : String
  args   : List String
  fuel   : Nat
deriving Repr

def defaultFuel : Nat := 1_000_000

def usage : String :=
"Usage: lake exe runner [--fuel N] [-h|--help] <file> <method> [args...]

  <file>    Path ending in .wat (read directly) or .wasm (decoded via
            `wasm-tools print`; requires wasm-tools on PATH).
  <method>  Export name, or a non-negative integer interpreted as a
            function index. The integer rule always wins — an export
            literally named \"0\" is unreachable.
  [args...] One numeric literal per declared parameter. Decimal (`42`,
            `-1`) and hex (`0xff`) accepted. The declared parameter
            type drives the width/signedness coercion.
  --fuel N  Reduction-step cap, default 1_000_000.
  -h, --help  Print this message and exit 0."

/-- Strip the `--fuel N` / `-h` / `--help` flags and return the
remaining positionals plus the chosen fuel. Bails on bad flag usage. -/
partial def splitFlags
    (toks : List String) (acc : List String) (fuel : Nat) (help : Bool)
    : Except String (List String × Nat × Bool) :=
  match toks with
  | [] => .ok (acc.reverse, fuel, help)
  | "-h" :: rest | "--help" :: rest =>
    splitFlags rest acc fuel true
  | "--fuel" :: nStr :: rest =>
    match nStr.toNat? with
    | some n => splitFlags rest acc n help
    | none   => .error s!"--fuel expects a non-negative integer, got `{nStr}`"
  | "--fuel" :: [] => .error "--fuel expects an argument"
  | tok :: rest =>
    if tok.startsWith "--fuel=" then
      let v := (tok.drop "--fuel=".length).toString
      match v.toNat? with
      | some n => splitFlags rest acc n help
      | none   => .error s!"--fuel expects a non-negative integer, got `{v}`"
    else
      splitFlags rest (tok :: acc) fuel help

def parseArgs (argv : List String) : Except String (Sum Unit Args) := do
  let (pos, fuel, help) ← splitFlags argv [] defaultFuel false
  if help then return .inl ()
  match pos with
  | file :: method :: args => return .inr { file, method, args, fuel }
  | [_] => .error "missing <method>"
  | []  => .error "missing <file> and <method>"

/-! ## `.wasm` handling -/

/-- Detect "command not found" robustly across the two ways `IO.Process` can
report a missing binary: an `IOError` thrown by `spawn`, or a non-zero exit
with the shell's "not found" stderr. -/
def wasmToolsPrint (path : String) : IO (Except String String) := do
  let res ← IO.Process.output { cmd := "wasm-tools", args := #["print", path] }
    |>.toBaseIO
  match res with
  | .error _ =>
    return .error "wasm-tools not found on PATH (needed to decode .wasm; install with 'brew install wasm-tools' or 'cargo install wasm-tools')"
  | .ok out =>
    if out.exitCode = 0 then return .ok out.stdout
    else return .error s!"wasm-tools failed: {out.stderr.trimAscii}"

/-- Load the WAT source for a module: read `.wat` directly, shell out for
`.wasm`. -/
def loadWat (path : String) : IO (Except String String) := do
  if path.endsWith ".wasm" then
    wasmToolsPrint path
  else
    try
      let src ← IO.FS.readFile path
      return .ok src
    catch e =>
      return .error s!"could not read {path}: {e.toString}"

/-! ## Pre-flight: imports -/

/-- Count `(import …)` forms inside a `(module …)` body. Used for the
pre-flight rejection; the decoder itself only flags function imports. -/
def countImports (src : String) : Nat :=
  match parseAll src with
  | .error _ => 0
  | .ok xs =>
    match xs with
    | [.list (.atom "module" :: body)] =>
      body.foldl (fun n e =>
        match e with
        | .list (.atom "import" :: _) => n + 1
        | _ => n) 0
    | _ => 0

/-! ## Argument coercion -/

def parseArgForType (t : ValueType) (s : String) : Except String Value :=
  match t with
  | .i32 =>
    match parseI32 s with
    | .ok v  => .ok (.i32 v)
    | .error _ => .error s!"argument out of range for i32: `{s}`"
  | .i64 =>
    match parseI64 s with
    | .ok v  => .ok (.i64 v)
    | .error _ => .error s!"argument out of range for i64: `{s}`"
  | .f32 =>
    -- No decimal float parser in core; a float CLI arg is its raw 32-bit
    -- IEEE-754 encoding (e.g. `0x3f800000` for `1.0`).
    match parseI32 s with
    | .ok v  => .ok (.f32 v)
    | .error _ => .error s!"f32 argument must be a 32-bit IEEE-754 bit pattern: `{s}`"
  | .f64 =>
    match parseI64 s with
    | .ok v  => .ok (.f64 v)
    | .error _ => .error s!"f64 argument must be a 64-bit IEEE-754 bit pattern: `{s}`"
  | .funcref =>
    -- No CLI surface for funcref args yet — pass `null` if the user
    -- writes "null", otherwise refuse.
    if s == "null" then .ok (.funcref none)
    else .error s!"funcref argument must be 'null', got `{s}`"
  | .externref =>
    if s == "null" then .ok (.externref none)
    else .error s!"externref argument must be 'null', got `{s}`"
  | .exnref =>
    if s == "null" then .ok (.exnref none)
    else .error s!"exnref argument must be 'null', got `{s}`"
  | .anyref =>
    if s == "null" then .ok (.anyref none)
    else .error s!"anyref argument must be 'null', got `{s}`"
  | .v128 =>
    .error s!"no CLI surface for v128 arguments: `{s}`"

def parseArgs?
    (params : List ValueType) (args : List String) : Except String (List Value) :=
  if params.length ≠ args.length then
    .error s!"arg-count mismatch: function expects {params.length}, got {args.length}"
  else
    let rec go : List ValueType → List String → Except String (List Value)
      | [], [] => .ok []
      | t :: ts, s :: ss => do
        let v ← parseArgForType t s
        let vs ← go ts ss
        .ok (v :: vs)
      | _, _ => .error "internal: param/arg length mismatch"
    go params args

/-! ## Method resolution -/

def resolveMethod (m : Module) (method : String) : Except String Nat :=
  match method.toNat? with
  | some n =>
    if n < m.funcs.length then .ok n
    else .error s!"function index {n} out of range (module has {m.funcs.length} functions)"
  | none =>
    match m.findExport method with
    | some idx => .ok idx
    | none     => .error s!"unknown export `{method}`"

/-! ## Result printing -/

def renderValue : Value → String
  | .i32 v            => toString v.toInt32.toInt
  | .i64 v            => toString v.toInt64.toInt
  | .f32 b            => toString (Float32.ofBits b).toFloat
  | .f64 b            => toString (Float.ofBits b)
  | .funcref none     => "null"
  | .funcref (some i) => s!"funcref:{i}"
  | .externref none     => "null"
  | .externref (some i) => s!"externref:{i}"
  | .exnref none        => "null"
  | .exnref (some i)    => s!"exnref:{i}"
  | .anyref none              => "null"
  | .anyref (some (.i31 n))   => s!"i31:{n.toInt32.toInt}"
  | .anyref (some (.struct a)) => s!"struct:{a}"
  | .anyref (some (.array a))  => s!"array:{a}"
  | .v128 b             => s!"v128:0x{String.ofList (Nat.toDigits 16 b.toNat)}"

/-! ## Exit codes -/

def EXIT_OK         : UInt32 := 0
def EXIT_TRAP       : UInt32 := 1
def EXIT_OUT_OF_FUEL: UInt32 := 2
def EXIT_ERR        : UInt32 := 3

/-- The big dispatcher. Returns the exit code; all stderr/stdout work is
done as a side effect for streaming. -/
def runOnce (a : Args) : IO UInt32 := do
  -- Load source
  let wat ← match (← loadWat a.file) with
    | .ok s => pure s
    | .error msg => IO.eprintln s!"error: {msg}"; return EXIT_ERR

  -- Pre-flight: imports
  let n := countImports wat
  if n > 0 then
    IO.eprintln s!"error: module declares imports ({n}), runner has no host environment"
    return EXIT_ERR

  -- Decode
  let m ← match decode wat with
    | .ok m => pure m
    | .error msg => IO.eprintln s!"error: {msg}"; return EXIT_ERR

  -- Resolve method
  let idx ← match resolveMethod m a.method with
    | .ok i => pure i
    | .error msg => IO.eprintln s!"error: {msg}"; return EXIT_ERR

  -- Function lookup (defensive — resolveMethod already bounds-checked)
  let f ← match m.funcs[idx]? with
    | some f => pure f
    | none =>
      IO.eprintln s!"error: function index {idx} out of range"
      return EXIT_ERR

  -- Parse args per declared parameter type
  let vs ← match parseArgs? f.params a.args with
    | .ok vs => pure vs
    | .error msg => IO.eprintln s!"error: {msg}"; return EXIT_ERR

  -- Execute. The runner is host-independent; pick `α := Unit` so the
  -- trivial empty `HostEnv Unit` defaults in and the module runs
  -- against no imports. `Wasm.run` expects params in *stack* order
  -- (top = last source arg) and reverses internally so local 0 maps
  -- to the first argument; `parseArgs?` gives them in source order,
  -- so we reverse here to match the call convention. (Single-arg
  -- functions are order-insensitive, which masked this for older
  -- samples.)
  --
  -- Evaluate constant-expression global initializers (`global.get`,
  -- extended-const arithmetic, GC `struct.new`/`array.new*`) into the
  -- fresh store before running, the same way the testsuite driver does
  -- at instantiation — otherwise those globals keep their zero
  -- placeholder. There are no imports here, so `global.get` of an
  -- imported global is unreachable; the import pre-flight above
  -- rejects any module that would need one.
  let store0 := m.runConstGlobals a.fuel (m.initialStore (α := Unit)) {}
  -- Data/elem segments whose offset is itself a const-expr are deferred
  -- by `initialStore`; write them now that the globals are evaluated.
  let store0 := m.runActiveSegments a.fuel store0 {}
  match Wasm.run a.fuel m idx store0 vs.reverse with
  | .Success results _ =>
    for v in results.reverse do
      IO.println (renderValue v)
    return EXIT_OK
  | .Trap _ msg =>
    if msg.isEmpty then IO.eprintln "trap"
    else IO.eprintln s!"trap: {msg}"
    return EXIT_TRAP
  | .OutOfFuel =>
    IO.eprintln "out of fuel"
    return EXIT_OUT_OF_FUEL
  | .Thrown tag _ _ =>
    IO.eprintln s!"uncaught exception (tag {tag})"
    return EXIT_TRAP
  | .Invalid msg =>
    IO.eprintln s!"error: {msg}"
    return EXIT_ERR

end Wasm.Runner

open Wasm.Runner in
def main (argv : List String) : IO UInt32 := do
  match parseArgs argv with
  | .error msg =>
    IO.eprintln s!"error: {msg}"
    IO.eprintln usage
    return EXIT_ERR
  | .ok (.inl ()) =>
    IO.println usage
    return EXIT_OK
  | .ok (.inr a) => runOnce a
