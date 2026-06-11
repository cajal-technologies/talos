import Interpreter.Wasm.Mem

namespace Wasm

/-! ## Value types and runtime values

Wasm's numeric types `i32`, `i64`, `f32`, `f64`, plus the `funcref`
reference type needed for tables and `call_indirect`. Floats are carried
by their IEEE-754 bit pattern (`f32` as `UInt32`, `f64` as `UInt64`); the
operations live in `Interpreter.Wasm.Float`. Other reference types remain
out of scope. Memory loads/stores, globals, tables, and indirect calls are
supported. -/

inductive ValueType where
  | i32
  | i64
  | f32
  | f64
  | funcref
deriving Repr, Inhabited, DecidableEq, BEq

inductive Value where
  | i32     (n : UInt32)
  | i64     (n : UInt64)
  /-- An `f32`, stored as its 32-bit IEEE-754 encoding. -/
  | f32     (bits : UInt32)
  /-- An `f64`, stored as its 64-bit IEEE-754 encoding. -/
  | f64     (bits : UInt64)
  /-- A `funcref`: `none` is the null ref; `some i` is a reference to
  function index `i` in the enclosing module's function space. -/
  | funcref (idx : Option Nat)
deriving Repr, Inhabited, DecidableEq, BEq

/-- Type-indexed zero used to initialise locals at function entry. The
zero for a float is `+0.0` (all-zero bits); for `funcref` the null reference. -/
def ValueType.zero : ValueType → Value
  | .i32     => .i32 0
  | .i64     => .i64 0
  | .f32     => .f32 0
  | .f64     => .f64 0
  | .funcref => .funcref none

/-- Module-level globals. Indexed by position in the module's globals list. -/
structure Globals where
  globals : List Value := []
deriving Repr, Inhabited

/-! ## Instructions

The instruction set mirrors `Interpreter.Core.Ast.Instr` minus the
features that require a `Store` (tables, `call_indirect`).
Naming follows Core where applicable; the two historical Wasm differences
(`and`, `br_if`) are kept for backward compatibility with the existing
examples. -/

inductive Instruction where
  -- Constants / locals
  | localGet : Nat → Instruction
  | localSet : Nat → Instruction
  | const    : UInt32 → Instruction
  | constI64 : UInt64 → Instruction

  -- Globals
  | globalGet : Nat → Instruction  -- global.get i: push globals[i]
  | globalSet : Nat → Instruction  -- global.set i: pop and write to globals[i]

  -- i32 arithmetic
  | add | sub | mul
  | divU | divS | remU | remS

  -- i32 comparison (results land as i32 0/1)
  | eqz | eq | ne
  | ltU | ltS | gtU | gtS | leU | leS | geU | geS

  -- i32 bitwise / shift / counting
  | and | or | xor
  | shl | shrU | shrS | rotl | rotr
  | clz | ctz | popcnt

  -- i64 arithmetic
  | addI64 | subI64 | mulI64
  | divUI64 | divSI64 | remUI64 | remSI64

  -- i64 comparison (results land as i32 0/1)
  | eqzI64 | eqI64 | neI64
  | ltUI64 | ltSI64 | gtUI64 | gtSI64 | leUI64 | leSI64 | geUI64 | geSI64

  -- i64 bitwise / shift / counting
  | andI64 | orI64 | xorI64
  | shlI64 | shrUI64 | shrSI64 | rotlI64 | rotrI64
  | clzI64 | ctzI64 | popcntI64

  -- Conversions / sign-extension
  | wrapI64
  | extendSI32 | extendUI32
  | extend8S   | extend16S
  | extend8SI64 | extend16SI64 | extend32SI64

  -- Float constants (carry the IEEE-754 bit pattern directly)
  | f32Const : UInt32 → Instruction
  | f64Const : UInt64 → Instruction

  -- Float arithmetic
  | f32Add | f32Sub | f32Mul | f32Div | f32Min | f32Max | f32Copysign
  | f64Add | f64Sub | f64Mul | f64Div | f64Min | f64Max | f64Copysign

  -- Float unary
  | f32Abs | f32Neg | f32Sqrt | f32Ceil | f32Floor | f32Trunc | f32Nearest
  | f64Abs | f64Neg | f64Sqrt | f64Ceil | f64Floor | f64Trunc | f64Nearest

  -- Float comparison (results land as i32 0/1)
  | f32Eq | f32Ne | f32Lt | f32Gt | f32Le | f32Ge
  | f64Eq | f64Ne | f64Lt | f64Gt | f64Le | f64Ge

  -- Float memory (static byte offset; address popped from stack as i32)
  | f32Load  : UInt32 → Instruction  -- f32.load:  4-byte load  → f32
  | f64Load  : UInt32 → Instruction  -- f64.load:  8-byte load  → f64
  | f32Store : UInt32 → Instruction  -- f32.store: 4-byte store
  | f64Store : UInt32 → Instruction  -- f64.store: 8-byte store

  -- Integer → float conversions (`S`/`U` = signed/unsigned source)
  | f32ConvertI32S | f32ConvertI32U | f32ConvertI64S | f32ConvertI64U
  | f64ConvertI32S | f64ConvertI32U | f64ConvertI64S | f64ConvertI64U

  -- Float → integer conversions, trapping on NaN / out-of-range
  | i32TruncF32S | i32TruncF32U | i32TruncF64S | i32TruncF64U
  | i64TruncF32S | i64TruncF32U | i64TruncF64S | i64TruncF64U

  -- Float → integer conversions, saturating (NaN → 0, clamp to range)
  | i32TruncSatF32S | i32TruncSatF32U | i32TruncSatF64S | i32TruncSatF64U
  | i64TruncSatF32S | i64TruncSatF32U | i64TruncSatF64S | i64TruncSatF64U

  -- Float ↔ float, and bitwise reinterpretation between a float and the
  -- same-width integer (a pure retag of the bits)
  | f32DemoteF64 | f64PromoteF32
  | i32ReinterpretF32 | i64ReinterpretF64 | f32ReinterpretI32 | f64ReinterpretI64

  -- Structured control. Each block-like form carries its arity:
  -- `paramArity` is the number of values consumed from the operand
  -- stack on entry, `resultArity` the number of values left on top
  -- when the construct exits via fall-through. The interpreter uses
  -- these to trim the stack at construct boundaries so structured
  -- control flow respects the wasm spec: a `br` to a `block`/`if`
  -- keeps `resultArity` values; a `br` back to a `loop` keeps
  -- `paramArity` values (the loop's "carried" iteration state).
  | block : (paramArity resultArity : Nat) → List Instruction → Instruction
  | loop  : (paramArity resultArity : Nat) → List Instruction → Instruction
  | iff   : (paramArity resultArity : Nat) → List Instruction → List Instruction → Instruction
  | br      : Nat → Instruction
  | br_if   : Nat → Instruction
  | brTable : List Nat → Nat → Instruction
  | ret     : Instruction
  | call    : Nat → Instruction

  -- Indirect call. `typeIdx` selects the expected signature from the
  -- enclosing module's type table; `tableIdx` selects the table (almost
  -- always 0 in practice). The runtime pops an `i32` index `i`, looks up
  -- `tables[tableIdx][i]`, requires it to be a non-null `funcref`, and
  -- traps "indirect call type mismatch" if the target function's
  -- signature differs from `types[typeIdx]`. Otherwise it dispatches to
  -- that function via the standard calling convention.
  | callIndirect : (typeIdx tableIdx : Nat) → Instruction

  -- Reference instructions. `funcref` values are already modelled by
  -- `Value.funcref (Option Nat)` (`none` = null, `some i` = a reference to
  -- function index `i`). These produce and test such values; none of them
  -- touch the store.
  | refNull   : Instruction        -- ref.null func: push the null funcref
  | refFunc   : Nat → Instruction  -- ref.func i:    push a reference to function `i`
  | refIsNull : Instruction        -- ref.is_null:   pop a ref, push i32 1 if null else 0

  -- Table instructions. The runtime tables live on the `Store` (one
  -- `TableInst = List (Option Nat)` per declared table). `table.get t`
  -- pops an i32 index `i` and pushes `tables[t][i]` as a `funcref`
  -- (trapping if `i` is past the table's current length); `table.size t`
  -- pushes the table's current length as an i32; `table.set t` pops a
  -- `funcref` and then an i32 index `i` and writes the funcref into
  -- `tables[t][i]` (trapping if `i` is out of bounds). A `tableIdx` that
  -- is itself out of range is a validation error, not a runtime trap.
  | tableGet  : Nat → Instruction  -- table.get t
  | tableSize : Nat → Instruction  -- table.size t
  | tableSet  : Nat → Instruction  -- table.set t
  | tableGrow : Nat → Instruction  -- table.grow t
  | tableFill : Nat → Instruction  -- table.fill t
  | tableCopy : (dstTableIdx srcTableIdx : Nat) → Instruction  -- table.copy dst src
  | tableInit : (tableIdx segIdx : Nat) → Instruction          -- table.init t e
  | elemDrop  : Nat → Instruction                               -- elem.drop e

  -- i32 memory loads (static byte offset; address popped from stack as i32)
  | load8U  : UInt32 → Instruction  -- i32.load8_u:  zero-extend 1 byte  → i32
  | load8S  : UInt32 → Instruction  -- i32.load8_s:  sign-extend 1 byte  → i32
  | load16U : UInt32 → Instruction  -- i32.load16_u: zero-extend 2 bytes → i32
  | load16S : UInt32 → Instruction  -- i32.load16_s: sign-extend 2 bytes → i32
  | load32  : UInt32 → Instruction  -- i32.load:     full 32-bit load     → i32

  -- i32 memory stores (static byte offset; value then address popped from stack)
  | store8  : UInt32 → Instruction  -- i32.store8:  write low 1 byte
  | store16 : UInt32 → Instruction  -- i32.store16: write low 2 bytes
  | store32 : UInt32 → Instruction  -- i32.store:   write 4 bytes

  -- i64 memory ops (static byte offset)
  | load64  : UInt32 → Instruction  -- i64.load:  8-byte load  → i64
  | store64 : UInt32 → Instruction  -- i64.store: 8-byte store

  -- i64 sized memory loads (address popped as i32)
  | load8UI64  : UInt32 → Instruction  -- i64.load8_u:  zero-extend 1 byte → i64
  | load8SI64  : UInt32 → Instruction  -- i64.load8_s:  sign-extend 1 byte → i64
  | load16UI64 : UInt32 → Instruction  -- i64.load16_u: zero-extend 2 bytes → i64
  | load16SI64 : UInt32 → Instruction  -- i64.load16_s: sign-extend 2 bytes → i64
  | load32UI64 : UInt32 → Instruction  -- i64.load32_u: zero-extend 4 bytes → i64
  | load32SI64 : UInt32 → Instruction  -- i64.load32_s: sign-extend 4 bytes → i64

  -- i64 sized memory stores (i64 value then i32 address popped)
  | store8I64  : UInt32 → Instruction  -- i64.store8:  write low 1 byte
  | store16I64 : UInt32 → Instruction  -- i64.store16: write low 2 bytes
  | store32I64 : UInt32 → Instruction  -- i64.store32: write low 4 bytes

  -- Memory size / grow (page = 64 KiB)
  | memorySize : Instruction              -- memory.size: push current pages as i32
  | memoryGrow : Instruction              -- memory.grow: pop delta i32; on success
                                          -- push old pages, on failure push -1

  -- Memory fill: pops [dst, val, len] (top = len), writes val.low8 byte
  -- into mem[dst, dst+len). Traps if dst+len > mem size in bytes.
  | memoryFill : Instruction

  -- Memory copy: pops [dst, src, len] (top = len). Copies len bytes
  -- from mem[src, src+len) to mem[dst, dst+len). Traps if either
  -- range escapes the legal byte span; overlap is handled correctly
  -- (memmove semantics).
  | memoryCopy : Instruction

  -- Memory init: pops [dst, src, len] (top = len). Copies len bytes
  -- from data segment `i` at offset src into mem at offset dst.
  -- Traps if src+len exceeds the segment's available length (a dropped
  -- segment behaves as length 0) or dst+len exceeds memory size.
  | memoryInit : Nat → Instruction

  -- Data drop: marks segment `i` as dropped (no further memory.init
  -- can read from it). Idempotent.
  | dataDrop : Nat → Instruction

  -- Parametric / nullary
  | drop
  | select
  | nop
  | unreachable
deriving Repr

abbrev Program := List Instruction

/-- A function declaration. `params` lists parameter types; `locals` lists
the non-param local types, each initialised to its type's zero value at
function entry. -/
structure Function where
  params  : List ValueType := []
  locals  : List ValueType := []
  body    : Program
  /-- Result types declared by the function. The interpreter applies the
  standard Wasm calling convention: params are reversed on entry so
  local 0 is the first (deepest) argument, and the top `results.length`
  values are returned to the caller on exit. -/
  results : List ValueType := []
deriving Repr, Inhabited

@[inline] def Function.numParams (f : Function) : Nat := f.params.length
@[inline] def Function.numLocals (f : Function) : Nat := f.locals.length

/-- A name-indexed entry point. The WAT decoder collects these from
`(export "name" (func $ref))` forms (inline + top-level); the emitter
renders them as `/-- export: foo -/` doc comments on the right `def`. -/
structure Export where
  name    : String
  funcIdx : Nat
deriving Repr, Inhabited, DecidableEq

/-- A data segment. An *active* segment carries `offset := some n` and
is copied into linear memory at module instantiation (then auto-dropped);
a *passive* segment carries `offset := none` and stays available to
`memory.init` until `data.drop` consumes it. -/
structure DataSegment where
  offset : Option UInt32
  bytes  : List UInt8
deriving Repr, Inhabited

/-- Declaration of a single linear memory. Wasm allows at most one
memory per module. -/
structure MemDecl where
  pagesMin : UInt32
  pagesMax : Option UInt32 := none
  data     : List DataSegment := []
deriving Repr, Inhabited

/-- Declaration of a module-level global with its initial value. -/
structure GlobalDecl where
  type : ValueType
  init : Value
deriving Repr, Inhabited

/-- A function type, identified by `(type N)` in the source. Stored on
the module so that `call_indirect` can compare the expected signature
against the target function's declared signature at runtime. -/
structure FuncType where
  params  : List ValueType := []
  results : List ValueType := []
deriving Repr, Inhabited, DecidableEq, BEq

/-- Declaration of a single table. The interpreter only models
`funcref` tables; the size bounds are the declared minimum and (optional)
declared maximum. A freshly instantiated table has `min` null refs. -/
structure TableDecl where
  min      : Nat
  max      : Option Nat := none
  elemType : ValueType  := .funcref
deriving Repr, Inhabited

/-- Declaration of a function imported from the host. Imports occupy the
low indices of the unified function index space: `call i` for
`i < imports.length` dispatches to the host environment's `i`-th
function; for `i ≥ imports.length` it dispatches to
`funcs[i - imports.length]`. The `params`/`results` are the import's
declared signature; the host environment is expected to honour it. -/
structure ImportDecl where
  «module» : String
  name     : String
  params   : List ValueType := []
  results  : List ValueType := []
deriving Repr, Inhabited, DecidableEq

/-- A `(elem ...)` declaration. *Active* segments carry
`tableIdx := some t` and `offset := some n` and are written into
`tables[t]` starting at offset `n` at instantiation time, then dropped.
*Passive* and *declarative* segments leave `offset := none` (declarative
additionally has `tableIdx := none`); their contents stay on the store
in `elementSegments` until consumed by `table.init` / `elem.drop`. -/
structure ElementSegment where
  tableIdx : Option Nat := none
  offset   : Option Nat := none
  funcs    : List (Option Nat) := []
deriving Repr, Inhabited

structure Module where
  funcs    : List Function
  exports  : List Export := []
  memory   : Option MemDecl := none
  globals  : List GlobalDecl := []
  /-- Imported functions, in declaration order. See `ImportDecl` for the
  index-space convention. Empty for modules with no imports. -/
  imports  : List ImportDecl := []
  /-- Index of the optional `(start $f)` function. Per the wasm spec it is
  invoked once during instantiation, after data/elem segments are written,
  with no arguments and no results. A trap during start makes the whole
  instantiation fail. -/
  startFunc : Option Nat := none
  /-- Function type declarations indexed by source-order position
  (`(type 0)`, `(type 1)`, ...). `call_indirect (type N)` looks the
  expected signature up here. -/
  types    : List FuncType := []
  /-- Table declarations. Wasm <2.0 allows at most one; we accept the
  whole list anyway. -/
  tables   : List TableDecl := []
  elements : List ElementSegment := []
deriving Repr, Inhabited

/-- Runtime representation of a single table: a list of `funcref` slots
(`none` = null, `some i` = function index `i`). The length is the
table's current size. -/
abbrev TableInst : Type := List (Option Nat)

/-- The mutable runtime state threaded through execution: module-level
globals, the (optional) linear memory, available bytes per data segment
(`none` = dropped or active-and-already-consumed; `some bs` = still
available to `memory.init`), runtime tables and per-element-segment
status, and a host-managed slot whose type `α` is supplied by the host.
The Wasm core never inspects `host`; only host imports do.

`α` is whatever shape a particular host needs — `Unit` for the
hostless corpus, a KV map for a blockchain demo, a byte-trace for a
logger, etc. No schema is baked into the Wasm core. -/
structure Store (α : Type) where
  globals         : Globals
  mem             : Mem
  dataSegments    : List (Option (List UInt8)) := []
  /-- Runtime tables. Same length and source order as the declaring
  module's `tables`; entry `t` has size at least `tables[t].min`. -/
  tables          : List TableInst := []
  /-- Per-segment runtime status, mirroring `dataSegments` for `data`.
  `none` = dropped or active-and-already-consumed; `some funcs` =
  passive segment still available to `table.init`. Same length as the
  declaring module's `elements` list. -/
  elementSegments : List (Option (List (Option Nat))) := []
  host            : α
deriving Repr

/-- Replace `list[i]` in place. Returns the original list unchanged
if `i ≥ list.length`. -/
private def listSetAt (l : List α) (i : Nat) (v : α) : List α :=
  match l, i with
  | [],     _     => []
  | _::xs, 0      => v :: xs
  | x::xs, i + 1  => x :: listSetAt xs i v

/-- Write `vs` into `l` starting at offset `off`, dropping writes that
fall past the end. Used to apply an active element segment to a fresh
table; bounds violations are detected by the caller before this is
invoked, so silent truncation here is unreachable in well-formed
input. -/
private def listWriteAt (l : List α) (off : Nat) (vs : List α) : List α :=
  match vs, off with
  | [], _ => l
  | v :: vs', 0     => match l with
    | []      => []
    | _ :: xs => v :: listWriteAt xs 0 vs'
  | _,        i + 1 => match l with
    | []      => []
    | x :: xs => x :: listWriteAt xs i vs

/-- Build the initial store for a module: evaluate each global's `init`
into `Globals.globals`; allocate a memory with `pagesMin` pages and
write each *active* data segment at its declared offset; track all
segments in `dataSegments` (passive → `some bytes`, active → `none`,
because active segments are spec-equivalent to "dropped" immediately
after instantiation). Allocate tables sized to each declaration's
minimum (filled with null refs) and apply every active element segment;
passive/declarative segments are stashed in `elementSegments` for
`table.init` to consume later. Modules with no memory get an empty
0-page memory. -/
def Module.initialStore [Inhabited α] (m : Module) : Store α :=
  let globals : Globals := { globals := m.globals.map (·.init) }
  let (mem, dataSegments) : Mem × List (Option (List UInt8)) :=
    match m.memory with
    | none      => (Mem.empty 0, [])
    | some decl =>
      let m0 := Mem.empty decl.pagesMin.toNat
      let mem : Mem := decl.data.foldl
        (fun acc seg => match seg.offset with
          | some off => acc.writeBytes off.toNat seg.bytes
          | none     => acc)
        m0
      let dataSegments : List (Option (List UInt8)) :=
        decl.data.map fun seg => match seg.offset with
          | some _ => none           -- active: auto-dropped after init
          | none   => some seg.bytes -- passive: available to memory.init
      (mem, dataSegments)
  -- Allocate tables filled with null refs at the declared minimum size.
  let baseTables : List TableInst :=
    m.tables.map fun td => (List.replicate td.min none : TableInst)
  -- Apply active element segments. Passive/declarative segments leave the
  -- table untouched and are tracked in `elementSegments` so `table.init`
  -- can consume them later.
  let tables : List TableInst := m.elements.foldl
    (fun acc seg =>
      match seg.tableIdx, seg.offset with
      | some t, some off =>
        match acc[t]? with
        | some tbl => listSetAt acc t (listWriteAt tbl off seg.funcs)
        | none     => acc
      | _, _ => acc)
    baseTables
  let elementSegments : List (Option (List (Option Nat))) :=
    m.elements.map fun seg => match seg.offset with
      | some _ => none           -- active: auto-dropped
      | none   => some seg.funcs -- passive / declarative
  { globals, mem, dataSegments, tables, elementSegments, host := default }

/-- Maximum number of pages an i32-indexed memory can hold (2^16, or 4 GiB).
This is the wasm spec hard ceiling; `memory.grow` may not exceed it
regardless of the per-module declared max. -/
def Module.memoryHardCap : Nat := 65536

/-- Effective `memory.grow` ceiling for `m`: the declared `pagesMax`
(if any) intersected with `memoryHardCap`. Modules with no memory
declaration get the hard cap; this is never observed in practice
because such modules have no memory instructions. -/
def Module.memoryCap (m : Module) : Nat :=
  match m.memory with
  | some d =>
    match d.pagesMax with
    | some n => Nat.min n.toNat Module.memoryHardCap
    | none   => Module.memoryHardCap
  | none => Module.memoryHardCap

/-- Look up the index of an exported function by name. -/
def Module.findExport (m : Module) (name : String) : Option Nat :=
  (m.exports.find? (·.name = name)).map (·.funcIdx)

end Wasm
