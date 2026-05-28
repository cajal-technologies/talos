import Interpreter.Wasm.Mem

namespace Wasm

/-! ## Value types and runtime values

Wasm currently supports the integer half of Wasm's numeric types
(`i32`, `i64`). Floats and reference types are out of scope; globals,
tables, and `call_indirect` are intentionally skipped — the state shape
has no `Store` for them. Memory loads/stores are supported. -/

inductive ValueType where
  | i32
  | i64
deriving Repr, Inhabited, DecidableEq, BEq

inductive Value where
  | i32 (n : UInt32)
  | i64 (n : UInt64)
deriving Repr, Inhabited, DecidableEq, BEq

/-- Type-indexed zero used to initialise locals at function entry. -/
def ValueType.zero : ValueType → Value
  | .i32 => .i32 0
  | .i64 => .i64 0

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

structure Module where
  funcs   : List Function
  exports : List Export := []
  memory  : Option MemDecl := none
  globals : List GlobalDecl := []
deriving Repr, Inhabited

/-- The mutable runtime state threaded through execution: module-level
globals, the (optional) linear memory, and the available bytes per
data segment (`none` = dropped or active-and-already-consumed; `some bs`
= still available to `memory.init`). The `dataSegments` list is
indexed by segment number in source order and has the same length as
the declaring module's data list. -/
structure Store where
  globals      : Globals
  mem          : Mem
  dataSegments : List (Option (List UInt8)) := []
deriving Repr, Inhabited

/-- Build the initial store for a module: evaluate each global's `init`
into `Globals.globals`; allocate a memory with `pagesMin` pages and
write each *active* data segment at its declared offset; track all
segments in `dataSegments` (passive → `some bytes`, active → `none`,
because active segments are spec-equivalent to "dropped" immediately
after instantiation). If the module has no memory, the store carries
an empty 0-page memory and an empty `dataSegments` (never observed). -/
def Module.initialStore (m : Module) : Store :=
  let globals : Globals := { globals := m.globals.map (·.init) }
  match m.memory with
  | none      => { globals, mem := Mem.empty 0, dataSegments := [] }
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
    { globals, mem, dataSegments }

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
