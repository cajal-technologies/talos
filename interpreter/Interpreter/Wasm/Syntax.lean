import Interpreter.Wasm.Mem
import Interpreter.Wasm.Simd

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
  | externref
  | v128
  | exnref
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
  /-- An `externref`: `none` is the null ref; `some n` is an opaque
  host reference distinguished only by its identity `n`. The wasm core
  never inspects the payload — it only moves externrefs around (locals,
  globals, tables, `select`) and tests them for null. -/
  | externref (idx : Option Nat)
  /-- A `v128` SIMD vector, stored as its 128-bit pattern (lane 0 at the
  least-significant end, matching wasm's little-endian lane order). -/
  | v128 (bits : BitVec 128)
  /-- An `exnref`: `none` is the null ref; `some i` indexes the exception
  package list on the `Store` (`Store.exns`), which `catch_ref` appends
  to and `throw_ref` re-raises from. -/
  | exnref (idx : Option Nat)
deriving Repr, Inhabited, DecidableEq, BEq

/-- Type-indexed zero used to initialise locals at function entry. The
zero for a float is `+0.0` (all-zero bits); for a reference type the
null reference of that type. -/
def ValueType.zero : ValueType → Value
  | .i32       => .i32 0
  | .i64       => .i64 0
  | .f32       => .f32 0
  | .f64       => .f64 0
  | .funcref   => .funcref none
  | .externref => .externref none
  | .v128      => .v128 0
  | .exnref    => .exnref none

/-- The scalar payload of a value, as the unsigned `Nat` of its bit
pattern, when the value is the scalar kind lane shape `sh` expects
(`i32` for i8x16/i16x8/i32x4, `i64` for i64x2, `f32`/`f64` for the float
shapes). Used by `vSplat`/`vReplaceLane`, which consume one scalar. -/
def Value.scalarBitsFor? : Simd.Shape → Value → Option Nat
  | .i8x16, .i32 x => some x.toNat
  | .i16x8, .i32 x => some x.toNat
  | .i32x4, .i32 x => some x.toNat
  | .i64x2, .i64 x => some x.toNat
  | .f32x4, .f32 x => some x.toNat
  | .f64x2, .f64 x => some x.toNat
  | _,      _      => none

/-- The address payload of an `i32` or `i64` operand as a `Nat`. Wasm's
64-bit address types (memory64) make the operand width per-memory; bulk
ops with several address operands accept each one by its runtime type. -/
def Value.addrNat? : Value → Option Nat
  | .i32 a => some a.toNat
  | .i64 a => some a.toNat
  | _      => none

/-- Null test for reference values: `some true/false` for refs, `none`
for non-reference values (ill-typed input). -/
def Value.isNullRef? : Value → Option Bool
  | .funcref r   => some r.isNone
  | .externref r => some r.isNone
  | .exnref r    => some r.isNone
  | _            => none

/-- A size/length result, typed by the owning memory/table's address
type: `i64` for 64-bit memories/tables (memory64 proposal), `i32`
otherwise. Used by `memory.size`, `table.size`, and the grow results. -/
def sizeValue (is64 : Bool) (n : Nat) : Value :=
  if is64 then .i64 (UInt64.ofNat n) else .i32 (UInt32.ofNat n)

@[simp] theorem sizeValue_false (n : Nat) :
    sizeValue false n = .i32 (UInt32.ofNat n) := rfl

@[simp] theorem sizeValue_true (n : Nat) :
    sizeValue true n = .i64 (UInt64.ofNat n) := rfl

/-- Module-level globals. Indexed by position in the module's globals list. -/
structure Globals where
  globals : List Value := []
deriving Repr, Inhabited

/-- One catch clause of a `try_table`. The label is a branch depth
resolved from just inside the construct (0 = the `try_table` itself).
`catch`/`catchRef` match one tag; the `All` forms match any. The `Ref`
forms additionally push the caught exception package as an `exnref`. -/
inductive CatchClause where
  | catch (tag label : Nat)
  | catchRef (tag label : Nat)
  | catchAll (label : Nat)
  | catchAllRef (label : Nat)
deriving Repr, Inhabited, DecidableEq

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

  -- Tail calls. `return_call f` replaces the current frame with an
  -- invocation of `f`: the callee's results become the current
  -- function's results (validation requires the result types to agree).
  -- The fuel-bounded interpreter resolves these in `run`, so deep chains
  -- of tail calls consume fuel but not host stack.
  | returnCall : Nat → Instruction
  | returnCallIndirect : (typeIdx tableIdx : Nat) → Instruction

  -- Exception handling (wasm 3.0). `throw t` pops tag `t`'s parameters
  -- and raises an exception that unwinds until a `tryTable` with a
  -- matching clause catches it; `throwRef` re-raises a caught exception
  -- package (trapping on the null exnref). `tryTable` executes its body
  -- like a `block`; clause labels are resolved as branches from just
  -- inside the construct (label 0 exits the `tryTable` itself).
  | throwI : (tagIdx : Nat) → Instruction
  | throwRef : Instruction
  | tryTable : (paramArity resultArity : Nat) → List CatchClause →
               List Instruction → Instruction

  -- Typed function references (wasm 3.0). `call_ref (type N)` pops a
  -- funcref and dispatches to it, trapping on null; the static type
  -- annotation needs no runtime check (validation guarantees it), so the
  -- immediate is kept only for round-tripping. `return_call_ref` is its
  -- tail-call form. `ref.as_non_null` asserts non-null (trapping
  -- otherwise); `br_on_null l` branches to `l` when the popped ref is
  -- null (consuming it) and pushes it back otherwise; `br_on_non_null l`
  -- branches with the ref kept when non-null and consumes it otherwise.
  | callRef : (typeIdx : Nat) → Instruction
  | returnCallRef : (typeIdx : Nat) → Instruction
  | refAsNonNull : Instruction
  | brOnNull : Nat → Instruction
  | brOnNonNull : Nat → Instruction

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
  | refNullExtern : Instruction    -- ref.null extern: push the null externref
  | refFunc   : Nat → Instruction  -- ref.func i:    push a reference to function `i`
  | refIsNull : Instruction        -- ref.is_null:   pop a ref, push i32 1 if null else 0

  -- Table instructions. The runtime tables live on the `Store` (one
  -- `TableInst = List Value`, holding reference values, per declared
  -- table). `table.get t` pops an i32 index `i` and pushes `tables[t][i]`
  -- (trapping if `i` is past the table's current length); `table.size t`
  -- pushes the table's current length as an i32. A `tableIdx` that is
  -- itself out of range is a validation error, not a runtime trap.
  | tableGet  : Nat → Instruction  -- table.get t
  | tableSize : Nat → Instruction  -- table.size t

  -- table.set t: pops [val(ref), idx(i32)] (top = val) and writes
  -- `tables[t][idx] := val`, trapping "out of bounds table access" if
  -- `idx` is past the table's current length.
  | tableSet  : Nat → Instruction

  -- table.grow t: pops [delta(i32), init(ref)] (top = delta). On success
  -- the table is extended by `delta` copies of `init` and the *old* size
  -- is pushed; on failure (past the declared max, or past the
  -- implementation's growth ceiling — the spec permits growth to fail)
  -- pushes -1.
  | tableGrow : Nat → Instruction

  -- table.fill t: pops [len(i32), val(ref), dst(i32)] (top = len) and
  -- writes `val` into `tables[t][dst, dst+len)`. Traps "out of bounds
  -- table access" before any write if `dst+len` exceeds the table size.
  | tableFill : Nat → Instruction

  -- table.copy d s: pops [len(i32), src(i32), dst(i32)] (top = len) and
  -- copies `tables[s][src, src+len)` to `tables[d][dst, dst+len)` with
  -- memmove semantics. Traps before any write if either range escapes
  -- its table.
  | tableCopy : (dstIdx srcIdx : Nat) → Instruction

  -- table.init t e: pops [len(i32), src(i32), dst(i32)] (top = len) and
  -- copies entries `[src, src+len)` of element segment `e` into
  -- `tables[t][dst, dst+len)`. A dropped segment behaves as length 0.
  -- Traps before any write on either bounds violation.
  | tableInit : (tableIdx elemIdx : Nat) → Instruction

  -- elem.drop e: mark element segment `e` as dropped. Idempotent.
  | elemDrop : Nat → Instruction

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

  -- Multi-memory. `memOp k op` runs the memory instruction `op` against
  -- memory index `k ≥ 1` (`Store.extraMems[k-1]`): the interpreter swaps
  -- that memory (and its declaration) into the default slot, runs `op`,
  -- and swaps the result back. The decoder only wraps memory
  -- instructions, and only when the index is non-zero.
  | memOp : (memIdx : Nat) → Instruction → Instruction

  -- memory.copy d s with distinct memories (multi-memory): pops
  -- [len, src, dst] (top = len; each i32 or i64 per its memory's address
  -- type) and copies from memory `s` to memory `d`, with both bounds
  -- checked before any write.
  | memoryCopyBetween : (dstMem srcMem : Nat) → Instruction

  -- SIMD (v128). Lane-level semantics live in `Interpreter.Wasm.Simd`;
  -- the constructors here group the proposal's ~240 mnemonics by
  -- operand/result shape. Memory variants mirror the scalar load/store
  -- constructors (static byte offset; i32 address popped from the stack).
  | vConst   : BitVec 128 → Instruction       -- v128.const
  | vUnOp    : Simd.UnOp → Instruction        -- v128 → v128
  | vBinOp   : Simd.BinOp → Instruction       -- v128 v128 → v128
  | vBitselect : Instruction                  -- v128 v128 v128 → v128
  | vTestOp  : Simd.TestOp → Instruction      -- v128 → i32
  | vShiftOp : Simd.ShiftOp → Instruction     -- v128 i32 → v128
  | vSplat   : Simd.Shape → Instruction       -- scalar → v128
  -- extract_lane: `signed` only meaningful for the i8x16/i16x8 `_s` forms
  | vExtractLane : Simd.Shape → (signed : Bool) → (lane : Nat) → Instruction
  | vReplaceLane : Simd.Shape → (lane : Nat) → Instruction
  | vShuffle : List Nat → Instruction         -- i8x16.shuffle (16 lane indices)
  -- Relaxed SIMD, deterministic choices (see Interpreter.Wasm.Simd):
  -- relaxed_madd/nmadd (unfused multiply-add) and the dot-add form.
  | vFma : Simd.Shape → (neg : Bool) → Instruction  -- v128³ → v128
  | vDotAdd : Instruction                           -- v128³ → v128
  | v128Load  : UInt32 → Instruction          -- v128.load: 16-byte load
  | v128Store : UInt32 → Instruction          -- v128.store: 16-byte store
  -- v128.load8x8_s/u, 16x4, 32x2: load 8 bytes, widen each half-lane
  | v128LoadExt : (srcBits : Nat) → (signed : Bool) → UInt32 → Instruction
  -- v128.load8/16/32/64_splat: load one lane, broadcast
  | v128LoadSplat : (bits : Nat) → UInt32 → Instruction
  -- v128.load32/64_zero: load one lane, zero the rest
  | v128LoadZero : (bits : Nat) → UInt32 → Instruction
  -- v128.load8/16/32/64_lane: load one lane into an existing vector
  | v128LoadLane  : (bits lane : Nat) → UInt32 → Instruction
  -- v128.store8/16/32/64_lane: store one lane of a vector
  | v128StoreLane : (bits lane : Nat) → UInt32 → Instruction

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
  /-- Target memory index (multi-memory): 0 is the default memory, k ≥ 1
  the k-th extra memory (`Module.extraMemories[k-1]`). -/
  memIdx : Nat := 0
deriving Repr, Inhabited

/-- Declaration of a single linear memory. Wasm allows at most one
memory per module. -/
structure MemDecl where
  pagesMin : UInt32
  pagesMax : Option UInt32 := none
  data     : List DataSegment := []
  /-- `true` for a 64-bit memory (the wasm 3.0 memory64 address type):
  addresses are popped as `i64`, and `memory.size` / `memory.grow` speak
  `i64` instead of `i32`. -/
  is64     : Bool := false
deriving Repr, Inhabited

/-- Declaration of a module-level global with its initial value. -/
structure GlobalDecl where
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
  /-- `true` for a 64-bit table (the wasm 3.0 table64 address type):
  element indices are popped as `i64`, and `table.size` / `table.grow`
  speak `i64` instead of `i32`. -/
  is64     : Bool := false
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
  /-- Additional memories (multi-memory proposal), in declaration order:
  memory index `k ≥ 1` is `extraMemories[k-1]`. Their active data
  segments live in `memory`'s (global, source-ordered) `data` list,
  routed by `DataSegment.memIdx`. -/
  extraMemories : List MemDecl := []
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
  /-- Names of imported non-function entities, aligned with the *first*
  k entries of the corresponding index space: per the wasm spec,
  imported globals/tables/memories occupy the low indices in import
  order, ahead of the module's own declarations. The decoder fills the
  corresponding decl slots with the import's declared shape (zero
  contents); the test harness substitutes registered/spectest values at
  instantiation. -/
  importedGlobals  : List (String × String) := []
  importedTables   : List (String × String) := []
  importedMemories : List (String × String) := []
  /-- Exported non-function entities: name → index into the
  corresponding index space. Used by the harness to resolve
  cross-module entity imports. -/
  globalExports : List (String × Nat) := []
  tableExports  : List (String × Nat) := []
  memoryExports : List (String × Nat) := []
  /-- Exception tags (exception-handling proposal), indexed by position;
  each carries the tag's parameter types (`results` is always empty). -/
  tags : List FuncType := []
deriving Repr, Inhabited

/-- Runtime representation of a single table: a list of reference
values (`.funcref` or `.externref`, matching the table's declared
element type). The length is the table's current size. -/
abbrev TableInst : Type := List Value

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
  /-- Runtime instances of the module's `extraMemories` (multi-memory):
  memory index `k ≥ 1` is `extraMems[k-1]`. -/
  extraMems       : List Mem := []
  dataSegments    : List (Option (List UInt8)) := []
  /-- Runtime tables. Same length and source order as the declaring
  module's `tables`; entry `t` has size at least `tables[t].min`. -/
  tables          : List TableInst := []
  /-- Per-segment runtime status, mirroring `dataSegments` for `data`.
  `none` = dropped or active-and-already-consumed; `some funcs` =
  passive segment still available to `table.init`. Same length as the
  declaring module's `elements` list. -/
  elementSegments : List (Option (List (Option Nat))) := []
  /-- Caught exception packages (tag index × thrown args in stack order),
  appended by `catch_ref` clauses and re-raised by `throw_ref`. Indexed
  by `Value.exnref`. -/
  exns            : List (Nat × List Value) := []
  host            : α
deriving Repr

/-- Replace `list[i]` in place. Returns the original list unchanged
if `i ≥ list.length`. -/
def listSetAt (l : List α) (i : Nat) (v : α) : List α :=
  match l, i with
  | [],     _     => []
  | _::xs, 0      => v :: xs
  | x::xs, i + 1  => x :: listSetAt xs i v

/-- Write `vs` into `l` starting at offset `off`, dropping writes that
fall past the end. Used to apply an active element segment to a fresh
table; bounds violations are detected by the caller before this is
invoked, so silent truncation here is unreachable in well-formed
input. -/
def listWriteAt (l : List α) (off : Nat) (vs : List α) : List α :=
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
  -- Apply the active data segments targeting memory `idx` to `m0`.
  -- Segments live in one global, source-ordered list (memory 0's
  -- `data`); `DataSegment.memIdx` routes each to its memory.
  let applySegs (segs : List DataSegment) (idx : Nat) (m0 : Mem) : Mem :=
    segs.foldl
      (fun acc seg => match seg.offset with
        | some off =>
          if seg.memIdx = idx then acc.writeBytes off.toNat seg.bytes else acc
        | none     => acc)
      m0
  let allSegs : List DataSegment := match m.memory with
    | some decl => decl.data
    | none      => []
  let (mem, dataSegments) : Mem × List (Option (List UInt8)) :=
    match m.memory with
    | none      => (Mem.empty 0, [])
    | some decl =>
      let mem : Mem := applySegs decl.data 0 (Mem.empty decl.pagesMin.toNat)
      let dataSegments : List (Option (List UInt8)) :=
        decl.data.map fun seg => match seg.offset with
          | some _ => none           -- active: auto-dropped after init
          | none   => some seg.bytes -- passive: available to memory.init
      (mem, dataSegments)
  -- Extra memories (multi-memory): memory k = extraMems[k-1].
  let extraMems : List Mem := m.extraMemories.zipIdx.map fun (decl, i) =>
    applySegs allSegs (i + 1) (Mem.empty decl.pagesMin.toNat)
  -- Allocate tables filled with the element type's null ref at the
  -- declared minimum size.
  let baseTables : List TableInst :=
    m.tables.map fun td => (List.replicate td.min td.elemType.zero : TableInst)
  -- Apply active element segments. Passive/declarative segments leave the
  -- table untouched and are tracked in `elementSegments` so `table.init`
  -- can consume them later.
  let tables : List TableInst := m.elements.foldl
    (fun acc seg =>
      match seg.tableIdx, seg.offset with
      | some t, some off =>
        match acc[t]? with
        | some tbl => listSetAt acc t (listWriteAt tbl off (seg.funcs.map Value.funcref))
        | none     => acc
      | _, _ => acc)
    baseTables
  let elementSegments : List (Option (List (Option Nat))) :=
    m.elements.map fun seg => match seg.offset with
      | some _ => none           -- active: auto-dropped
      | none   => some seg.funcs -- passive / declarative
  { globals, mem, extraMems, dataSegments, tables, elementSegments, host := default }

/-- Maximum number of pages an i32-indexed memory can hold (2^16, or 4 GiB).
This is the wasm spec hard ceiling; `memory.grow` may not exceed it
regardless of the per-module declared max. -/
def Module.memoryHardCap : Nat := 65536

/-- Effective `memory.grow` ceiling for `m`: the declared `pagesMax`
(if any) intersected with `memoryHardCap`. Modules with no memory
declaration get the hard cap; this is never observed in practice
because such modules have no memory instructions.

The 65536-page (4 GiB) ceiling deliberately applies to 64-bit
(memory64) memories as well: the spec permits `memory.grow` to fail
for implementation-defined reasons, and this interpreter caps every
memory at the i32 hard limit. -/
def Module.memoryCap (m : Module) : Nat :=
  match m.memory with
  | some d =>
    match d.pagesMax with
    | some n => Nat.min n.toNat Module.memoryHardCap
    | none   => Module.memoryHardCap
  | none => Module.memoryHardCap

/-- Whether the module's memory is 64-bit-addressed (memory64). -/
def Module.memIs64 (m : Module) : Bool :=
  match m.memory with
  | some d => d.is64
  | none   => false

/-- Whether table `t` is 64-bit-indexed (table64). -/
def Module.tableIs64 (m : Module) (t : Nat) : Bool :=
  match m.tables[t]? with
  | some td => td.is64
  | none    => false

/-- Look up the index of an exported function by name. -/
def Module.findExport (m : Module) (name : String) : Option Nat :=
  (m.exports.find? (·.name = name)).map (·.funcIdx)

/-- Signature of a function in the *unified* index space: indices below
`imports.length` resolve to the import's declared signature, the rest to
the in-module function's declared signature. Used by `call_indirect` to
type-check the table entry against the expected `(type N)` — looking the
target up in `m.funcs` directly would be off by `imports.length` for
modules with function imports. -/
def Module.funcSig? (m : Module) (i : Nat) : Option FuncType :=
  match m.imports[i]? with
  | some imp => some { params := imp.params, results := imp.results }
  | none     =>
    match m.funcs[i - m.imports.length]? with
    | some f => some { params := f.params, results := f.results }
    | none   => none

/-- Implementation ceiling on `table.grow`. The wasm spec allows growth
to fail for implementation-defined reasons; this interpreter materialises
tables as Lean lists, so unbounded growth (the suite probes deltas up to
`0xFFFF_FFF0`) must be refused rather than attempted. Growth that stays
within a table's *declared* max is always honoured — declared maxima in
practice are small — and growth beyond this ceiling fails with -1. -/
def Module.tableHardCap : Nat := 1_000_000

/-- Effective `table.grow` ceiling for table `t` of `m`: the declared max
(if any) intersected with the implementation ceiling `tableHardCap`. -/
def Module.tableCap (m : Module) (t : Nat) : Nat :=
  match m.tables[t]? with
  | some td =>
    match td.max with
    | some n => Nat.min n Module.tableHardCap
    | none   => Module.tableHardCap
  | none => Module.tableHardCap

end Wasm
