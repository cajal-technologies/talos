import Interpreter.Wasm.Syntax
import Interpreter.Wasm.Float
import Interpreter.Wasm.Locals
import Interpreter.Wasm.Continuation
import Interpreter.Wasm.Host

namespace Wasm

/-! ## Numeric helpers (carried over from `Interpreter.Core.Interp`). -/

/-- Number of leading zero bits in a 32-bit word; 32 if zero. -/
def clz32 : Nat → UInt32 → Nat
  | 0, _ => 32
  | k + 1, a => if a &&& 0x80000000 ≠ 0 then 32 - (k + 1) else clz32 k (a <<< 1)

/-- Number of trailing zero bits in a 32-bit word; 32 if zero. -/
def ctz32 : Nat → UInt32 → Nat
  | 0, _ => 32
  | k + 1, a => if a &&& 1 ≠ 0 then 32 - (k + 1) else ctz32 k (a >>> 1)

/-- Number of one bits in a 32-bit word. -/
def popcnt32 : Nat → UInt32 → Nat → Nat
  | 0, _, acc => acc
  | k + 1, a, acc => popcnt32 k (a >>> 1) (acc + (a &&& 1).toNat)

/-- Number of leading zero bits in a 64-bit word; 64 if zero. -/
def clz64 : Nat → UInt64 → Nat
  | 0, _ => 64
  | k + 1, a => if a &&& 0x8000000000000000 ≠ 0 then 64 - (k + 1) else clz64 k (a <<< 1)

/-- Number of trailing zero bits in a 64-bit word; 64 if zero. -/
def ctz64 : Nat → UInt64 → Nat
  | 0, _ => 64
  | k + 1, a => if a &&& 1 ≠ 0 then 64 - (k + 1) else ctz64 k (a >>> 1)

/-- Number of one bits in a 64-bit word. -/
def popcnt64 : Nat → UInt64 → Nat → Nat
  | 0, _, acc => acc
  | k + 1, a, acc => popcnt64 k (a >>> 1) (acc + (a &&& 1).toNat)

/-- Sign-extend the low `bits` bits of `n` to a signed `Int`. -/
def signExtend (n : Nat) (bits : Nat) : Int :=
  let half := 2 ^ (bits - 1)
  let bound := 2 ^ bits
  if n ≥ half then (n : Int) - (bound : Int) else (n : Int)

/-- Whether `ht` is one of the abstract heap types in the `any` hierarchy
(the only ones a managed `anyref` can inhabit), as opposed to the
`func`/`extern` families. Concrete struct/array type indices also live
under `any`. -/
def GcHeapType.inAnyHierarchy : GcHeapType → Bool
  | .any | .eq | .i31 | .structT | .arrayT | .noneT | .concrete _ => true
  | _ => false

/-- Decide whether a (non-null) managed reference `r` is a subtype of the
abstract heap type `ht`. Concrete struct/array type indices are resolved
against the module's GC type definitions and their declared supertypes. -/
def AnyRef.matchesHeap (m : Module) (st : Store α) (ht : GcHeapType) : AnyRef → Bool
  | .i31 _ => match ht with
    | .any | .eq | .i31 => true
    | _ => false
  | .struct addr => match ht with
    | .any | .eq | .structT => true
    | .concrete t => match st.gcHeap[addr]? with
      | some obj => m.gcTypeSubtype obj.typeIdx t
      | none     => false
    | _ => false
  | .array addr => match ht with
    | .any | .eq | .arrayT => true
    | .concrete t => match st.gcHeap[addr]? with
      | some obj => m.gcTypeSubtype obj.typeIdx t
      | none     => false
    | _ => false

/-- Whether reference value `v` matches the target reference type
`(ref null?ₙ ht)` used by `ref.test`/`ref.cast`/`br_on_cast`. The null
reference matches exactly when the target is nullable and `ht` is in the
same (any vs func vs extern) bottom family.

A non-null funcref matches the abstract `func` heap type always, and a
concrete target `(ref $ft)` when the function's declared type is a
subtype of `$ft` (issue #96). When the declared type is unrecorded
(`funcTypeIdx? = none`, hand-built modules) the check degrades to
structural equality of the function's signature against the target's
composite type, mirroring `Module.indirectCallTypeOk`. -/
def gcRefMatches (m : Module) (st : Store α) (nullable : Bool)
    (ht : GcHeapType) : Value → Bool
  | .anyref none      => nullable && ht.inAnyHierarchy
  | .anyref (some r)  => r.matchesHeap m st ht
  | .funcref none     =>
    nullable &&
    (ht == .func || ht == .noFunc ||
     -- Null also inhabits every nullable *concrete* function type: the
     -- null funcref has type `nofunc`, the bottom of the func family.
     (match ht with
      | .concrete t => match m.gcComposite? t with
        | some (.func _) => true
        | _ => false
      | _ => false))
  | .funcref (some f) => match ht with
    | .func       => true
    | .concrete t =>
      (match m.funcTypeIdx? f with
       | some src => m.gcTypeSubtype src t
       | none     => match m.funcSig? f, m.gcComposite? t with
         | some fn, some (.func ty) => fn == ty
         | _, _ => false)
    | _ => false
  | .externref none   => nullable && (ht == .extern || ht == .noExtern)
  | .externref (some _) => ht == .extern
  | _                 => false

/-- Truncate a value to a packed field's width when storing it (GC
proposal); non-packed fields store the value unchanged. -/
def FieldType.pack (ft : FieldType) (v : Value) : Value :=
  match ft.storage, v with
  | .packed 8,  .i32 x => .i32 (x &&& 0xff)
  | .packed 16, .i32 x => .i32 (x &&& 0xffff)
  | _,          _      => v

/-- Read a field/element with sign extension (`*.get_s`): a packed
`i8`/`i16` slot is sign-extended to `i32`; everything else is unchanged. -/
def FieldType.readS (ft : FieldType) (v : Value) : Value :=
  match ft.storage, v with
  | .packed 8,  .i32 x => .i32 (if x &&& 0x80 ≠ 0 then x ||| 0xffffff00 else x)
  | .packed 16, .i32 x => .i32 (if x &&& 0x8000 ≠ 0 then x ||| 0xffff0000 else x)
  | _,          _      => v

/-- Read `n` little-endian bytes from a byte list as a `Nat`. Missing bytes
read as 0 (callers bounds-check first). -/
def readBytesLE (bytes : List UInt8) (off n : Nat) : Nat :=
  (List.range n).foldl (fun acc i => acc + (bytes[off + i]?.getD 0).toNat * 2 ^ (8 * i)) 0

/-- Read one storage-type element from a byte list (little-endian), for
`array.new_data` / `array.init_data`. -/
def readStorageLE (storage : StorageType) (bytes : List UInt8) (off : Nat) : Value :=
  let n := readBytesLE bytes off storage.byteSize
  match storage with
  | .packed _ => .i32 (UInt32.ofNat n)
  | .val .i32 => .i32 (UInt32.ofNat n)
  | .val .i64 => .i64 (UInt64.ofNat n)
  | .val .f32 => .f32 (UInt32.ofNat n)
  | .val .f64 => .f64 (UInt64.ofNat n)
  | .val _    => .i32 0

/-- Evaluate a simple element-segment item constant expression to its
reference value (GC proposal). Covers the forms element segments use:
`ref.func`; the null refs `ref.null func`/`extern`/`exn` and `ref.null`
of a GC heap type; the `i32`/`i64` scalar constants; and `ref.i31` of an
`i32.const`. Heap-allocating items (`struct.new`) are not handled here. -/
def evalConstRef : Program → Option Value
  | [.refFunc f]                 => some (.funcref (some f))
  | [.refNull]                   => some (.funcref none)
  | [.refNullExtern]             => some (.externref none)
  | [.refNullExn]                => some (.exnref none)
  | [.gc .refNullAny]            => some (.anyref none)
  | [.const n]                   => some (.i32 n)
  | [.constI64 n]                => some (.i64 n)
  | [.const n, .gc .refI31]      => some (.anyref (some (.i31 (n &&& 0x7fffffff))))
  | _                            => none

/-- The reference values a (passive, non-dropped) element segment yields,
preferring decoded GC const-expr items and falling back to funcref
indices. -/
def ElementSegment.values (seg : ElementSegment) : List Value :=
  if seg.exprs.isEmpty then seg.funcs.map Value.funcref
  else seg.exprs.map (fun e => (evalConstRef e).getD (.anyref none))

/-- Execute one GC-proposal instruction. These never consume fuel or
recurse into `exec`/`run` — `struct.new`/`array.new` allocate on
`st.gcHeap`, the accessors read/update it, and `ref.test`/`ref.cast` decide
subtyping via `gcRefMatches` — so they live outside the fuel-threaded
`execOne` mutual block, dispatched from it by a single `gc` arm. -/
def execGcOp (m : Module) (st : Store α) (s : Locals) : GcOp → Continuation α
  | .refNullAny => .Fallthrough st { s with values := .anyref none :: s.values }
  | .refI31 => match s.values with
    | .i32 x :: vs =>
      .Fallthrough st { s with values := .anyref (some (.i31 (x &&& 0x7fffffff))) :: vs }
    | _ => .Invalid "refI31: ill-shaped operand stack"
  | .i31GetU => match s.values with
    | .anyref (some (.i31 n)) :: vs =>
      .Fallthrough st { s with values := .i32 n :: vs }
    | .anyref none :: _ => .Trap st "null i31 reference"
    | _ => .Invalid "i31GetU: ill-shaped operand stack"
  | .i31GetS => match s.values with
    | .anyref (some (.i31 n)) :: vs =>
      let signed := if n &&& 0x40000000 ≠ 0 then n ||| 0x80000000 else n
      .Fallthrough st { s with values := .i32 signed :: vs }
    | .anyref none :: _ => .Trap st "null i31 reference"
    | _ => .Invalid "i31GetS: ill-shaped operand stack"
  | .refEq => match s.values with
    | .anyref a :: .anyref b :: vs =>
      .Fallthrough st { s with values := .i32 (if a == b then 1 else 0) :: vs }
    | _ => .Invalid "refEq: ill-shaped operand stack"
  | .refTest nullable ht => match s.values with
    | v :: vs => match v with
      | .anyref _ | .funcref _ | .externref _ | .exnref _ =>
        .Fallthrough st
          { s with values := .i32 (if gcRefMatches m st nullable ht v then 1 else 0) :: vs }
      | _ => .Invalid "refTest: non-reference operand"
    | _ => .Invalid "refTest: ill-shaped operand stack"
  | .refCast nullable ht => match s.values with
    | v :: vs => match v with
      | .anyref _ | .funcref _ | .externref _ | .exnref _ =>
        if gcRefMatches m st nullable ht v then
          .Fallthrough st { s with values := v :: vs }
        else .Trap st "cast failure"
      | _ => .Invalid "refCast: non-reference operand"
    | _ => .Invalid "refCast: ill-shaped operand stack"
  -- `br_on_cast`/`br_on_cast_fail`: the ref stays on the operand stack in
  -- both the taken and the fall-through case.
  | .brOnCast label nullable ht => match s.values with
    | v :: _ =>
      if gcRefMatches m st nullable ht v then .Break label st s else .Fallthrough st s
    | _ => .Invalid "brOnCast: ill-shaped operand stack"
  | .brOnCastFail label nullable ht => match s.values with
    | v :: _ =>
      if gcRefMatches m st nullable ht v then .Fallthrough st s else .Break label st s
    | _ => .Invalid "brOnCastFail: ill-shaped operand stack"
  -- Structs. `struct.new` pops one value per field (last field on top).
  | .structNew t => match m.structFields? t with
    | some fields =>
      let n := fields.length
      if s.values.length < n then .Invalid "structNew: operand stack underflow"
      else
        let args := (s.values.take n).reverse
        let packed := (fields.zip args).map (fun (ft, v) => ft.pack v)
        .Fallthrough { st with gcHeap := st.gcHeap ++ [.struct t packed] }
          { s with values := .anyref (some (.struct st.gcHeap.length)) :: s.values.drop n }
    | none => .Invalid "structNew: not a struct type"
  | .structNewDefault t => match m.structFields? t with
    | some fields =>
      .Fallthrough
        { st with gcHeap := st.gcHeap ++ [.struct t (fields.map (·.storage.zero))] }
        { s with values := .anyref (some (.struct st.gcHeap.length)) :: s.values }
    | none => .Invalid "structNewDefault: not a struct type"
  | .structGet _ f => match s.values with
    | .anyref (some (.struct addr)) :: vs => match st.gcHeap[addr]? with
      | some (.struct _ fields) => match fields[f]? with
        | some v => .Fallthrough st { s with values := v :: vs }
        | none   => .Invalid "structGet: field index out of range"
      | _ => .Invalid "structGet: not a struct"
    | .anyref none :: _ => .Trap st "null structure reference"
    | _ => .Invalid "structGet: ill-shaped operand stack"
  | .structGetU _ f => match s.values with
    | .anyref (some (.struct addr)) :: vs => match st.gcHeap[addr]? with
      | some (.struct _ fields) => match fields[f]? with
        | some v => .Fallthrough st { s with values := v :: vs }
        | none   => .Invalid "structGetU: field index out of range"
      | _ => .Invalid "structGetU: not a struct"
    | .anyref none :: _ => .Trap st "null structure reference"
    | _ => .Invalid "structGetU: ill-shaped operand stack"
  | .structGetS t f => match s.values with
    | .anyref (some (.struct addr)) :: vs => match st.gcHeap[addr]? with
      | some (.struct _ fields) => match fields[f]?, m.structField? t f with
        | some v, some ft => .Fallthrough st { s with values := ft.readS v :: vs }
        | _, _ => .Invalid "structGetS: field index out of range"
      | _ => .Invalid "structGetS: not a struct"
    | .anyref none :: _ => .Trap st "null structure reference"
    | _ => .Invalid "structGetS: ill-shaped operand stack"
  | .structSet t f => match s.values with
    | val :: .anyref (some (.struct addr)) :: vs => match st.gcHeap[addr]? with
      | some (.struct ty fields) =>
        let pval := match m.structField? t f with | some ft => ft.pack val | none => val
        .Fallthrough { st with gcHeap := st.gcHeap.set addr (.struct ty (fields.set f pval)) }
          { s with values := vs }
      | _ => .Invalid "structSet: not a struct"
    | _ :: .anyref none :: _ => .Trap st "null structure reference"
    | _ => .Invalid "structSet: ill-shaped operand stack"
  -- Arrays.
  | .arrayNew t => match s.values with
    | .i32 len :: init :: vs =>
      let pinit := match m.arrayElem? t with | some ft => ft.pack init | none => init
      .Fallthrough { st with gcHeap := st.gcHeap ++ [.array t (List.replicate len.toNat pinit)] }
        { s with values := .anyref (some (.array st.gcHeap.length)) :: vs }
    | _ => .Invalid "arrayNew: ill-shaped operand stack"
  | .arrayNewDefault t => match s.values with
    | .i32 len :: vs =>
      let z := match m.arrayElem? t with | some ft => ft.storage.zero | none => .i32 0
      .Fallthrough { st with gcHeap := st.gcHeap ++ [.array t (List.replicate len.toNat z)] }
        { s with values := .anyref (some (.array st.gcHeap.length)) :: vs }
    | _ => .Invalid "arrayNewDefault: ill-shaped operand stack"
  | .arrayNewFixed t n =>
    if s.values.length < n then .Invalid "arrayNewFixed: operand stack underflow"
    else
      let elems := (s.values.take n).reverse
      let pelems := match m.arrayElem? t with | some ft => elems.map ft.pack | none => elems
      .Fallthrough { st with gcHeap := st.gcHeap ++ [.array t pelems] }
        { s with values := .anyref (some (.array st.gcHeap.length)) :: s.values.drop n }
  | .arrayGet _ => match s.values with
    | .i32 idx :: .anyref (some (.array addr)) :: vs => match st.gcHeap[addr]? with
      | some (.array _ elems) => match elems[idx.toNat]? with
        | some v => .Fallthrough st { s with values := v :: vs }
        | none   => .Trap st "out of bounds array access"
      | _ => .Invalid "arrayGet: not an array"
    | _ :: .anyref none :: _ => .Trap st "null array reference"
    | _ => .Invalid "arrayGet: ill-shaped operand stack"
  | .arrayGetU _ => match s.values with
    | .i32 idx :: .anyref (some (.array addr)) :: vs => match st.gcHeap[addr]? with
      | some (.array _ elems) => match elems[idx.toNat]? with
        | some v => .Fallthrough st { s with values := v :: vs }
        | none   => .Trap st "out of bounds array access"
      | _ => .Invalid "arrayGetU: not an array"
    | _ :: .anyref none :: _ => .Trap st "null array reference"
    | _ => .Invalid "arrayGetU: ill-shaped operand stack"
  | .arrayGetS t => match s.values with
    | .i32 idx :: .anyref (some (.array addr)) :: vs => match st.gcHeap[addr]? with
      | some (.array _ elems) => match elems[idx.toNat]?, m.arrayElem? t with
        | some v, some ft => .Fallthrough st { s with values := ft.readS v :: vs }
        | _, _ => .Trap st "out of bounds array access"
      | _ => .Invalid "arrayGetS: not an array"
    | _ :: .anyref none :: _ => .Trap st "null array reference"
    | _ => .Invalid "arrayGetS: ill-shaped operand stack"
  | .arraySet t => match s.values with
    | val :: .i32 idx :: .anyref (some (.array addr)) :: vs => match st.gcHeap[addr]? with
      | some (.array ty elems) =>
        if idx.toNat ≥ elems.length then .Trap st "out of bounds array access"
        else
          let pval := match m.arrayElem? t with | some ft => ft.pack val | none => val
          .Fallthrough { st with gcHeap := st.gcHeap.set addr (.array ty (elems.set idx.toNat pval)) }
            { s with values := vs }
      | _ => .Invalid "arraySet: not an array"
    | _ :: _ :: .anyref none :: _ => .Trap st "null array reference"
    | _ => .Invalid "arraySet: ill-shaped operand stack"
  | .arrayLen => match s.values with
    | .anyref (some (.array addr)) :: vs => match st.gcHeap[addr]? with
      | some (.array _ elems) =>
        .Fallthrough st { s with values := .i32 (UInt32.ofNat elems.length) :: vs }
      | _ => .Invalid "arrayLen: not an array"
    | .anyref none :: _ => .Trap st "null array reference"
    | _ => .Invalid "arrayLen: ill-shaped operand stack"
  -- `array.fill $t`: [arrayref, d, val, n] → fill elems[d..d+n) with val.
  | .arrayFill t => match s.values with
    | .i32 n :: val :: .i32 d :: .anyref (some (.array addr)) :: vs => match st.gcHeap[addr]? with
      | some (.array ty elems) =>
        if d.toNat + n.toNat > elems.length then .Trap st "out of bounds array access"
        else
          let pval := match m.arrayElem? t with | some ft => ft.pack val | none => val
          let elems' := (List.range elems.length).map fun i =>
            if d.toNat ≤ i && i < d.toNat + n.toNat then pval else elems[i]!
          .Fallthrough { st with gcHeap := st.gcHeap.set addr (.array ty elems') } { s with values := vs }
      | _ => .Invalid "arrayFill: not an array"
    | _ :: _ :: _ :: .anyref none :: _ => .Trap st "null array reference"
    | _ => .Invalid "arrayFill: ill-shaped operand stack"
  -- `array.copy $dt $st`: [dst, dstD, src, srcD, n] → copy elements.
  | .arrayCopy _ _ => match s.values with
    | .i32 n :: .i32 srcD :: .anyref (some (.array srcAddr)) :: .i32 dstD
        :: .anyref (some (.array dstAddr)) :: vs =>
      match st.gcHeap[srcAddr]?, st.gcHeap[dstAddr]? with
      | some (.array _ srcElems), some (.array dty dstElems) =>
        if srcD.toNat + n.toNat > srcElems.length || dstD.toNat + n.toNat > dstElems.length then
          .Trap st "out of bounds array access"
        else
          let dstElems' := (List.range dstElems.length).map fun i =>
            if dstD.toNat ≤ i && i < dstD.toNat + n.toNat then srcElems[srcD.toNat + (i - dstD.toNat)]!
            else dstElems[i]!
          .Fallthrough { st with gcHeap := st.gcHeap.set dstAddr (.array dty dstElems') } { s with values := vs }
      | _, _ => .Invalid "arrayCopy: not an array"
    -- A null source or destination array reference traps, even when n = 0,
    -- mirroring every other array op (arrayGet/Set/Fill/...).
    | .i32 _ :: .i32 _ :: .anyref none :: _ => .Trap st "null array reference"
    | .i32 _ :: .i32 _ :: _ :: .i32 _ :: .anyref none :: _ => .Trap st "null array reference"
    | _ => .Invalid "arrayCopy: ill-shaped operand stack"
  -- `array.new_data $t $d`: [off, n] → array of n elements read from data
  -- segment `d` (little-endian, sized by the element storage type).
  | .arrayNewData t d => match s.values with
    | .i32 n :: .i32 off :: vs => match m.arrayElem? t, st.dataSegments[d]? with
      | some ft, some (some bytes) =>
        let sz := ft.storage.byteSize
        if off.toNat + n.toNat * sz > bytes.length then .Trap st "out of bounds memory access"
        else
          let elems := (List.range n.toNat).map fun i => readStorageLE ft.storage bytes (off.toNat + i * sz)
          .Fallthrough { st with gcHeap := st.gcHeap ++ [.array t elems] }
            { s with values := .anyref (some (.array st.gcHeap.length)) :: vs }
      | _, _ => .Trap st "out of bounds memory access"
    | _ => .Invalid "arrayNewData: ill-shaped operand stack"
  -- `array.init_data $t $d`: [arrayref, d, off, n] → write into existing array.
  | .arrayInitData t d => match s.values with
    | .i32 n :: .i32 off :: .i32 dstD :: .anyref (some (.array addr)) :: vs =>
      match m.arrayElem? t, st.gcHeap[addr]?, st.dataSegments[d]? with
      | some ft, some (.array ty elems), some (some bytes) =>
        let sz := ft.storage.byteSize
        if off.toNat + n.toNat * sz > bytes.length || dstD.toNat + n.toNat > elems.length then
          .Trap st "out of bounds memory access"
        else
          let elems' := (List.range elems.length).map fun i =>
            if dstD.toNat ≤ i && i < dstD.toNat + n.toNat then
              readStorageLE ft.storage bytes (off.toNat + (i - dstD.toNat) * sz)
            else elems[i]!
          .Fallthrough { st with gcHeap := st.gcHeap.set addr (.array ty elems') } { s with values := vs }
      | _, _, _ => .Trap st "out of bounds memory access"
    | _ :: _ :: _ :: .anyref none :: _ => .Trap st "null array reference"
    | _ => .Invalid "arrayInitData: ill-shaped operand stack"
  -- `array.new_elem`/`array.init_elem`: element-segment-sourced arrays. Only
  -- funcref segments (stored as func indices) are modelled.
  | .arrayNewElem t e => match s.values with
    | .i32 n :: .i32 off :: vs => match st.elementSegments[e]?, m.elements[e]? with
      | some (some _), some seg =>
        let refs := seg.values
        if off.toNat + n.toNat > refs.length then .Trap st "out of bounds table access"
        else
          let elems := (List.range n.toNat).map fun i => refs[off.toNat + i]!
          .Fallthrough { st with gcHeap := st.gcHeap ++ [.array t elems] }
            { s with values := .anyref (some (.array st.gcHeap.length)) :: vs }
      | _, _ => .Trap st "out of bounds table access"
    | _ => .Invalid "arrayNewElem: ill-shaped operand stack"
  | .arrayInitElem _ e => match s.values with
    | .i32 n :: .i32 off :: .i32 dstD :: .anyref (some (.array addr)) :: vs =>
      match st.gcHeap[addr]?, st.elementSegments[e]?, m.elements[e]? with
      | some (.array ty elems), some (some _), some seg =>
        let refs := seg.values
        if off.toNat + n.toNat > refs.length || dstD.toNat + n.toNat > elems.length then
          .Trap st "out of bounds table access"
        else
          let elems' := (List.range elems.length).map fun i =>
            if dstD.toNat ≤ i && i < dstD.toNat + n.toNat then refs[off.toNat + (i - dstD.toNat)]!
            else elems[i]!
          .Fallthrough { st with gcHeap := st.gcHeap.set addr (.array ty elems') } { s with values := vs }
      | _, _, _ => .Trap st "out of bounds table access"
    | _ :: _ :: _ :: .anyref none :: _ => .Trap st "null array reference"
    | _ => .Invalid "arrayInitElem: ill-shaped operand stack"

/-! ## Big-step fuel-bounded interpreter.

Mutual recursion across three entry points:

* `execOne` runs a single instruction.
* `exec`    runs a `Program` (list of instructions) sequentially.
* `run`     runs a function call from a `Module` by index.

Stack-shape mismatches yield `Continuation.Invalid` — those should be ruled
out by a future validator; until then the interpreter defends against them
at runtime. Real Wasm traps (division by zero, signed-divide overflow,
`unreachable`) yield `Continuation.Trap` with a descriptive string. -/

mutual

def execOne (fuel : Nat) (m : Module) (st : Store α) (s : Locals) (inst : Instruction)
    (env : HostEnv α := {}) : Continuation α :=
  match fuel, inst with
    | 0, _ => .OutOfFuel

    -- Locals
    | _, Instruction.localGet i => match s.get i with
      | some v => .Fallthrough st { s with values := v :: s.values }
      | none   => .Invalid "localGet index out of bounds"
    | _, Instruction.localSet i => match s.values with
      | v :: vs => match s.set? i v with
        | some s => .Fallthrough st { s with values := vs }
        | none   => .Invalid "localSet index out of bounds"
      | _ => .Invalid "localSet with empty stack"

    -- Globals
    | _, Instruction.globalGet i => match st.globals.globals[i]? with
      | some v => .Fallthrough st { s with values := v :: s.values }
      | none   => .Invalid "globalGet index out of bounds"
    | _, Instruction.globalSet i => match s.values with
      | v :: vs => match st.globals.globals[i]? with
        | some _ =>
          .Fallthrough { st with globals := { globals := st.globals.globals.set i v } }
                       { s with values := vs }
        | none => .Invalid "globalSet index out of bounds"
      | _ => .Invalid "globalSet with empty stack"

    -- Constants
    | _, Instruction.const v    => .Fallthrough st { s with values := .i32 v :: s.values }
    | _, Instruction.constI64 v => .Fallthrough st { s with values := .i64 v :: s.values }

    -- i32 arithmetic
    | _, Instruction.add => match s.values with
      | .i32 a :: .i32 b :: vs => .Fallthrough st { s with values := .i32 (a + b) :: vs }
      | _ => .Invalid "add: ill-shaped operand stack"
    | _, Instruction.sub => match s.values with
      | .i32 a :: .i32 b :: vs => .Fallthrough st { s with values := .i32 (b - a) :: vs }
      | _ => .Invalid "sub: ill-shaped operand stack"
    | _, Instruction.mul => match s.values with
      | .i32 a :: .i32 b :: vs => .Fallthrough st { s with values := .i32 (a * b) :: vs }
      | _ => .Invalid "mul: ill-shaped operand stack"
    | _, Instruction.divU => match s.values with
      | .i32 b :: .i32 a :: vs =>
        if b = 0 then .Trap st "integer divide by zero"
        else .Fallthrough st { s with values := .i32 (a / b) :: vs }
      | _ => .Invalid "divU: ill-shaped operand stack"
    | _, Instruction.divS => match s.values with
      | .i32 b :: .i32 a :: vs =>
        if b = 0 then .Trap st "integer divide by zero"
        else if a = 0x80000000 ∧ b = 0xFFFFFFFF then .Trap st "integer overflow"
        else
          let q : UInt32 := (Int32.ofInt (Int.tdiv a.toInt32.toInt b.toInt32.toInt)).toUInt32
          .Fallthrough st { s with values := .i32 q :: vs }
      | _ => .Invalid "divS: ill-shaped operand stack"
    | _, Instruction.remU => match s.values with
      | .i32 b :: .i32 a :: vs =>
        if b = 0 then .Trap st "integer divide by zero"
        else .Fallthrough st { s with values := .i32 (a % b) :: vs }
      | _ => .Invalid "remU: ill-shaped operand stack"
    | _, Instruction.remS => match s.values with
      | .i32 b :: .i32 a :: vs =>
        if b = 0 then .Trap st "integer divide by zero"
        else
          let r' : UInt32 := (Int32.ofInt (Int.tmod a.toInt32.toInt b.toInt32.toInt)).toUInt32
          .Fallthrough st { s with values := .i32 r' :: vs }
      | _ => .Invalid "remS: ill-shaped operand stack"

    -- i32 comparison
    | _, Instruction.eqz => match s.values with
      | .i32 a :: vs => .Fallthrough st { s with values := .i32 (if a = 0 then 1 else 0) :: vs }
      | _ => .Invalid "eqz: ill-shaped operand stack"
    | _, Instruction.eq => match s.values with
      | .i32 b :: .i32 a :: vs => .Fallthrough st { s with values := .i32 (if a = b then 1 else 0) :: vs }
      | _ => .Invalid "eq: ill-shaped operand stack"
    | _, Instruction.ne => match s.values with
      | .i32 b :: .i32 a :: vs => .Fallthrough st { s with values := .i32 (if a ≠ b then 1 else 0) :: vs }
      | _ => .Invalid "ne: ill-shaped operand stack"
    | _, Instruction.ltU => match s.values with
      | .i32 b :: .i32 a :: vs => .Fallthrough st { s with values := .i32 (if a < b then 1 else 0) :: vs }
      | _ => .Invalid "ltU: ill-shaped operand stack"
    | _, Instruction.ltS => match s.values with
      | .i32 b :: .i32 a :: vs => .Fallthrough st { s with values := .i32 (if a.toInt32 < b.toInt32 then 1 else 0) :: vs }
      | _ => .Invalid "ltS: ill-shaped operand stack"
    | _, Instruction.gtU => match s.values with
      | .i32 b :: .i32 a :: vs => .Fallthrough st { s with values := .i32 (if a > b then 1 else 0) :: vs }
      | _ => .Invalid "gtU: ill-shaped operand stack"
    | _, Instruction.gtS => match s.values with
      | .i32 b :: .i32 a :: vs => .Fallthrough st { s with values := .i32 (if a.toInt32 > b.toInt32 then 1 else 0) :: vs }
      | _ => .Invalid "gtS: ill-shaped operand stack"
    | _, Instruction.leU => match s.values with
      | .i32 b :: .i32 a :: vs => .Fallthrough st { s with values := .i32 (if a ≤ b then 1 else 0) :: vs }
      | _ => .Invalid "leU: ill-shaped operand stack"
    | _, Instruction.leS => match s.values with
      | .i32 b :: .i32 a :: vs => .Fallthrough st { s with values := .i32 (if a.toInt32 ≤ b.toInt32 then 1 else 0) :: vs }
      | _ => .Invalid "leS: ill-shaped operand stack"
    | _, Instruction.geU => match s.values with
      | .i32 b :: .i32 a :: vs => .Fallthrough st { s with values := .i32 (if a ≥ b then 1 else 0) :: vs }
      | _ => .Invalid "geU: ill-shaped operand stack"
    | _, Instruction.geS => match s.values with
      | .i32 b :: .i32 a :: vs => .Fallthrough st { s with values := .i32 (if a.toInt32 ≥ b.toInt32 then 1 else 0) :: vs }
      | _ => .Invalid "geS: ill-shaped operand stack"

    -- i32 bitwise / shift / counting
    | _, Instruction.and => match s.values with
      | .i32 a :: .i32 b :: vs => .Fallthrough st { s with values := .i32 (a &&& b) :: vs }
      | _ => .Invalid "and: ill-shaped operand stack"
    | _, Instruction.or => match s.values with
      | .i32 b :: .i32 a :: vs => .Fallthrough st { s with values := .i32 (a ||| b) :: vs }
      | _ => .Invalid "or: ill-shaped operand stack"
    | _, Instruction.xor => match s.values with
      | .i32 b :: .i32 a :: vs => .Fallthrough st { s with values := .i32 (a ^^^ b) :: vs }
      | _ => .Invalid "xor: ill-shaped operand stack"
    | _, Instruction.shl => match s.values with
      | .i32 b :: .i32 a :: vs =>
        let k := b % 32
        .Fallthrough st { s with values := .i32 (a <<< k) :: vs }
      | _ => .Invalid "shl: ill-shaped operand stack"
    | _, Instruction.shrU => match s.values with
      | .i32 b :: .i32 a :: vs =>
        let k := b % 32
        .Fallthrough st { s with values := .i32 (a >>> k) :: vs }
      | _ => .Invalid "shrU: ill-shaped operand stack"
    | _, Instruction.shrS => match s.values with
      | .i32 b :: .i32 a :: vs =>
        let k : Nat := (b % 32).toNat
        let r' : UInt32 := UInt32.ofNat (BitVec.sshiftRight a.toBitVec k).toNat
        .Fallthrough st { s with values := .i32 r' :: vs }
      | _ => .Invalid "shrS: ill-shaped operand stack"
    | _, Instruction.rotl => match s.values with
      | .i32 b :: .i32 a :: vs =>
        let k := b % 32
        let r' : UInt32 := if k = 0 then a else (a <<< k) ||| (a >>> (32 - k))
        .Fallthrough st { s with values := .i32 r' :: vs }
      | _ => .Invalid "rotl: ill-shaped operand stack"
    | _, Instruction.rotr => match s.values with
      | .i32 b :: .i32 a :: vs =>
        let k := b % 32
        let r' : UInt32 := if k = 0 then a else (a >>> k) ||| (a <<< (32 - k))
        .Fallthrough st { s with values := .i32 r' :: vs }
      | _ => .Invalid "rotr: ill-shaped operand stack"
    | _, Instruction.clz => match s.values with
      | .i32 a :: vs => .Fallthrough st { s with values := .i32 (UInt32.ofNat (clz32 32 a)) :: vs }
      | _ => .Invalid "clz: ill-shaped operand stack"
    | _, Instruction.ctz => match s.values with
      | .i32 a :: vs => .Fallthrough st { s with values := .i32 (UInt32.ofNat (ctz32 32 a)) :: vs }
      | _ => .Invalid "ctz: ill-shaped operand stack"
    | _, Instruction.popcnt => match s.values with
      | .i32 a :: vs => .Fallthrough st { s with values := .i32 (UInt32.ofNat (popcnt32 32 a 0)) :: vs }
      | _ => .Invalid "popcnt: ill-shaped operand stack"

    -- i64 arithmetic
    | _, Instruction.addI64 => match s.values with
      | .i64 b :: .i64 a :: vs => .Fallthrough st { s with values := .i64 (a + b) :: vs }
      | _ => .Invalid "addI64: ill-shaped operand stack"
    | _, Instruction.subI64 => match s.values with
      | .i64 b :: .i64 a :: vs => .Fallthrough st { s with values := .i64 (a - b) :: vs }
      | _ => .Invalid "subI64: ill-shaped operand stack"
    | _, Instruction.mulI64 => match s.values with
      | .i64 b :: .i64 a :: vs => .Fallthrough st { s with values := .i64 (a * b) :: vs }
      | _ => .Invalid "mulI64: ill-shaped operand stack"
    | _, Instruction.divUI64 => match s.values with
      | .i64 b :: .i64 a :: vs =>
        if b = 0 then .Trap st "integer divide by zero"
        else .Fallthrough st { s with values := .i64 (a / b) :: vs }
      | _ => .Invalid "divUI64: ill-shaped operand stack"
    | _, Instruction.divSI64 => match s.values with
      | .i64 b :: .i64 a :: vs =>
        if b = 0 then .Trap st "integer divide by zero"
        else if a = 0x8000000000000000 ∧ b = 0xFFFFFFFFFFFFFFFF then .Trap st "integer overflow"
        else
          let q : UInt64 := (Int64.ofInt (Int.tdiv a.toInt64.toInt b.toInt64.toInt)).toUInt64
          .Fallthrough st { s with values := .i64 q :: vs }
      | _ => .Invalid "divSI64: ill-shaped operand stack"
    | _, Instruction.remUI64 => match s.values with
      | .i64 b :: .i64 a :: vs =>
        if b = 0 then .Trap st "integer divide by zero"
        else .Fallthrough st { s with values := .i64 (a % b) :: vs }
      | _ => .Invalid "remUI64: ill-shaped operand stack"
    | _, Instruction.remSI64 => match s.values with
      | .i64 b :: .i64 a :: vs =>
        if b = 0 then .Trap st "integer divide by zero"
        else
          let r' : UInt64 := (Int64.ofInt (Int.tmod a.toInt64.toInt b.toInt64.toInt)).toUInt64
          .Fallthrough st { s with values := .i64 r' :: vs }
      | _ => .Invalid "remSI64: ill-shaped operand stack"

    -- i64 comparison (result is i32 0/1)
    | _, Instruction.eqzI64 => match s.values with
      | .i64 a :: vs => .Fallthrough st { s with values := .i32 (if a = 0 then 1 else 0) :: vs }
      | _ => .Invalid "eqzI64: ill-shaped operand stack"
    | _, Instruction.eqI64 => match s.values with
      | .i64 b :: .i64 a :: vs => .Fallthrough st { s with values := .i32 (if a = b then 1 else 0) :: vs }
      | _ => .Invalid "eqI64: ill-shaped operand stack"
    | _, Instruction.neI64 => match s.values with
      | .i64 b :: .i64 a :: vs => .Fallthrough st { s with values := .i32 (if a ≠ b then 1 else 0) :: vs }
      | _ => .Invalid "neI64: ill-shaped operand stack"
    | _, Instruction.ltUI64 => match s.values with
      | .i64 b :: .i64 a :: vs => .Fallthrough st { s with values := .i32 (if a < b then 1 else 0) :: vs }
      | _ => .Invalid "ltUI64: ill-shaped operand stack"
    | _, Instruction.ltSI64 => match s.values with
      | .i64 b :: .i64 a :: vs => .Fallthrough st { s with values := .i32 (if a.toInt64 < b.toInt64 then 1 else 0) :: vs }
      | _ => .Invalid "ltSI64: ill-shaped operand stack"
    | _, Instruction.gtUI64 => match s.values with
      | .i64 b :: .i64 a :: vs => .Fallthrough st { s with values := .i32 (if a > b then 1 else 0) :: vs }
      | _ => .Invalid "gtUI64: ill-shaped operand stack"
    | _, Instruction.gtSI64 => match s.values with
      | .i64 b :: .i64 a :: vs => .Fallthrough st { s with values := .i32 (if a.toInt64 > b.toInt64 then 1 else 0) :: vs }
      | _ => .Invalid "gtSI64: ill-shaped operand stack"
    | _, Instruction.leUI64 => match s.values with
      | .i64 b :: .i64 a :: vs => .Fallthrough st { s with values := .i32 (if a ≤ b then 1 else 0) :: vs }
      | _ => .Invalid "leUI64: ill-shaped operand stack"
    | _, Instruction.leSI64 => match s.values with
      | .i64 b :: .i64 a :: vs => .Fallthrough st { s with values := .i32 (if a.toInt64 ≤ b.toInt64 then 1 else 0) :: vs }
      | _ => .Invalid "leSI64: ill-shaped operand stack"
    | _, Instruction.geUI64 => match s.values with
      | .i64 b :: .i64 a :: vs => .Fallthrough st { s with values := .i32 (if a ≥ b then 1 else 0) :: vs }
      | _ => .Invalid "geUI64: ill-shaped operand stack"
    | _, Instruction.geSI64 => match s.values with
      | .i64 b :: .i64 a :: vs => .Fallthrough st { s with values := .i32 (if a.toInt64 ≥ b.toInt64 then 1 else 0) :: vs }
      | _ => .Invalid "geSI64: ill-shaped operand stack"

    -- i64 bitwise / shift / counting
    | _, Instruction.andI64 => match s.values with
      | .i64 b :: .i64 a :: vs => .Fallthrough st { s with values := .i64 (a &&& b) :: vs }
      | _ => .Invalid "andI64: ill-shaped operand stack"
    | _, Instruction.orI64 => match s.values with
      | .i64 b :: .i64 a :: vs => .Fallthrough st { s with values := .i64 (a ||| b) :: vs }
      | _ => .Invalid "orI64: ill-shaped operand stack"
    | _, Instruction.xorI64 => match s.values with
      | .i64 b :: .i64 a :: vs => .Fallthrough st { s with values := .i64 (a ^^^ b) :: vs }
      | _ => .Invalid "xorI64: ill-shaped operand stack"
    | _, Instruction.shlI64 => match s.values with
      | .i64 b :: .i64 a :: vs =>
        let k := b % 64
        .Fallthrough st { s with values := .i64 (a <<< k) :: vs }
      | _ => .Invalid "shlI64: ill-shaped operand stack"
    | _, Instruction.shrUI64 => match s.values with
      | .i64 b :: .i64 a :: vs =>
        let k := b % 64
        .Fallthrough st { s with values := .i64 (a >>> k) :: vs }
      | _ => .Invalid "shrUI64: ill-shaped operand stack"
    | _, Instruction.shrSI64 => match s.values with
      | .i64 b :: .i64 a :: vs =>
        let k : Nat := (b % 64).toNat
        let r' : UInt64 := UInt64.ofNat (BitVec.sshiftRight a.toBitVec k).toNat
        .Fallthrough st { s with values := .i64 r' :: vs }
      | _ => .Invalid "shrSI64: ill-shaped operand stack"
    | _, Instruction.rotlI64 => match s.values with
      | .i64 b :: .i64 a :: vs =>
        let k := b % 64
        let r' : UInt64 := if k = 0 then a else (a <<< k) ||| (a >>> (64 - k))
        .Fallthrough st { s with values := .i64 r' :: vs }
      | _ => .Invalid "rotlI64: ill-shaped operand stack"
    | _, Instruction.rotrI64 => match s.values with
      | .i64 b :: .i64 a :: vs =>
        let k := b % 64
        let r' : UInt64 := if k = 0 then a else (a >>> k) ||| (a <<< (64 - k))
        .Fallthrough st { s with values := .i64 r' :: vs }
      | _ => .Invalid "rotrI64: ill-shaped operand stack"
    | _, Instruction.clzI64 => match s.values with
      | .i64 a :: vs => .Fallthrough st { s with values := .i64 (UInt64.ofNat (clz64 64 a)) :: vs }
      | _ => .Invalid "clzI64: ill-shaped operand stack"
    | _, Instruction.ctzI64 => match s.values with
      | .i64 a :: vs => .Fallthrough st { s with values := .i64 (UInt64.ofNat (ctz64 64 a)) :: vs }
      | _ => .Invalid "ctzI64: ill-shaped operand stack"
    | _, Instruction.popcntI64 => match s.values with
      | .i64 a :: vs => .Fallthrough st { s with values := .i64 (UInt64.ofNat (popcnt64 64 a 0)) :: vs }
      | _ => .Invalid "popcntI64: ill-shaped operand stack"

    -- Conversions / sign-extension
    | _, Instruction.wrapI64 => match s.values with
      | .i64 a :: vs => .Fallthrough st { s with values := .i32 (UInt32.ofNat (a.toNat % 2 ^ 32)) :: vs }
      | _ => .Invalid "wrapI64: ill-shaped operand stack"
    | _, Instruction.extendUI32 => match s.values with
      | .i32 a :: vs => .Fallthrough st { s with values := .i64 (UInt64.ofNat a.toNat) :: vs }
      | _ => .Invalid "extendUI32: ill-shaped operand stack"
    | _, Instruction.extendSI32 => match s.values with
      | .i32 a :: vs => .Fallthrough st { s with values := .i64 ((Int64.ofInt a.toInt32.toInt).toUInt64) :: vs }
      | _ => .Invalid "extendSI32: ill-shaped operand stack"
    | _, Instruction.extend8S => match s.values with
      | .i32 a :: vs =>
        let r' : UInt32 := (Int32.ofInt (signExtend (a.toNat % 256) 8)).toUInt32
        .Fallthrough st { s with values := .i32 r' :: vs }
      | _ => .Invalid "extend8S: ill-shaped operand stack"
    | _, Instruction.extend16S => match s.values with
      | .i32 a :: vs =>
        let r' : UInt32 := (Int32.ofInt (signExtend (a.toNat % 65536) 16)).toUInt32
        .Fallthrough st { s with values := .i32 r' :: vs }
      | _ => .Invalid "extend16S: ill-shaped operand stack"
    | _, Instruction.extend8SI64 => match s.values with
      | .i64 a :: vs =>
        let r' : UInt64 := (Int64.ofInt (signExtend (a.toNat % 256) 8)).toUInt64
        .Fallthrough st { s with values := .i64 r' :: vs }
      | _ => .Invalid "extend8SI64: ill-shaped operand stack"
    | _, Instruction.extend16SI64 => match s.values with
      | .i64 a :: vs =>
        let r' : UInt64 := (Int64.ofInt (signExtend (a.toNat % 65536) 16)).toUInt64
        .Fallthrough st { s with values := .i64 r' :: vs }
      | _ => .Invalid "extend16SI64: ill-shaped operand stack"
    | _, Instruction.extend32SI64 => match s.values with
      | .i64 a :: vs =>
        let r' : UInt64 := (Int64.ofInt (signExtend (a.toNat % 2 ^ 32) 32)).toUInt64
        .Fallthrough st { s with values := .i64 r' :: vs }
      | _ => .Invalid "extend32SI64: ill-shaped operand stack"

    -- Float constants
    | _, Instruction.f32Const v => .Fallthrough st { s with values := .f32 v :: s.values }
    | _, Instruction.f64Const v => .Fallthrough st { s with values := .f64 v :: s.values }

    -- f32 arithmetic. The top operand is `b`, the one below it `a`; results
    -- follow the wasm convention `a ⊘ b` (`sub` is `a - b`, `div` is `a / b`).
    | _, Instruction.f32Add => match s.values with
      | .f32 b :: .f32 a :: vs => .Fallthrough st { s with values := .f32 (f32Add a b) :: vs }
      | _ => .Invalid "f32Add: ill-shaped operand stack"
    | _, Instruction.f32Sub => match s.values with
      | .f32 b :: .f32 a :: vs => .Fallthrough st { s with values := .f32 (f32Sub a b) :: vs }
      | _ => .Invalid "f32Sub: ill-shaped operand stack"
    | _, Instruction.f32Mul => match s.values with
      | .f32 b :: .f32 a :: vs => .Fallthrough st { s with values := .f32 (f32Mul a b) :: vs }
      | _ => .Invalid "f32Mul: ill-shaped operand stack"
    | _, Instruction.f32Div => match s.values with
      | .f32 b :: .f32 a :: vs => .Fallthrough st { s with values := .f32 (f32Div a b) :: vs }
      | _ => .Invalid "f32Div: ill-shaped operand stack"
    | _, Instruction.f32Min => match s.values with
      | .f32 b :: .f32 a :: vs => .Fallthrough st { s with values := .f32 (f32Min a b) :: vs }
      | _ => .Invalid "f32Min: ill-shaped operand stack"
    | _, Instruction.f32Max => match s.values with
      | .f32 b :: .f32 a :: vs => .Fallthrough st { s with values := .f32 (f32Max a b) :: vs }
      | _ => .Invalid "f32Max: ill-shaped operand stack"
    | _, Instruction.f32Copysign => match s.values with
      | .f32 b :: .f32 a :: vs => .Fallthrough st { s with values := .f32 (f32Copysign a b) :: vs }
      | _ => .Invalid "f32Copysign: ill-shaped operand stack"

    -- f64 arithmetic
    | _, Instruction.f64Add => match s.values with
      | .f64 b :: .f64 a :: vs => .Fallthrough st { s with values := .f64 (f64Add a b) :: vs }
      | _ => .Invalid "f64Add: ill-shaped operand stack"
    | _, Instruction.f64Sub => match s.values with
      | .f64 b :: .f64 a :: vs => .Fallthrough st { s with values := .f64 (f64Sub a b) :: vs }
      | _ => .Invalid "f64Sub: ill-shaped operand stack"
    | _, Instruction.f64Mul => match s.values with
      | .f64 b :: .f64 a :: vs => .Fallthrough st { s with values := .f64 (f64Mul a b) :: vs }
      | _ => .Invalid "f64Mul: ill-shaped operand stack"
    | _, Instruction.f64Div => match s.values with
      | .f64 b :: .f64 a :: vs => .Fallthrough st { s with values := .f64 (f64Div a b) :: vs }
      | _ => .Invalid "f64Div: ill-shaped operand stack"
    | _, Instruction.f64Min => match s.values with
      | .f64 b :: .f64 a :: vs => .Fallthrough st { s with values := .f64 (f64Min a b) :: vs }
      | _ => .Invalid "f64Min: ill-shaped operand stack"
    | _, Instruction.f64Max => match s.values with
      | .f64 b :: .f64 a :: vs => .Fallthrough st { s with values := .f64 (f64Max a b) :: vs }
      | _ => .Invalid "f64Max: ill-shaped operand stack"
    | _, Instruction.f64Copysign => match s.values with
      | .f64 b :: .f64 a :: vs => .Fallthrough st { s with values := .f64 (f64Copysign a b) :: vs }
      | _ => .Invalid "f64Copysign: ill-shaped operand stack"

    -- f32 unary
    | _, Instruction.f32Abs => match s.values with
      | .f32 a :: vs => .Fallthrough st { s with values := .f32 (f32Abs a) :: vs }
      | _ => .Invalid "f32Abs: ill-shaped operand stack"
    | _, Instruction.f32Neg => match s.values with
      | .f32 a :: vs => .Fallthrough st { s with values := .f32 (f32Neg a) :: vs }
      | _ => .Invalid "f32Neg: ill-shaped operand stack"
    | _, Instruction.f32Sqrt => match s.values with
      | .f32 a :: vs => .Fallthrough st { s with values := .f32 (f32Sqrt a) :: vs }
      | _ => .Invalid "f32Sqrt: ill-shaped operand stack"
    | _, Instruction.f32Ceil => match s.values with
      | .f32 a :: vs => .Fallthrough st { s with values := .f32 (f32Ceil a) :: vs }
      | _ => .Invalid "f32Ceil: ill-shaped operand stack"
    | _, Instruction.f32Floor => match s.values with
      | .f32 a :: vs => .Fallthrough st { s with values := .f32 (f32Floor a) :: vs }
      | _ => .Invalid "f32Floor: ill-shaped operand stack"
    | _, Instruction.f32Trunc => match s.values with
      | .f32 a :: vs => .Fallthrough st { s with values := .f32 (f32Trunc a) :: vs }
      | _ => .Invalid "f32Trunc: ill-shaped operand stack"
    | _, Instruction.f32Nearest => match s.values with
      | .f32 a :: vs => .Fallthrough st { s with values := .f32 (f32Nearest a) :: vs }
      | _ => .Invalid "f32Nearest: ill-shaped operand stack"

    -- f64 unary
    | _, Instruction.f64Abs => match s.values with
      | .f64 a :: vs => .Fallthrough st { s with values := .f64 (f64Abs a) :: vs }
      | _ => .Invalid "f64Abs: ill-shaped operand stack"
    | _, Instruction.f64Neg => match s.values with
      | .f64 a :: vs => .Fallthrough st { s with values := .f64 (f64Neg a) :: vs }
      | _ => .Invalid "f64Neg: ill-shaped operand stack"
    | _, Instruction.f64Sqrt => match s.values with
      | .f64 a :: vs => .Fallthrough st { s with values := .f64 (f64Sqrt a) :: vs }
      | _ => .Invalid "f64Sqrt: ill-shaped operand stack"
    | _, Instruction.f64Ceil => match s.values with
      | .f64 a :: vs => .Fallthrough st { s with values := .f64 (f64Ceil a) :: vs }
      | _ => .Invalid "f64Ceil: ill-shaped operand stack"
    | _, Instruction.f64Floor => match s.values with
      | .f64 a :: vs => .Fallthrough st { s with values := .f64 (f64Floor a) :: vs }
      | _ => .Invalid "f64Floor: ill-shaped operand stack"
    | _, Instruction.f64Trunc => match s.values with
      | .f64 a :: vs => .Fallthrough st { s with values := .f64 (f64Trunc a) :: vs }
      | _ => .Invalid "f64Trunc: ill-shaped operand stack"
    | _, Instruction.f64Nearest => match s.values with
      | .f64 a :: vs => .Fallthrough st { s with values := .f64 (f64Nearest a) :: vs }
      | _ => .Invalid "f64Nearest: ill-shaped operand stack"

    -- f32 comparison (top = `b`, below = `a`; compares `a ⋈ b`)
    | _, Instruction.f32Eq => match s.values with
      | .f32 b :: .f32 a :: vs => .Fallthrough st { s with values := .i32 (if f32Eq a b then 1 else 0) :: vs }
      | _ => .Invalid "f32Eq: ill-shaped operand stack"
    | _, Instruction.f32Ne => match s.values with
      | .f32 b :: .f32 a :: vs => .Fallthrough st { s with values := .i32 (if f32Ne a b then 1 else 0) :: vs }
      | _ => .Invalid "f32Ne: ill-shaped operand stack"
    | _, Instruction.f32Lt => match s.values with
      | .f32 b :: .f32 a :: vs => .Fallthrough st { s with values := .i32 (if f32Lt a b then 1 else 0) :: vs }
      | _ => .Invalid "f32Lt: ill-shaped operand stack"
    | _, Instruction.f32Gt => match s.values with
      | .f32 b :: .f32 a :: vs => .Fallthrough st { s with values := .i32 (if f32Gt a b then 1 else 0) :: vs }
      | _ => .Invalid "f32Gt: ill-shaped operand stack"
    | _, Instruction.f32Le => match s.values with
      | .f32 b :: .f32 a :: vs => .Fallthrough st { s with values := .i32 (if f32Le a b then 1 else 0) :: vs }
      | _ => .Invalid "f32Le: ill-shaped operand stack"
    | _, Instruction.f32Ge => match s.values with
      | .f32 b :: .f32 a :: vs => .Fallthrough st { s with values := .i32 (if f32Ge a b then 1 else 0) :: vs }
      | _ => .Invalid "f32Ge: ill-shaped operand stack"

    -- f64 comparison
    | _, Instruction.f64Eq => match s.values with
      | .f64 b :: .f64 a :: vs => .Fallthrough st { s with values := .i32 (if f64Eq a b then 1 else 0) :: vs }
      | _ => .Invalid "f64Eq: ill-shaped operand stack"
    | _, Instruction.f64Ne => match s.values with
      | .f64 b :: .f64 a :: vs => .Fallthrough st { s with values := .i32 (if f64Ne a b then 1 else 0) :: vs }
      | _ => .Invalid "f64Ne: ill-shaped operand stack"
    | _, Instruction.f64Lt => match s.values with
      | .f64 b :: .f64 a :: vs => .Fallthrough st { s with values := .i32 (if f64Lt a b then 1 else 0) :: vs }
      | _ => .Invalid "f64Lt: ill-shaped operand stack"
    | _, Instruction.f64Gt => match s.values with
      | .f64 b :: .f64 a :: vs => .Fallthrough st { s with values := .i32 (if f64Gt a b then 1 else 0) :: vs }
      | _ => .Invalid "f64Gt: ill-shaped operand stack"
    | _, Instruction.f64Le => match s.values with
      | .f64 b :: .f64 a :: vs => .Fallthrough st { s with values := .i32 (if f64Le a b then 1 else 0) :: vs }
      | _ => .Invalid "f64Le: ill-shaped operand stack"
    | _, Instruction.f64Ge => match s.values with
      | .f64 b :: .f64 a :: vs => .Fallthrough st { s with values := .i32 (if f64Ge a b then 1 else 0) :: vs }
      | _ => .Invalid "f64Ge: ill-shaped operand stack"

    -- Float memory loads / stores. Bytes move unchanged through the same
    -- little-endian `Mem` words the i32/i64 accesses use.
    | _, .f32Load off => match s.values with
      | .i32 a :: vs =>
        if a.toNat + off.toNat + 4 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          .Fallthrough st { s with values := .f32 (st.mem.read32 (a + off)) :: vs }
      | .i64 a :: vs =>
        if a.toNat + off.toNat + 4 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          .Fallthrough st { s with values := .f32 (st.mem.read32 (a.toUInt32 + off)) :: vs }
      | _ => .Invalid "f32Load: ill-shaped operand stack"
    | _, .f64Load off => match s.values with
      | .i32 a :: vs =>
        if a.toNat + off.toNat + 8 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          .Fallthrough st { s with values := .f64 (st.mem.read64 (a + off)) :: vs }
      | .i64 a :: vs =>
        if a.toNat + off.toNat + 8 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          .Fallthrough st { s with values := .f64 (st.mem.read64 (a.toUInt32 + off)) :: vs }
      | _ => .Invalid "f64Load: ill-shaped operand stack"
    | _, .f32Store off => match s.values with
      | .f32 v :: .i32 a :: vs =>
        if a.toNat + off.toNat + 4 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          .Fallthrough { st with mem := st.mem.write32 (a + off) v } { s with values := vs }
      | .f32 v :: .i64 a :: vs =>
        if a.toNat + off.toNat + 4 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          .Fallthrough { st with mem := st.mem.write32 (a.toUInt32 + off) v } { s with values := vs }
      | _ => .Invalid "f32Store: ill-shaped operand stack"
    | _, .f64Store off => match s.values with
      | .f64 v :: .i32 a :: vs =>
        if a.toNat + off.toNat + 8 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          .Fallthrough { st with mem := st.mem.write64 (a + off) v } { s with values := vs }
      | .f64 v :: .i64 a :: vs =>
        if a.toNat + off.toNat + 8 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          .Fallthrough { st with mem := st.mem.write64 (a.toUInt32 + off) v } { s with values := vs }
      | _ => .Invalid "f64Store: ill-shaped operand stack"

    -- Integer → float
    | _, Instruction.f32ConvertI32S => match s.values with
      | .i32 a :: vs => .Fallthrough st { s with values := .f32 (f32ConvertI32S a) :: vs }
      | _ => .Invalid "f32ConvertI32S: ill-shaped operand stack"
    | _, Instruction.f32ConvertI32U => match s.values with
      | .i32 a :: vs => .Fallthrough st { s with values := .f32 (f32ConvertI32U a) :: vs }
      | _ => .Invalid "f32ConvertI32U: ill-shaped operand stack"
    | _, Instruction.f32ConvertI64S => match s.values with
      | .i64 a :: vs => .Fallthrough st { s with values := .f32 (f32ConvertI64S a) :: vs }
      | _ => .Invalid "f32ConvertI64S: ill-shaped operand stack"
    | _, Instruction.f32ConvertI64U => match s.values with
      | .i64 a :: vs => .Fallthrough st { s with values := .f32 (f32ConvertI64U a) :: vs }
      | _ => .Invalid "f32ConvertI64U: ill-shaped operand stack"
    | _, Instruction.f64ConvertI32S => match s.values with
      | .i32 a :: vs => .Fallthrough st { s with values := .f64 (f64ConvertI32S a) :: vs }
      | _ => .Invalid "f64ConvertI32S: ill-shaped operand stack"
    | _, Instruction.f64ConvertI32U => match s.values with
      | .i32 a :: vs => .Fallthrough st { s with values := .f64 (f64ConvertI32U a) :: vs }
      | _ => .Invalid "f64ConvertI32U: ill-shaped operand stack"
    | _, Instruction.f64ConvertI64S => match s.values with
      | .i64 a :: vs => .Fallthrough st { s with values := .f64 (f64ConvertI64S a) :: vs }
      | _ => .Invalid "f64ConvertI64S: ill-shaped operand stack"
    | _, Instruction.f64ConvertI64U => match s.values with
      | .i64 a :: vs => .Fallthrough st { s with values := .f64 (f64ConvertI64U a) :: vs }
      | _ => .Invalid "f64ConvertI64U: ill-shaped operand stack"

    -- Float → integer (trapping). NaN traps "invalid conversion to
    -- integer"; an out-of-range magnitude traps "integer overflow".
    | _, Instruction.i32TruncF32S => match s.values with
      | .f32 a :: vs => match i32TruncF32S a with
        | some r => .Fallthrough st { s with values := .i32 r :: vs }
        | none => if (Float32.ofBits a).isNaN then .Trap st "invalid conversion to integer"
                  else .Trap st "integer overflow"
      | _ => .Invalid "i32TruncF32S: ill-shaped operand stack"
    | _, Instruction.i32TruncF32U => match s.values with
      | .f32 a :: vs => match i32TruncF32U a with
        | some r => .Fallthrough st { s with values := .i32 r :: vs }
        | none => if (Float32.ofBits a).isNaN then .Trap st "invalid conversion to integer"
                  else .Trap st "integer overflow"
      | _ => .Invalid "i32TruncF32U: ill-shaped operand stack"
    | _, Instruction.i32TruncF64S => match s.values with
      | .f64 a :: vs => match i32TruncF64S a with
        | some r => .Fallthrough st { s with values := .i32 r :: vs }
        | none => if (Float.ofBits a).isNaN then .Trap st "invalid conversion to integer"
                  else .Trap st "integer overflow"
      | _ => .Invalid "i32TruncF64S: ill-shaped operand stack"
    | _, Instruction.i32TruncF64U => match s.values with
      | .f64 a :: vs => match i32TruncF64U a with
        | some r => .Fallthrough st { s with values := .i32 r :: vs }
        | none => if (Float.ofBits a).isNaN then .Trap st "invalid conversion to integer"
                  else .Trap st "integer overflow"
      | _ => .Invalid "i32TruncF64U: ill-shaped operand stack"
    | _, Instruction.i64TruncF32S => match s.values with
      | .f32 a :: vs => match i64TruncF32S a with
        | some r => .Fallthrough st { s with values := .i64 r :: vs }
        | none => if (Float32.ofBits a).isNaN then .Trap st "invalid conversion to integer"
                  else .Trap st "integer overflow"
      | _ => .Invalid "i64TruncF32S: ill-shaped operand stack"
    | _, Instruction.i64TruncF32U => match s.values with
      | .f32 a :: vs => match i64TruncF32U a with
        | some r => .Fallthrough st { s with values := .i64 r :: vs }
        | none => if (Float32.ofBits a).isNaN then .Trap st "invalid conversion to integer"
                  else .Trap st "integer overflow"
      | _ => .Invalid "i64TruncF32U: ill-shaped operand stack"
    | _, Instruction.i64TruncF64S => match s.values with
      | .f64 a :: vs => match i64TruncF64S a with
        | some r => .Fallthrough st { s with values := .i64 r :: vs }
        | none => if (Float.ofBits a).isNaN then .Trap st "invalid conversion to integer"
                  else .Trap st "integer overflow"
      | _ => .Invalid "i64TruncF64S: ill-shaped operand stack"
    | _, Instruction.i64TruncF64U => match s.values with
      | .f64 a :: vs => match i64TruncF64U a with
        | some r => .Fallthrough st { s with values := .i64 r :: vs }
        | none => if (Float.ofBits a).isNaN then .Trap st "invalid conversion to integer"
                  else .Trap st "integer overflow"
      | _ => .Invalid "i64TruncF64U: ill-shaped operand stack"

    -- Float → integer (saturating; never traps)
    | _, Instruction.i32TruncSatF32S => match s.values with
      | .f32 a :: vs => .Fallthrough st { s with values := .i32 (i32TruncSatF32S a) :: vs }
      | _ => .Invalid "i32TruncSatF32S: ill-shaped operand stack"
    | _, Instruction.i32TruncSatF32U => match s.values with
      | .f32 a :: vs => .Fallthrough st { s with values := .i32 (i32TruncSatF32U a) :: vs }
      | _ => .Invalid "i32TruncSatF32U: ill-shaped operand stack"
    | _, Instruction.i32TruncSatF64S => match s.values with
      | .f64 a :: vs => .Fallthrough st { s with values := .i32 (i32TruncSatF64S a) :: vs }
      | _ => .Invalid "i32TruncSatF64S: ill-shaped operand stack"
    | _, Instruction.i32TruncSatF64U => match s.values with
      | .f64 a :: vs => .Fallthrough st { s with values := .i32 (i32TruncSatF64U a) :: vs }
      | _ => .Invalid "i32TruncSatF64U: ill-shaped operand stack"
    | _, Instruction.i64TruncSatF32S => match s.values with
      | .f32 a :: vs => .Fallthrough st { s with values := .i64 (i64TruncSatF32S a) :: vs }
      | _ => .Invalid "i64TruncSatF32S: ill-shaped operand stack"
    | _, Instruction.i64TruncSatF32U => match s.values with
      | .f32 a :: vs => .Fallthrough st { s with values := .i64 (i64TruncSatF32U a) :: vs }
      | _ => .Invalid "i64TruncSatF32U: ill-shaped operand stack"
    | _, Instruction.i64TruncSatF64S => match s.values with
      | .f64 a :: vs => .Fallthrough st { s with values := .i64 (i64TruncSatF64S a) :: vs }
      | _ => .Invalid "i64TruncSatF64S: ill-shaped operand stack"
    | _, Instruction.i64TruncSatF64U => match s.values with
      | .f64 a :: vs => .Fallthrough st { s with values := .i64 (i64TruncSatF64U a) :: vs }
      | _ => .Invalid "i64TruncSatF64U: ill-shaped operand stack"

    -- Float ↔ float, and bitwise reinterpret (a pure retag of the bits)
    | _, Instruction.f32DemoteF64 => match s.values with
      | .f64 a :: vs => .Fallthrough st { s with values := .f32 (f32DemoteF64 a) :: vs }
      | _ => .Invalid "f32DemoteF64: ill-shaped operand stack"
    | _, Instruction.f64PromoteF32 => match s.values with
      | .f32 a :: vs => .Fallthrough st { s with values := .f64 (f64PromoteF32 a) :: vs }
      | _ => .Invalid "f64PromoteF32: ill-shaped operand stack"
    | _, Instruction.i32ReinterpretF32 => match s.values with
      | .f32 b :: vs => .Fallthrough st { s with values := .i32 b :: vs }
      | _ => .Invalid "i32ReinterpretF32: ill-shaped operand stack"
    | _, Instruction.i64ReinterpretF64 => match s.values with
      | .f64 b :: vs => .Fallthrough st { s with values := .i64 b :: vs }
      | _ => .Invalid "i64ReinterpretF64: ill-shaped operand stack"
    | _, Instruction.f32ReinterpretI32 => match s.values with
      | .i32 b :: vs => .Fallthrough st { s with values := .f32 b :: vs }
      | _ => .Invalid "f32ReinterpretI32: ill-shaped operand stack"
    | _, Instruction.f64ReinterpretI64 => match s.values with
      | .i64 b :: vs => .Fallthrough st { s with values := .f64 b :: vs }
      | _ => .Invalid "f64ReinterpretI64: ill-shaped operand stack"

    -- Structured control. Stack discipline matches the wasm spec:
    -- on entry, the top `paramArity` values are the construct's inputs;
    -- on a `br` to a `block`/`if` we keep the top `resultArity` values
    -- (the block's output); on a `br` back to a `loop` we keep the top
    -- `paramArity` values (the loop's next-iteration inputs). Values
    -- pushed between the entry mark and the kept top are discarded —
    -- the validator guarantees there are exactly the right number of
    -- "kept" values on top at every branch and at fall-through.
    | f + 1, .block paramArity resultArity body =>
      let belowStack := s.values.drop paramArity
      match exec f m st s body env with
      | .Fallthrough r' s' =>
        .Fallthrough r' { s' with values := s'.values.take resultArity ++ belowStack }
      | .Break 0 r' s' =>
        -- `br 0` to a block exits with the block's result values. We
        -- preserve whatever the brancher left on top (validator says
        -- it's exactly `resultArity` values).
        .Fallthrough r' { s' with values := s'.values.take resultArity ++ belowStack }
      | .Break (k + 1) r' s' => .Break k r' s'
      | other => other
    | f + 1, .loop paramArity resultArity body =>
      let belowStack := s.values.drop paramArity
      match exec f m st s body env with
      | .Fallthrough r' s' =>
        .Fallthrough r' { s' with values := s'.values.take resultArity ++ belowStack }
      | .Break 0 r' s' =>
        -- `br 0` to a loop = restart from the top. Reset the stack to
        -- the kept top values (the loop's next-iteration params) atop
        -- the entry's below-stack, then re-execute the loop.
        execOne f m r' { s' with values := s'.values.take paramArity ++ belowStack } inst env
      | .Break (k + 1) r' s' => .Break k r' s'
      | other => other
    | f + 1, .iff paramArity resultArity thn els => match s.values with
      | .i32 c :: vs =>
        let belowStack := vs.drop paramArity
        let s' : Locals := { s with values := vs }
        let body := if c ≠ 0 then thn else els
        match exec f m st s' body env with
        | .Fallthrough r' s'' =>
          .Fallthrough r' { s'' with values := s''.values.take resultArity ++ belowStack }
        | .Break 0 r' s'' =>
          .Fallthrough r' { s'' with values := s''.values.take resultArity ++ belowStack }
        | .Break (k + 1) r' s'' => .Break k r' s''
        | other => other
      | _ => .Invalid "iff: ill-shaped operand stack"

    -- Branching
    | _, .br n => .Break n st s
    | _, .br_if n => match s.values with
      | .i32 0 :: vs => .Fallthrough st { s with values := vs }
      | .i32 _ :: vs => .Break n st { s with values := vs }
      | _ => .Invalid "br_if: ill-shaped operand stack"
    | _, .brTable targets dflt => match s.values with
      | .i32 i :: vs =>
        let n := i.toNat
        let lbl := if h : n < targets.length then targets[n] else dflt
        .Break lbl st { s with values := vs }
      | _ => .Invalid "brTable: ill-shaped operand stack"

    -- Calls
    | f + 1, .call id => match run f m id st s.values env with
      | .Success vs st' => .Fallthrough st' { s with values := vs }
      | .Trap st' msg   => .Trap st' msg
      | .Invalid msg    => .Invalid msg
      | .OutOfFuel      => .OutOfFuel
      | .Thrown tag args st' => .Throwing tag args st' s

    -- Tail calls. Both build a `ReturnCall` continuation; `run` resolves
    -- the re-dispatch (consuming one unit of fuel per tail call), so a
    -- chain of N tail calls needs O(N) fuel but constant host stack.
    -- `return_call_indirect` performs the same table lookup, null check,
    -- and signature check as `call_indirect`, with the same trap wording.
    | _, .returnCall id => .ReturnCall id st s.values
    | _, .returnCallIndirect typeIdx tableIdx => match s.values with
      | .i32 i :: rest =>
        match st.tables[tableIdx]? with
        | none     => .Invalid s!"returnCallIndirect: table index {tableIdx} out of range"
        | some tbl =>
          match tbl[i.toNat]? with
          | none                       => .Trap st "undefined element"
          | some (.funcref none)       => .Trap st "uninitialized element"
          | some (.funcref (some fid)) =>
            match m.funcSig? fid with
            | none    => .Invalid s!"returnCallIndirect: function index {fid} out of range"
            | some fn =>
              match m.types[typeIdx]? with
              | none    => .Invalid s!"returnCallIndirect: type index {typeIdx} out of range"
              | some ty =>
                if m.indirectCallTypeOk fid typeIdx fn ty = true then
                  .ReturnCall fid st rest
                else .Trap st "indirect call type mismatch"
          | some _ => .Invalid "returnCallIndirect: non-funcref table entry"
      | .i64 i :: rest =>
        match st.tables[tableIdx]? with
        | none     => .Invalid s!"returnCallIndirect: table index {tableIdx} out of range"
        | some tbl =>
          match tbl[i.toNat]? with
          | none                       => .Trap st "undefined element"
          | some (.funcref none)       => .Trap st "uninitialized element"
          | some (.funcref (some fid)) =>
            match m.funcSig? fid with
            | none    => .Invalid s!"returnCallIndirect: function index {fid} out of range"
            | some fn =>
              match m.types[typeIdx]? with
              | none    => .Invalid s!"returnCallIndirect: type index {typeIdx} out of range"
              | some ty =>
                if m.indirectCallTypeOk fid typeIdx fn ty = true then
                  .ReturnCall fid st rest
                else .Trap st "indirect call type mismatch"
          | some _ => .Invalid "returnCallIndirect: non-funcref table entry"
      | _ => .Invalid "returnCallIndirect: ill-shaped operand stack"

    -- Exception handling. `throw` pops the tag's parameters and raises;
    -- `tryTable` runs its body like a `block` and intercepts a raised
    -- exception with the first matching clause, branching to the
    -- clause's label with the exception's arguments (plus the package as
    -- an `exnref` for the `_ref` forms; `catch_all` passes no values).
    | _, .throwI tagIdx =>
      match m.tags[tagIdx]? with
      | none => .Invalid s!"throw: tag index {tagIdx} out of range"
      | some tagTy =>
        let n := tagTy.params.length
        if s.values.length < n then .Invalid "throw: ill-shaped operand stack"
        else .Throwing tagIdx (s.values.take n) st { s with values := s.values.drop n }
    | _, .throwRef => match s.values with
      | .exnref none :: _ => .Trap st "null exception reference"
      | .exnref (some i) :: vs =>
        match st.exns[i]? with
        | none => .Invalid s!"throwRef: exception index {i} out of range"
        | some (tag, args) => .Throwing tag args st { s with values := vs }
      | _ => .Invalid "throwRef: ill-shaped operand stack"
    | f + 1, .tryTable ps rs catches body =>
      let belowStack := s.values.drop ps
      match exec f m st s body env with
      | .Fallthrough r' s' =>
        .Fallthrough r' { s' with values := s'.values.take rs ++ belowStack }
      | .Break 0 r' s' =>
        .Fallthrough r' { s' with values := s'.values.take rs ++ belowStack }
      | .Break (k + 1) r' s' => .Break k r' s'
      | .Throwing tag args r' s' =>
        match catches.find? (fun c => match c with
          | .catch t _ | .catchRef t _ => t = tag
          | .catchAll _ | .catchAllRef _ => true) with
        | none => .Throwing tag args r' s'
        | some c =>
          -- Values pushed for the branch target (head = top of stack)
          -- and the possibly-extended store (the `_ref` forms register
          -- the exception package).
          let (vals, r'') : List Value × Store α := match c with
            | .catch _ _      => (args, r')
            | .catchAll _     => ([], r')
            | .catchRef _ _   =>
              (.exnref (some r'.exns.length) :: args,
               { r' with exns := r'.exns ++ [(tag, args)] })
            | .catchAllRef _  =>
              ([.exnref (some r'.exns.length)],
               { r' with exns := r'.exns ++ [(tag, args)] })
          let lbl : Nat := match c with
            | .catch _ l | .catchRef _ l | .catchAll l | .catchAllRef l => l
          -- A caught exception branches like a `br lbl` executed at the
          -- position of the `tryTable` itself: label 0 is the construct
          -- *enclosing* it, so the break propagates outward unchanged.
          .Break lbl r'' { s' with values := vals ++ belowStack }
      | other => other

    -- Typed function references. `call_ref` dispatches through a popped
    -- funcref (null traps with the spec's wording); validation makes a
    -- runtime signature check unnecessary. `return_call_ref` is the
    -- tail-call form, resolved by `run` like the other tail calls.
    | f + 1, .callRef _typeIdx => match s.values with
      | .funcref none :: _ => .Trap st "null function reference"
      | .funcref (some fid) :: rest =>
        (match run f m fid st rest env with
         | .Success vs st' => .Fallthrough st' { s with values := vs }
         | .Trap st' msg   => .Trap st' msg
         | .Invalid msg    => .Invalid msg
         | .OutOfFuel      => .OutOfFuel
         | .Thrown tag args st' => .Throwing tag args st' s)
      | _ => .Invalid "callRef: ill-shaped operand stack"
    | _, .returnCallRef _typeIdx => match s.values with
      | .funcref none :: _ => .Trap st "null function reference"
      | .funcref (some fid) :: rest => .ReturnCall fid st rest
      | _ => .Invalid "returnCallRef: ill-shaped operand stack"
    | _, .refAsNonNull => match s.values with
      | v :: vs =>
        match v.isNullRef? with
        | some true  => .Trap st "null reference"
        | some false => .Fallthrough st { s with values := v :: vs }
        | none       => .Invalid "refAsNonNull: ill-shaped operand stack"
      | _ => .Invalid "refAsNonNull: ill-shaped operand stack"
    | _, .brOnNull n => match s.values with
      | v :: vs =>
        match v.isNullRef? with
        | some true  => .Break n st { s with values := vs }
        | some false => .Fallthrough st { s with values := v :: vs }
        | none       => .Invalid "brOnNull: ill-shaped operand stack"
      | _ => .Invalid "brOnNull: ill-shaped operand stack"
    | _, .brOnNonNull n => match s.values with
      | v :: vs =>
        match v.isNullRef? with
        | some true  => .Fallthrough st { s with values := vs }
        | some false => .Break n st { s with values := v :: vs }
        | none       => .Invalid "brOnNonNull: ill-shaped operand stack"
      | _ => .Invalid "brOnNonNull: ill-shaped operand stack"

    -- Indirect call. Pop an i32 index, look up the entry in the chosen
    -- table, then dispatch to the referenced function — trapping on
    -- out-of-bounds, null refs, or signature mismatches against the
    -- declared `(type N)`. Trap message strings match the wasm spec's
    -- canonical wording so the testsuite's `assert_trap` text matcher
    -- accepts them.
    | f + 1, .callIndirect typeIdx tableIdx => match s.values with
      | .i32 i :: rest =>
        match st.tables[tableIdx]? with
        | none     => .Invalid s!"callIndirect: table index {tableIdx} out of range"
        | some tbl =>
          match tbl[i.toNat]? with
          | none                       => .Trap st "undefined element"
          | some (.funcref none)       => .Trap st "uninitialized element"
          | some (.funcref (some fid)) =>
            -- Signature lookup is in the *unified* function index space
            -- (imports first), matching what the table entry refers to.
            match m.funcSig? fid with
            | none    => .Invalid s!"callIndirect: function index {fid} out of range"
            | some fn =>
              match m.types[typeIdx]? with
              | none    => .Invalid s!"callIndirect: type index {typeIdx} out of range"
              | some ty =>
                if m.indirectCallTypeOk fid typeIdx fn ty = true then
                  match run f m fid st rest env with
                  | .Success vs st' => .Fallthrough st' { s with values := vs }
                  | .Trap st' msg   => .Trap st' msg
                  | .Invalid msg    => .Invalid msg
                  | .OutOfFuel      => .OutOfFuel
                  | .Thrown tag args st' => .Throwing tag args st' s
                else .Trap st "indirect call type mismatch"
          | some _ => .Invalid "callIndirect: non-funcref table entry"
      -- table64: the selector arrives as an i64. The flow is identical to
      -- the i32 arm above.
      | .i64 i :: rest =>
        match st.tables[tableIdx]? with
        | none     => .Invalid s!"callIndirect: table index {tableIdx} out of range"
        | some tbl =>
          match tbl[i.toNat]? with
          | none                       => .Trap st "undefined element"
          | some (.funcref none)       => .Trap st "uninitialized element"
          | some (.funcref (some fid)) =>
            match m.funcSig? fid with
            | none    => .Invalid s!"callIndirect: function index {fid} out of range"
            | some fn =>
              match m.types[typeIdx]? with
              | none    => .Invalid s!"callIndirect: type index {typeIdx} out of range"
              | some ty =>
                if m.indirectCallTypeOk fid typeIdx fn ty = true then
                  match run f m fid st rest env with
                  | .Success vs st' => .Fallthrough st' { s with values := vs }
                  | .Trap st' msg   => .Trap st' msg
                  | .Invalid msg    => .Invalid msg
                  | .OutOfFuel      => .OutOfFuel
                  | .Thrown tag args st' => .Throwing tag args st' s
                else .Trap st "indirect call type mismatch"
          | some _ => .Invalid "callIndirect: non-funcref table entry"
      | _ => .Invalid "callIndirect: ill-shaped operand stack"

    -- Memory load / store. Every access traps when
    -- `addr.toNat + off.toNat + size > byteCap`; the check is done in
    -- `Nat` to avoid the i32 wraparound that would otherwise hide
    -- accesses with `addr = 0xFFFFFFFC` and `size = 4`, etc.
    | _, .load8U off => match s.values with
      | .i32 a :: vs =>
        if a.toNat + off.toNat + 1 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          let v : UInt32 := (st.mem.read8 (a + off)).toUInt32
          .Fallthrough st { s with values := .i32 v :: vs }
      | .i64 a :: vs =>
        if a.toNat + off.toNat + 1 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          let v : UInt32 := (st.mem.read8 (a.toUInt32 + off)).toUInt32
          .Fallthrough st { s with values := .i32 v :: vs }
      | _ => .Invalid "load8U: ill-shaped operand stack"
    | _, .load8S off => match s.values with
      | .i32 a :: vs =>
        if a.toNat + off.toNat + 1 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          let v : UInt32 := (Int32.ofInt (signExtend (st.mem.read8 (a + off)).toNat 8)).toUInt32
          .Fallthrough st { s with values := .i32 v :: vs }
      | .i64 a :: vs =>
        if a.toNat + off.toNat + 1 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          let v : UInt32 := (Int32.ofInt (signExtend (st.mem.read8 (a.toUInt32 + off)).toNat 8)).toUInt32
          .Fallthrough st { s with values := .i32 v :: vs }
      | _ => .Invalid "load8S: ill-shaped operand stack"
    | _, .load16U off => match s.values with
      | .i32 a :: vs =>
        if a.toNat + off.toNat + 2 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          let v := st.mem.read16 (a + off)
          .Fallthrough st { s with values := .i32 v :: vs }
      | .i64 a :: vs =>
        if a.toNat + off.toNat + 2 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          let v := st.mem.read16 (a.toUInt32 + off)
          .Fallthrough st { s with values := .i32 v :: vs }
      | _ => .Invalid "load16U: ill-shaped operand stack"
    | _, .load16S off => match s.values with
      | .i32 a :: vs =>
        if a.toNat + off.toNat + 2 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          let v : UInt32 := (Int32.ofInt (signExtend (st.mem.read16 (a + off)).toNat 16)).toUInt32
          .Fallthrough st { s with values := .i32 v :: vs }
      | .i64 a :: vs =>
        if a.toNat + off.toNat + 2 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          let v : UInt32 := (Int32.ofInt (signExtend (st.mem.read16 (a.toUInt32 + off)).toNat 16)).toUInt32
          .Fallthrough st { s with values := .i32 v :: vs }
      | _ => .Invalid "load16S: ill-shaped operand stack"
    | _, .load32 off => match s.values with
      | .i32 a :: vs =>
        if a.toNat + off.toNat + 4 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          let v := st.mem.read32 (a + off)
          .Fallthrough st { s with values := .i32 v :: vs }
      | .i64 a :: vs =>
        if a.toNat + off.toNat + 4 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          let v := st.mem.read32 (a.toUInt32 + off)
          .Fallthrough st { s with values := .i32 v :: vs }
      | _ => .Invalid "load32: ill-shaped operand stack"
    | _, .store8 off => match s.values with
      | .i32 v :: .i32 a :: vs =>
        if a.toNat + off.toNat + 1 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          let mem' := st.mem.write8 (a + off) v.toUInt8
          .Fallthrough { st with mem := mem' } { s with values := vs }
      | .i32 v :: .i64 a :: vs =>
        if a.toNat + off.toNat + 1 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          let mem' := st.mem.write8 (a.toUInt32 + off) v.toUInt8
          .Fallthrough { st with mem := mem' } { s with values := vs }
      | _ => .Invalid "store8: ill-shaped operand stack"
    | _, .store16 off => match s.values with
      | .i32 v :: .i32 a :: vs =>
        if a.toNat + off.toNat + 2 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          let mem' := st.mem.write16 (a + off) v
          .Fallthrough { st with mem := mem' } { s with values := vs }
      | .i32 v :: .i64 a :: vs =>
        if a.toNat + off.toNat + 2 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          let mem' := st.mem.write16 (a.toUInt32 + off) v
          .Fallthrough { st with mem := mem' } { s with values := vs }
      | _ => .Invalid "store16: ill-shaped operand stack"
    | _, .store32 off => match s.values with
      | .i32 v :: .i32 a :: vs =>
        if a.toNat + off.toNat + 4 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          let mem' := st.mem.write32 (a + off) v
          .Fallthrough { st with mem := mem' } { s with values := vs }
      | .i32 v :: .i64 a :: vs =>
        if a.toNat + off.toNat + 4 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          let mem' := st.mem.write32 (a.toUInt32 + off) v
          .Fallthrough { st with mem := mem' } { s with values := vs }
      | _ => .Invalid "store32: ill-shaped operand stack"
    | _, .load64 off => match s.values with
      | .i32 a :: vs =>
        if a.toNat + off.toNat + 8 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          let v := st.mem.read64 (a + off)
          .Fallthrough st { s with values := .i64 v :: vs }
      | .i64 a :: vs =>
        if a.toNat + off.toNat + 8 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          let v := st.mem.read64 (a.toUInt32 + off)
          .Fallthrough st { s with values := .i64 v :: vs }
      | _ => .Invalid "load64: ill-shaped operand stack"
    | _, .store64 off => match s.values with
      | .i64 v :: .i32 a :: vs =>
        if a.toNat + off.toNat + 8 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          let mem' := st.mem.write64 (a + off) v
          .Fallthrough { st with mem := mem' } { s with values := vs }
      | .i64 v :: .i64 a :: vs =>
        if a.toNat + off.toNat + 8 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          let mem' := st.mem.write64 (a.toUInt32 + off) v
          .Fallthrough { st with mem := mem' } { s with values := vs }
      | _ => .Invalid "store64: ill-shaped operand stack"

    | _, .load8UI64 off => match s.values with
      | .i32 a :: vs =>
        if a.toNat + off.toNat + 1 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          let v : UInt64 := (st.mem.read8 (a + off)).toUInt64
          .Fallthrough st { s with values := .i64 v :: vs }
      | .i64 a :: vs =>
        if a.toNat + off.toNat + 1 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          let v : UInt64 := (st.mem.read8 (a.toUInt32 + off)).toUInt64
          .Fallthrough st { s with values := .i64 v :: vs }
      | _ => .Invalid "load8UI64: ill-shaped operand stack"
    | _, .load8SI64 off => match s.values with
      | .i32 a :: vs =>
        if a.toNat + off.toNat + 1 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          let v : UInt64 := (Int64.ofInt (signExtend (st.mem.read8 (a + off)).toNat 8)).toUInt64
          .Fallthrough st { s with values := .i64 v :: vs }
      | .i64 a :: vs =>
        if a.toNat + off.toNat + 1 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          let v : UInt64 := (Int64.ofInt (signExtend (st.mem.read8 (a.toUInt32 + off)).toNat 8)).toUInt64
          .Fallthrough st { s with values := .i64 v :: vs }
      | _ => .Invalid "load8SI64: ill-shaped operand stack"
    | _, .load16UI64 off => match s.values with
      | .i32 a :: vs =>
        if a.toNat + off.toNat + 2 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          let v : UInt64 := (st.mem.read16 (a + off)).toUInt64
          .Fallthrough st { s with values := .i64 v :: vs }
      | .i64 a :: vs =>
        if a.toNat + off.toNat + 2 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          let v : UInt64 := (st.mem.read16 (a.toUInt32 + off)).toUInt64
          .Fallthrough st { s with values := .i64 v :: vs }
      | _ => .Invalid "load16UI64: ill-shaped operand stack"
    | _, .load16SI64 off => match s.values with
      | .i32 a :: vs =>
        if a.toNat + off.toNat + 2 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          let v : UInt64 := (Int64.ofInt (signExtend (st.mem.read16 (a + off)).toNat 16)).toUInt64
          .Fallthrough st { s with values := .i64 v :: vs }
      | .i64 a :: vs =>
        if a.toNat + off.toNat + 2 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          let v : UInt64 := (Int64.ofInt (signExtend (st.mem.read16 (a.toUInt32 + off)).toNat 16)).toUInt64
          .Fallthrough st { s with values := .i64 v :: vs }
      | _ => .Invalid "load16SI64: ill-shaped operand stack"
    | _, .load32UI64 off => match s.values with
      | .i32 a :: vs =>
        if a.toNat + off.toNat + 4 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          let v : UInt64 := (st.mem.read32 (a + off)).toUInt64
          .Fallthrough st { s with values := .i64 v :: vs }
      | .i64 a :: vs =>
        if a.toNat + off.toNat + 4 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          let v : UInt64 := (st.mem.read32 (a.toUInt32 + off)).toUInt64
          .Fallthrough st { s with values := .i64 v :: vs }
      | _ => .Invalid "load32UI64: ill-shaped operand stack"
    | _, .load32SI64 off => match s.values with
      | .i32 a :: vs =>
        if a.toNat + off.toNat + 4 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          let v : UInt64 := (Int64.ofInt (signExtend (st.mem.read32 (a + off)).toNat 32)).toUInt64
          .Fallthrough st { s with values := .i64 v :: vs }
      | .i64 a :: vs =>
        if a.toNat + off.toNat + 4 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          let v : UInt64 := (Int64.ofInt (signExtend (st.mem.read32 (a.toUInt32 + off)).toNat 32)).toUInt64
          .Fallthrough st { s with values := .i64 v :: vs }
      | _ => .Invalid "load32SI64: ill-shaped operand stack"
    | _, .store8I64 off => match s.values with
      | .i64 v :: .i32 a :: vs =>
        if a.toNat + off.toNat + 1 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          let mem' := st.mem.write8 (a + off) v.toUInt8
          .Fallthrough { st with mem := mem' } { s with values := vs }
      | .i64 v :: .i64 a :: vs =>
        if a.toNat + off.toNat + 1 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          let mem' := st.mem.write8 (a.toUInt32 + off) v.toUInt8
          .Fallthrough { st with mem := mem' } { s with values := vs }
      | _ => .Invalid "store8I64: ill-shaped operand stack"
    | _, .store16I64 off => match s.values with
      | .i64 v :: .i32 a :: vs =>
        if a.toNat + off.toNat + 2 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          let mem' := st.mem.write16 (a + off) v.toUInt32
          .Fallthrough { st with mem := mem' } { s with values := vs }
      | .i64 v :: .i64 a :: vs =>
        if a.toNat + off.toNat + 2 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          let mem' := st.mem.write16 (a.toUInt32 + off) v.toUInt32
          .Fallthrough { st with mem := mem' } { s with values := vs }
      | _ => .Invalid "store16I64: ill-shaped operand stack"
    | _, .store32I64 off => match s.values with
      | .i64 v :: .i32 a :: vs =>
        if a.toNat + off.toNat + 4 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          let mem' := st.mem.write32 (a + off) v.toUInt32
          .Fallthrough { st with mem := mem' } { s with values := vs }
      | .i64 v :: .i64 a :: vs =>
        if a.toNat + off.toNat + 4 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          let mem' := st.mem.write32 (a.toUInt32 + off) v.toUInt32
          .Fallthrough { st with mem := mem' } { s with values := vs }
      | _ => .Invalid "store32I64: ill-shaped operand stack"

    -- Memory size / grow. `memory.grow`'s cap is computed once via
    -- `Module.memoryCap` so the semantics and the corresponding wp
    -- lemma share a single matchable shape.
    | _, .memorySize =>
      -- The result type follows the declared memory's address type
      -- (memory64): i64 pages for a 64-bit memory, i32 otherwise.
      .Fallthrough st { s with values := sizeValue m.memIs64 st.mem.pages :: s.values }
    | _, .memoryGrow => match s.values with
      | .i32 delta :: vs =>
        match st.mem.grow delta m.memoryCap with
        | some (mem', cur) =>
          .Fallthrough { st with mem := mem' }
            { s with values := .i32 cur.toUInt32 :: vs }
        | none =>
          .Fallthrough st { s with values := .i32 (0xFFFFFFFF : UInt32) :: vs }
      -- memory64: delta and result are i64. A delta of 2^32 pages or more
      -- can never fit under the implementation cap, so it fails directly
      -- (the spec permits growth to fail); otherwise defer to `Mem.grow`
      -- with the (faithful) 32-bit truncation of the delta.
      | .i64 delta :: vs =>
        if delta.toNat ≥ 2 ^ 32 then
          .Fallthrough st { s with values := .i64 (0xFFFFFFFFFFFFFFFF : UInt64) :: vs }
        else
          match st.mem.grow delta.toUInt32 m.memoryCap with
          | some (mem', cur) =>
            .Fallthrough { st with mem := mem' }
              { s with values := .i64 cur.toUInt64 :: vs }
          | none =>
            .Fallthrough st { s with values := .i64 (0xFFFFFFFFFFFFFFFF : UInt64) :: vs }
      | _ => .Invalid "memoryGrow: ill-shaped operand stack"

    -- Memory fill. Wasm stack discipline: dst is pushed first, then val,
    -- then len, so the list (top = head) has len :: val :: dst :: …
    -- Trap if [dst, dst+len) escapes the legal byte range; the trap is
    -- observed *before* any write, matching the spec's atomicity.
    | _, .memoryFill => match s.values with
      | .i32 len :: .i32 val :: .i32 dst :: vs =>
        let byteCap : Nat := st.mem.pages * 65536
        if dst.toNat + len.toNat > byteCap then
          .Trap st "out of bounds memory access"
        else
          let mem' := st.mem.fill dst.toNat len.toNat val.toUInt8
          .Fallthrough { st with mem := mem' } { s with values := vs }
      -- memory64: dst and len are i64; the fill value stays i32 per spec.
      | .i64 len :: .i32 val :: .i64 dst :: vs =>
        let byteCap : Nat := st.mem.pages * 65536
        if dst.toNat + len.toNat > byteCap then
          .Trap st "out of bounds memory access"
        else
          let mem' := st.mem.fill dst.toNat len.toNat val.toUInt8
          .Fallthrough { st with mem := mem' } { s with values := vs }
      | _ => .Invalid "memoryFill: ill-shaped operand stack"

    -- memory.copy: pops len :: src :: dst (top = len). Trap is observed
    -- *before* any write, matching the spec's atomicity: if either the
    -- source or destination range escapes the legal byte span, the
    -- whole instruction traps with no partial effect.
    | _, .memoryCopy => match s.values with
      | .i32 len :: .i32 src :: .i32 dst :: vs =>
        let byteCap : Nat := st.mem.pages * 65536
        if dst.toNat + len.toNat > byteCap ∨ src.toNat + len.toNat > byteCap then
          .Trap st "out of bounds memory access"
        else
          let mem' := st.mem.copy dst.toNat src.toNat len.toNat
          .Fallthrough { st with mem := mem' } { s with values := vs }
      -- memory64: all three operands are i64.
      | .i64 len :: .i64 src :: .i64 dst :: vs =>
        let byteCap : Nat := st.mem.pages * 65536
        if dst.toNat + len.toNat > byteCap ∨ src.toNat + len.toNat > byteCap then
          .Trap st "out of bounds memory access"
        else
          let mem' := st.mem.copy dst.toNat src.toNat len.toNat
          .Fallthrough { st with mem := mem' } { s with values := vs }
      | _ => .Invalid "memoryCopy: ill-shaped operand stack"

    -- memory.init i: pops len :: src :: dst (top = len). Source bytes
    -- come from data segment `i`; a dropped segment is modelled as
    -- having length 0, so any nonzero-length init from it traps on
    -- the source-bounds check. Both bounds are checked atomically
    -- before any write.
    | _, .memoryInit i => match s.values with
      | .i32 len :: .i32 src :: .i32 dst :: vs =>
        match st.dataSegments[i]? with
        | none => .Invalid s!"memoryInit: segment index {i} out of range"
        | some none =>
          -- segment already dropped: equivalent to length-0 source
          if 0 < len.toNat ∨ dst.toNat + len.toNat > st.mem.pages * 65536 then
            .Trap st "out of bounds memory access"
          else
            .Fallthrough st { s with values := vs }
        | some (some segBytes) =>
          if src.toNat + len.toNat > segBytes.length
             ∨ dst.toNat + len.toNat > st.mem.pages * 65536 then
            .Trap st "out of bounds memory access"
          else
            let mem' := st.mem.writeBytesFrom dst.toNat segBytes src.toNat len.toNat
            .Fallthrough { st with mem := mem' } { s with values := vs }
      -- memory64: dst takes the memory's address type (i64); src and len
      -- index into the data segment and stay i32 per spec.
      | .i32 len :: .i32 src :: .i64 dst :: vs =>
        match st.dataSegments[i]? with
        | none => .Invalid s!"memoryInit: segment index {i} out of range"
        | some none =>
          if 0 < len.toNat ∨ dst.toNat + len.toNat > st.mem.pages * 65536 then
            .Trap st "out of bounds memory access"
          else
            .Fallthrough st { s with values := vs }
        | some (some segBytes) =>
          if src.toNat + len.toNat > segBytes.length
             ∨ dst.toNat + len.toNat > st.mem.pages * 65536 then
            .Trap st "out of bounds memory access"
          else
            let mem' := st.mem.writeBytesFrom dst.toNat segBytes src.toNat len.toNat
            .Fallthrough { st with mem := mem' } { s with values := vs }
      | _ => .Invalid "memoryInit: ill-shaped operand stack"

    -- data.drop i: mark segment `i` as no-longer-available. Idempotent
    -- (dropping an already-dropped segment is a no-op).
    | _, .dataDrop i =>
      match st.dataSegments[i]? with
      | none => .Invalid s!"dataDrop: segment index {i} out of range"
      | some _ =>
        let dataSegments' := st.dataSegments.set i none
        .Fallthrough { st with dataSegments := dataSegments' } s

    -- Multi-memory. Swap memory `k` (and its declaration) into the
    -- default slot, run the wrapped memory instruction, then swap the
    -- (possibly written) memory back into `extraMems`. The wrapped
    -- instruction never breaks/returns, so only `Fallthrough` and `Trap`
    -- carry a store to map back.
    | f + 1, .memOp k inner =>
      match st.extraMems[k - 1]?, m.extraMemories[k - 1]? with
      | some memK, some declK =>
        let stIn : Store α := { st with mem := memK }
        let mIn : Module := { m with memory := some declK }
        let restore (st' : Store α) : Store α :=
          { st' with mem := st.mem, extraMems := st.extraMems.set (k - 1) st'.mem }
        match execOne f mIn stIn s inner env with
        | .Fallthrough st' s' => .Fallthrough (restore st') s'
        | .Trap st' msg       => .Trap (restore st') msg
        | .Throwing t a st' s' => .Throwing t a (restore st') s'
        | other               => other
      | _, _ => .Invalid s!"memOp: memory index {k} out of range"

    -- Cross-memory memory.copy (multi-memory). Each address operand is
    -- read by its runtime width (i32 or i64, per its memory's declared
    -- address type); bounds are checked in ℕ before any write.
    | _, .memoryCopyBetween dstMem srcMem => match s.values with
      | lenV :: srcV :: dstV :: vs =>
        match lenV.addrNat?, srcV.addrNat?, dstV.addrNat? with
        | some len, some src, some dst =>
          let memOf : Nat → Option Mem := fun k =>
            if k = 0 then some st.mem else st.extraMems[k - 1]?
          match memOf dstMem, memOf srcMem with
          | some dMem, some sMem =>
            if dst + len > dMem.pages * 65536 ∨ src + len > sMem.pages * 65536 then
              .Trap st "out of bounds memory access"
            else
              let dMem' := dMem.writeBytes dst (sMem.readBytes src len)
              let st' :=
                if dstMem = 0 then { st with mem := dMem' }
                else { st with extraMems := st.extraMems.set (dstMem - 1) dMem' }
              .Fallthrough st' { s with values := vs }
          | _, _ => .Invalid "memoryCopyBetween: memory index out of range"
        | _, _, _ => .Invalid "memoryCopyBetween: ill-shaped operand stack"
      | _ => .Invalid "memoryCopyBetween: ill-shaped operand stack"

    -- SIMD (v128). Lane semantics live in `Interpreter.Wasm.Simd`; the
    -- arms here only manage the operand stack and (for the memory
    -- variants) the usual Nat-domain bounds checks. A v128 occupies 16
    -- bytes in memory, lane 0 first (little-endian), so the two 64-bit
    -- halves are the low word at `a` and the high word at `a+8`.
    | _, .vConst bits => .Fallthrough st { s with values := .v128 bits :: s.values }
    | _, .vUnOp op => match s.values with
      | .v128 a :: vs => .Fallthrough st { s with values := .v128 (op.eval a) :: vs }
      | _ => .Invalid "vUnOp: ill-shaped operand stack"
    | _, .vBinOp op => match s.values with
      | .v128 b :: .v128 a :: vs =>
        .Fallthrough st { s with values := .v128 (op.eval a b) :: vs }
      | _ => .Invalid "vBinOp: ill-shaped operand stack"
    | _, .vFma sh neg => match s.values with
      | .v128 c :: .v128 b :: .v128 a :: vs =>
        .Fallthrough st { s with values := .v128 (Simd.fma sh neg a b c) :: vs }
      | _ => .Invalid "vFma: ill-shaped operand stack"
    | _, .vDotAdd => match s.values with
      | .v128 c :: .v128 b :: .v128 a :: vs =>
        .Fallthrough st { s with values := .v128 (Simd.dotAdd a b c) :: vs }
      | _ => .Invalid "vDotAdd: ill-shaped operand stack"
    | _, .vBitselect => match s.values with
      | .v128 c :: .v128 b :: .v128 a :: vs =>
        .Fallthrough st { s with values := .v128 ((a &&& c) ||| (b &&& ~~~c)) :: vs }
      | _ => .Invalid "vBitselect: ill-shaped operand stack"
    | _, .vTestOp op => match s.values with
      | .v128 a :: vs => .Fallthrough st { s with values := .i32 (op.eval a) :: vs }
      | _ => .Invalid "vTestOp: ill-shaped operand stack"
    | _, .vShiftOp op => match s.values with
      | .i32 k :: .v128 a :: vs =>
        .Fallthrough st { s with values := .v128 (op.eval a k) :: vs }
      | _ => .Invalid "vShiftOp: ill-shaped operand stack"
    | _, .vSplat sh => match s.values with
      | v :: vs =>
        match v.scalarBitsFor? sh with
        | some x => .Fallthrough st { s with values := .v128 (Simd.splat sh x) :: vs }
        | none   => .Invalid "vSplat: ill-shaped operand stack"
      | _ => .Invalid "vSplat: ill-shaped operand stack"
    | _, .vExtractLane sh signed lane => match s.values with
      | .v128 a :: vs =>
        let n := Simd.getLane sh.laneBits lane a
        let v : Value := match sh with
          | .i8x16 => .i32 (if signed then UInt32.ofNat (Simd.toU 32 (Simd.sx 8 n))
                            else UInt32.ofNat n)
          | .i16x8 => .i32 (if signed then UInt32.ofNat (Simd.toU 32 (Simd.sx 16 n))
                            else UInt32.ofNat n)
          | .i32x4 => .i32 (UInt32.ofNat n)
          | .i64x2 => .i64 (UInt64.ofNat n)
          | .f32x4 => .f32 (UInt32.ofNat n)
          | .f64x2 => .f64 (UInt64.ofNat n)
        .Fallthrough st { s with values := v :: vs }
      | _ => .Invalid "vExtractLane: ill-shaped operand stack"
    | _, .vReplaceLane sh lane => match s.values with
      | v :: .v128 a :: vs =>
        match v.scalarBitsFor? sh with
        | some x =>
          .Fallthrough st
            { s with values := .v128 (Simd.setLane sh.laneBits lane a x) :: vs }
        | none => .Invalid "vReplaceLane: ill-shaped operand stack"
      | _ => .Invalid "vReplaceLane: ill-shaped operand stack"
    | _, .vShuffle idx => match s.values with
      | .v128 b :: .v128 a :: vs =>
        .Fallthrough st { s with values := .v128 (Simd.shuffle idx a b) :: vs }
      | _ => .Invalid "vShuffle: ill-shaped operand stack"
    | _, .v128Load off => match s.values with
      | .i32 a :: vs =>
        if a.toNat + off.toNat + 16 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          let lo := st.mem.read64 (a + off)
          let hi := st.mem.read64 (a + off + 8)
          let bits := BitVec.ofNat 128 (lo.toNat + hi.toNat * 2 ^ 64)
          .Fallthrough st { s with values := .v128 bits :: vs }
      | .i64 a :: vs =>
        if a.toNat + off.toNat + 16 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          let lo := st.mem.read64 (a.toUInt32 + off)
          let hi := st.mem.read64 (a.toUInt32 + off + 8)
          let bits := BitVec.ofNat 128 (lo.toNat + hi.toNat * 2 ^ 64)
          .Fallthrough st { s with values := .v128 bits :: vs }
      | _ => .Invalid "v128Load: ill-shaped operand stack"
    | _, .v128Store off => match s.values with
      | .v128 v :: .i32 a :: vs =>
        if a.toNat + off.toNat + 16 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          let lo := UInt64.ofNat (v.toNat % 2 ^ 64)
          let hi := UInt64.ofNat (v.toNat / 2 ^ 64)
          let mem' := (st.mem.write64 (a + off) lo).write64 (a + off + 8) hi
          .Fallthrough { st with mem := mem' } { s with values := vs }
      | .v128 v :: .i64 a :: vs =>
        if a.toNat + off.toNat + 16 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          let lo := UInt64.ofNat (v.toNat % 2 ^ 64)
          let hi := UInt64.ofNat (v.toNat / 2 ^ 64)
          let mem' := (st.mem.write64 (a.toUInt32 + off) lo).write64 (a.toUInt32 + off + 8) hi
          .Fallthrough { st with mem := mem' } { s with values := vs }
      | _ => .Invalid "v128Store: ill-shaped operand stack"
    | _, .v128LoadExt srcBits signed off => match s.values with
      | .i32 a :: vs =>
        if a.toNat + off.toNat + 8 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          let word := st.mem.read64 (a + off)
          let dstBits := srcBits * 2
          let cnt := 64 / srcBits
          let lanes := (List.range cnt).map fun i =>
            let n := (word.toNat >>> (i * srcBits)) % 2 ^ srcBits
            if signed then Simd.toU dstBits (Simd.sx srcBits n) else n
          .Fallthrough st { s with values := .v128 (Simd.ofLanes dstBits lanes) :: vs }
      | .i64 a :: vs =>
        if a.toNat + off.toNat + 8 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          let word := st.mem.read64 (a.toUInt32 + off)
          let dstBits := srcBits * 2
          let cnt := 64 / srcBits
          let lanes := (List.range cnt).map fun i =>
            let n := (word.toNat >>> (i * srcBits)) % 2 ^ srcBits
            if signed then Simd.toU dstBits (Simd.sx srcBits n) else n
          .Fallthrough st { s with values := .v128 (Simd.ofLanes dstBits lanes) :: vs }
      | _ => .Invalid "v128LoadExt: ill-shaped operand stack"
    | _, .v128LoadSplat bits off => match s.values with
      | .i32 a :: vs =>
        if a.toNat + off.toNat + bits / 8 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          let n : Nat := match bits with
            | 8  => (st.mem.read8 (a + off)).toNat
            | 16 => (st.mem.read16 (a + off)).toNat
            | 32 => (st.mem.read32 (a + off)).toNat
            | _  => (st.mem.read64 (a + off)).toNat
          let lanes := List.replicate (128 / bits) n
          .Fallthrough st { s with values := .v128 (Simd.ofLanes bits lanes) :: vs }
      | .i64 a :: vs =>
        if a.toNat + off.toNat + bits / 8 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          let n : Nat := match bits with
            | 8  => (st.mem.read8 (a.toUInt32 + off)).toNat
            | 16 => (st.mem.read16 (a.toUInt32 + off)).toNat
            | 32 => (st.mem.read32 (a.toUInt32 + off)).toNat
            | _  => (st.mem.read64 (a.toUInt32 + off)).toNat
          let lanes := List.replicate (128 / bits) n
          .Fallthrough st { s with values := .v128 (Simd.ofLanes bits lanes) :: vs }
      | _ => .Invalid "v128LoadSplat: ill-shaped operand stack"
    | _, .v128LoadZero bits off => match s.values with
      | .i32 a :: vs =>
        if a.toNat + off.toNat + bits / 8 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          let n : Nat := match bits with
            | 32 => (st.mem.read32 (a + off)).toNat
            | _  => (st.mem.read64 (a + off)).toNat
          .Fallthrough st { s with values := .v128 (BitVec.ofNat 128 n) :: vs }
      | .i64 a :: vs =>
        if a.toNat + off.toNat + bits / 8 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          let n : Nat := match bits with
            | 32 => (st.mem.read32 (a.toUInt32 + off)).toNat
            | _  => (st.mem.read64 (a.toUInt32 + off)).toNat
          .Fallthrough st { s with values := .v128 (BitVec.ofNat 128 n) :: vs }
      | _ => .Invalid "v128LoadZero: ill-shaped operand stack"
    | _, .v128LoadLane bits lane off => match s.values with
      | .v128 v :: .i32 a :: vs =>
        if a.toNat + off.toNat + bits / 8 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          let n : Nat := match bits with
            | 8  => (st.mem.read8 (a + off)).toNat
            | 16 => (st.mem.read16 (a + off)).toNat
            | 32 => (st.mem.read32 (a + off)).toNat
            | _  => (st.mem.read64 (a + off)).toNat
          .Fallthrough st { s with values := .v128 (Simd.setLane bits lane v n) :: vs }
      | .v128 v :: .i64 a :: vs =>
        if a.toNat + off.toNat + bits / 8 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          let n : Nat := match bits with
            | 8  => (st.mem.read8 (a.toUInt32 + off)).toNat
            | 16 => (st.mem.read16 (a.toUInt32 + off)).toNat
            | 32 => (st.mem.read32 (a.toUInt32 + off)).toNat
            | _  => (st.mem.read64 (a.toUInt32 + off)).toNat
          .Fallthrough st { s with values := .v128 (Simd.setLane bits lane v n) :: vs }
      | _ => .Invalid "v128LoadLane: ill-shaped operand stack"
    | _, .v128StoreLane bits lane off => match s.values with
      | .v128 v :: .i32 a :: vs =>
        if a.toNat + off.toNat + bits / 8 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          let n := Simd.getLane bits lane v
          let mem' := match bits with
            | 8  => st.mem.write8  (a + off) (UInt8.ofNat n)
            | 16 => st.mem.write16 (a + off) (UInt32.ofNat n)
            | 32 => st.mem.write32 (a + off) (UInt32.ofNat n)
            | _  => st.mem.write64 (a + off) (UInt64.ofNat n)
          .Fallthrough { st with mem := mem' } { s with values := vs }
      | .v128 v :: .i64 a :: vs =>
        if a.toNat + off.toNat + bits / 8 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          let n := Simd.getLane bits lane v
          let mem' := match bits with
            | 8  => st.mem.write8  (a.toUInt32 + off) (UInt8.ofNat n)
            | 16 => st.mem.write16 (a.toUInt32 + off) (UInt32.ofNat n)
            | 32 => st.mem.write32 (a.toUInt32 + off) (UInt32.ofNat n)
            | _  => st.mem.write64 (a.toUInt32 + off) (UInt64.ofNat n)
          .Fallthrough { st with mem := mem' } { s with values := vs }
      | _ => .Invalid "v128StoreLane: ill-shaped operand stack"

    -- Return / parametric / nullary
    | _, .ret  => .Return st s.values
    | _, .drop => match s.values with
      | _ :: vs => .Fallthrough st { s with values := vs }
      | _ => .Invalid "drop: empty operand stack"
    | _, .select => match s.values with
      | .i32 c :: v2 :: v1 :: vs =>
        let picked := if c ≠ 0 then v1 else v2
        .Fallthrough st { s with values := picked :: vs }
      | _ => .Invalid "select: ill-shaped operand stack"
    | _, .nop => .Fallthrough st s
    | _, .unreachable => .Trap st "unreachable"

    -- Reference instructions. Reference values are carried directly on
    -- the operand stack (`Value.funcref` / `Value.externref`), so these
    -- never touch the store: the null/func constructors just push a
    -- value, `refIsNull` inspects one.
    | _, .refNull       => .Fallthrough st { s with values := .funcref none :: s.values }
    | _, .refNullExtern => .Fallthrough st { s with values := .externref none :: s.values }
    | _, .refNullExn    => .Fallthrough st { s with values := .exnref none :: s.values }
    | _, .refFunc fidx  => .Fallthrough st { s with values := .funcref (some fidx) :: s.values }
    | _, .refIsNull => match s.values with
      | .funcref r :: vs =>
        .Fallthrough st { s with values := .i32 (if r.isNone then 1 else 0) :: vs }
      | .externref r :: vs =>
        .Fallthrough st { s with values := .i32 (if r.isNone then 1 else 0) :: vs }
      | .anyref r :: vs =>
        .Fallthrough st { s with values := .i32 (if r.isNone then 1 else 0) :: vs }
      | .exnref r :: vs =>
        .Fallthrough st { s with values := .i32 (if r.isNone then 1 else 0) :: vs }
      | _ => .Invalid "refIsNull: ill-shaped operand stack"

    -- GC-proposal instructions (i31/structs/arrays/casts): all are
    -- non-recursive single steps, handled by `execGcOp`.
    | _, .gc g => execGcOp m st s g

    -- Table read instructions. Both look the runtime table up on the
    -- store; neither mutates it. An out-of-range *table* index is a
    -- validation error (`.Invalid`); an out-of-bounds *element* index is a
    -- genuine runtime trap, with the wasm spec's canonical wording so the
    -- testsuite's `assert_trap` text matcher accepts it.
    | _, .tableGet tableIdx => match s.values with
      | .i32 i :: vs =>
        match st.tables[tableIdx]? with
        | none     => .Invalid s!"tableGet: table index {tableIdx} out of range"
        | some tbl =>
          match tbl[i.toNat]? with
          | none   => .Trap st "out of bounds table access"
          | some r => .Fallthrough st { s with values := r :: vs }
      -- table64: the element index arrives as an i64.
      | .i64 i :: vs =>
        match st.tables[tableIdx]? with
        | none     => .Invalid s!"tableGet: table index {tableIdx} out of range"
        | some tbl =>
          match tbl[i.toNat]? with
          | none   => .Trap st "out of bounds table access"
          | some r => .Fallthrough st { s with values := r :: vs }
      | _ => .Invalid "tableGet: ill-shaped operand stack"
    | _, .tableSize tableIdx =>
      match st.tables[tableIdx]? with
      | none     => .Invalid s!"tableSize: table index {tableIdx} out of range"
      | some tbl =>
        -- The result type follows the declared table's address type
        -- (table64): i64 for a 64-bit table, i32 otherwise.
        .Fallthrough st
          { s with values := sizeValue (m.tableIs64 tableIdx) tbl.length :: s.values }

    -- table.set t: pops [val(ref), idx(i32)] (top = val).
    | _, .tableSet tableIdx => match s.values with
      | v :: .i32 i :: vs =>
        match st.tables[tableIdx]? with
        | none     => .Invalid s!"tableSet: table index {tableIdx} out of range"
        | some tbl =>
          if i.toNat < tbl.length then
            let tables' := listSetAt st.tables tableIdx (listSetAt tbl i.toNat v)
            .Fallthrough { st with tables := tables' } { s with values := vs }
          else .Trap st "out of bounds table access"
      -- table64: the element index arrives as an i64.
      | v :: .i64 i :: vs =>
        match st.tables[tableIdx]? with
        | none     => .Invalid s!"tableSet: table index {tableIdx} out of range"
        | some tbl =>
          if i.toNat < tbl.length then
            let tables' := listSetAt st.tables tableIdx (listSetAt tbl i.toNat v)
            .Fallthrough { st with tables := tables' } { s with values := vs }
          else .Trap st "out of bounds table access"
      | _ => .Invalid "tableSet: ill-shaped operand stack"

    -- table.grow t: pops [delta(i32), init(ref)] (top = delta). Pushes
    -- the old size on success, -1 on failure. Growth past the declared
    -- max (or the implementation ceiling, see `Module.tableCap`) fails.
    | _, .tableGrow tableIdx => match s.values with
      | .i32 delta :: init :: vs =>
        match st.tables[tableIdx]? with
        | none     => .Invalid s!"tableGrow: table index {tableIdx} out of range"
        | some tbl =>
          let cur := tbl.length
          if cur + delta.toNat ≤ m.tableCap tableIdx then
            let tables' := listSetAt st.tables tableIdx
              (tbl ++ List.replicate delta.toNat init)
            .Fallthrough { st with tables := tables' }
              { s with values := .i32 (UInt32.ofNat cur) :: vs }
          else
            .Fallthrough st { s with values := .i32 (0xFFFFFFFF : UInt32) :: vs }
      -- table64: delta and result are i64.
      | .i64 delta :: init :: vs =>
        match st.tables[tableIdx]? with
        | none     => .Invalid s!"tableGrow: table index {tableIdx} out of range"
        | some tbl =>
          let cur := tbl.length
          if cur + delta.toNat ≤ m.tableCap tableIdx then
            let tables' := listSetAt st.tables tableIdx
              (tbl ++ List.replicate delta.toNat init)
            .Fallthrough { st with tables := tables' }
              { s with values := .i64 (UInt64.ofNat cur) :: vs }
          else
            .Fallthrough st { s with values := .i64 (0xFFFFFFFFFFFFFFFF : UInt64) :: vs }
      | _ => .Invalid "tableGrow: ill-shaped operand stack"

    -- table.fill t: pops [len(i32), val(ref), dst(i32)] (top = len).
    -- Bounds are checked before any write, matching the spec's atomicity.
    | _, .tableFill tableIdx => match s.values with
      | .i32 len :: v :: .i32 dst :: vs =>
        match st.tables[tableIdx]? with
        | none     => .Invalid s!"tableFill: table index {tableIdx} out of range"
        | some tbl =>
          if dst.toNat + len.toNat > tbl.length then
            .Trap st "out of bounds table access"
          else
            let tbl' := listWriteAt tbl dst.toNat (List.replicate len.toNat v)
            .Fallthrough { st with tables := listSetAt st.tables tableIdx tbl' }
              { s with values := vs }
      -- table64: dst and len are i64.
      | .i64 len :: v :: .i64 dst :: vs =>
        match st.tables[tableIdx]? with
        | none     => .Invalid s!"tableFill: table index {tableIdx} out of range"
        | some tbl =>
          if dst.toNat + len.toNat > tbl.length then
            .Trap st "out of bounds table access"
          else
            let tbl' := listWriteAt tbl dst.toNat (List.replicate len.toNat v)
            .Fallthrough { st with tables := listSetAt st.tables tableIdx tbl' }
              { s with values := vs }
      | _ => .Invalid "tableFill: ill-shaped operand stack"

    -- table.copy d s: pops [len(i32), src(i32), dst(i32)] (top = len).
    -- The source slice is captured before the write, so overlapping
    -- ranges behave like memmove, as the spec requires.
    | _, .tableCopy dstIdx srcIdx => match s.values with
      | .i32 len :: .i32 src :: .i32 dst :: vs =>
        match st.tables[dstIdx]?, st.tables[srcIdx]? with
        | some dstTbl, some srcTbl =>
          if dst.toNat + len.toNat > dstTbl.length
             ∨ src.toNat + len.toNat > srcTbl.length then
            .Trap st "out of bounds table access"
          else
            let slice := (srcTbl.drop src.toNat).take len.toNat
            let dstTbl' := listWriteAt dstTbl dst.toNat slice
            .Fallthrough { st with tables := listSetAt st.tables dstIdx dstTbl' }
              { s with values := vs }
        | _, _ => .Invalid s!"tableCopy: table index out of range"
      -- table64: all three operands are i64.
      | .i64 len :: .i64 src :: .i64 dst :: vs =>
        match st.tables[dstIdx]?, st.tables[srcIdx]? with
        | some dstTbl, some srcTbl =>
          if dst.toNat + len.toNat > dstTbl.length
             ∨ src.toNat + len.toNat > srcTbl.length then
            .Trap st "out of bounds table access"
          else
            let slice := (srcTbl.drop src.toNat).take len.toNat
            let dstTbl' := listWriteAt dstTbl dst.toNat slice
            .Fallthrough { st with tables := listSetAt st.tables dstIdx dstTbl' }
              { s with values := vs }
        | _, _ => .Invalid s!"tableCopy: table index out of range"
      | _ => .Invalid "tableCopy: ill-shaped operand stack"

    -- table.init t e: pops [len(i32), src(i32), dst(i32)] (top = len).
    -- A dropped segment behaves as length 0; bounds are checked before
    -- any write.
    | _, .tableInit tableIdx elemIdx => match s.values with
      | .i32 len :: .i32 src :: .i32 dst :: vs =>
        match st.tables[tableIdx]? with
        | none     => .Invalid s!"tableInit: table index {tableIdx} out of range"
        | some tbl =>
          match st.elementSegments[elemIdx]? with
          | none => .Invalid s!"tableInit: segment index {elemIdx} out of range"
          | some dropped? =>
            -- A non-dropped (passive/declarative) segment takes its values
            -- from `m.elements`, covering the const-expr item form; a dropped
            -- segment (which includes active segments, auto-dropped at
            -- instantiation) is empty.
            let vals := match dropped? with
              | none   => []
              | some _ => (m.elements[elemIdx]?.map ElementSegment.values).getD []
            if src.toNat + len.toNat > vals.length
               ∨ dst.toNat + len.toNat > tbl.length then
              .Trap st "out of bounds table access"
            else
              let slice := (vals.drop src.toNat).take len.toNat
              let tbl' := listWriteAt tbl dst.toNat slice
              .Fallthrough { st with tables := listSetAt st.tables tableIdx tbl' }
                { s with values := vs }
      -- table64: dst takes the table's address type (i64); src and len
      -- index into the element segment and stay i32 per spec.
      | .i32 len :: .i32 src :: .i64 dst :: vs =>
        match st.tables[tableIdx]? with
        | none     => .Invalid s!"tableInit: table index {tableIdx} out of range"
        | some tbl =>
          match st.elementSegments[elemIdx]? with
          | none => .Invalid s!"tableInit: segment index {elemIdx} out of range"
          | some dropped? =>
            -- A non-dropped (passive/declarative) segment takes its values
            -- from `m.elements`, covering the const-expr item form; a dropped
            -- segment (which includes active segments, auto-dropped at
            -- instantiation) is empty.
            let vals := match dropped? with
              | none   => []
              | some _ => (m.elements[elemIdx]?.map ElementSegment.values).getD []
            if src.toNat + len.toNat > vals.length
               ∨ dst.toNat + len.toNat > tbl.length then
              .Trap st "out of bounds table access"
            else
              let slice := (vals.drop src.toNat).take len.toNat
              let tbl' := listWriteAt tbl dst.toNat slice
              .Fallthrough { st with tables := listSetAt st.tables tableIdx tbl' }
                { s with values := vs }
      | _ => .Invalid "tableInit: ill-shaped operand stack"

    -- elem.drop e: mark element segment `e` as dropped. Idempotent.
    | _, .elemDrop elemIdx =>
      match st.elementSegments[elemIdx]? with
      | none => .Invalid s!"elemDrop: segment index {elemIdx} out of range"
      | some _ =>
        .Fallthrough { st with elementSegments := st.elementSegments.set elemIdx none } s

def exec (fuel : Nat) (m : Module) (st : Store α) (s : Locals) (p : Program)
    (env : HostEnv α := {}) : Continuation α :=
  match p with
  | [] => .Fallthrough st s
  | inst :: rest => match execOne fuel m st s inst env with
    | Continuation.Fallthrough st s => exec fuel m st s rest env
    | other => other

def run (fuel : Nat) (m : Module) (id : Nat)
        (initial : Store α) (params : List Value) (env : HostEnv α := {}) : Result α :=
  -- Unified function index space: indices `< m.imports.length` resolve to
  -- host imports via `env.funcs`; the remainder map to `m.funcs` after
  -- shifting down by `m.imports.length`. Matching on `m.imports[id]?`
  -- (rather than computing the boolean) keeps the lemma surface clean:
  -- modules with `imports = []` reduce the host arm away by computation.
  match m.imports[id]? with
  | some imp =>
    match env.funcs[id]? with
    | none    => .Invalid s!"unresolved host function: index {id}"
    | some hf =>
      let callerRemainder := params.drop imp.params.length
      -- Same calling convention as the wasm path: params reversed so the
      -- host receives the first declared param first.
      let hostArgs := (params.take imp.params.length).reverse
      match hf.invoke initial hostArgs with
      | .Return vs st' =>
        .Success (vs.take imp.results.length ++ callerRemainder) st'
      | .Trap st' msg  => .Trap st' msg
  | none =>
    match m.funcs[id - m.imports.length]? with
    | some f =>
      -- Standard Wasm calling convention. Params are reversed so local 0
      -- is the first (deepest) argument; only the top `f.results.length`
      -- values are returned to the caller; remaining caller args pass
      -- through unchanged.
      let callerRemainder := params.drop f.numParams
      match exec fuel m initial (f.toLocals (params.take f.numParams).reverse) f.body env with
      | Continuation.Fallthrough st s => .Success (s.values.take f.results.length ++ callerRemainder) st
      | Continuation.Return st vs     => .Success (vs.take f.results.length ++ callerRemainder) st
      | Continuation.Break 0 st s     => .Success (s.values.take f.results.length ++ callerRemainder) st
      | Continuation.Break (_+1) _ _  => .Invalid "Unexpected break targeting scope out of function"
      | Continuation.Invalid msg      => .Invalid msg
      | Continuation.OutOfFuel        => .OutOfFuel
      | Continuation.Trap st msg      => .Trap st msg
      -- Tail call: the callee replaces this frame. Validation guarantees
      -- the callee's result types equal `f.results`, so truncating its
      -- results to `f.results.length` and restoring this frame's
      -- caller-remainder preserves the standard calling convention.
      | Continuation.Throwing tag args st' _ => .Thrown tag args st'
      | Continuation.ReturnCall id' st' vs =>
        match runTail fuel m id' st' vs env with
        | .Success vs2 st2 => .Success (vs2.take f.results.length ++ callerRemainder) st2
        | other => other
    | none => .Invalid "Function index out of bounds"

/-- Resolve a pending tail call: re-dispatch with one less fuel. Kept as
its own (mutual) definition so `run`'s equation lemma does not mention
`run` itself — `simp only [run]` unfolds one frame and stops at
`runTail`, exactly like the pre-tail-call unfolding discipline. -/
def runTail (fuel : Nat) (m : Module) (id : Nat)
    (st : Store α) (vs : List Value) (env : HostEnv α := {}) : Result α :=
  match fuel with
  | 0 => .OutOfFuel
  | f' + 1 => run f' m id st vs env

end

/-- Evaluate the constant-expression initializers of globals that need to
run at instantiation (GC proposal: `struct.new`/`array.new*` allocate heap
objects). Each global's `initExpr` is executed in order against the
current store — so a later initializer sees earlier globals (`global.get`)
and the accumulated `gcHeap` — and its result value is written into the
global slot. Globals with an empty `initExpr` keep their decoded `init`. -/
def Module.runConstGlobals (fuel : Nat) (m : Module) (st : Store α)
    (env : HostEnv α := {}) : Store α := Id.run do
  let mut st := st
  let mut gi := 0
  for g in m.globals do
    if !g.initExpr.isEmpty then
      match exec fuel m st {} g.initExpr env with
      | .Fallthrough st' s' =>
        match s'.values with
        | v :: _ =>
          st := { st' with globals := { globals := st'.globals.globals.set gi v } }
        | [] => pure ()
      | _ => pure ()
    gi := gi + 1
  return st

/-- Evaluate the constant-expression items of active GC element segments
(GC proposal) and write the resulting reference values into their tables.
Runs after `runConstGlobals` so items may read globals. Plain funcref
segments (`funcs`) are applied separately and have no `exprs`. -/
def Module.runConstElems (fuel : Nat) (m : Module) (st : Store α)
    (env : HostEnv α := {}) : Store α := Id.run do
  let mut st := st
  for seg in m.elements do
    match seg.tableIdx, seg.offset with
    | some ti, some off =>
      -- Segments whose offset is itself a pending const-expr are written
      -- by `runActiveSegments` (which knows the real offset) instead.
      if !seg.exprs.isEmpty && seg.offsetExpr.isEmpty then
        let mut i := 0
        for e in seg.exprs do
          match exec fuel m st {} e env with
          | .Fallthrough st' s' =>
            st := st'
            match s'.values, st'.tables[ti]? with
            | v :: _, some tbl =>
              st := { st' with tables := st'.tables.set ti (tbl.set (off + i) v) }
            | _, _ => pure ()
          | _ => pure ()
          i := i + 1
    | _, _ => pure ()
  return st

/-- Write the active data/element segments whose offset is a constant
expression that could not be folded at decode time (`global.get` of an
imported global, extended-const arithmetic). `Module.initialStore` skips
these segments (their offset depends on the store); this pass evaluates
each `offsetExpr` against the current store and writes the segment at
the computed offset. Runs after `runConstGlobals` so the offsets see the
evaluated (and imported) globals. -/
def Module.runActiveSegments (fuel : Nat) (m : Module) (st : Store α)
    (env : HostEnv α := {}) : Store α := Id.run do
  let mut st := st
  -- Evaluate one offset const-expr to a byte/element offset. `i64`
  -- results come from memory64/table64 modules.
  let evalOffset (st : Store α) (prog : Program) : Option Nat :=
    match exec fuel m st {} prog env with
    | .Fallthrough _ s' =>
      match s'.values with
      | .i32 v :: _ => some v.toNat
      | .i64 v :: _ => some v.toNat
      | _           => none
    | _ => none
  -- Active data segments with a pending offset expression. Segments live
  -- in one global, source-ordered list (memory 0's `data`), routed to
  -- their memory by `DataSegment.memIdx`.
  let segs := match m.memory with
    | some decl => decl.data
    | none      => []
  for seg in segs do
    if seg.offset.isSome && !seg.offsetExpr.isEmpty then
      match evalOffset st seg.offsetExpr with
      | some off =>
        if seg.memIdx = 0 then
          st := { st with mem := st.mem.writeBytes off seg.bytes }
        else
          match st.extraMems[seg.memIdx - 1]? with
          | some mem0 =>
            let mems := st.extraMems.set (seg.memIdx - 1) (mem0.writeBytes off seg.bytes)
            st := { st with extraMems := mems }
          | none => pure ()
      | none => pure ()
  -- Active element segments with a pending offset expression.
  for seg in m.elements do
    match seg.tableIdx, seg.offset with
    | some ti, some _ =>
      if !seg.offsetExpr.isEmpty then
        match evalOffset st seg.offsetExpr, st.tables[ti]? with
        | some off, some tbl =>
          if seg.exprs.isEmpty then
            let tbls := st.tables.set ti (listWriteAt tbl off (seg.funcs.map Value.funcref))
            st := { st with tables := tbls }
          else
            -- GC const-expr items, as in `runConstElems`, but at the
            -- evaluated offset.
            let mut i := 0
            for e in seg.exprs do
              match exec fuel m st {} e env with
              | .Fallthrough st' s' =>
                st := st'
                match s'.values, st'.tables[ti]? with
                | v :: _, some tbl' =>
                  st := { st' with tables := st'.tables.set ti (tbl'.set (off + i) v) }
                | _, _ => pure ()
              | _ => pure ()
              i := i + 1
        | _, _ => pure ()
    | _, _ => pure ()
  return st

end Wasm
