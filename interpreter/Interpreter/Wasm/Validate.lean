import Interpreter.Wasm.Syntax

/-!
# A partial static validator (GC proposal)

`Module.validate` performs the structural well-formedness checks the spec
testsuite's `assert_invalid` / `assert_malformed` commands exercise for the
GC proposal: type-index ranges, `sub` subtyping (finality + structural
subtype), field/element mutability, and constant-expression initializers.

It is deliberately run **only** on modules an `assert_invalid` /
`assert_malformed` command already declares ill-formed (see the testsuite
harness), so it never rejects a module a normal `(module …)` command would
accept — a too-aggressive check can only make an already-invalid module
pass for a slightly different reason, never break a valid one. A full
operand-stack type checker (for the `type mismatch` cases) is future work.
-/

namespace Wasm

/-- Whether composite `a` is a structural subtype of composite `b`
(reflexive comparison is handled by the caller). Mutable fields/elements
are invariant; we conservatively require matching storage type and
mutability, and exact func signatures. -/
def CompositeType.structSubtype : CompositeType → CompositeType → Bool
  | .struct af, .struct bf =>
    af.length ≥ bf.length &&
    (List.range bf.length).all fun i => match af[i]?, bf[i]? with
      | some x, some y => x.storage == y.storage && x.isMut == y.isMut
      | _, _ => false
  | .array ae, .array be => ae.storage == be.storage && ae.isMut == be.isMut
  | .func a, .func b => a.params == b.params && a.results == b.results
  | _, _ => false

/-- Recursively collect every instruction in a program, descending into the
bodies of `block`/`loop`/`if`/`try_table`. -/
partial def Program.allInstrs (p : Program) : List Instruction :=
  p.flatMap fun i => i :: match i with
    | .block _ _ body _ _ | .loop _ _ body _ _ => Program.allInstrs body
    | .iff _ _ thn els _ _ => Program.allInstrs thn ++ Program.allInstrs els
    | .tryTable _ _ _ body _ _ => Program.allInstrs body
    | _ => []

/-- The GC type indices an instruction's immediates reference. Function type
indices on `(return_)call_indirect` and `(return_)call_ref` index `Module.types`
instead and are checked by `Instruction.checkFunctionRefs`. -/
def Instruction.gcTypeRefs : Instruction → List Nat
  | .gc op => match op with
    | .refNullAny _ => []
    | .structNew t | .structNewDefault t
    | .arrayNew t | .arrayNewDefault t | .arrayNewFixed t _
    | .arrayGet t | .arrayGetS t | .arrayGetU t | .arraySet t
    | .arrayFill t | .arrayNewData t _ | .arrayInitData t _
    | .arrayNewElem t _ | .arrayInitElem t _ => [t]
    | .structGet t _ | .structGetS t _ | .structGetU t _ | .structSet t _ => [t]
    | .arrayCopy a b => [a, b]
    | .refTest _ (.concrete t) | .refCast _ (.concrete t)
    | .brOnCast _ _ (.concrete t) | .brOnCastFail _ _ (.concrete t) => [t]
    | _ => []
  | _ => []

/-! ### Bulk-memory reference validation

These checks discharge the index failures which the executable small-step
machine retains only as defensive `InternalError`s. `data.drop` deliberately
does not require a memory, while `memory.init` requires both its selected
memory and its data segment to exist. -/

def Module.memoryDecl? (m : Module) (index : Nat) : Option MemDecl :=
  if index = 0 then m.memory else m.extraMemories[index - 1]?

def Module.dataSegmentCount (m : Module) : Nat :=
  match m.memory with
  | some memory => memory.data.length
  | none => 0

def Instruction.isScalarMemoryAccess : Instruction → Bool
  | .load8U _ | .load8S _ | .load16U _ | .load16S _ | .load32 _
  | .store8 _ | .store16 _ | .store32 _
  | .load64 _ | .store64 _
  | .load8UI64 _ | .load8SI64 _ | .load16UI64 _ | .load16SI64 _
  | .load32UI64 _ | .load32SI64 _
  | .store8I64 _ | .store16I64 _ | .store32I64 _
  | .f32Load _ | .f64Load _ | .f32Store _ | .f64Store _ => true
  | _ => false

def Instruction.isSimdMemoryAccess : Instruction → Bool
  | .v128Load _ | .v128Store _
  | .v128LoadExt _ _ _ | .v128LoadSplat _ _ | .v128LoadZero _ _
  | .v128LoadLane _ _ _ | .v128StoreLane _ _ _ => true
  | _ => false

def Instruction.checkBulkMemoryRefs
    (m : Module) : Instruction → Except String Unit
  | .memorySize | .memoryGrow | .memoryFill | .memoryCopy =>
      if (m.memoryDecl? 0).isNone then .error "unknown memory"
      else .ok ()
  | .memoryInit dataIndex =>
      if (m.memoryDecl? 0).isNone then .error "unknown memory"
      else if dataIndex ≥ m.dataSegmentCount then .error "unknown data segment"
      else .ok ()
  | .dataDrop dataIndex =>
      if dataIndex ≥ m.dataSegmentCount then .error "unknown data segment"
      else .ok ()
  | .memOp memoryIndex (.memoryInit dataIndex) =>
      if (m.memoryDecl? memoryIndex).isNone then .error "unknown memory"
      else if dataIndex ≥ m.dataSegmentCount then .error "unknown data segment"
      else .ok ()
  | .memOp memoryIndex .memoryFill =>
      if (m.memoryDecl? memoryIndex).isNone then .error "unknown memory"
      else .ok ()
  | .memOp memoryIndex .memoryCopy =>
      if (m.memoryDecl? memoryIndex).isNone then .error "unknown memory"
      else .ok ()
  | .memOp memoryIndex .memorySize =>
      if (m.memoryDecl? memoryIndex).isNone then .error "unknown memory"
      else .ok ()
  | .memOp memoryIndex .memoryGrow =>
      if (m.memoryDecl? memoryIndex).isNone then .error "unknown memory"
      else .ok ()
  | .memOp memoryIndex operation =>
      if operation.isScalarMemoryAccess || operation.isSimdMemoryAccess then
        if (m.memoryDecl? memoryIndex).isNone then .error "unknown memory"
        else .ok ()
      else .ok ()
  | operation =>
      if operation.isScalarMemoryAccess || operation.isSimdMemoryAccess then
        if (m.memoryDecl? 0).isNone then .error "unknown memory"
        else .ok ()
      else .ok ()

/-! ### SIMD immediate validation -/

def Instruction.checkSimdImmediates : Instruction → Except String Unit
  | .vExtractLane shape _ lane | .vReplaceLane shape lane =>
      if lane ≥ shape.laneCount then .error "invalid lane index" else .ok ()
  | .v128LoadLane bits lane _ | .v128StoreLane bits lane _ =>
      if bits = 0 || 128 % bits != 0 || lane ≥ 128 / bits then
        .error "invalid lane index"
      else
        .ok ()
  | .vShuffle indices =>
      if indices.length != 16 || indices.any (· ≥ 32) then
        .error "invalid lane index"
      else
        .ok ()
  | _ => .ok ()

theorem Instruction.checkBulkMemoryRefs_memoryFill_ok
    (m : Module)
    (h : Instruction.memoryFill.checkBulkMemoryRefs m = .ok ()) :
    (m.memoryDecl? 0).isSome = true := by
  simp only [Instruction.checkBulkMemoryRefs] at h
  split at h <;>
    simp_all [Option.isSome_iff_ne_none, Option.isNone_iff_eq_none]

theorem Instruction.checkBulkMemoryRefs_memorySize_ok
    (m : Module)
    (h : Instruction.memorySize.checkBulkMemoryRefs m = .ok ()) :
    (m.memoryDecl? 0).isSome = true := by
  simp only [Instruction.checkBulkMemoryRefs] at h
  split at h <;>
    simp_all [Option.isSome_iff_ne_none, Option.isNone_iff_eq_none]

theorem Instruction.checkBulkMemoryRefs_memoryGrow_ok
    (m : Module)
    (h : Instruction.memoryGrow.checkBulkMemoryRefs m = .ok ()) :
    (m.memoryDecl? 0).isSome = true := by
  simp only [Instruction.checkBulkMemoryRefs] at h
  split at h <;>
    simp_all [Option.isSome_iff_ne_none, Option.isNone_iff_eq_none]

theorem Instruction.checkBulkMemoryRefs_memoryCopy_ok
    (m : Module)
    (h : Instruction.memoryCopy.checkBulkMemoryRefs m = .ok ()) :
    (m.memoryDecl? 0).isSome = true := by
  simp only [Instruction.checkBulkMemoryRefs] at h
  split at h <;>
    simp_all [Option.isSome_iff_ne_none, Option.isNone_iff_eq_none]

theorem Instruction.checkBulkMemoryRefs_memoryInit_ok
    (m : Module) (dataIndex : Nat)
    (h : (Instruction.memoryInit dataIndex).checkBulkMemoryRefs m = .ok ()) :
    (m.memoryDecl? 0).isSome = true ∧
      dataIndex < m.dataSegmentCount := by
  simp only [Instruction.checkBulkMemoryRefs] at h
  split at h <;>
    simp_all [Option.isSome_iff_ne_none, Option.isNone_iff_eq_none]

theorem Instruction.checkBulkMemoryRefs_dataDrop_ok
    (m : Module) (dataIndex : Nat)
    (h : (Instruction.dataDrop dataIndex).checkBulkMemoryRefs m = .ok ()) :
    dataIndex < m.dataSegmentCount := by
  simp only [Instruction.checkBulkMemoryRefs] at h
  split at h <;> simp_all

theorem Instruction.checkBulkMemoryRefs_indexedMemoryInit_ok
    (m : Module) (memoryIndex dataIndex : Nat)
    (h : Instruction.checkBulkMemoryRefs m
      (.memOp memoryIndex (.memoryInit dataIndex)) = .ok ()) :
    (m.memoryDecl? memoryIndex).isSome = true ∧
      dataIndex < m.dataSegmentCount := by
  simp only [Instruction.checkBulkMemoryRefs] at h
  split at h <;>
    simp_all [Option.isSome_iff_ne_none, Option.isNone_iff_eq_none]

theorem Instruction.checkBulkMemoryRefs_indexedMemoryFill_ok
    (m : Module) (memoryIndex : Nat)
    (h : Instruction.checkBulkMemoryRefs m
      (.memOp memoryIndex .memoryFill) = .ok ()) :
    (m.memoryDecl? memoryIndex).isSome = true := by
  simp only [Instruction.checkBulkMemoryRefs] at h
  split at h <;>
    simp_all [Option.isSome_iff_ne_none, Option.isNone_iff_eq_none]

theorem Instruction.checkBulkMemoryRefs_indexedMemoryCopy_ok
    (m : Module) (memoryIndex : Nat)
    (h : Instruction.checkBulkMemoryRefs m
      (.memOp memoryIndex .memoryCopy) = .ok ()) :
    (m.memoryDecl? memoryIndex).isSome = true := by
  simp only [Instruction.checkBulkMemoryRefs] at h
  split at h <;>
    simp_all [Option.isSome_iff_ne_none, Option.isNone_iff_eq_none]

theorem Instruction.checkBulkMemoryRefs_indexedMemorySize_ok
    (m : Module) (memoryIndex : Nat)
    (h : Instruction.checkBulkMemoryRefs m
      (.memOp memoryIndex .memorySize) = .ok ()) :
    (m.memoryDecl? memoryIndex).isSome = true := by
  simp only [Instruction.checkBulkMemoryRefs] at h
  split at h <;>
    simp_all [Option.isSome_iff_ne_none, Option.isNone_iff_eq_none]

theorem Instruction.checkBulkMemoryRefs_indexedMemoryGrow_ok
    (m : Module) (memoryIndex : Nat)
    (h : Instruction.checkBulkMemoryRefs m
      (.memOp memoryIndex .memoryGrow) = .ok ()) :
    (m.memoryDecl? memoryIndex).isSome = true := by
  simp only [Instruction.checkBulkMemoryRefs] at h
  split at h <;>
    simp_all [Option.isSome_iff_ne_none, Option.isNone_iff_eq_none]

theorem Instruction.checkBulkMemoryRefs_scalar_ok
    (m : Module) (operation : Instruction)
    (hscalar : operation.isScalarMemoryAccess = true)
    (h : operation.checkBulkMemoryRefs m = .ok ()) :
    (m.memoryDecl? 0).isSome = true := by
  cases operation <;>
    simp_all [Instruction.isScalarMemoryAccess,
      Instruction.checkBulkMemoryRefs, Option.isSome_iff_ne_none,
      Option.isNone_iff_eq_none]

theorem Instruction.checkBulkMemoryRefs_indexedScalar_ok
    (m : Module) (memoryIndex : Nat) (operation : Instruction)
    (hscalar : operation.isScalarMemoryAccess = true)
    (h : (Instruction.memOp memoryIndex operation).checkBulkMemoryRefs m =
      .ok ()) :
    (m.memoryDecl? memoryIndex).isSome = true := by
  cases operation <;>
    simp_all [Instruction.isScalarMemoryAccess,
      Instruction.checkBulkMemoryRefs, Option.isSome_iff_ne_none,
      Option.isNone_iff_eq_none]

/-- Instantiation preserves exactly one runtime status entry per declared data
segment. This is the bridge from validator index bounds to the lookup required
by `stepChecked?`. -/
theorem Module.initialStore_dataSegments_length [Inhabited α] (m : Module) :
    (m.initialStore : Store α).dataSegments.length = m.dataSegmentCount := by
  cases hmemory : m.memory with
  | none =>
      simp [Module.initialStore, Module.dataSegmentCount, hmemory]
  | some memory =>
      simp [Module.initialStore, Module.dataSegmentCount, hmemory]

theorem Module.initialStore_dataSegment_exists [Inhabited α]
    (m : Module) (index : Nat) (hindex : index < m.dataSegmentCount) :
    ∃ segment,
      (m.initialStore : Store α).dataSegments[index]? = some segment := by
  have hinBounds :
      index < (m.initialStore : Store α).dataSegments.length := by
    rw [m.initialStore_dataSegments_length]
    exact hindex
  exact ⟨_, List.getElem?_eq_getElem hinBounds⟩

/-! ### Table/element-segment reference validation -/

def Module.tableDecl? (m : Module) (index : Nat) : Option TableDecl :=
  m.tables[index]?

def Module.elementSegmentCount (m : Module) : Nat :=
  m.elements.length

def Instruction.checkTableSegmentRefs
    (m : Module) : Instruction → Except String Unit
  | .tableGet tableIndex | .tableSet tableIndex | .tableSize tableIndex
  | .tableGrow tableIndex | .tableFill tableIndex =>
      if (m.tableDecl? tableIndex).isNone then .error "unknown table"
      else .ok ()
  | .tableCopy destinationTableIndex sourceTableIndex =>
      if (m.tableDecl? destinationTableIndex).isNone then
        .error "unknown table"
      else if (m.tableDecl? sourceTableIndex).isNone then
        .error "unknown table"
      else .ok ()
  | .tableInit tableIndex elementIndex =>
      if (m.tableDecl? tableIndex).isNone then .error "unknown table"
      else if elementIndex ≥ m.elementSegmentCount then
        .error "unknown element segment"
      else .ok ()
  | .elemDrop elementIndex =>
      if elementIndex ≥ m.elementSegmentCount then
        .error "unknown element segment"
      else .ok ()
  | _ => .ok ()

theorem Instruction.checkTableSegmentRefs_table_ok
    (m : Module) (tableIndex : Nat) (operation : Instruction)
    (hoperation :
      operation = .tableGet tableIndex ∨
      operation = .tableSet tableIndex ∨
      operation = .tableSize tableIndex ∨
      operation = .tableGrow tableIndex ∨
      operation = .tableFill tableIndex)
    (h : operation.checkTableSegmentRefs m = .ok ()) :
    (m.tableDecl? tableIndex).isSome = true := by
  rcases hoperation with rfl | rfl | rfl | rfl | rfl <;>
    simp only [Instruction.checkTableSegmentRefs] at h <;>
    split at h <;>
    simp_all [Option.isSome_iff_ne_none, Option.isNone_iff_eq_none]

theorem Instruction.checkTableSegmentRefs_tableCopy_ok
    (m : Module) (destinationTableIndex sourceTableIndex : Nat)
    (h : Instruction.checkTableSegmentRefs m
      (.tableCopy destinationTableIndex sourceTableIndex) = .ok ()) :
    (m.tableDecl? destinationTableIndex).isSome = true ∧
      (m.tableDecl? sourceTableIndex).isSome = true := by
  grind [Instruction.checkTableSegmentRefs, Option.isSome_iff_ne_none,
    Option.isNone_iff_eq_none]

theorem Instruction.checkTableSegmentRefs_tableInit_ok
    (m : Module) (tableIndex elementIndex : Nat)
    (h : Instruction.checkTableSegmentRefs m
      (.tableInit tableIndex elementIndex) = .ok ()) :
    (m.tableDecl? tableIndex).isSome = true ∧
      elementIndex < m.elementSegmentCount := by
  simp only [Instruction.checkTableSegmentRefs] at h
  split at h <;>
    simp_all [Option.isSome_iff_ne_none, Option.isNone_iff_eq_none]

theorem Instruction.checkTableSegmentRefs_elemDrop_ok
    (m : Module) (elementIndex : Nat)
    (h : (Instruction.elemDrop elementIndex).checkTableSegmentRefs m =
      .ok ()) :
    elementIndex < m.elementSegmentCount := by
  simp only [Instruction.checkTableSegmentRefs] at h
  split at h <;> simp_all

theorem listSetAt_length (values : List α) (index : Nat) (value : α) :
    (listSetAt values index value).length = values.length := by
  induction values generalizing index with
  | nil => simp [listSetAt]
  | cons head tail ih =>
      cases index with
      | zero => simp [listSetAt]
      | succ index => simp [listSetAt, ih]

theorem Module.initialStore_elementSegments_length [Inhabited α]
    (m : Module) :
    (m.initialStore : Store α).elementSegments.length =
      m.elementSegmentCount := by
  simp [Module.initialStore, Module.elementSegmentCount]

theorem Module.initialStore_elementSegment_exists [Inhabited α]
    (m : Module) (index : Nat)
    (hindex : index < m.elementSegmentCount) :
    ∃ segment,
      (m.initialStore : Store α).elementSegments[index]? = some segment := by
  have hinBounds :
      index < (m.initialStore : Store α).elementSegments.length := by
    rw [m.initialStore_elementSegments_length]
    exact hindex
  exact ⟨_, List.getElem?_eq_getElem hinBounds⟩

theorem Module.initialStore_tables_length [Inhabited α] (m : Module) :
    (m.initialStore : Store α).tables.length = m.tables.length := by
  simp only [Module.initialStore]
  let updateTable : List TableInst → ElementSegment → List TableInst :=
    fun tables segment =>
      match segment.tableIdx, segment.offset with
      | some tableIndex, some offset =>
        if segment.offsetExpr.isEmpty then
          match tables[tableIndex]? with
          | some table =>
            if offset + segment.plainValues.length ≤ table.length then
              listSetAt tables tableIndex
                (listWriteAt table offset segment.plainValues)
            else tables
          | none => tables
        else tables
      | _, _ => tables
  have hupdate (tables : List TableInst) (segment : ElementSegment) :
      (updateTable tables segment).length = tables.length := by
    unfold updateTable
    grind [listSetAt_length]
  have hfold (segments : List ElementSegment) (tables : List TableInst) :
      (segments.foldl updateTable tables).length = tables.length := by
    induction segments generalizing tables with
    | nil => rfl
    | cons segment rest ih =>
        simp only [List.foldl_cons]
        rw [ih, hupdate]
  change
    (m.elements.foldl updateTable
      (m.tables.map fun table =>
        (List.replicate table.min table.elemType.zero : TableInst))).length =
      m.tables.length
  rw [hfold]
  simp

theorem Module.initialStore_table_exists [Inhabited α]
    (m : Module) (index : Nat)
    (hindex : (m.tableDecl? index).isSome = true) :
    ∃ table, (m.initialStore : Store α).tables[index]? = some table := by
  have hdeclared : index < m.tables.length := by
    cases htable : m.tables[index]? with
    | none => simp [Module.tableDecl?, htable] at hindex
    | some table =>
        exact (List.getElem?_eq_some_iff.mp htable).1
  have hinBounds : index < (m.initialStore : Store α).tables.length := by
    rw [m.initialStore_tables_length]
    exact hdeclared
  exact ⟨_, List.getElem?_eq_getElem hinBounds⟩

/-! ### Global reference validation -/

def Instruction.checkGlobalRefs
    (m : Module) : Instruction → Except String Unit
  | .globalGet index =>
      if m.globals[index]?.isNone then .error "unknown global" else .ok ()
  | .globalSet index =>
      match m.globals[index]? with
      | none => .error "unknown global"
      | some global =>
        if global.isMut then .ok () else .error "immutable global"
  | _ => .ok ()

theorem Instruction.checkGlobalRefs_get_ok
    (m : Module) (index : Nat)
    (h : (Instruction.globalGet index).checkGlobalRefs m = .ok ()) :
    ∃ global, m.globals[index]? = some global := by
  cases hglobal : m.globals[index]? with
  | none => simp [Instruction.checkGlobalRefs, hglobal] at h
  | some global => exact ⟨global, rfl⟩

theorem Instruction.checkGlobalRefs_set_ok
    (m : Module) (index : Nat)
    (h : (Instruction.globalSet index).checkGlobalRefs m = .ok ()) :
    ∃ global, m.globals[index]? = some global := by
  cases hglobal : m.globals[index]? with
  | none => simp [Instruction.checkGlobalRefs, hglobal] at h
  | some global => exact ⟨global, rfl⟩

theorem Instruction.checkGlobalRefs_set_mutable
    (m : Module) (index : Nat)
    (h : (Instruction.globalSet index).checkGlobalRefs m = .ok ()) :
    ∃ global, m.globals[index]? = some global ∧ global.isMut = true := by
  cases hglobal : m.globals[index]? with
  | none => simp [Instruction.checkGlobalRefs, hglobal] at h
  | some global =>
      simp [Instruction.checkGlobalRefs, hglobal] at h
      exact ⟨global, rfl, h⟩

/-! ### Local reference validation -/

def Instruction.checkLocalRefs
    (localCount : Nat) : Instruction → Except String Unit
  | .localGet index | .localSet index =>
      if index ≥ localCount then .error "unknown local" else .ok ()
  | _ => .ok ()

theorem Instruction.checkLocalRefs_ok
    (localCount index : Nat) (operation : Instruction)
    (hoperation :
      operation = .localGet index ∨ operation = .localSet index)
    (h : operation.checkLocalRefs localCount = .ok ()) :
    index < localCount := by
  rcases hoperation with rfl | rfl <;>
    simp [Instruction.checkLocalRefs] at h ⊢
  · omega
  · omega

/-! ### Function and call-immediate validation -/

def Program.declaresFunctionRef (program : Program) (functionIndex : Nat) : Bool :=
  program.allInstrs.any fun
    | .refFunc index => index == functionIndex
    | _ => false

def Module.functionRefDeclared (m : Module) (functionIndex : Nat) : Bool :=
  m.exports.any (·.funcIdx == functionIndex) ||
  (m.globals.any fun global =>
    global.sourceInit.any (·.declaresFunctionRef functionIndex)) ||
  (m.elements.any fun segment =>
    segment.funcs.any (· == some functionIndex) ||
    segment.exprs.any (·.declaresFunctionRef functionIndex))

def Instruction.checkFunctionRefs
    (m : Module) : Instruction → Except String Unit
  | .call functionIndex | .returnCall functionIndex =>
      if (m.funcSig? functionIndex).isNone then .error "unknown function"
      else .ok ()
  | .refFunc functionIndex =>
      if (m.funcSig? functionIndex).isNone then .error "unknown function"
      else if !m.functionRefDeclared functionIndex then
        .error "undeclared function reference"
      else .ok ()
  | .callIndirect typeIndex tableIndex
  | .returnCallIndirect typeIndex tableIndex =>
      if m.types[typeIndex]?.isNone then .error "unknown type"
      else if (m.tableDecl? tableIndex).isNone then .error "unknown table"
      else .ok ()
  | .callRef typeIndex | .returnCallRef typeIndex =>
      if m.types[typeIndex]?.isNone then .error "unknown type"
      else .ok ()
  | _ => .ok ()

theorem Instruction.checkFunctionRefs_direct_ok
    (m : Module) (functionIndex : Nat) (operation : Instruction)
    (hoperation :
      operation = .call functionIndex ∨
      operation = .returnCall functionIndex ∨
      operation = .refFunc functionIndex)
    (h : operation.checkFunctionRefs m = .ok ()) :
    ∃ signature, m.funcSig? functionIndex = some signature := by
  rcases hoperation with rfl | rfl | rfl <;>
    cases hsignature : m.funcSig? functionIndex with
    | none => simp [Instruction.checkFunctionRefs, hsignature] at h
    | some signature => exact ⟨signature, rfl⟩

theorem Instruction.checkFunctionRefs_indirect_ok
    (m : Module) (typeIndex tableIndex : Nat) (operation : Instruction)
    (hoperation :
      operation = .callIndirect typeIndex tableIndex ∨
      operation = .returnCallIndirect typeIndex tableIndex)
    (h : operation.checkFunctionRefs m = .ok ()) :
    (∃ signature, m.types[typeIndex]? = some signature) ∧
      (∃ table, m.tableDecl? tableIndex = some table) := by
  rcases hoperation with rfl | rfl <;>
    cases hsignature : m.types[typeIndex]? with
    | none => simp [Instruction.checkFunctionRefs, hsignature] at h
    | some signature =>
      cases htable : m.tableDecl? tableIndex with
      | none =>
        simp [Instruction.checkFunctionRefs, hsignature, htable] at h
      | some table => exact ⟨⟨signature, rfl⟩, ⟨table, rfl⟩⟩

/-! ### Module interface validation -/

def Module.checkStart (m : Module) : Except String Unit :=
  match m.startFunc with
  | none => .ok ()
  | some index =>
      match m.funcSig? index with
      | none => .error "unknown function"
      | some signature =>
          if !signature.params.isEmpty || !signature.results.isEmpty then
            .error "start function"
          else
            .ok ()

def Module.checkInterface (m : Module) : Except String Unit := do
  for item in m.exports do
    if (m.funcSig? item.funcIdx).isNone then throw "unknown function"
  for (_, index) in m.globalExports do
    if m.globals[index]?.isNone then throw "unknown global"
  for (_, index) in m.tableExports do
    if (m.tableDecl? index).isNone then throw "unknown table"
  for (_, index) in m.memoryExports do
    if (m.memoryDecl? index).isNone then throw "unknown memory"
  let names :=
    m.exports.map (·.name) ++
    m.globalExports.map (·.1) ++
    m.tableExports.map (·.1) ++
    m.memoryExports.map (·.1)
  if _h : names.Nodup then pure () else throw "duplicate export name"
  m.checkStart

theorem Module.checkStart_ok
    (m : Module) (index : Nat)
    (hstart : m.startFunc = some index)
    (h : m.checkStart = .ok ()) :
    ∃ signature, m.funcSig? index = some signature ∧
      signature.params = [] ∧ signature.results = [] := by
  simp only [Module.checkStart, hstart] at h
  cases hsignature : m.funcSig? index with
  | none => simp [hsignature] at h
  | some signature =>
      simp [hsignature] at h
      exact ⟨signature, rfl, h⟩

/-! ### Active segment resource validation -/

def DataSegment.checkMemoryRef
    (m : Module) (segment : DataSegment) : Except String Unit :=
  match segment.offset with
  | none => .ok ()
  | some _ =>
      if (m.memoryDecl? segment.memIdx).isNone then .error "unknown memory"
      else .ok ()

theorem DataSegment.checkMemoryRef_active_ok
    (m : Module) (segment : DataSegment) (offset : UInt32)
    (hoffset : segment.offset = some offset)
    (h : segment.checkMemoryRef m = .ok ()) :
    ∃ memory, m.memoryDecl? segment.memIdx = some memory := by
  simp only [DataSegment.checkMemoryRef, hoffset] at h
  cases hmemory : m.memoryDecl? segment.memIdx with
  | none => simp [hmemory] at h
  | some memory => exact ⟨memory, rfl⟩

def ElementSegment.checkTableRef
    (m : Module) (segment : ElementSegment) : Except String Unit :=
  match segment.offset with
  | none => .ok ()
  | some _ =>
      match segment.tableIdx with
      | none => .error "unknown table"
      | some index =>
          if (m.tableDecl? index).isNone then .error "unknown table" else .ok ()

theorem ElementSegment.checkTableRef_active_ok
    (m : Module) (segment : ElementSegment) (offset tableIndex : Nat)
    (hoffset : segment.offset = some offset)
    (htableIndex : segment.tableIdx = some tableIndex)
    (h : segment.checkTableRef m = .ok ()) :
    ∃ table, m.tableDecl? tableIndex = some table := by
  simp only [ElementSegment.checkTableRef, hoffset, htableIndex] at h
  cases htable : m.tableDecl? tableIndex with
  | none => simp [htable] at h
  | some table => exact ⟨table, rfl⟩

/-- Whether a constant-expression program uses only constant instructions
(the forms a global / element initializer may contain). -/
def Program.isConstExpr (p : Program) : Bool :=
  p.all fun i => match i with
    | .const _ | .constI64 _ | .f32Const _ | .f64Const _ | .vConst _
    | .refNull _ | .refNullExtern _ | .refNullExn _ | .refFunc _ => true
    | .globalGet _ => true
    | .add | .sub | .mul | .addI64 | .subI64 | .mulI64 => true
    | .gc g => match g with
      | .refI31 | .refNullAny _ | .structNew _ | .structNewDefault _
      | .arrayNew _ | .arrayNewDefault _ | .arrayNewFixed _ _ => true
      | _ => false
    | _ => false

/-! ### Control-label validation

The function body has an implicit label at depth `0`; each structured control
instruction adds one inner label. Branches outside that range are rejected
before execution, rather than becoming a checked-step `InternalError`.
-/

partial def Program.checkBranchDepth
    (labels : Nat) (program : Program) : Except String Unit := do
  for instruction in program do
    match instruction with
    | .block _ _ body _ _ | .loop _ _ body _ _ =>
        Program.checkBranchDepth (labels + 1) body
    | .iff _ _ thenBody elseBody _ _ =>
        Program.checkBranchDepth (labels + 1) thenBody
        Program.checkBranchDepth (labels + 1) elseBody
    | .tryTable _ _ _ body _ _ =>
        Program.checkBranchDepth (labels + 1) body
    | .br depth | .br_if depth
    | .brOnNull depth | .brOnNonNull depth =>
        if depth > labels then throw "unknown label"
    | .brTable targets defaultTarget =>
        if defaultTarget > labels || targets.any (· > labels) then
          throw "unknown label"
    | .gc (.brOnCast depth _ _) | .gc (.brOnCastFail depth _ _) =>
        if depth > labels then throw "unknown label"
    | _ => pure ()

/-! ### Operand-stack type check

The checker models straight-line instructions precisely and recursively checks
`block`, `loop`, `if`, and `try_table`. Decoded structured instructions retain
their exact parameter/result types; cached arities and optional metadata keep
legacy handwritten modules source-compatible. Unknowns remain only for
polymorphic operands that are genuinely absent after an unreachable point.

An unsupported instruction makes the checker bail out for that function. This
preserves the partial validator's key property: it rejects only programs whose
ill-typedness it can establish. -/

/-- Resolve symbolic heap types retained by the decoder. -/
def Module.resolveHeapType (m : Module) : GcHeapType → GcHeapType
  | .named name =>
      match m.gcTypes.findIdx? (·.sourceName = some name) with
      | some index => .concrete index
      | none => .named name
  | heap => heap

def Module.heapSubtype (m : Module) (actual expected : GcHeapType) : Bool :=
  let actual := m.resolveHeapType actual
  let expected := m.resolveHeapType expected
  if actual == expected then true else
  match actual, expected with
  | .noFunc, .func | .noExtern, .extern | .noExn, .exn => true
  | .noneT, .any | .noneT, .eq | .noneT, .i31
  | .noneT, .structT | .noneT, .arrayT | .noneT, .concrete _ => true
  | .i31, .eq | .i31, .any => true
  | .structT, .eq | .structT, .any
  | .arrayT, .eq | .arrayT, .any => true
  | .eq, .any => true
  | .concrete source, .concrete target => m.gcTypeSubtype source target
  | .concrete source, expected =>
      match m.gcComposite? source, expected with
      | some (.func _), .func => true
      | some (.struct _), .structT | some (.struct _), .eq
      | some (.struct _), .any => true
      | some (.array _), .arrayT | some (.array _), .eq
      | some (.array _), .any => true
      | _, _ => false
  | _, _ => false

def ValueType.reference? : ValueType → Option (Bool × GcHeapType)
  | .funcref => some (true, .func)
  | .externref => some (true, .extern)
  | .exnref => some (true, .exn)
  | .anyref => some (true, .any)
  | .ref nullable heap => some (nullable, heap)
  | _ => none

/-- Static value compatibility (`actual <: expected`). -/
def Module.vtCompat (m : Module) (actual expected : ValueType) : Bool :=
  match actual, expected with
  | .i32, .i32 | .i64, .i64 | .f32, .f32 | .f64, .f64 | .v128, .v128 => true
  | actual, expected =>
      match actual.reference?, expected.reference? with
      | some (actualNullable, actualHeap),
          some (expectedNullable, expectedHeap) =>
          (!actualNullable || expectedNullable) &&
            m.heapSubtype actualHeap expectedHeap
      | _, _ => false

abbrev CheckedType := Option ValueType

structure CheckState where
  /-- Operand types, with the top of stack at the head. `none` is the
  polymorphic type produced by an unreachable branch-only exit. -/
  stack : List CheckedType
  /-- No fall-through path currently reaches this point. Instructions after
  `br`, `return`, or `unreachable` are checked with stack polymorphism. -/
  unreachable : Bool := false
  /-- Branches which leave the current instruction sequence. A surrounding
  structured construct consumes depth zero and decrements the rest. -/
  transfers : List Nat := []

def checkedCompat (m : Module) (actual : CheckedType)
    (expected : ValueType) : Bool :=
  match actual with
  | none => true
  | some valueType => m.vtCompat valueType expected

def resultTypesCompat (m : Module)
    (actual expected : List ValueType) : Bool :=
  actual.length = expected.length &&
    (actual.zip expected).all fun pair => m.vtCompat pair.1 pair.2

def checkedIsRef : CheckedType → Bool
  | none => true
  | some .funcref | some .externref | some .anyref | some .exnref
  | some (.ref _ _) => true
  | some _ => false

/-- Refine a statically known reference after a successful non-null test.
`none` remains the polymorphic unreachable-stack type. -/
def checkedNonNull : CheckedType → CheckedType
  | none => none
  | some valueType =>
    match valueType.reference? with
    | some (_, heapType) => some (.ref false heapType)
    | none => some valueType

def CheckState.popExpected
    (m : Module) (state : CheckState)
    (expected : ValueType) : Except String CheckState :=
  match state.stack with
  | actual :: rest =>
      if checkedCompat m actual expected then
        .ok { state with stack := rest }
      else
        .error "type mismatch"
  | [] =>
      if state.unreachable then .ok state else .error "type mismatch"

def CheckState.popAny
    (state : CheckState) : Except String (CheckedType × CheckState) :=
  match state.stack with
  | actual :: rest => .ok (actual, { state with stack := rest })
  | [] =>
      if state.unreachable then .ok (none, state)
      else .error "type mismatch"

def CheckState.popAnyN
    (count : Nat) (state : CheckState) :
    Except String (List CheckedType × CheckState) := do
  let mut current := state
  let mut popped := []
  for _ in [0:count] do
    let (valueType, next) ← current.popAny
    popped := popped ++ [valueType]
    current := next
  return (popped, current)

def CheckState.applySig
    (m : Module) (state : CheckState)
    (signature : List ValueType × List ValueType) :
    Except String CheckState := do
  let mut current := state
  for expected in signature.1 do
    current ← current.popExpected m expected
  return { current with
    stack := signature.2.reverse.map some ++ current.stack }

def CheckState.requireArity
    (state : CheckState) (arity : Nat) : Except String (List CheckedType) :=
  if state.unreachable then
    if state.stack.length > arity then
      .error "type mismatch"
    else
      .ok (state.stack ++ List.replicate (arity - state.stack.length) none)
  else if state.stack.length = arity then
    .ok state.stack
  else
    .error "type mismatch"

abbrev LabelType := Nat × Option (List ValueType)

def CheckState.branchTo
    (m : Module) (state : CheckState)
    (labels : List LabelType) (depth : Nat) :
    Except String CheckState := do
  let some (arity, types?) := labels[depth]?
    | throw "unknown label"
  let _checked ← match types? with
    | some types => state.applySig m (types.reverse, [])
    | none => state.popAnyN arity |>.map (·.2)
  return { state with
    stack := []
    unreachable := true
    transfers := depth :: state.transfers }

def CheckState.requireTypes
    (m : Module) (state : CheckState) (types : List ValueType) :
    Except String (List CheckedType) := do
  let actual ← state.requireArity types.length
  for (actualType, expectedType) in actual.zip types.reverse do
    if !checkedCompat m actualType expectedType then throw "type mismatch"
  return types.reverse.map some

def declaredTypes?
    (arity : Nat) (types : List ValueType) : Option (List ValueType) :=
  if types.length = arity then some types else none

def lowerTransfers (transfers : List Nat) : List Nat :=
  transfers.filterMap fun
    | 0 => none
    | depth + 1 => some depth

/-- The storage type's value type, as seen by the stack checker. -/
def StorageType.vt : StorageType → ValueType
  | .val vt   => vt
  | .packed _ => .i32

/-- The static value type a global exposes. The `type` field was dropped
from `GlobalDecl` (it was unused at runtime), so recover the declared type
from the initializer value the decoder stored. -/
def Value.toValueType : Value → ValueType
  | .i32 _       => .i32
  | .i64 _       => .i64
  | .f32 _       => .f32
  | .f64 _       => .f64
  | .v128 _      => .v128
  | .funcref _   => .funcref
  | .externref _ => .externref
  | .exnref _    => .exnref
  | .anyref _    => .anyref

def GlobalDecl.valueType (global : GlobalDecl) : ValueType :=
  global.declaredType.getD global.init.toValueType

/-- Scalar load/store signature once the selected memory's address width is
known. The operand list is top-of-stack first, matching `straightSig`. -/
def Instruction.scalarMemorySig
    (addressType : ValueType) : Instruction →
      Option (List ValueType × List ValueType)
  | .load8U _ | .load8S _ | .load16U _ | .load16S _ | .load32 _ =>
      some ([addressType], [.i32])
  | .store8 _ | .store16 _ | .store32 _ =>
      some ([.i32, addressType], [])
  | .load64 _
  | .load8UI64 _ | .load8SI64 _ | .load16UI64 _ | .load16SI64 _
  | .load32UI64 _ | .load32SI64 _ =>
      some ([addressType], [.i64])
  | .store64 _ | .store8I64 _ | .store16I64 _ | .store32I64 _ =>
      some ([.i64, addressType], [])
  | .f32Load _ => some ([addressType], [.f32])
  | .f64Load _ => some ([addressType], [.f64])
  | .f32Store _ => some ([.f32, addressType], [])
  | .f64Store _ => some ([.f64, addressType], [])
  | _ => none

def Simd.Shape.scalarType : Simd.Shape → ValueType
  | .i8x16 | .i16x8 | .i32x4 => .i32
  | .i64x2 => .i64
  | .f32x4 => .f32
  | .f64x2 => .f64

def Instruction.simdMemorySig
    (addressType : ValueType) : Instruction →
      Option (List ValueType × List ValueType)
  | .v128Load _ | .v128LoadExt _ _ _
  | .v128LoadSplat _ _ | .v128LoadZero _ _ =>
      some ([addressType], [.v128])
  | .v128Store _ => some ([.v128, addressType], [])
  | .v128LoadLane _ _ _ =>
      some ([.v128, addressType], [.v128])
  | .v128StoreLane _ _ _ =>
      some ([.v128, addressType], [])
  | _ => none

/-- The `(pops, pushes)` operand-stack signature of a straight-line
instruction (top of stack first in each list), or `none` to bail out
(control flow or an instruction this partial checker does not model). -/
def Instruction.straightSig (m : Module) (locals : List ValueType)
    : Instruction → Option (List ValueType × List ValueType)
  | .const _    => some ([], [.i32])
  | .constI64 _ => some ([], [.i64])
  | .f32Const _ => some ([], [.f32])
  | .f64Const _ => some ([], [.f64])
  | .localGet i => (locals[i]?).map fun t => ([], [t])
  | .localSet i => (locals[i]?).map fun t => ([t], [])
  | .globalGet i => (m.globals[i]?).map fun g => ([], [g.valueType])
  | .globalSet i => (m.globals[i]?).map fun g => ([g.valueType], [])
  | .drop => none   -- polymorphic operand; skip rather than guess
  | .add | .sub | .mul | .divU | .divS | .remU | .remS
  | .and | .or | .xor | .shl | .shrU | .shrS | .rotl | .rotr =>
    some ([.i32, .i32], [.i32])
  | .eqz => some ([.i32], [.i32])
  | .clz | .ctz | .popcnt => some ([.i32], [.i32])
  | .eq | .ne | .ltU | .ltS | .gtU | .gtS | .leU | .leS | .geU | .geS =>
    some ([.i32, .i32], [.i32])
  | .addI64 | .subI64 | .mulI64
  | .divUI64 | .divSI64 | .remUI64 | .remSI64
  | .andI64 | .orI64 | .xorI64
  | .shlI64 | .shrUI64 | .shrSI64 | .rotlI64 | .rotrI64 =>
    some ([.i64, .i64], [.i64])
  | .eqzI64 => some ([.i64], [.i32])
  | .eqI64 | .neI64
  | .ltUI64 | .ltSI64 | .gtUI64 | .gtSI64
  | .leUI64 | .leSI64 | .geUI64 | .geSI64 =>
    some ([.i64, .i64], [.i32])
  | .clzI64 | .ctzI64 | .popcntI64 => some ([.i64], [.i64])
  | .wrapI64 => some ([.i64], [.i32])
  | .extendSI32 | .extendUI32 => some ([.i32], [.i64])
  | .extend8S | .extend16S => some ([.i32], [.i32])
  | .extend8SI64 | .extend16SI64 | .extend32SI64 =>
    some ([.i64], [.i64])
  | .f32Add | .f32Sub | .f32Mul | .f32Div
  | .f32Min | .f32Max | .f32Copysign =>
    some ([.f32, .f32], [.f32])
  | .f64Add | .f64Sub | .f64Mul | .f64Div
  | .f64Min | .f64Max | .f64Copysign =>
    some ([.f64, .f64], [.f64])
  | .f32Abs | .f32Neg | .f32Sqrt | .f32Ceil
  | .f32Floor | .f32Trunc | .f32Nearest =>
    some ([.f32], [.f32])
  | .f64Abs | .f64Neg | .f64Sqrt | .f64Ceil
  | .f64Floor | .f64Trunc | .f64Nearest =>
    some ([.f64], [.f64])
  | .f32Eq | .f32Ne | .f32Lt | .f32Gt | .f32Le | .f32Ge =>
    some ([.f32, .f32], [.i32])
  | .f64Eq | .f64Ne | .f64Lt | .f64Gt | .f64Le | .f64Ge =>
    some ([.f64, .f64], [.i32])
  | .f32ConvertI32S | .f32ConvertI32U => some ([.i32], [.f32])
  | .f32ConvertI64S | .f32ConvertI64U => some ([.i64], [.f32])
  | .f64ConvertI32S | .f64ConvertI32U => some ([.i32], [.f64])
  | .f64ConvertI64S | .f64ConvertI64U => some ([.i64], [.f64])
  | .i32TruncF32S | .i32TruncF32U
  | .i32TruncSatF32S | .i32TruncSatF32U =>
    some ([.f32], [.i32])
  | .i32TruncF64S | .i32TruncF64U
  | .i32TruncSatF64S | .i32TruncSatF64U =>
    some ([.f64], [.i32])
  | .i64TruncF32S | .i64TruncF32U
  | .i64TruncSatF32S | .i64TruncSatF32U =>
    some ([.f32], [.i64])
  | .i64TruncF64S | .i64TruncF64U
  | .i64TruncSatF64S | .i64TruncSatF64U =>
    some ([.f64], [.i64])
  | .f32DemoteF64 => some ([.f64], [.f32])
  | .f64PromoteF32 => some ([.f32], [.f64])
  | .i32ReinterpretF32 => some ([.f32], [.i32])
  | .i64ReinterpretF64 => some ([.f64], [.i64])
  | .f32ReinterpretI32 => some ([.i32], [.f32])
  | .f64ReinterpretI64 => some ([.i64], [.f64])
  | .vConst _ => some ([], [.v128])
  | .vUnOp _ => some ([.v128], [.v128])
  | .vBinOp _ => some ([.v128, .v128], [.v128])
  | .vBitselect | .vFma _ _ | .vDotAdd =>
      some ([.v128, .v128, .v128], [.v128])
  | .vTestOp _ => some ([.v128], [.i32])
  | .vShiftOp _ => some ([.i32, .v128], [.v128])
  | .vSplat shape => some ([shape.scalarType], [.v128])
  | .vExtractLane shape _ _ =>
      some ([.v128], [shape.scalarType])
  | .vReplaceLane shape _ =>
      some ([shape.scalarType, .v128], [.v128])
  | .vShuffle _ => some ([.v128, .v128], [.v128])
  | .tableGet tableIndex =>
    (m.tableDecl? tableIndex).map fun table =>
      ([if table.is64 then .i64 else .i32], [table.elemType])
  | .tableSet tableIndex =>
    (m.tableDecl? tableIndex).map fun table =>
      ([table.elemType, if table.is64 then .i64 else .i32], [])
  | .tableSize tableIndex =>
    (m.tableDecl? tableIndex).map fun table =>
      ([], [if table.is64 then .i64 else .i32])
  | .tableGrow tableIndex =>
    (m.tableDecl? tableIndex).map fun table =>
      let addressType := if table.is64 then .i64 else .i32
      ([addressType, table.elemType], [addressType])
  | .tableFill tableIndex =>
    (m.tableDecl? tableIndex).map fun table =>
      let addressType := if table.is64 then .i64 else .i32
      ([addressType, table.elemType, addressType], [])
  | .tableCopy destinationTableIndex sourceTableIndex =>
    (m.tableDecl? destinationTableIndex).bind fun destinationTable =>
      (m.tableDecl? sourceTableIndex).map fun sourceTable =>
        let destinationType :=
          if destinationTable.is64 then .i64 else .i32
        let sourceType := if sourceTable.is64 then .i64 else .i32
        let lengthType :=
          if destinationTable.is64 && sourceTable.is64 then .i64 else .i32
        ([lengthType, sourceType, destinationType], [])
  | .call functionIndex =>
    (m.funcSig? functionIndex).map fun signature =>
      (signature.params.reverse, signature.results)
  | .callIndirect typeIndex tableIndex =>
    (m.types[typeIndex]?).bind fun signature =>
      (m.tableDecl? tableIndex).map fun table =>
        let selectorType := if table.is64 then .i64 else .i32
        (selectorType :: signature.params.reverse, signature.results)
  | .callRef typeIndex =>
    (m.types[typeIndex]?).map fun signature =>
      (.ref true (.concrete typeIndex) ::
        signature.params.reverse, signature.results)
  | .refNull staticType => some ([], [staticType])
  | .refNullExtern staticType => some ([], [staticType])
  | .refNullExn staticType => some ([], [staticType])
  | .refFunc functionIndex =>
      some ([], [
        match m.funcTypeIdx? functionIndex with
        | some typeIndex => .ref false (.concrete typeIndex)
        | none => .funcref])
  | .tableInit tableIndex _ =>
    (m.tableDecl? tableIndex).map fun table =>
      ([.i32, .i32, if table.is64 then .i64 else .i32], [])
  | .elemDrop _ => some ([], [])
  | .memorySize =>
    m.memory.map fun memory =>
      let addressType := if memory.is64 then .i64 else .i32
      ([], [addressType])
  | .memoryGrow =>
    m.memory.map fun memory =>
      let addressType := if memory.is64 then .i64 else .i32
      ([addressType], [addressType])
  | .memoryFill =>
    m.memory.map fun memory =>
      let addressType := if memory.is64 then .i64 else .i32
      ([addressType, .i32, addressType], [])
  | .memoryCopy =>
    m.memory.map fun memory =>
      let addressType := if memory.is64 then .i64 else .i32
      ([addressType, addressType, addressType], [])
  | .memoryInit _ =>
    m.memory.map fun memory =>
      ([.i32, .i32, if memory.is64 then .i64 else .i32], [])
  | .dataDrop _ => some ([], [])
  | .memOp memoryIndex (.memoryInit _) =>
    (m.memoryDecl? memoryIndex).map fun memory =>
      ([.i32, .i32, if memory.is64 then .i64 else .i32], [])
  | .memOp memoryIndex .memoryFill =>
    (m.memoryDecl? memoryIndex).map fun memory =>
      let addressType := if memory.is64 then .i64 else .i32
      ([addressType, .i32, addressType], [])
  | .memOp memoryIndex .memoryCopy =>
    (m.memoryDecl? memoryIndex).map fun memory =>
      let addressType := if memory.is64 then .i64 else .i32
      ([addressType, addressType, addressType], [])
  | .memOp memoryIndex .memorySize =>
    (m.memoryDecl? memoryIndex).map fun memory =>
      let addressType := if memory.is64 then .i64 else .i32
      ([], [addressType])
  | .memOp memoryIndex .memoryGrow =>
    (m.memoryDecl? memoryIndex).map fun memory =>
      let addressType := if memory.is64 then .i64 else .i32
      ([addressType], [addressType])
  | .memOp memoryIndex operation =>
    (m.memoryDecl? memoryIndex).bind fun memory =>
      let addressType := if memory.is64 then .i64 else .i32
      (operation.scalarMemorySig addressType).orElse fun _ =>
        operation.simdMemorySig addressType
  | .gc op => match op with
    | .refNullAny staticType => some ([], [staticType])
    | .refI31 => some ([.i32], [.ref false .i31])
    | .i31GetS | .i31GetU => some ([.anyref], [.i32])
    | .refEq => some ([.ref true .eq, .ref true .eq], [.i32])
    | .anyConvertExtern => some ([.externref], [.anyref])
    | .externConvertAny => some ([.anyref], [.externref])
    | .structGet t f | .structGetS t f | .structGetU t f =>
      (m.structField? t f).map fun ft =>
        ([.ref true (.concrete t)], [ft.storage.vt])
    | .structSet t f =>
      (m.structField? t f).map fun ft =>
        ([ft.storage.vt, .ref true (.concrete t)], [])
    | .structNew t =>
      (m.structFields? t).map fun fs =>
        ((fs.map (·.storage.vt)).reverse,
          [.ref false (.concrete t)])
    | .arrayGet t | .arrayGetS t | .arrayGetU t =>
      (m.arrayElem? t).map fun ft =>
        ([.i32, .ref true (.concrete t)], [ft.storage.vt])
    | .arraySet t =>
      (m.arrayElem? t).map fun ft =>
        ([ft.storage.vt, .i32, .ref true (.concrete t)], [])
    | .arrayLen => some ([.anyref], [.i32])
    | .arrayNewDefault t =>
      (m.arrayElem? t).map fun _ =>
        ([.i32], [.ref false (.concrete t)])
    | .arrayNew t =>
      (m.arrayElem? t).map fun ft =>
        ([.i32, ft.storage.vt], [.ref false (.concrete t)])
    | .arrayCopy destinationType sourceType =>
      some
        ([.i32, .i32, .ref true (.concrete sourceType), .i32,
          .ref true (.concrete destinationType)], [])
    | _ => none
  | operation =>
    m.memory.bind fun memory =>
      let addressType := if memory.is64 then .i64 else .i32
      (operation.scalarMemorySig addressType).orElse fun _ =>
        operation.simdMemorySig addressType

/-- Recursively check a program. `none` means an unsupported instruction was
encountered, so callers conservatively accept the whole function. -/
partial def Program.checkTypes
    (m : Module) (locals functionResults : List ValueType)
    (labels : List LabelType) (program : Program) (state : CheckState) :
    Except String (Option CheckState) := do
  match program with
  | [] => return some state
  | instruction :: rest =>
    let next? ← match instruction with
      | .nop => pure (some state)
      | .unreachable =>
          pure (some { state with stack := [], unreachable := true })
      | .drop => do
          let (_, next) ← state.popAny
          pure (some next)
      | .select => do
          let afterCondition ← state.popExpected m .i32
          let (right, afterRight) ← afterCondition.popAny
          let (left, afterLeft) ← afterRight.popAny
          match left, right with
          | some leftType, some rightType =>
              if !m.vtCompat leftType rightType then throw "type mismatch"
              pure (some { afterLeft with stack := some leftType :: afterLeft.stack })
          | some valueType, none | none, some valueType =>
              pure (some { afterLeft with stack := some valueType :: afterLeft.stack })
          | none, none =>
              pure (some { afterLeft with stack := none :: afterLeft.stack })
      | .refIsNull => do
          let (referenceType, next) ← state.popAny
          if !checkedIsRef referenceType then throw "type mismatch"
          pure (some { next with stack := some .i32 :: next.stack })
      | .refAsNonNull => do
          let (referenceType, next) ← state.popAny
          if !checkedIsRef referenceType then throw "type mismatch"
          pure (some
            { next with stack := checkedNonNull referenceType :: next.stack })
      | .brOnNull depth => do
          let (referenceType, afterReference) ← state.popAny
          if !checkedIsRef referenceType then throw "type mismatch"
          let some (arity, types?) := labels[depth]?
            | throw "unknown label"
          let fallthrough ← match types? with
            | some types =>
                let rest ← afterReference.applySig m (types.reverse, [])
                pure
                  { rest with stack := types.reverse.map some ++ rest.stack }
            | none =>
                let (arguments, rest) ← afterReference.popAnyN arity
                pure { rest with stack := arguments ++ rest.stack }
          pure (some
            { fallthrough with
              stack := checkedNonNull referenceType :: fallthrough.stack })
      | .brOnNonNull depth => do
          let (referenceType, afterReference) ← state.popAny
          if !checkedIsRef referenceType then throw "type mismatch"
          let refinedState :=
            { state with
              stack := checkedNonNull referenceType :: afterReference.stack }
          let some (arity, types?) := labels[depth]?
            | throw "unknown label"
          let fallthrough ← match types? with
            | some types =>
                let branchTypes := types.reverse
                let rest ← refinedState.applySig m (branchTypes, [])
                pure
                  { rest with stack := (branchTypes.drop 1).map some ++ rest.stack }
            | none =>
                let (arguments, rest) ← refinedState.popAnyN arity
                pure { rest with stack := arguments.drop 1 ++ rest.stack }
          pure (some fallthrough)
      | .tryTable paramArity resultArity catches body
          paramTypes resultTypes => do
          let parameterTypes? := declaredTypes? paramArity paramTypes
          let resultTypes? := declaredTypes? resultArity resultTypes
          let (parameters, outer) ← match parameterTypes? with
            | some types => do
                let outer ← state.applySig m (types.reverse, [])
                pure (types.reverse.map some, outer)
            | none => state.popAnyN paramArity
          for clause in catches do
            let (label, caughtTypes) ← match clause with
              | .catch tagIndex label =>
                  let some tag := m.tags[tagIndex]?
                    | throw "unknown tag"
                  pure (label, tag.params.reverse)
              | .catchRef tagIndex label =>
                  let some tag := m.tags[tagIndex]?
                    | throw "unknown tag"
                  pure (label, .exnref :: tag.params.reverse)
              | .catchAll label => pure (label, [])
              | .catchAllRef label => pure (label, [.exnref])
            let some (labelArity, labelTypes?) := labels[label]?
              | throw "unknown label"
            if caughtTypes.length != labelArity then throw "type mismatch"
            match labelTypes? with
            | some labelTypes =>
                if !resultTypesCompat m caughtTypes labelTypes.reverse then
                  throw "type mismatch"
            | none => pure ()
          let inner : CheckState :=
            { stack := parameters, unreachable := false }
          let some bodyState ←
              Program.checkTypes m locals functionResults
                ((resultArity, resultTypes?) :: labels) body inner
            | return none
          let fallthrough ← match resultTypes? with
            | some types => bodyState.requireTypes m types
            | none => bodyState.requireArity resultArity
          pure (some
            { stack := fallthrough ++ outer.stack
              unreachable := state.unreachable
              transfers :=
                lowerTransfers bodyState.transfers ++ state.transfers })
      | .block paramArity resultArity body paramTypes resultTypes => do
          let parameterTypes? := declaredTypes? paramArity paramTypes
          let resultTypes? := declaredTypes? resultArity resultTypes
          let (parameters, outer) ← match parameterTypes? with
            | some types => do
                let outer ← state.applySig m (types.reverse, [])
                pure (types.reverse.map some, outer)
            | none => state.popAnyN paramArity
          let inner : CheckState :=
            { stack := parameters, unreachable := false }
          let some bodyState ←
              Program.checkTypes m locals functionResults
                ((resultArity, resultTypes?) :: labels) body inner
            | return none
          let fallthrough ← match resultTypes? with
            | some types => bodyState.requireTypes m types
            | none => bodyState.requireArity resultArity
          pure (some
            { stack := fallthrough ++ outer.stack
              unreachable := state.unreachable
              transfers := lowerTransfers bodyState.transfers ++ state.transfers })
      | .loop paramArity resultArity body paramTypes resultTypes => do
          let parameterTypes? := declaredTypes? paramArity paramTypes
          let resultTypes? := declaredTypes? resultArity resultTypes
          let (parameters, outer) ← match parameterTypes? with
            | some types => do
                let outer ← state.applySig m (types.reverse, [])
                pure (types.reverse.map some, outer)
            | none => state.popAnyN paramArity
          let inner : CheckState :=
            { stack := parameters, unreachable := false }
          let some bodyState ←
              Program.checkTypes m locals functionResults
                ((paramArity, parameterTypes?) :: labels) body inner
            | return none
          let fallthrough ← match resultTypes? with
            | some types => bodyState.requireTypes m types
            | none => bodyState.requireArity resultArity
          pure (some
            { stack := fallthrough ++ outer.stack
              unreachable := state.unreachable
              transfers := lowerTransfers bodyState.transfers ++ state.transfers })
      | .iff paramArity resultArity thenBody elseBody
          paramTypes resultTypes => do
          let afterCondition ← state.popExpected m .i32
          let parameterTypes? := declaredTypes? paramArity paramTypes
          let resultTypes? := declaredTypes? resultArity resultTypes
          let (parameters, outer) ← match parameterTypes? with
            | some types => do
                let outer ← afterCondition.applySig m (types.reverse, [])
                pure (types.reverse.map some, outer)
            | none => afterCondition.popAnyN paramArity
          let branchStart : CheckState :=
            { stack := parameters, unreachable := false }
          let some thenState ←
              Program.checkTypes m locals functionResults
                ((resultArity, resultTypes?) :: labels) thenBody branchStart
            | return none
          let some elseState ←
              Program.checkTypes m locals functionResults
                ((resultArity, resultTypes?) :: labels) elseBody branchStart
            | return none
          let thenResults ← match resultTypes? with
            | some types => thenState.requireTypes m types
            | none => thenState.requireArity resultArity
          let elseResults ← match resultTypes? with
            | some types => elseState.requireTypes m types
            | none => elseState.requireArity resultArity
          let mut merged : List CheckedType := []
          for (left, right) in thenResults.zip elseResults do
            match left, right with
            | some leftType, some rightType =>
                if !m.vtCompat leftType rightType then throw "type mismatch"
                merged := merged ++ [some leftType]
            | some valueType, none | none, some valueType =>
                merged := merged ++ [some valueType]
            | none, none => merged := merged ++ [none]
          pure (some
            { stack := merged ++ outer.stack
              unreachable := state.unreachable
              transfers :=
                lowerTransfers thenState.transfers ++
                lowerTransfers elseState.transfers ++ state.transfers })
      | .br depth => some <$> state.branchTo m labels depth
      | .br_if depth => do
          let afterCondition ← state.popExpected m .i32
          let some (arity, types?) := labels[depth]?
            | throw "unknown label"
          let fallthrough ← match types? with
          | some types =>
              let rest ← afterCondition.applySig m (types.reverse, [])
              pure
                { rest with stack := types.reverse.map some ++ rest.stack }
          | none =>
              let (arguments, rest) ← afterCondition.popAnyN arity
              pure { rest with stack := arguments ++ rest.stack }
          pure (some fallthrough)
      | .brTable targets defaultTarget => do
          let afterSelector ← state.popExpected m .i32
          let some (defaultArity, defaultTypes?) := labels[defaultTarget]?
            | throw "unknown label"
          for target in targets do
            let some (targetArity, targetTypes?) := labels[target]?
              | throw "unknown label"
            if targetArity != defaultArity then throw "type mismatch"
            match defaultTypes?, targetTypes? with
            | some defaultTypes, some targetTypes =>
                if !resultTypesCompat m targetTypes defaultTypes then
                  throw "type mismatch"
            | _, _ => pure ()
          match defaultTypes? with
          | some types =>
              let _ ← afterSelector.applySig m (types.reverse, [])
              pure ()
          | none =>
              let _ ← afterSelector.popAnyN defaultArity
              pure ()
          pure (some
            { afterSelector with
              stack := []
              unreachable := true
              transfers := defaultTarget :: targets ++ afterSelector.transfers })
      | .ret => do
          let next ← state.applySig m (functionResults.reverse, [])
          pure (some
            { next with
              stack := []
              unreachable := true
              transfers := 0 :: next.transfers })
      | .throwI tagIndex => do
          let some tag := m.tags[tagIndex]?
            | throw "unknown tag"
          let next ← state.applySig m (tag.params.reverse, [])
          pure (some
            { next with
              stack := []
              unreachable := true })
      | .throwRef => do
          let next ← state.popExpected m .exnref
          pure (some
            { next with
              stack := []
              unreachable := true })
      | .returnCall functionIndex => do
          let some signature := m.funcSig? functionIndex
            | throw "unknown function"
          if !resultTypesCompat m signature.results functionResults then
            throw "type mismatch"
          let next ← state.applySig m (signature.params.reverse, [])
          pure (some
            { next with
              stack := []
              unreachable := true
              transfers := 0 :: next.transfers })
      | .returnCallIndirect typeIndex tableIndex => do
          let some signature := m.types[typeIndex]?
            | throw "unknown type"
          let some table := m.tableDecl? tableIndex
            | throw "unknown table"
          if !resultTypesCompat m signature.results functionResults then
            throw "type mismatch"
          let selectorType := if table.is64 then .i64 else .i32
          let next ← state.applySig m
            (selectorType :: signature.params.reverse, [])
          pure (some
            { next with
              stack := []
              unreachable := true
              transfers := 0 :: next.transfers })
      | .returnCallRef typeIndex => do
          let some signature := m.types[typeIndex]?
            | throw "unknown type"
          if !resultTypesCompat m signature.results functionResults then
            throw "type mismatch"
          let next ← state.applySig m
            (.ref true (.concrete typeIndex) ::
              signature.params.reverse, [])
          pure (some
            { next with
              stack := []
              unreachable := true
              transfers := 0 :: next.transfers })
      | _ =>
          match instruction.straightSig m locals with
          | none => pure none
          | some signature => some <$> state.applySig m signature
    match next? with
    | none => return none
    | some next =>
        Program.checkTypes m locals functionResults labels rest next

/-- Operand-stack type check of one function body. Unsupported instructions
conservatively make the check succeed. -/
def Module.checkFuncStraight (m : Module) (f : Function) : Except String Unit := do
  let locals := f.params ++ f.locals
  let some finalState ←
      Program.checkTypes m locals f.results
        [(f.results.length, some f.results)] f.body
        { stack := [] }
    | return ()
  let results ← finalState.requireArity f.results.length
  for (actual, expected) in results.reverse.zip f.results do
    if !checkedCompat m actual expected then throw "type mismatch"

def Module.checkConstProgram
    (m : Module) (program : Program) (expected : ValueType) :
    Except String Unit := do
  if !program.isConstExpr then throw "constant expression required"
  m.checkFuncStraight { body := program, results := [expected] }
  for instruction in program.allInstrs do
    match instruction with
    | .globalGet referencedIndex =>
        match m.globals[referencedIndex]? with
        | none => throw "unknown global"
        | some referenced =>
            if referenced.isMut then throw "constant expression required"
    | .refFunc functionIndex =>
        if (m.funcSig? functionIndex).isNone then throw "unknown function"
    | _ => pure ()

/-- Run the partial structural validator. `throw` on the first violation. -/
def Module.validate (m : Module) : Except String Unit := do
  m.checkInterface
  if m.dataWithoutMemory then throw "unknown memory"
  match m.memory with
  | none => pure ()
  | some memory =>
      for segment in memory.data do
        segment.checkMemoryRef m
        match segment.offset with
        | none => pure ()
        | some _ =>
            let some selectedMemory := m.memoryDecl? segment.memIdx
              | throw "unknown memory"
            let addressType := if selectedMemory.is64 then .i64 else .i32
            match segment.offsetType with
            | some sourceType =>
                if !m.vtCompat sourceType addressType then throw "type mismatch"
            | none => pure ()
            if segment.offsetExprPresent then
              m.checkConstProgram segment.offsetExpr addressType
  for segment in m.elements do
    segment.checkTableRef m
    for functionIndex in segment.funcs do
      match functionIndex with
      | none => pure ()
      | some index =>
          if (m.funcSig? index).isNone then throw "unknown function"
    let segmentType := segment.elemType.getD .funcref
    for expression in segment.exprs do
      m.checkConstProgram expression segmentType
    match segment.offset with
    | none => pure ()
    | some _ =>
        let some tableIndex := segment.tableIdx
          | throw "unknown table"
        let some table := m.tableDecl? tableIndex
          | throw "unknown table"
        if !m.vtCompat segmentType table.elemType then throw "type mismatch"
        let addressType := if table.is64 then .i64 else .i32
        match segment.offsetType with
        | some sourceType =>
            if !m.vtCompat sourceType addressType then throw "type mismatch"
        | none => pure ()
        if segment.offsetExprPresent then
          m.checkConstProgram segment.offsetExpr addressType
  let nTypes := m.gcTypes.length
  -- Hand-built globals without a retained source initializer must agree with
  -- their literal runtime value. Decoded globals are checked from
  -- `sourceInit` below: their `init` field may intentionally be a broad
  -- placeholder (for example `.funcref` for a precise `(ref $type)`).
  for global in m.globals do
    if global.sourceInit.isNone && global.initExpr.isEmpty &&
        !m.vtCompat global.init.toValueType global.valueType then
      throw "type mismatch"
    match global.init with
    | .funcref (some functionIndex) =>
        if (m.funcSig? functionIndex).isNone then throw "unknown function"
    | _ => pure ()
  for (global, index) in m.globals.zipIdx do
    match global.sourceInit with
    | none => pure ()
    | some program =>
      if !program.isConstExpr then throw "constant expression required"
      m.checkFuncStraight
        { body := program, results := [global.valueType] }
      for instruction in program.allInstrs do
        match instruction with
        | .globalGet referencedIndex =>
          if referencedIndex ≥ index then throw "unknown global"
          match m.globals[referencedIndex]? with
          | some referenced =>
            if referenced.isMut then throw "constant expression required"
          | none => throw "unknown global"
        | _ => pure ()
  -- 1. `sub` declarations: supertype in range, non-final, and a structural
  -- supertype of the declared composite.
  for td in m.gcTypes do
    match td.super with
    | none => pure ()
    | some s =>
      if s ≥ nTypes then throw "unknown type"
      let sup := m.gcTypes[s]!
      if sup.«final» then throw "sub type"
      if !td.comp.structSubtype sup.comp then throw "sub type"
  -- 2. Instruction immediates: GC type indices in range; struct/array
  -- mutating accessors target a mutable field / element.
  for f in m.funcs do
    for i in f.body.allInstrs do
      for t in i.gcTypeRefs do
        if t ≥ nTypes then throw "unknown type"
      i.checkBulkMemoryRefs m
      i.checkTableSegmentRefs m
      i.checkGlobalRefs m
      i.checkLocalRefs (f.params.length + f.locals.length)
      i.checkFunctionRefs m
      i.checkSimdImmediates
      match i with
      | .gc (.structSet t fld) =>
        match m.structField? t fld with
        | some ft => if !ft.isMut then throw "immutable field"
        | none    => throw "unknown type"
      | .gc (.arraySet t) =>
        match m.arrayElem? t with
        | some ft => if !ft.isMut then throw "immutable array"
        | none    => throw "unknown type"
      | .gc (.arrayInitData t _) =>
        match m.arrayElem? t with
        | none => throw "unknown type"
        | some ft =>
          if !ft.isMut then throw "immutable array"
          match ft.storage with
          | .packed _ => pure ()
          | .val .i32 | .val .i64 | .val .f32 | .val .f64 | .val .v128 =>
            pure ()
          | _ => throw "array type is not numeric or vector"
      | .gc (.arrayCopy destinationType sourceType) =>
        let destination ← match m.arrayElem? destinationType with
          | some fieldType => pure fieldType
          | none => throw "unknown type"
        let source ← match m.arrayElem? sourceType with
          | some fieldType => pure fieldType
          | none => throw "unknown type"
        if !destination.isMut then throw "immutable array"
        if destination.storage != source.storage then
          throw "array types do not match"
      | _ => pure ()
  -- 3. Global initializers must be constant expressions.
  for g in m.globals do
    if !g.initExpr.isEmpty && !g.initExpr.isConstExpr then
      throw "constant expression required"
  -- 4. Straight-line operand-stack type check of each function body.
  for f in m.funcs do
    Program.checkBranchDepth 0 f.body
    m.checkFuncStraight f

end Wasm
