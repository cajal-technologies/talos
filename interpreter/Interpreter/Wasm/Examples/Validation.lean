import Interpreter.Wasm.SmallStep
import Interpreter.Wasm.Examples.Harness
import Interpreter.Wasm.Validate

kernel_decoder

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-!
# Validator conformance suite

Decidable checks pinning what `Module.validate` accepts and what it rejects.
Each `invalid…Module` is paired with the exact diagnostic the validator must
produce; each `valid…ValidationModule` records a shape that must keep
validating.

Nothing here executes a module, so the suite is independent of the small-step
machine. It was split out of `Interpreter.Wasm.Examples.SmallStep`, whose
namespace it still shares, so every check keeps its name.
-/

namespace Wasm.Examples.SmallStep

open Wasm.SmallStep

/-! ### `select` result annotations

The untyped `select` accepts only numeric and vector operands; a reference
operand needs `select (result t)`, whose single type must name a declared
type. Mirrors `select.wast:384-398` and `ref.wast:78`. -/

def invalidImplicitSelectOnFuncrefValidationModule : Module :=
  { funcs :=
      [{ params := [.funcref],
         body := [.localGet 0, .localGet 0, .const 1, .select, .drop] }] }

def invalidImplicitSelectOnExternrefValidationModule : Module :=
  { funcs :=
      [{ params := [.externref],
         body := [.localGet 0, .localGet 0, .const 1, .select, .drop] }] }

def validTypedSelectOnFuncrefValidationModule : Module :=
  { funcs :=
      [{ params := [.funcref],
         body := [.localGet 0, .localGet 0, .const 1, .select (some [.funcref])],
         results := [.funcref] }] }

def invalidTypedSelectUnknownTypeValidationModule : Module :=
  { funcs :=
      [{ body := [.unreachable, .select (some [.ref false (.concrete 1)]), .drop] }] }

def invalidTypedSelectNoResultValidationModule : Module :=
  { funcs := [{ body := [.nop, .nop, .const 1, .select (some [])] }] }

def invalidTypedSelectTwoResultsValidationModule : Module :=
  { funcs :=
      [{ body := [.const 1, .const 2, .const 1, .select (some [.i32, .i32])],
         results := [.i32, .i32] }] }

def validTypedSelectAfterUnreachableValidationModule : Module :=
  { funcs := [{ body := [.unreachable, .select (some [.i32])], results := [.i32] }] }

def validUntypedSelectNumericValidationModule : Module :=
  { funcs :=
      [{ body := [.const 1, .const 2, .const 0, .select], results := [.i32] }] }

/-- `struct.new_default` is outside the partial stack checker, which then stops
checking the function. The annotation checks must not depend on reaching the
`select`. -/
def invalidTypedSelectUnknownTypeAfterUnmodelledValidationModule : Module :=
  { gcTypes := [{ comp := .struct [] }]
    funcs :=
      [{ body :=
          [.gc (.structNewDefault 0), .drop,
           .unreachable, .select (some [.ref false (.concrete 7)]), .drop] }] }

def invalidTypedSelectNoResultAfterUnmodelledValidationModule : Module :=
  { gcTypes := [{ comp := .struct [] }]
    funcs :=
      [{ body :=
          [.gc (.structNewDefault 0), .drop, .unreachable, .select (some []), .drop] }] }

def validTypedSelectAfterUnmodelledValidationModule : Module :=
  { gcTypes := [{ comp := .struct [] }]
    funcs :=
      [{ body :=
          [.gc (.structNewDefault 0), .drop, .unreachable, .select (some [.i32]), .drop] }] }

/-! Decoded `select` annotations: the decoder keeps `(result …)` as written in
the folded and unfolded forms, and fails on a token that is not a value type.
How many types there are is a typing question, left to validation. -/

/-- The `select` annotations in a decoded module's function bodies, in order,
or `none` if the module does not decode. -/
def decodedSelectAnnotations (wat : String) : Option (List (Option (List ValueType))) :=
  (Wasm.Decoder.Wat.decode wat).toOption.map fun m =>
    m.funcs.flatMap fun f => f.body.allInstrs.filterMap fun
      | .select resultTypes => some resultTypes
      | _ => none

/-- The decoder's error, or `none` if `wat` decodes. -/
def decodeErrorOf (wat : String) : Option String :=
  match Wasm.Decoder.Wat.decode wat with
  | .error message => some message
  | .ok _ => none

def unfoldedFuncrefSelectWat : String :=
  "(module (func (result funcref) ref.null func ref.null func i32.const 0 select (result funcref)))"

def foldedFuncrefSelectWat : String :=
  "(module (func (result funcref)
     (select (result funcref) (ref.null func) (ref.null func) (i32.const 0))))"

def namedRefSelectWat : String :=
  "(module (type $t (func)) (func (param (ref null $t)) (result (ref null $t))
     local.get 0 local.get 0 i32.const 0 select (result (ref null $t))))"

def indexedRefSelectWat : String :=
  "(module (type (func)) (func (param (ref 0)) (result (ref 0))
     (select (result (ref 0)) (local.get 0) (local.get 0) (i32.const 0))))"

def untypedSelectWat : String :=
  "(module (func (result i32) i32.const 1 i32.const 2 i32.const 0 select))"

def emptySelectAnnotationWat : String :=
  "(module (func i32.const 1 i32.const 2 i32.const 0 select (result) drop))"

def twoSelectAnnotationsWat : String :=
  "(module (func (result i32 i32) i32.const 1 i32.const 2 i32.const 0
     select (result i32) (result i32)))"

def unknownTypeSelectAnnotationWat : String :=
  "(module (func (result funcref)
     (select (result (ref null 5)) (ref.null func) (ref.null func) (i32.const 0))))"

def malformedAtomSelectWat : String :=
  "(module (func (result i32) i32.const 1 i32.const 2 i32.const 0 select (result i32 bogus)))"

def malformedNestedSelectWat : String :=
  "(module (func (result i32) i32.const 1 i32.const 2 i32.const 0 select (result (bogus))))"

def malformedHeapTypeSelectWat : String :=
  "(module (func (result funcref) ref.null func ref.null func i32.const 0
     select (result (ref null bogus))))"

def malformedAtomFoldedSelectWat : String :=
  "(module (func (result i32)
     (select (result i32 bogus) (i32.const 1) (i32.const 2) (i32.const 0))))"

def malformedNestedFoldedSelectWat : String :=
  "(module (func (result i32)
     (select (result (bogus)) (i32.const 1) (i32.const 2) (i32.const 0))))"

def invalidDataDropModule : Module :=
  { funcs := [{ body := [.dataDrop 0] }] }

def invalidMemoryInitIndexModule : Module :=
  { funcs :=
      [{ body := [.const 0, .const 0, .const 0, .memoryInit 1] }]
    memory := some
      { pagesMin := 1
        data := [{ offset := none, bytes := [1] }] } }

def validMemoryInit64ValidationModule : Module :=
  { funcs :=
      [{ body := [.constI64 0, .const 0, .const 1, .memoryInit 0] }]
    memory := some
      { pagesMin := 1
        is64 := true
        data := [{ offset := none, bytes := [1] }] } }

/-! ### Table declarations

Reversed limits (`table.wast:27/31`, `table64.wast:16/20`) and a non-nullable
element type without an initializer (`table.wast:71-136`). -/

def invalidNonNullableTableElementValidationModule : Module :=
  { funcs := [], tables := [{ min := 0, elemType := .ref false .func }] }

def invalidNonNullableConcreteTableElementValidationModule : Module :=
  { funcs := [], types := [{}],
    tables := [{ min := 10, elemType := .ref false (.concrete 0) }] }

/-- An imported non-nullable table is initialised by its exporter, so no
initializer is needed and the declaration is valid. -/
def validImportedNonNullableTableValidationModule : Module :=
  { funcs := []
    importedTables := [("M", "t")]
    tables := [{ min := 10, elemType := .ref false .func }] }

def validNullableConcreteTableElementValidationModule : Module :=
  { funcs := [], types := [{}],
    tables := [{ min := 10, elemType := .ref true (.concrete 0) }] }

def invalidReversedTableLimitsValidationModule : Module :=
  { funcs := [], tables := [{ min := 1, max := some 0 }] }

def invalidReversedTable64LimitsValidationModule : Module :=
  { funcs := [], tables := [{ min := 0xffff_ffff, max := some 0, is64 := true }] }

/-- Limits are checked on imported tables too (only the defaultable-element
rule exempts imports). -/
def invalidReversedImportedTableLimitsValidationModule : Module :=
  { funcs := []
    importedTables := [("M", "t")]
    tables := [{ min := 1, max := some 0 }] }

/-- A hand-built 32-bit table whose minimum exceeds `2^32-1` (`table.wast:36`). -/
def invalidOversizedTableMinValidationModule : Module :=
  { funcs := [], tables := [{ min := 0x1_0000_0000 }] }

/-- A hand-built 32-bit table whose maximum exceeds `2^32-1` (`table.wast:44`). -/
def invalidOversizedTableMaxValidationModule : Module :=
  { funcs := [], tables := [{ min := 0, max := some 0x1_0000_0000 }] }

/-- The 32-bit range does not apply to 64-bit tables. -/
def validLargeTable64LimitsValidationModule : Module :=
  { funcs := [], tables := [{ min := 0x1_0000_0000, is64 := true }] }

def validEqualTableLimitsValidationModule : Module :=
  { funcs := [], tables := [{ min := 3, max := some 3 }] }

def validUnboundedTableValidationModule : Module :=
  { funcs := [], tables := [{ min := 0xffff_ffff }] }

def invalidMemoryFillWithoutMemoryModule : Module :=
  { funcs := [{ body := [.const 0, .const 0, .const 0, .memoryFill] }] }

def validMemoryFill64ValidationModule : Module :=
  { funcs :=
      [{ body := [.constI64 0, .const 0, .constI64 1, .memoryFill] }]
    memory := some { pagesMin := 1, is64 := true } }

def invalidMemoryCopy64LengthModule : Module :=
  { funcs :=
      [{ body :=
          [.constI64 0, .constI64 0, .const 1, .memoryCopy] }]
    memory := some { pagesMin := 1, is64 := true } }

def validMemoryCopy64ValidationModule : Module :=
  { funcs :=
      [{ body :=
          [.constI64 0, .constI64 0, .constI64 1, .memoryCopy] }]
    memory := some { pagesMin := 1, is64 := true } }

def invalidLoadWithoutMemoryModule : Module :=
  { funcs := [{ body := [.const 0, .load32 0], results := [.i32] }] }

def invalidMemory64LoadAddressModule : Module :=
  { funcs := [{ body := [.const 0, .load32 0], results := [.i32] }]
    memory := some { pagesMin := 1, is64 := true } }

def validMemory64LoadValidationModule : Module :=
  { funcs := [{ body := [.constI64 0, .load32 0], results := [.i32] }]
    memory := some { pagesMin := 1, is64 := true } }

def validMemory64I64StoreValidationModule : Module :=
  { funcs := [{ body := [.constI64 0, .constI64 1, .store64 0] }]
    memory := some { pagesMin := 1, is64 := true } }

def invalidMemorySizeWithoutMemoryModule : Module :=
  { funcs := [{ body := [.memorySize], results := [.i32] }] }

def validMemory64SizeValidationModule : Module :=
  { funcs := [{ body := [.memorySize], results := [.i64] }]
    memory := some { pagesMin := 1, is64 := true } }

def invalidMemory64GrowDeltaModule : Module :=
  { funcs := [{ body := [.const 1, .memoryGrow], results := [.i64] }]
    memory := some { pagesMin := 1, is64 := true } }

def validMemory64GrowValidationModule : Module :=
  { funcs := [{ body := [.constI64 1, .memoryGrow], results := [.i64] }]
    memory := some { pagesMin := 1, is64 := true } }

def invalidGlobalGetIndexModule : Module :=
  { funcs := [{ body := [.globalGet 0], results := [.i32] }] }

def invalidGlobalSetIndexModule : Module :=
  { funcs := [{ body := [.const 0, .globalSet 1] }]
    globals := [{ init := .i32 0 }] }

def invalidImmutableGlobalSetModule : Module :=
  { funcs := [{ body := [.const 0, .globalSet 0] }]
    globals :=
      [{ init := .i32 0, declaredType := some .i32, isMut := false }] }

def invalidGlobalInitializerTypeModule : Module :=
  { funcs := []
    globals :=
      [{ init := .f32 0, declaredType := some .i32, isMut := false }] }

def invalidGlobalInitializerInstructionModule : Module :=
  { funcs := []
    globals :=
      [{ init := .i32 0, declaredType := some .i32, isMut := false,
         sourceInit := some [.const 0, .nop] }] }

def invalidForwardGlobalInitializerModule : Module :=
  { funcs := []
    globals :=
      [ { init := .i32 0, declaredType := some .i32, isMut := false,
          sourceInit := some [.globalGet 1] }
      , { init := .i32 0, declaredType := some .i32, isMut := false,
          sourceInit := some [.const 0] } ] }

def invalidElemDropModule : Module :=
  { funcs := [{ body := [.elemDrop 0] }] }

def invalidTableInitTableModule : Module :=
  { funcs :=
      [{ body := [.const 0, .const 0, .const 0, .tableInit 0 0] }]
    elements := [{ funcs := [some 0] }] }

def invalidTableInitElementModule : Module :=
  { funcs :=
      [{ body := [.const 0, .const 0, .const 0, .tableInit 0 1] }]
    tables := [{ min := 1 }]
    elements := [{ funcs := [some 0] }] }

def validTableInit64ValidationModule : Module :=
  { funcs :=
      [{ body := [.constI64 0, .const 0, .const 1, .tableInit 0 0] }]
    tables := [{ min := 1, is64 := true }]
    elements := [{ funcs := [some 0] }] }

def invalidTableGetIndexModule : Module :=
  { funcs := [{ body := [.const 0, .tableGet 0], results := [.funcref] }] }

def validTable64FillValidationModule : Module :=
  { funcs :=
      [{ params := [.i64, .externref, .i64],
         body := [.localGet 0, .localGet 1, .localGet 2, .tableFill 0] }]
    tables := [{ min := 1, elemType := .externref, is64 := true }] }

def validMixedTableCopyValidationModule : Module :=
  { funcs :=
      [{ params := [.i32, .i64, .i32],
         body := [.localGet 0, .localGet 1, .localGet 2, .tableCopy 0 1] }]
    tables :=
      [ { min := 1, is64 := false }
      , { min := 1, is64 := true } ] }

def invalidMixedTableCopyLengthModule : Module :=
  { funcs :=
      [{ params := [.i32, .i64, .i64],
         body := [.localGet 0, .localGet 1, .localGet 2, .tableCopy 0 1] }]
    tables :=
      [ { min := 1, is64 := false }
      , { min := 1, is64 := true } ] }

def invalidDirectCallIndexModule : Module :=
  { funcs := [{ body := [.call 1] }] }

def validImportedCallValidationModule : Module :=
  { imports := [{ module := "host", name := "f",
                  params := [.i32], results := [.i64] }]
    funcs :=
      [{ body := [.const 7, .call 0], results := [.i64] }] }

def invalidIndirectCallTypeModule : Module :=
  { funcs := [{ body := [.const 0, .callIndirect 0 0] }]
    tables := [{ min := 1 }] }

def validTable64IndirectCallValidationModule : Module :=
  { funcs :=
      [{ body := [.constI64 0, .callIndirect 0 0], results := [.i32] }]
    types := [{ results := [.i32] }]
    gcTypes := [{ comp := .func { results := [.i32] } }]
    tables := [{ min := 1, is64 := true }] }

def invalidRefFuncIndexModule : Module :=
  { funcs := [{ body := [.refFunc 1], results := [.funcref] }] }

def invalidStructuredBlockExtraValueModule : Module :=
  { funcs := [{ body := [.block 0 0 [.const 1]] }] }

def invalidStructuredBlockMissingResultModule : Module :=
  { funcs := [{ body := [.block 0 1 []], results := [.i32] }] }

def invalidStructuredIfResultMismatchModule : Module :=
  { funcs :=
      [{ body := [.const 0, .iff 0 1 [.const 1] [.constI64 1]],
         results := [.i32] }] }

def validStructuredBranchPolymorphicModule : Module :=
  { funcs :=
      [{ body := [.block 0 1 [.const 7, .br 0, .add]],
         results := [.i32] }] }

def invalidSimdExtractLaneModule : Module :=
  { funcs :=
      [{ body := [.vConst 0, .vExtractLane .i8x16 false 16],
         results := [.i32] }] }

def invalidSimdSplatOperandModule : Module :=
  { funcs :=
      [{ body := [.constI64 0, .vSplat .i32x4],
         results := [.v128] }] }

def validSimdSplatValidationModule : Module :=
  { funcs :=
      [{ body := [.const 0, .vSplat .i32x4],
         results := [.v128] }] }

def invalidSimdLoadWithoutMemoryModule : Module :=
  { funcs :=
      [{ body := [.const 0, .v128Load 0],
         results := [.v128] }] }

def validMemory64SimdLoadValidationModule : Module :=
  { funcs :=
      [{ body := [.constI64 0, .v128Load 0],
         results := [.v128] }]
    memory := some { pagesMin := 1, is64 := true } }

def invalidLocalIndexValidationModule : Module :=
  { funcs := [{ body := [.localGet 0] }] }

def invalidUnreachableLocalIndexValidationModule : Module :=
  { funcs := [{ body := [.unreachable, .localSet 0] }] }

def validParamAndLocalIndexValidationModule : Module :=
  { funcs :=
      [{ params := [.i32], locals := [.i64],
         body := [.localGet 0, .drop, .localGet 1],
         results := [.i64] }] }

def invalidFunctionExportValidationModule : Module :=
  { funcs := [], exports := [{ name := "missing", funcIdx := 0 }] }

def invalidDuplicateCrossKindExportValidationModule : Module :=
  { funcs := [{ body := [] }]
    exports := [{ name := "same", funcIdx := 0 }]
    memory := some { pagesMin := 0 }
    memoryExports := [("same", 0)] }

def invalidStartSignatureValidationModule : Module :=
  { funcs := [{ params := [.i32], body := [] }]
    startFunc := some 0 }

def invalidStartIndexValidationModule : Module :=
  { funcs := [], startFunc := some 0 }

def validImportedStartValidationModule : Module :=
  { funcs := []
    imports := [{ module := "host", name := "start" }]
    startFunc := some 0 }

def invalidSyntheticDataMemoryValidationModule : Module :=
  { funcs := []
    memory := some
      { pagesMin := 0
        data := [{ offset := some 0, bytes := [] }] }
    dataWithoutMemory := true }

def invalidDataOffsetTypeValidationModule : Module :=
  { funcs := []
    memory := some
      { pagesMin := 1
        data :=
          [{ offset := some 0, offsetType := some .i64, bytes := [] }] } }

def validMemory64DataOffsetValidationModule : Module :=
  { funcs := []
    memory := some
      { pagesMin := 1
        is64 := true
        data :=
          [{ offset := some 0, offsetType := some .i64, bytes := [] }] } }

def invalidActiveElementTableValidationModule : Module :=
  { funcs := []
    elements :=
      [{ tableIdx := some 0, offset := some 0,
         offsetType := some .i32, elemType := some .funcref }] }

def invalidActiveElementTypeValidationModule : Module :=
  { funcs := []
    tables := [{ min := 1, elemType := .externref }]
    elements :=
      [{ tableIdx := some 0, offset := some 0,
         offsetType := some .i32, elemType := some .funcref }] }

def validTable64ElementOffsetValidationModule : Module :=
  { funcs := []
    tables := [{ min := 1, is64 := true }]
    elements :=
      [{ tableIdx := some 0, offset := some 0,
         offsetType := some .i64, elemType := some .funcref }] }

def invalidDirectTailCallResultValidationModule : Module :=
  { funcs :=
      [{ body := [.returnCall 1], results := [.i32] },
       { body := [.constI64 0], results := [.i64] }] }

def validDirectTailCallValidationModule : Module :=
  { funcs :=
      [{ body := [.returnCall 1], results := [.i32] },
       { body := [.const 0], results := [.i32] }] }

def invalidIndirectTailCallResultValidationModule : Module :=
  { funcs :=
      [{ body := [.const 0, .returnCallIndirect 0 0], results := [.i32] }]
    types := [{ results := [.i64] }]
    gcTypes := [{ comp := .func { results := [.i64] } }]
    tables := [{ min := 1 }] }

def invalidReferenceTailCallResultValidationModule : Module :=
  { funcs :=
      [{ body := [.refNull, .returnCallRef 0], results := [.i32] }]
    types := [{ results := [.i64] }]
    gcTypes := [{ comp := .func { results := [.i64] } }] }

def invalidRefAsNonNullPolymorphicResultValidationModule : Module :=
  { funcs :=
      [{ body := [.unreachable, .refAsNonNull, .f32Abs] }] }

def invalidRefIsNullScalarValidationModule : Module :=
  { funcs :=
      [{ body := [.const 0, .refIsNull, .drop] }] }

def validPolymorphicReferenceValidationModule : Module :=
  { funcs :=
      [{ body := [.unreachable, .refAsNonNull, .refIsNull, .drop] }] }

def invalidImmutableArrayCopyValidationModule : Module :=
  { funcs :=
      [{ body :=
          [.unreachable, .gc (.arrayCopy 0 1)] }]
    gcTypes :=
      [{ comp := .array { storage := .packed 8 } },
       { comp := .array { storage := .packed 8, isMut := true } }] }

def invalidMismatchedArrayCopyValidationModule : Module :=
  { funcs :=
      [{ body :=
          [.unreachable, .gc (.arrayCopy 0 1)] }]
    gcTypes :=
      [{ comp := .array { storage := .packed 8, isMut := true } },
       { comp := .array { storage := .packed 16 } }] }

def validArrayCopyValidationModule : Module :=
  { funcs :=
      [{ params :=
          [.ref false (.concrete 0), .ref false (.concrete 1)]
         body :=
          [.localGet 0, .const 0, .localGet 1, .const 0, .const 0,
           .gc (.arrayCopy 0 1)] }]
    gcTypes :=
      [{ comp := .array { storage := .packed 8, isMut := true } },
       { comp := .array { storage := .packed 8 } }] }

def invalidTypedBlockResultValidationModule : Module :=
  { funcs :=
      [{ body :=
          [.block 0 1 [.f32Const 0] [] [.i32], .drop] }] }

def invalidTypedBlockBranchValidationModule : Module :=
  { funcs :=
      [{ body :=
          [.block 0 1 [.f32Const 0, .br 0] [] [.i32], .drop] }] }

def invalidTypedLoopParameterValidationModule : Module :=
  { funcs :=
      [{ body :=
          [.f32Const 0,
           .loop 1 0 [.br 0] [.i32] []] }] }

def validTypedStructuredValidationModule : Module :=
  { funcs :=
      [{ body :=
          [.const 7,
           .block 1 1 [.br 0] [.i32] [.i32],
           .drop] }] }

def invalidUnknownThrowValidationModule : Module :=
  { funcs := [{ body := [.throwI 0] }] }

def invalidThrowArgumentValidationModule : Module :=
  { tags := [{ params := [.i32] }]
    funcs := [{ body := [.throwI 0] }] }

def invalidThrowRefOperandValidationModule : Module :=
  { funcs := [{ body := [.throwRef] }] }

def invalidTryTableResultValidationModule : Module :=
  { funcs :=
      [{ body :=
          [.tryTable 0 1 [] [] [] [.i32]],
         results := [.i32] }] }

def invalidCatchRefTargetValidationModule : Module :=
  { tags := [{}]
    funcs :=
      [{ body :=
          [.tryTable 0 0 [.catchRef 0 0] []] }] }

def validTryTableCatchValidationModule : Module :=
  { tags := [{}]
    funcs :=
      [{ body :=
          [.tryTable 0 0 [.catch 0 0] [.throwI 0]] }] }

def invalidBrOnNullScalarValidationModule : Module :=
  { funcs := [{ body := [.const 0, .brOnNull 0] }] }

def invalidBrOnNonNullTargetValidationModule : Module :=
  { funcs :=
      [{ body := [.refNullExtern, .brOnNonNull 0],
         results := [.i32] }] }

def validReferenceBranchValidationModule : Module :=
  { funcs :=
      [{ body := [.refNull, .brOnNull 0, .drop] }] }

def invalidBroadReturnCallRefValidationModule : Module :=
  { types := [{}]
    gcTypes := [{ comp := .func {} }]
    funcs :=
      [{ params := [.funcref],
         body := [.localGet 0, .returnCallRef 0] }] }

def validPreciseReturnCallRefValidationModule : Module :=
  { types := [{}]
    gcTypes := [{ comp := .func {} }]
    exports := [{ name := "callee", funcIdx := 1 }]
    funcs :=
      [{ body := [.refFunc 1, .returnCallRef 0] },
       { body := [], typeIdx := some 0 }] }

def invalidRefEqAnyValidationModule : Module :=
  { funcs :=
      [{ params := [.ref true .any],
         body := [.localGet 0, .localGet 0, .gc .refEq, .drop] }] }

def validationErrorIs (module : Module) (expected : String) : Bool :=
  match module.validate with
  | .error actual => actual == expected
  | .ok () => false

def validationSucceeds (module : Module) : Bool :=
  match module.validate with
  | .ok () => true
  | .error _ => false

def passiveDataWithoutMemoryModule : Module :=
  decodeOrDefault "(module (data \"payload\"))"

def activeDataWithoutMemoryModule : Module :=
  decodeOrDefault "(module (data (i32.const 0) \"payload\"))"

def floatConstantGlobalValidationModule : Module :=
  decodeOrDefault "(module (global f32 (f32.const 1)))"

def immutableArrayInitDataValidationModule : Module :=
  decodeOrDefault
    "(module
       (type $a (array i8))
       (data $d \"a\")
       (func (param (ref $a))
         (array.init_data $a 0
           (local.get 0) (i32.const 0) (i32.const 0) (i32.const 0))))"

def referenceArrayInitDataValidationModule : Module :=
  decodeOrDefault
    "(module
       (type $a (array (mut funcref)))
       (data $d \"a\")
       (func (param (ref $a))
         (array.init_data $a 0
           (local.get 0) (i32.const 0) (i32.const 0) (i32.const 0))))"

def preciseArrayConstructorValidationModule : Module :=
  decodeOrDefault
    "(module
       (type $a (array f32))
       (global (ref $a)
         (array.new $a (f32.const 1) (i32.const 3))))"

def crossTypedArrayGetValidationModule : Module :=
  decodeOrDefault
    "(module
       (type $bytes (array i8))
       (type $floats (array f32))
       (func (param (ref $bytes))
         (array.get $floats (local.get 0) (i32.const 0))
         drop))"

def declarativeFunctionReferenceValidationModule : Module :=
  decodeOrDefault
    "(module
       (elem declare func $f)
       (type $t (func))
       (func $f (type $t))
       (func (ref.func $f) drop))"

def preciseFunctionReferenceGlobalValidationModule : Module :=
  decodeOrDefault
    "(module
       (type $t (func))
       (elem declare func $f)
       (global (ref $t) (ref.func $f))
       (func $f (type $t)))"

def covariantElementTableValidationModule : Module :=
  decodeOrDefault
    "(module
       (type $t (func))
       (table 1 (ref null $t))
       (elem (table 0) (i32.const 0)
         (ref $t) (ref.func $f))
       (func $f (type $t)))"

def brOnNonNullRefinementValidationModule : Module :=
  decodeOrDefault
    "(module
       (type $t (func))
       (func (param (ref null $t))
         (drop
           (block (result (ref $t))
             (br_on_non_null 0 (local.get 0))
             unreachable))))"

theorem validator_accepts_passive_data_without_linear_memory :
    passiveDataWithoutMemoryModule.dataWithoutMemory = false ∧
      validationSucceeds passiveDataWithoutMemoryModule = true := by cbv

theorem validator_rejects_active_data_without_linear_memory :
    activeDataWithoutMemoryModule.dataWithoutMemory = true ∧
      validationErrorIs activeDataWithoutMemoryModule "unknown memory" = true := by cbv

theorem validator_accepts_float_constant_global :
    validationSucceeds floatConstantGlobalValidationModule = true := by cbv

theorem validator_rejects_immutable_array_init_data :
    validationErrorIs immutableArrayInitDataValidationModule
      "immutable array" = true := by cbv

theorem validator_rejects_reference_array_init_data :
    validationErrorIs referenceArrayInitDataValidationModule
      "array type is not numeric or vector" = true := by cbv

theorem validator_accepts_precise_array_constructor_result :
    validationSucceeds preciseArrayConstructorValidationModule = true := by cbv

theorem validator_rejects_cross_typed_array_get :
    validationErrorIs crossTypedArrayGetValidationModule
      "type mismatch" = true := by cbv

theorem validator_accepts_declarative_function_reference :
    validationSucceeds declarativeFunctionReferenceValidationModule = true := by cbv

theorem validator_accepts_precise_function_reference_global :
    validationSucceeds preciseFunctionReferenceGlobalValidationModule = true := by cbv

theorem validator_accepts_nonnull_element_for_nullable_table :
    validationSucceeds covariantElementTableValidationModule = true := by cbv

theorem validator_accepts_br_on_non_null_refinement :
    validationSucceeds brOnNonNullRefinementValidationModule = true := by cbv

theorem validator_rejects_implicit_select_on_funcref :
    validationErrorIs invalidImplicitSelectOnFuncrefValidationModule
      "type mismatch" = true := by decide +kernel

theorem validator_rejects_implicit_select_on_externref :
    validationErrorIs invalidImplicitSelectOnExternrefValidationModule
      "type mismatch" = true := by decide +kernel

theorem validator_accepts_typed_select_on_funcref :
    validationSucceeds validTypedSelectOnFuncrefValidationModule = true := by decide +kernel

theorem validator_rejects_typed_select_unknown_type :
    validationErrorIs invalidTypedSelectUnknownTypeValidationModule
      "unknown type" = true := by decide +kernel

theorem validator_rejects_typed_select_without_result :
    validationErrorIs invalidTypedSelectNoResultValidationModule
      "invalid result arity" = true := by decide +kernel

theorem validator_rejects_typed_select_with_two_results :
    validationErrorIs invalidTypedSelectTwoResultsValidationModule
      "invalid result arity" = true := by decide +kernel

theorem validator_accepts_typed_select_after_unreachable :
    validationSucceeds validTypedSelectAfterUnreachableValidationModule = true := by decide +kernel

theorem validator_accepts_untyped_numeric_select :
    validationSucceeds validUntypedSelectNumericValidationModule = true := by decide +kernel

theorem validator_rejects_typed_select_unknown_type_after_unmodelled :
    validationErrorIs invalidTypedSelectUnknownTypeAfterUnmodelledValidationModule
      "unknown type" = true := by decide +kernel

theorem validator_rejects_typed_select_without_result_after_unmodelled :
    validationErrorIs invalidTypedSelectNoResultAfterUnmodelledValidationModule
      "invalid result arity" = true := by decide +kernel

theorem validator_accepts_typed_select_after_unmodelled :
    validationSucceeds validTypedSelectAfterUnmodelledValidationModule = true := by
  decide +kernel

theorem decoder_keeps_unfolded_select_annotation :
    decodedSelectAnnotations unfoldedFuncrefSelectWat = some [some [.funcref]] := by cbv

theorem decoder_keeps_folded_select_annotation :
    decodedSelectAnnotations foldedFuncrefSelectWat = some [some [.funcref]] := by cbv

theorem decoder_keeps_named_ref_select_annotation :
    decodedSelectAnnotations namedRefSelectWat = some [some [.ref true (.named "t")]] := by
  cbv

theorem decoder_keeps_indexed_ref_select_annotation :
    decodedSelectAnnotations indexedRefSelectWat =
      some [some [.ref false (.concrete 0)]] := by cbv

theorem decoder_keeps_untyped_select_unannotated :
    decodedSelectAnnotations untypedSelectWat = some [none] := by cbv

theorem decoder_keeps_empty_select_annotation :
    decodedSelectAnnotations emptySelectAnnotationWat = some [some []] := by cbv

theorem decoder_joins_select_annotations :
    decodedSelectAnnotations twoSelectAnnotationsWat = some [some [.i32, .i32]] := by cbv

theorem decoder_keeps_unknown_type_select_annotation :
    decodedSelectAnnotations unknownTypeSelectAnnotationWat =
      some [some [.ref true (.concrete 5)]] := by cbv

theorem validator_accepts_decoded_typed_selects :
    (validationSucceeds (decodeOrDefault unfoldedFuncrefSelectWat) &&
      validationSucceeds (decodeOrDefault foldedFuncrefSelectWat) &&
      validationSucceeds (decodeOrDefault namedRefSelectWat) &&
      validationSucceeds (decodeOrDefault indexedRefSelectWat)) = true := by cbv

theorem validator_rejects_decoded_empty_select_annotation :
    validationErrorIs (decodeOrDefault emptySelectAnnotationWat)
      "invalid result arity" = true := by cbv

theorem validator_rejects_decoded_two_select_annotations :
    validationErrorIs (decodeOrDefault twoSelectAnnotationsWat)
      "invalid result arity" = true := by cbv

theorem validator_rejects_decoded_unknown_type_select_annotation :
    validationErrorIs (decodeOrDefault unknownTypeSelectAnnotationWat)
      "unknown type" = true := by cbv

theorem decoder_rejects_malformed_select_atom :
    decodeErrorOf malformedAtomSelectWat = some "malformed select result type" := by cbv

theorem decoder_rejects_malformed_select_nested_form :
    decodeErrorOf malformedNestedSelectWat = some "malformed select result type" := by cbv

theorem decoder_rejects_malformed_select_heap_type :
    decodeErrorOf malformedHeapTypeSelectWat = some "malformed select result type" := by cbv

theorem decoder_rejects_malformed_folded_select_atom :
    decodeErrorOf malformedAtomFoldedSelectWat = some "malformed select result type" := by
  cbv

theorem decoder_rejects_malformed_folded_select_nested_form :
    decodeErrorOf malformedNestedFoldedSelectWat = some "malformed select result type" := by
  cbv

theorem validator_rejects_unknown_data_drop :
    validationErrorIs invalidDataDropModule "unknown data segment" = true := by decide +kernel

theorem validator_rejects_unknown_memory_init_segment :
    validationErrorIs invalidMemoryInitIndexModule
      "unknown data segment" = true := by decide +kernel

theorem validator_accepts_typed_memory64_init :
    validationSucceeds validMemoryInit64ValidationModule = true := by decide +kernel

theorem validator_rejects_non_nullable_table_element :
    validationErrorIs invalidNonNullableTableElementValidationModule
      "type mismatch" = true := by decide +kernel

theorem validator_rejects_non_nullable_concrete_table_element :
    validationErrorIs invalidNonNullableConcreteTableElementValidationModule
      "type mismatch" = true := by decide +kernel

theorem validator_accepts_imported_non_nullable_table :
    validationSucceeds validImportedNonNullableTableValidationModule = true := by decide +kernel

theorem validator_accepts_nullable_concrete_table_element :
    validationSucceeds validNullableConcreteTableElementValidationModule = true := by decide +kernel

theorem validator_rejects_reversed_table_limits :
    validationErrorIs invalidReversedTableLimitsValidationModule
      "size minimum must not be greater than maximum" = true := by decide +kernel

theorem validator_rejects_reversed_table64_limits :
    validationErrorIs invalidReversedTable64LimitsValidationModule
      "size minimum must not be greater than maximum" = true := by decide +kernel

theorem validator_rejects_reversed_imported_table_limits :
    validationErrorIs invalidReversedImportedTableLimitsValidationModule
      "size minimum must not be greater than maximum" = true := by decide +kernel

theorem validator_rejects_oversized_table_min :
    validationErrorIs invalidOversizedTableMinValidationModule
      "table size" = true := by decide +kernel

theorem validator_rejects_oversized_table_max :
    validationErrorIs invalidOversizedTableMaxValidationModule
      "table size" = true := by decide +kernel

theorem validator_accepts_large_table64_limits :
    validationSucceeds validLargeTable64LimitsValidationModule = true := by decide +kernel

theorem validator_accepts_equal_table_limits :
    validationSucceeds validEqualTableLimitsValidationModule = true := by decide +kernel

theorem validator_accepts_unbounded_table :
    validationSucceeds validUnboundedTableValidationModule = true := by decide +kernel

theorem validator_rejects_memory_fill_without_memory :
    validationErrorIs invalidMemoryFillWithoutMemoryModule
      "unknown memory" = true := by decide +kernel

theorem validator_accepts_typed_memory64_fill :
    validationSucceeds validMemoryFill64ValidationModule = true := by decide +kernel

theorem validator_rejects_mistyped_memory64_copy_length :
    validationErrorIs invalidMemoryCopy64LengthModule
      "type mismatch" = true := by decide +kernel

theorem validator_accepts_typed_memory64_copy :
    validationSucceeds validMemoryCopy64ValidationModule = true := by decide +kernel

theorem validator_rejects_load_without_memory :
    validationErrorIs invalidLoadWithoutMemoryModule
      "unknown memory" = true := by decide +kernel

theorem validator_rejects_mistyped_memory64_load_address :
    validationErrorIs invalidMemory64LoadAddressModule
      "type mismatch" = true := by decide +kernel

theorem validator_accepts_typed_memory64_load :
    validationSucceeds validMemory64LoadValidationModule = true := by decide +kernel

theorem validator_accepts_typed_memory64_i64_store :
    validationSucceeds validMemory64I64StoreValidationModule = true := by decide +kernel

theorem validator_rejects_memory_size_without_memory :
    validationErrorIs invalidMemorySizeWithoutMemoryModule
      "unknown memory" = true := by decide +kernel

theorem validator_accepts_typed_memory64_size :
    validationSucceeds validMemory64SizeValidationModule = true := by decide +kernel

theorem validator_rejects_mistyped_memory64_grow_delta :
    validationErrorIs invalidMemory64GrowDeltaModule
      "type mismatch" = true := by decide +kernel

theorem validator_accepts_typed_memory64_grow :
    validationSucceeds validMemory64GrowValidationModule = true := by decide +kernel

theorem validator_rejects_unknown_global_get :
    validationErrorIs invalidGlobalGetIndexModule
      "unknown global" = true := by decide +kernel

theorem validator_rejects_unknown_global_set :
    validationErrorIs invalidGlobalSetIndexModule
      "unknown global" = true := by decide +kernel

theorem validator_rejects_immutable_global_set :
    validationErrorIs invalidImmutableGlobalSetModule
      "immutable global" = true := by decide +kernel

theorem validator_rejects_mistyped_global_initializer :
    validationErrorIs invalidGlobalInitializerTypeModule
      "type mismatch" = true := by decide +kernel

theorem validator_rejects_nonconstant_global_initializer :
    validationErrorIs invalidGlobalInitializerInstructionModule
      "constant expression required" = true := by decide +kernel

theorem validator_rejects_forward_global_initializer :
    validationErrorIs invalidForwardGlobalInitializerModule
      "unknown global" = true := by decide +kernel

theorem validator_rejects_unknown_element_drop :
    validationErrorIs invalidElemDropModule
      "unknown element segment" = true := by decide +kernel

theorem validator_rejects_unknown_table_init_table :
    validationErrorIs invalidTableInitTableModule "unknown table" = true := by decide +kernel

theorem validator_rejects_unknown_table_init_element :
    validationErrorIs invalidTableInitElementModule
      "unknown element segment" = true := by decide +kernel

theorem validator_accepts_typed_table64_init :
    validationSucceeds validTableInit64ValidationModule = true := by decide +kernel

theorem validator_rejects_unknown_table_get :
    validationErrorIs invalidTableGetIndexModule "unknown table" = true := by decide +kernel

theorem validator_accepts_typed_table64_fill :
    validationSucceeds validTable64FillValidationModule = true := by decide +kernel

theorem validator_accepts_typed_mixed_table_copy :
    validationSucceeds validMixedTableCopyValidationModule = true := by decide +kernel

theorem validator_rejects_mistyped_mixed_table_copy_length :
    validationErrorIs invalidMixedTableCopyLengthModule
      "type mismatch" = true := by decide +kernel

theorem validator_rejects_unknown_direct_call :
    validationErrorIs invalidDirectCallIndexModule
      "unknown function" = true := by decide +kernel

theorem validator_accepts_typed_imported_call :
    validationSucceeds validImportedCallValidationModule = true := by decide +kernel

theorem validator_rejects_unknown_indirect_call_type :
    validationErrorIs invalidIndirectCallTypeModule
      "unknown type" = true := by decide +kernel

theorem validator_accepts_typed_table64_indirect_call :
    validationSucceeds validTable64IndirectCallValidationModule = true := by decide +kernel

theorem validator_rejects_unknown_ref_func :
    validationErrorIs invalidRefFuncIndexModule
      "unknown function" = true := by decide +kernel

theorem validator_rejects_extra_block_value :
    validationErrorIs invalidStructuredBlockExtraValueModule
      "type mismatch" = true := by decide +kernel

theorem validator_rejects_missing_block_result :
    validationErrorIs invalidStructuredBlockMissingResultModule
      "type mismatch" = true := by decide +kernel

theorem validator_rejects_mismatched_if_results :
    validationErrorIs invalidStructuredIfResultMismatchModule
      "type mismatch" = true := by decide +kernel

theorem validator_accepts_branch_stack_polymorphism :
    validationSucceeds validStructuredBranchPolymorphicModule = true := by decide +kernel

theorem validator_rejects_invalid_simd_lane :
    validationErrorIs invalidSimdExtractLaneModule
      "invalid lane index" = true := by decide +kernel

theorem validator_rejects_mistyped_simd_splat :
    validationErrorIs invalidSimdSplatOperandModule
      "type mismatch" = true := by decide +kernel

theorem validator_accepts_typed_simd_splat :
    validationSucceeds validSimdSplatValidationModule = true := by decide +kernel

theorem validator_rejects_simd_load_without_memory :
    validationErrorIs invalidSimdLoadWithoutMemoryModule
      "unknown memory" = true := by decide +kernel

theorem validator_accepts_memory64_simd_load :
    validationSucceeds validMemory64SimdLoadValidationModule = true := by decide +kernel

theorem validator_rejects_unknown_local :
    validationErrorIs invalidLocalIndexValidationModule
      "unknown local" = true := by decide +kernel

theorem validator_rejects_unknown_local_after_unreachable :
    validationErrorIs invalidUnreachableLocalIndexValidationModule
      "unknown local" = true := by decide +kernel

theorem validator_accepts_param_and_local_indices :
    validationSucceeds validParamAndLocalIndexValidationModule = true := by decide +kernel

theorem validator_rejects_unknown_function_export :
    validationErrorIs invalidFunctionExportValidationModule
      "unknown function" = true := by decide +kernel

theorem validator_rejects_duplicate_cross_kind_export :
    validationErrorIs invalidDuplicateCrossKindExportValidationModule
      "duplicate export name" = true := by decide +kernel

theorem validator_rejects_start_signature :
    validationErrorIs invalidStartSignatureValidationModule
      "start function" = true := by decide +kernel

theorem validator_rejects_unknown_start_function :
    validationErrorIs invalidStartIndexValidationModule
      "unknown function" = true := by decide +kernel

theorem validator_accepts_imported_start_function :
    validationSucceeds validImportedStartValidationModule = true := by decide +kernel

theorem validator_rejects_decoder_synthesized_data_memory :
    validationErrorIs invalidSyntheticDataMemoryValidationModule
      "unknown memory" = true := by decide +kernel

theorem validator_rejects_mistyped_data_offset :
    validationErrorIs invalidDataOffsetTypeValidationModule
      "type mismatch" = true := by decide +kernel

theorem validator_accepts_memory64_data_offset :
    validationSucceeds validMemory64DataOffsetValidationModule = true := by decide +kernel

theorem validator_rejects_active_element_without_table :
    validationErrorIs invalidActiveElementTableValidationModule
      "unknown table" = true := by decide +kernel

theorem validator_rejects_active_element_type_mismatch :
    validationErrorIs invalidActiveElementTypeValidationModule
      "type mismatch" = true := by decide +kernel

theorem validator_accepts_table64_element_offset :
    validationSucceeds validTable64ElementOffsetValidationModule = true := by decide +kernel

theorem validator_rejects_direct_tail_call_result_mismatch :
    validationErrorIs invalidDirectTailCallResultValidationModule
      "type mismatch" = true := by decide +kernel

theorem validator_accepts_direct_tail_call :
    validationSucceeds validDirectTailCallValidationModule = true := by decide +kernel

theorem validator_rejects_indirect_tail_call_result_mismatch :
    validationErrorIs invalidIndirectTailCallResultValidationModule
      "type mismatch" = true := by decide +kernel

theorem validator_rejects_reference_tail_call_result_mismatch :
    validationErrorIs invalidReferenceTailCallResultValidationModule
      "type mismatch" = true := by decide +kernel

theorem validator_rejects_polymorphic_ref_as_non_null_result :
    validationErrorIs invalidRefAsNonNullPolymorphicResultValidationModule
      "type mismatch" = true := by decide +kernel

theorem validator_rejects_ref_is_null_on_scalar :
    validationErrorIs invalidRefIsNullScalarValidationModule
      "type mismatch" = true := by decide +kernel

theorem validator_accepts_polymorphic_reference_operations :
    validationSucceeds validPolymorphicReferenceValidationModule = true := by decide +kernel

theorem validator_rejects_copy_into_immutable_array :
    validationErrorIs invalidImmutableArrayCopyValidationModule
      "immutable array" = true := by decide +kernel

theorem validator_rejects_mismatched_array_copy :
    validationErrorIs invalidMismatchedArrayCopyValidationModule
      "array types do not match" = true := by decide +kernel

theorem validator_accepts_matching_array_copy :
    validationSucceeds validArrayCopyValidationModule = true := by decide +kernel

theorem validator_rejects_typed_block_result_mismatch :
    validationErrorIs invalidTypedBlockResultValidationModule
      "type mismatch" = true := by decide +kernel

theorem validator_rejects_typed_block_branch_mismatch :
    validationErrorIs invalidTypedBlockBranchValidationModule
      "type mismatch" = true := by decide +kernel

theorem validator_rejects_typed_loop_parameter_mismatch :
    validationErrorIs invalidTypedLoopParameterValidationModule
      "type mismatch" = true := by decide +kernel

theorem validator_accepts_typed_structured_control :
    validationSucceeds validTypedStructuredValidationModule = true := by decide +kernel

theorem validator_rejects_unknown_throw_tag :
    validationErrorIs invalidUnknownThrowValidationModule
      "unknown tag" = true := by decide +kernel

theorem validator_rejects_missing_throw_argument :
    validationErrorIs invalidThrowArgumentValidationModule
      "type mismatch" = true := by decide +kernel

theorem validator_rejects_missing_throw_ref_operand :
    validationErrorIs invalidThrowRefOperandValidationModule
      "type mismatch" = true := by decide +kernel

theorem validator_rejects_try_table_result_mismatch :
    validationErrorIs invalidTryTableResultValidationModule
      "type mismatch" = true := by decide +kernel

theorem validator_rejects_catch_ref_target_mismatch :
    validationErrorIs invalidCatchRefTargetValidationModule
      "type mismatch" = true := by decide +kernel

theorem validator_accepts_typed_try_table_catch :
    validationSucceeds validTryTableCatchValidationModule = true := by decide +kernel

theorem validator_rejects_br_on_null_scalar :
    validationErrorIs invalidBrOnNullScalarValidationModule
      "type mismatch" = true := by decide +kernel

theorem validator_rejects_br_on_non_null_target_mismatch :
    validationErrorIs invalidBrOnNonNullTargetValidationModule
      "type mismatch" = true := by decide +kernel

theorem validator_accepts_reference_branch :
    validationSucceeds validReferenceBranchValidationModule = true := by decide +kernel

theorem validator_rejects_broad_return_call_ref :
    validationErrorIs invalidBroadReturnCallRefValidationModule
      "type mismatch" = true := by decide +kernel

theorem validator_accepts_precise_return_call_ref :
    validationSucceeds validPreciseReturnCallRefValidationModule = true := by decide +kernel

theorem validator_rejects_ref_eq_on_anyref :
    validationErrorIs invalidRefEqAnyValidationModule
      "type mismatch" = true := by decide +kernel

/-! ### Local initialization (function-references proposal)

A local whose type has no default value (a non-nullable reference) may only be
read after `local.set`/`local.tee` on every path, and a structured construct
forgets the initializations made inside it when it ends. Mirrors
`local_init.wast` and `func.wast:660`. -/

def invalidUninitializedLocalValidationModule : Module :=
  { funcs :=
      [{ locals := [.ref false .«extern»],
         body := [.localGet 0, .drop] }] }

def invalidUninitializedLocalAfterBlockValidationModule : Module :=
  { funcs :=
      [{ params := [.ref false .«extern»], locals := [.ref false .«extern»],
         body :=
          [.block 0 0 [.localGet 0, .localSet 1, .localGet 0, .localTee 1, .drop],
           .localGet 1, .drop] }] }

def invalidUninitializedLocalInElseValidationModule : Module :=
  { funcs :=
      [{ params := [.ref false .«extern»], locals := [.ref false .«extern»],
         body :=
          [.const 0,
           .iff 0 0 [.localGet 0, .localSet 1] [.localGet 1, .drop]] }] }

def invalidUninitializedLocalFromIfValidationModule : Module :=
  { funcs :=
      [{ params := [.ref false .«extern»], locals := [.ref false .«extern»],
         body :=
          [.const 0,
           .iff 0 0 [.localGet 0, .localSet 1] [.localGet 0, .localSet 1],
           .localGet 1, .drop] }] }

def invalidUninitializedConcreteLocalValidationModule : Module :=
  { types := [{ params := [], results := [] }]
    funcs :=
      [{ locals := [.ref false (.concrete 0)],
         body := [.localGet 0, .drop] }] }

def validInitializedLocalAfterSetValidationModule : Module :=
  { funcs :=
      [{ params := [.ref false .«extern»], locals := [.ref false .«extern»],
         body := [.localGet 0, .localSet 1, .localGet 1],
         results := [.ref false .«extern»] }] }

def validInitializedLocalAfterTeeValidationModule : Module :=
  { funcs :=
      [{ params := [.ref false .«extern»], locals := [.ref false .«extern»],
         body := [.localGet 0, .localTee 1, .drop, .localGet 1],
         results := [.ref false .«extern»] }] }

def validInitializedLocalReadInBlockValidationModule : Module :=
  { funcs :=
      [{ params := [.ref false .«extern»], locals := [.ref false .«extern»],
         body := [.localGet 0, .localSet 1, .block 0 1 [.localGet 1]],
         results := [.ref false .«extern»] }] }

def validDefaultableLocalReadBeforeSetValidationModule : Module :=
  { funcs :=
      [{ locals := [.externref, .i32],
         body := [.localGet 0, .drop, .localGet 1, .drop] }] }

/-! Structured constructs other than `block`/`if`: a `loop` or `try_table`
body starts from the initializations made before it and forgets its own when
it ends, at any nesting depth. Stack polymorphism after `unreachable` does not
initialize a local, while a `local.set` in unreachable code still does. -/

def invalidUninitializedLocalAfterLoopValidationModule : Module :=
  { funcs :=
      [{ params := [.ref false .«extern»], locals := [.ref false .«extern»],
         body := [.loop 0 0 [.localGet 0, .localSet 1], .localGet 1, .drop] }] }

def validInitializedLocalReadInLoopValidationModule : Module :=
  { funcs :=
      [{ params := [.ref false .«extern»], locals := [.ref false .«extern»],
         body := [.localGet 0, .localSet 1, .loop 0 0 [.localGet 1, .drop]] }] }

def validLocalSetThenReadInLoopValidationModule : Module :=
  { funcs :=
      [{ params := [.ref false .«extern»], locals := [.ref false .«extern»],
         body := [.loop 0 0 [.localGet 0, .localSet 1, .localGet 1, .drop]] }] }

def invalidUninitializedLocalAfterTryTableValidationModule : Module :=
  { funcs :=
      [{ params := [.ref false .«extern»], locals := [.ref false .«extern»],
         body :=
          [.tryTable 0 0 [] [.localGet 0, .localSet 1] [] [], .localGet 1, .drop] }] }

def validInitializedLocalReadInTryTableValidationModule : Module :=
  { funcs :=
      [{ params := [.ref false .«extern»], locals := [.ref false .«extern»],
         body :=
          [.localGet 0, .localSet 1, .tryTable 0 0 [] [.localGet 1, .drop] [] []] }] }

def invalidUninitializedLocalAfterNestedBlockValidationModule : Module :=
  { funcs :=
      [{ params := [.ref false .«extern»], locals := [.ref false .«extern»],
         body :=
          [.block 0 0 [.block 0 0 [.localGet 0, .localSet 1], .localGet 1, .drop]] }] }

def validInitializedLocalReadInNestedBlockValidationModule : Module :=
  { funcs :=
      [{ params := [.ref false .«extern»], locals := [.ref false .«extern»],
         body :=
          [.localGet 0, .localSet 1,
           .block 0 0 [.loop 0 0 [.block 0 0 [.localGet 1, .drop]]]] }] }

def invalidUninitializedLocalAfterUnreachableValidationModule : Module :=
  { funcs :=
      [{ locals := [.ref false .«extern»],
         body := [.unreachable, .localGet 0, .drop] }] }

def validLocalSetInUnreachableCodeValidationModule : Module :=
  { funcs :=
      [{ locals := [.ref false .«extern»],
         body := [.unreachable, .localSet 0, .localGet 0, .drop] }] }

theorem validator_rejects_uninitialized_local :
    validationErrorIs invalidUninitializedLocalValidationModule
      "uninitialized local" = true := by decide +kernel

theorem validator_rejects_uninitialized_local_after_block :
    validationErrorIs invalidUninitializedLocalAfterBlockValidationModule
      "uninitialized local" = true := by decide +kernel

theorem validator_rejects_uninitialized_local_in_else :
    validationErrorIs invalidUninitializedLocalInElseValidationModule
      "uninitialized local" = true := by decide +kernel

theorem validator_rejects_uninitialized_local_from_if :
    validationErrorIs invalidUninitializedLocalFromIfValidationModule
      "uninitialized local" = true := by decide +kernel

theorem validator_rejects_uninitialized_concrete_local :
    validationErrorIs invalidUninitializedConcreteLocalValidationModule
      "uninitialized local" = true := by decide +kernel

theorem validator_accepts_initialized_local_after_set :
    validationSucceeds validInitializedLocalAfterSetValidationModule = true := by decide +kernel

theorem validator_accepts_initialized_local_after_tee :
    validationSucceeds validInitializedLocalAfterTeeValidationModule = true := by decide +kernel

theorem validator_accepts_initialized_local_read_in_block :
    validationSucceeds validInitializedLocalReadInBlockValidationModule = true := by decide +kernel

theorem validator_accepts_defaultable_local_read_before_set :
    validationSucceeds validDefaultableLocalReadBeforeSetValidationModule = true := by decide +kernel

theorem validator_rejects_uninitialized_local_after_loop :
    validationErrorIs invalidUninitializedLocalAfterLoopValidationModule
      "uninitialized local" = true := by decide +kernel

theorem validator_accepts_initialized_local_read_in_loop :
    validationSucceeds validInitializedLocalReadInLoopValidationModule = true := by
  decide +kernel

theorem validator_accepts_local_set_then_read_in_loop :
    validationSucceeds validLocalSetThenReadInLoopValidationModule = true := by
  decide +kernel

theorem validator_rejects_uninitialized_local_after_try_table :
    validationErrorIs invalidUninitializedLocalAfterTryTableValidationModule
      "uninitialized local" = true := by decide +kernel

theorem validator_accepts_initialized_local_read_in_try_table :
    validationSucceeds validInitializedLocalReadInTryTableValidationModule = true := by
  decide +kernel

theorem validator_rejects_uninitialized_local_after_nested_block :
    validationErrorIs invalidUninitializedLocalAfterNestedBlockValidationModule
      "uninitialized local" = true := by decide +kernel

theorem validator_accepts_initialized_local_read_in_nested_block :
    validationSucceeds validInitializedLocalReadInNestedBlockValidationModule = true := by
  decide +kernel

theorem validator_rejects_uninitialized_local_after_unreachable :
    validationErrorIs invalidUninitializedLocalAfterUnreachableValidationModule
      "uninitialized local" = true := by decide +kernel

theorem validator_accepts_local_set_in_unreachable_code :
    validationSucceeds validLocalSetInUnreachableCodeValidationModule = true := by
  decide +kernel

end Wasm.Examples.SmallStep
