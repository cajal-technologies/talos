import Verifier.Emit

namespace Verifier.EmitFidelity

open Wasm

def fidelityModule : Wasm.Module := {
  funcs := [{
    params := [.i32]
    locals := [.i64]
    body := [
      .block 1 1 [.refNull (.ref true .func)] [.i32] [.i64],
      .loop 1 0 [] [.i64] [],
      .iff 0 1 [] [] [] [.i32],
      .tryTable 0 0 [.catchAll 0] [] [] [],
      .refNullExtern (.ref false .extern),
      .refNullExn (.ref true .exn),
      .gc (.refCast true (.named "Node"))
    ]
    results := [.i64]
    typeIdx := some 3
  }]
  exports := [{ name := "run", funcIdx := 0 }]
  memory := some {
    pagesMin := 1
    pagesMax := some 4
    data := [{
      offset := some 7
      bytes := [1, 2]
      memIdx := 2
      offsetType := some .i64
      offsetExprPresent := true
      offsetExpr := [.globalGet 0]
    }]
    is64 := true
  }
  extraMemories := [{ pagesMin := 2, pagesMax := some 8, is64 := true }]
  dataWithoutMemory := true
  globals := [{
    init := .i64 9
    declaredType := some .i64
    isMut := false
    sourceInit := some [.constI64 9]
    initExpr := [.globalGet 0]
  }]
  imports := [{ «module» := "host", name := "read", params := [.i64], results := [.i32] }]
  startFunc := some 0
  types := [{ params := [.i32], results := [.i64] }]
  gcTypes := [
    { comp := .func { params := [.i32], results := [.i64] } },
    {
      comp := .struct [{ storage := .packed 8, isMut := true }]
      sourceName := some "Node"
      super := some 0
      «final» := false
      recGroup := some 4
    },
    { comp := .array { storage := .val (.ref false (.named "Node")), isMut := true } }
  ]
  tables := [{ min := 1, max := some 3, elemType := .externref, is64 := true }]
  elements := [{
    tableIdx := some 0
    offset := some 2
    offsetType := some .i64
    offsetExprPresent := true
    elemType := some .externref
    declarative := true
    funcs := [some 0, none]
    exprs := [[.refNullExtern (.ref true .extern)]]
    offsetExpr := [.globalGet 0]
  }]
  importedGlobals := [("host", "g")]
  importedTables := [("host", "t")]
  importedMemories := [("host", "m")]
  importedTags := [("host", "tag")]
  globalExports := [("g", 0)]
  tableExports := [("t", 0)]
  memoryExports := [("m", 0)]
  tagExports := [("tag", 0)]
  tags := [{ params := [.i32], results := [] }]
}

private def emittedFunctions := Verifier.Emit.funcBodies fidelityModule
private def emittedModule := Verifier.Emit.module fidelityModule

private def commentSafetyModule : Wasm.Module := {
  imports := [{ «module» := "host", name := "read", params := [], results := [] }]
  funcs := [{ params := [], locals := [], body := [], results := [] }]
  exports := [{ name := "break -/ #check False /-", funcIdx := 1 }]
}

private def emittedCommentSafetyFunctions :=
  Verifier.Emit.funcBodies commentSafetyModule

#guard emittedFunctions.contains "typeIdx := some 3"
#guard emittedFunctions.contains ".block 1 1"
#guard emittedFunctions.contains "[.i32] [.i64]"
#guard emittedFunctions.contains ".refNullExtern (.ref false (.extern))"
#guard emittedFunctions.contains ".gc (Wasm.GcOp.refCast true (Wasm.GcHeapType.named \"Node\"))"
#guard emittedModule.contains "memIdx := 2"
#guard emittedModule.contains "offsetType := some (.i64)"
#guard emittedModule.contains "offsetExprPresent := true"
#guard emittedModule.contains "is64 := true"
#guard emittedModule.contains "sourceInit := some ("
#guard emittedModule.contains "initExpr := ["
#guard emittedModule.contains "extraMemories := ["
#guard emittedModule.contains "dataWithoutMemory := true"
#guard emittedModule.contains "startFunc := some 0"
#guard emittedModule.contains "gcTypes := ["
#guard emittedModule.contains "recGroup := some 4"
#guard emittedModule.contains ".array ({ storage := .val (.ref false (.named \"Node\"))"
#guard emittedModule.contains "declarative := true"
#guard emittedModule.contains "elemType := some (.externref)"
#guard emittedModule.contains "exprs := ["
#guard emittedModule.contains "importedMemories := ["
#guard emittedModule.contains "globalExports := ["
#guard emittedModule.contains "tagExports := ["
#guard emittedModule.contains "tags := ["
#guard emittedCommentSafetyFunctions.contains "/-- Exported function. -/"
#guard !(emittedCommentSafetyFunctions.contains "break -/")

end Verifier.EmitFidelity
