import Verifier.EmitFidelity

namespace Verifier.EmitRoundTrip

open Wasm

private def goldenFunctions : String := r#"def func0 : Wasm.Program :=
  [
  .block 1 1 [
    .refNull (.ref true (.func))
  ] [.i32] [.i64],
  .loop 1 0 [] [.i64] [],
  .iff 0 1 [] [] [] [.i32],
  .tryTable 0 0 [Wasm.CatchClause.catchAll 0] [] [] [],
  .refNullExtern (.ref false (.extern)),
  .refNullExn (.ref true (.exn)),
  .gc (Wasm.GcOp.refCast true (Wasm.GcHeapType.named "Node"))
]

def func0Def : Wasm.Function :=
  { params := [.i32], locals := [.i64], body := func0, results := [.i64], typeIdx := some 3 }"#

private def goldenModule : String := r#"{
  imports := [
    { «module» := "host", name := "read", params := [.i64], results := [.i32] }
  ],
  funcs := [
    func0Def
  ],
  exports := [
    { name := "run", funcIdx := 0 }
  ],
  memory := some (Wasm.MemDecl.mk (1 : UInt32) (some (4 : UInt32)) ([
      { offset := some (7 : UInt32), bytes := [(1 : UInt8), (2 : UInt8)], memIdx := 2, offsetType := some (.i64), offsetExprPresent := true, offsetExpr := [
          .globalGet 0
        ] }
    ]) true),
  extraMemories := [
    Wasm.MemDecl.mk (2 : UInt32) (some (8 : UInt32)) ([]) true
  ],
  dataWithoutMemory := true,
  globals := [
    { init := .i64 (9 : UInt64), declaredType := some (.i64), isMut := false, sourceInit := some ([
        .constI64 (9 : UInt64)
      ]), initExpr := [
        .globalGet 0
      ] }
  ],
  startFunc := some 0,
  types := [
    { params := [.i32], results := [.i64] }
  ],
  gcTypes := [
    { comp := .func ({ params := [.i32], results := [.i64] }), sourceName := none, super := none, «final» := true, recGroup := none },
    { comp := .struct [{ storage := .packed 8, isMut := true }], sourceName := some "Node", super := some 0, «final» := false, recGroup := some 4 },
    { comp := .array ({ storage := .val (.ref false (.named "Node")), isMut := true }), sourceName := none, super := none, «final» := true, recGroup := none }
  ],
  tables := [
    { min := 1, max := some 3, elemType := .externref, is64 := true }
  ],
  elements := [
    { tableIdx := some 0, offset := some 2, offsetType := some (.i64), offsetExprPresent := true, elemType := some (.externref), declarative := true, funcs := [some 0, none], exprs := [
        [
          .refNullExtern (.ref true (.extern))
        ]
      ], offsetExpr := [
        .globalGet 0
      ] }
  ],
  importedGlobals := [
    ("host", "g")
  ],
  importedTables := [
    ("host", "t")
  ],
  importedMemories := [
    ("host", "m")
  ],
  importedTags := [
    ("host", "tag")
  ],
  globalExports := [
    ("g", 0)
  ],
  tableExports := [
    ("t", 0)
  ],
  memoryExports := [
    ("m", 0)
  ],
  tagExports := [
    ("tag", 0)
  ],
  tags := [
    { params := [.i32], results := [] }
  ]
}"#

#guard Verifier.Emit.funcBodies Verifier.EmitFidelity.fidelityModule = goldenFunctions
#guard Verifier.Emit.module Verifier.EmitFidelity.fidelityModule = goldenModule

namespace ReElaborated

def func0 : Wasm.Program :=
  [
  .block 1 1 [
    .refNull (.ref true (.func))
  ] [.i32] [.i64],
  .loop 1 0 [] [.i64] [],
  .iff 0 1 [] [] [] [.i32],
  .tryTable 0 0 [Wasm.CatchClause.catchAll 0] [] [] [],
  .refNullExtern (.ref false (.extern)),
  .refNullExn (.ref true (.exn)),
  .gc (Wasm.GcOp.refCast true (Wasm.GcHeapType.named "Node"))
]

def func0Def : Wasm.Function :=
  { params := [.i32], locals := [.i64], body := func0, results := [.i64], typeIdx := some 3 }

def «module» : Wasm.Module := {
  imports := [
    { «module» := "host", name := "read", params := [.i64], results := [.i32] }
  ],
  funcs := [
    func0Def
  ],
  exports := [
    { name := "run", funcIdx := 0 }
  ],
  memory := some (Wasm.MemDecl.mk (1 : UInt32) (some (4 : UInt32)) ([
      { offset := some (7 : UInt32), bytes := [(1 : UInt8), (2 : UInt8)], memIdx := 2, offsetType := some (.i64), offsetExprPresent := true, offsetExpr := [
          .globalGet 0
        ] }
    ]) true),
  extraMemories := [
    Wasm.MemDecl.mk (2 : UInt32) (some (8 : UInt32)) ([]) true
  ],
  dataWithoutMemory := true,
  globals := [
    { init := .i64 (9 : UInt64), declaredType := some (.i64), isMut := false, sourceInit := some ([
        .constI64 (9 : UInt64)
      ]), initExpr := [
        .globalGet 0
      ] }
  ],
  startFunc := some 0,
  types := [
    { params := [.i32], results := [.i64] }
  ],
  gcTypes := [
    { comp := .func ({ params := [.i32], results := [.i64] }), sourceName := none, super := none, «final» := true, recGroup := none },
    { comp := .struct [{ storage := .packed 8, isMut := true }], sourceName := some "Node", super := some 0, «final» := false, recGroup := some 4 },
    { comp := .array ({ storage := .val (.ref false (.named "Node")), isMut := true }), sourceName := none, super := none, «final» := true, recGroup := none }
  ],
  tables := [
    { min := 1, max := some 3, elemType := .externref, is64 := true }
  ],
  elements := [
    { tableIdx := some 0, offset := some 2, offsetType := some (.i64), offsetExprPresent := true, elemType := some (.externref), declarative := true, funcs := [some 0, none], exprs := [
        [
          .refNullExtern (.ref true (.extern))
        ]
      ], offsetExpr := [
        .globalGet 0
      ] }
  ],
  importedGlobals := [
    ("host", "g")
  ],
  importedTables := [
    ("host", "t")
  ],
  importedMemories := [
    ("host", "m")
  ],
  importedTags := [
    ("host", "tag")
  ],
  globalExports := [
    ("g", 0)
  ],
  tableExports := [
    ("t", 0)
  ],
  memoryExports := [
    ("m", 0)
  ],
  tagExports := [
    ("tag", 0)
  ],
  tags := [
    { params := [.i32], results := [] }
  ]
}

end ReElaborated

theorem rich_module_roundtrip :
    ReElaborated.module = Verifier.EmitFidelity.fidelityModule := by
  rfl

private def goldenDriftCheck : String := r#"/-- Exact source of `module.wat` captured when `verifier emit` last ran. -/
private def expectedWatSource : String := "(module\n  ;; exact\n)"

-- Compile-time drift check: errors if `module.wat` is absent or has changed.
#guard_msgs (drop info) in
#eval show IO Unit from do
  let path : System.FilePath := "rust/build/demo/program.wat"
  unless ← path.pathExists do
    throw <| IO.userError
      s!"{path} is missing; cannot validate Program.lean provenance."
  let actual ← IO.FS.readFile path
  if actual ≠ expectedWatSource then
    throw <| IO.userError
      s!"{path} has drifted from Program.lean; re-run `lake exe verifier emit`.""#

#guard Verifier.Emit.driftCheck "rust/build/demo/program.wat" "(module\n  ;; exact\n)" =
  goldenDriftCheck

end Verifier.EmitRoundTrip
