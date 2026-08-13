import Interpreter.Wasm.SmallStep

/-!
# Selection sort: two handwritten Wasm programs

This tutorial uses two implementations of the same in-place selection sort.
The recursive implementation expresses both the minimum scan and the suffix
traversal with function calls; its proof will follow those calls by induction.
The loop implementation expresses the traversals with structured loops; its
proof will instead use an outer and an inner loop invariant.

The values being sorted are Wasm `i64`s interpreted as unsigned `UInt64`s.
The `StdIO` wrapper and the shared public correctness statement live in
`CodeLib.Examples.SelectionSort.StdIO`.
-/

namespace Wasm.Examples.SelectionSort

open Wasm

/-! ## Small Wasm-building helpers -/

def incrementLocal (index : Nat) : Program :=
  [.localGet index, .const 1, .add, .localSet index]

def addressAt (base index : Nat) : Program :=
  [.localGet base, .localGet index, .const 8, .mul, .add]

def loadAt (base index : Nat) : Program :=
  addressAt base index ++ [.load64 0]

def storeAt (base index : Nat) (value : Program) : Program :=
  addressAt base index ++ value ++ [.store64 0]

def swapAt (base left right temporary : Nat) : Program :=
  loadAt base left ++ [.localSet temporary] ++
  storeAt base left (loadAt base right) ++
  storeAt base right [.localGet temporary]

def swapFirstWith (base right temporary : Nat) : Program :=
  [.localGet base, .load64 0, .localSet temporary,
   .localGet base] ++ loadAt base right ++ [.store64 0] ++
  storeAt base right [.localGet temporary]

def whileLoopCode (condition body : Program) : Program :=
  condition ++ [.eqz, .br_if 1] ++ body ++ [.br 0]

def whileDo (condition body : Program) : Program :=
  [.block 0 0 [.loop 0 0 (whileLoopCode condition body)]]

/-! ## Recursive implementation

`findMinRecursive` has parameters `(array, length, best, scan)` and returns the
index of the least unsigned `i64` value seen from `scan` onward. The sort entry
swaps that value into the first cell and recursively sorts the suffix.
-/

def findMinRecursiveBody (selfIndex : Nat) : Program :=
  [.localGet 3, .localGet 1, .ltU, .eqz,
   .iff 0 0 [.localGet 2, .ret] []] ++
  loadAt 0 3 ++ loadAt 0 2 ++
  [.ltUI64,
   .iff 0 0 [.localGet 3, .localSet 2] [],
   .localGet 0, .localGet 1, .localGet 2,
   .localGet 3, .const 1, .add,
   .call selfIndex,
   .ret]

def findMinRecursiveFunction (selfIndex : Nat) : Function :=
  { params := [.i32, .i32, .i32, .i32]
    results := [.i32]
    body := findMinRecursiveBody selfIndex }

def recursiveSelectionSortBody
    (findMinIndex selfIndex : Nat) : Program :=
  [.localGet 1, .const 2, .ltU,
   .iff 0 0 [.ret] [],
   .localGet 0, .localGet 1, .const 0, .const 1,
   .call findMinIndex,
   .localSet 2] ++
  swapAt 0 3 2 4 ++
  [.localGet 0, .const 8, .add,
   .localGet 1, .const 1, .sub,
   .call selfIndex,
   .ret]

def recursiveSelectionSortFunction
    (findMinIndex selfIndex : Nat) : Function :=
  { params := [.i32, .i32]
    locals := [.i32, .i32, .i64]
    body := recursiveSelectionSortBody findMinIndex selfIndex }

/-! ## Loop implementation

Parameters are `(array, length)`. Locals `2` through `5` are respectively the
outer index, current minimum index, scan index, and `i64` swap temporary.
-/

def loopSelectionSortInnerCondition : Program :=
  [.localGet 4, .localGet 1, .ltU]

def loopSelectionSortInnerStep : Program :=
  loadAt 0 4 ++ loadAt 0 3 ++
  [.ltUI64,
   .iff 0 0 [.localGet 4, .localSet 3] []] ++
  incrementLocal 4

def loopSelectionSortOuterCondition : Program :=
  [.localGet 2, .const 1, .add, .localGet 1, .ltU]

def loopSelectionSortOuterStep : Program :=
  [.localGet 2, .localSet 3,
   .localGet 2, .const 1, .add, .localSet 4] ++
  whileDo loopSelectionSortInnerCondition loopSelectionSortInnerStep ++
  swapAt 0 2 3 5 ++
  incrementLocal 2

def loopSelectionSortBody : Program :=
  [.const 0, .localSet 2] ++
  whileDo loopSelectionSortOuterCondition loopSelectionSortOuterStep ++
  [.ret]

def loopSelectionSortFunction : Function :=
  { params := [.i32, .i32]
    locals := [.i32, .i32, .i32, .i64]
    body := loopSelectionSortBody }

end Wasm.Examples.SelectionSort
