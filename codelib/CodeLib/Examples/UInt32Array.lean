import CodeLib.RustStd.MemArray.SmallStep

/-!
# UInt32 array program combinators

Instruction sequences shared by the handwritten array algorithms.
-/

namespace Wasm.Examples.UInt32Array

open Wasm

def increment (index : Nat) : Program :=
  [.localGet index, .const 1, .add, .localSet index]

def address (base index : Nat) : Program :=
  [.localGet base, .localGet index, .const 4, .mul, .add]

def loadAt (base index : Nat) : Program :=
  address base index ++ [.load32 0]

def storeAt (base index : Nat) (value : Program) : Program :=
  address base index ++ value ++ [.store32 0]

def whileLoopCode (condition body : Program) : Program :=
  condition ++ [.eqz, .br_if 1] ++ body ++ [.br 0]

def whileDo (condition body : Program) : Program :=
  [.block 0 0 [.loop 0 0 (whileLoopCode condition body)]]

def lessLocal (lhs rhs : Nat) : Program :=
  [.localGet lhs, .localGet rhs, .ltU]

end Wasm.Examples.UInt32Array
