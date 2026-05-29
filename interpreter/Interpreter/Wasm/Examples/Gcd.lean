import Interpreter.Wasm.Wp.Tactic
import Interpreter.Wasm.Wp.Block
import Interpreter.Wasm.Wp.Loop
 
namespace Wasm
 
def Gcd : Program := [
  .loop [
    .block [
      .localGet 1,          -- push b
      .eqz,                 -- b == 0 ?
      .br_if 0,             -- if b==0: exit block → exits loop
      .localGet 0,          -- push a
      .localGet 1,          -- push b    stack: [b, a]
      .remU,                -- push a % b
      .localSet 2,          -- temp := a % b
      .localGet 1,          -- push b
      .localSet 0,          -- a := b
      .localGet 2,          -- push temp
      .localSet 1,          -- b := temp
      .br 1                 -- jump to top of loop (continue)
    ]
  ],
  .localGet 0               -- return a
]
 
end Wasm