import Project.HexStdio.Program
open Wasm
def ob : Program := match Project.HexStdio.func8[5]? with
| some (Instruction.block _ _ body _ _) => body
| _ => []
def lb : Program := match ob[2]? with
| some (Instruction.loop _ _ body _ _) => body
| _ => []
#eval IO.println s!"outer {ob.length} loop {lb.length} head {repr ob.head?}"
