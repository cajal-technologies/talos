import Project.HexStdio.Spec
open Wasm
#eval IO.println s!"mems={repr Project.HexStdio.«module».mems}"
#eval IO.println s!"memory={repr Project.HexStdio.«module».memory}"
#eval IO.println s!"initial pages={((Universal.State.ofInput []).wasm.mem.pages)}"
#check Project.HexStdio.«module».memory
