import Project.HexStdio.Spec
open Wasm
#eval IO.println s!"memory={repr Project.HexStdio.«module».memory}"
#eval IO.println s!"initial pages={(Project.HexStdio.«module».initialStore (α := Universal.State)).mem.pages}"
#check Project.HexStdio.«module».memory
