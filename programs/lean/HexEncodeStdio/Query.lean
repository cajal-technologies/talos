import Project.HexStdio.Program

open Wasm

def dumpProgram (p : Program) : IO Unit :=
  for (instr, i) in p.toArray.zipIdx do
    IO.println (toString i ++ ": " ++ reprStr instr)

#eval IO.println "func2"
#eval dumpProgram Project.HexStdio.func2
#eval IO.println "func6"
#eval dumpProgram Project.HexStdio.func6
#eval IO.println "func7"
#eval dumpProgram Project.HexStdio.func7
#eval IO.println "func8"
#eval dumpProgram Project.HexStdio.func8
#eval IO.println "func10"
#eval dumpProgram Project.HexStdio.func10
#eval IO.println "func4"
#eval dumpProgram Project.HexStdio.func4
#eval IO.println "func12"
#eval dumpProgram Project.HexStdio.func12
#eval IO.println "func13"
#eval dumpProgram Project.HexStdio.func13
#eval IO.println "func15"
#eval dumpProgram Project.HexStdio.func15
#eval IO.println "func16"
#eval dumpProgram Project.HexStdio.func16
#eval IO.println "func17"
#eval dumpProgram Project.HexStdio.func17
