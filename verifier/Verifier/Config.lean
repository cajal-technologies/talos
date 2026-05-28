import Verifier.Toml

/-!
# Verifier configuration files

`verifier.toml` lives next to a rust crate's `Cargo.toml`; `origin.toml`
lives in the lean verification subfolder. Both use the restricted TOML
dialect from `Verifier.Toml` — flat `key = "value"` pairs only. A `[build]`
table is *emulated* with the flat keys `build_command` and
`build_artifact`, which keeps the parser trivial.

Schema:

```
# verifier.toml (rust side)
lean_project        = "../../.."          # path to dir containing lakefile.toml
verification_folder = "Programs/X/Foo"    # subfolder inside the lean project
build_command       = "cargo build ..."   # optional; default is the built-in cargo wasm command
build_artifact      = "target/.../{crate}.wasm"  # optional; default matches built-in command

# origin.toml (lean side)
rust_project = "../../../../rust/..."     # path back to the rust project dir
```
-/

namespace Verifier

/-- Build configuration. Both fields default to the built-in cargo wasm
command and its conventional artifact path. -/
structure BuildConfig where
  /-- Shell-style command to build the wasm binary. Parsed by splitting on
  ASCII spaces (no quoting). When `none`, the verifier uses the built-in
  `cargo build --release --target wasm32-unknown-unknown`. -/
  command  : Option String := none
  /-- Filesystem path (relative to the rust project dir) of the produced
  wasm binary. The substring `{crate}` is replaced with the crate name
  (from `Cargo.toml`'s `[package].name`, with `-` → `_`). When `none`,
  defaults to `target/wasm32-unknown-unknown/release/{crate}.wasm`. -/
  artifact : Option String := none

structure VerifierToml where
  leanProject        : String
  verificationFolder : String
  build              : BuildConfig := {}

structure OriginToml where
  rustProject : String

namespace BuildConfig

/-- The default build command, matching the previous hard-coded behaviour. -/
def defaultCommand : String :=
  "cargo build --release --target wasm32-unknown-unknown"

/-- The default artifact path template. -/
def defaultArtifact : String :=
  "target/wasm32-unknown-unknown/release/{crate}.wasm"

/-- Effective build command (configured or default). -/
def effectiveCommand (b : BuildConfig) : String :=
  b.command.getD defaultCommand

/-- Effective artifact path template (configured or default). -/
def effectiveArtifact (b : BuildConfig) : String :=
  b.artifact.getD defaultArtifact

end BuildConfig

/-- Substitute `{crate}` in an artifact template. -/
def substituteCrate (template : String) (crate : String) : String :=
  -- Cargo replaces `-` with `_` in the on-disk filename.
  let fs := crate.map (fun c => if c = '-' then '_' else c)
  template.replace "{crate}" fs

/-- Split a shell-style command into program + args by whitespace. No
quoting is supported (we control the defaults; users who need shell
features can wrap their command in a script). -/
def splitCommand (cmd : String) : Option (String × Array String) :=
  let parts := (cmd.splitOn " ").filter (·.length > 0)
  match parts with
  | []      => none
  | p :: ps => some (p, ps.toArray)

namespace Toml

/-- Parse and validate `verifier.toml`. -/
def readVerifier (path : System.FilePath) : IO VerifierToml := do
  let txt ← IO.FS.readFile path
  let t ← match Verifier.Toml.parse txt with
    | .ok t   => pure t
    | .error e => throw (IO.userError s!"{path}: {e}")
  let req k := match Verifier.Toml.require t k path.toString with
    | .ok v  => pure v
    | .error e => throw (IO.userError e)
  let lp ← req "lean_project"
  let vf ← req "verification_folder"
  let cmd := Verifier.Toml.get? t "build_command"
  let art := Verifier.Toml.get? t "build_artifact"
  pure {
    leanProject := lp,
    verificationFolder := vf,
    build := { command := cmd, artifact := art }
  }

/-- Parse `verifier.toml` permissively: every field is optional. This is
the form `verifier new` writes (an empty file is valid). -/
def readVerifierOptional (path : System.FilePath) : IO VerifierToml := do
  let txt ← IO.FS.readFile path
  let t ← match Verifier.Toml.parse txt with
    | .ok t   => pure t
    | .error e => throw (IO.userError s!"{path}: {e}")
  pure {
    leanProject := (Verifier.Toml.get? t "lean_project").getD "",
    verificationFolder := (Verifier.Toml.get? t "verification_folder").getD "",
    build := {
      command := Verifier.Toml.get? t "build_command",
      artifact := Verifier.Toml.get? t "build_artifact"
    }
  }

/-- Parse and validate `origin.toml`. -/
def readOrigin (path : System.FilePath) : IO OriginToml := do
  let txt ← IO.FS.readFile path
  let t ← match Verifier.Toml.parse txt with
    | .ok t   => pure t
    | .error e => throw (IO.userError s!"{path}: {e}")
  match Verifier.Toml.require t "rust_project" path.toString with
  | .ok v  => pure { rustProject := v }
  | .error e => throw (IO.userError e)

/-- Render `verifier.toml`. Omits build keys when set to defaults. -/
def renderVerifier (v : VerifierToml) : String :=
  let base : Verifier.Toml.Table :=
    [ ("lean_project", v.leanProject),
      ("verification_folder", v.verificationFolder) ]
  let withCmd := match v.build.command with
    | some c => base ++ [("build_command", c)]
    | none   => base
  let withArt := match v.build.artifact with
    | some a => withCmd ++ [("build_artifact", a)]
    | none   => withCmd
  Verifier.Toml.render withArt

def renderOrigin (o : OriginToml) : String :=
  Verifier.Toml.render [("rust_project", o.rustProject)]

end Toml

end Verifier
