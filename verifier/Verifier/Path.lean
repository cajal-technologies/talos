open System (FilePath)

namespace Verifier.Path

def normalize (p : FilePath) : FilePath :=
  let parts := p.components
  let rev := parts.foldl (init := ([] : List String)) fun acc c =>
    match c, acc with
    | ".", _              => acc
    | "..", h :: t        => if h ≠ ".." && h ≠ "" then t else c :: acc
    | _, _                => c :: acc
  ⟨System.FilePath.pathSeparator.toString.intercalate rev.reverse⟩

def relativeTo («from» «to» : FilePath) : FilePath :=
  let f := «from».components.filter (· ≠ "")
  let t := «to».components.filter (· ≠ "")
  let rec strip : List String → List String → List String × List String
    | a :: as, b :: bs => if a = b then strip as bs else (a :: as, b :: bs)
    | xs,      ys      => (xs, ys)
  let (upFrom, downTo) := strip f t
  let parts := upFrom.map (fun _ => "..") ++ downTo
  if parts.isEmpty then ⟨"."⟩
  else ⟨System.FilePath.pathSeparator.toString.intercalate parts⟩

def absNormalize (p : FilePath) : IO FilePath := do
  let abs ← if p.isAbsolute then pure p else
    let cwd ← IO.currentDir
    pure (cwd / p)
  pure (normalize abs)

end Verifier.Path
