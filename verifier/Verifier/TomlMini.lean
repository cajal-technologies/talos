/-!
# TomlMini — a deliberately tiny TOML reader/writer

The verifier's two control files (`verifier.toml`, `origin.toml`) only ever
hold a handful of `key = "value"` pairs. Pulling a real TOML library would
balloon the dependency graph; instead this module supports exactly the
shape `verifier new` emits:

* blank lines and `# …` comments are skipped,
* each significant line is `<key> = "<value>"`,
* `\"` and `\\` escapes are recognised inside the value.

Anything else is a parse error.

We work in `List Char` throughout, on purpose: the `String` API in recent
Lean toolchains has been migrating to a slice-based interface, and the
sequence of trims / drops we need has been changing shape. `List Char` is
boring and stable.
-/

namespace Verifier.TomlMini

abbrev Table := List (String × String)

private def isSpace (c : Char) : Bool :=
  c = ' ' || c = '\t' || c = '\r' || c = '\n'

private def trimL (cs : List Char) : List Char := cs.dropWhile isSpace

private def trimR (cs : List Char) : List Char :=
  (cs.reverse.dropWhile isSpace).reverse

private def trim (cs : List Char) : List Char := trimR (trimL cs)

private def isPrefix (pref : List Char) (cs : List Char) : Bool :=
  match pref, cs with
  | [],      _       => true
  | _,       []      => false
  | p :: ps, c :: rs => p = c && isPrefix ps rs

private partial def unescapeAux : List Char → List Char → Except String (List Char)
  | [],                  acc => .ok acc.reverse
  | '\\' :: '"'  :: rest, acc => unescapeAux rest ('"'  :: acc)
  | '\\' :: '\\' :: rest, acc => unescapeAux rest ('\\' :: acc)
  | '\\' :: c    :: _,    _   => .error s!"unknown escape \\{c} in toml string literal"
  | c :: rest,            acc => unescapeAux rest (c :: acc)

private def unescape (cs : List Char) : Except String String := do
  let out ← unescapeAux cs []
  return String.ofList out

private partial def scanString
    (lineNo : Nat) (key : String)
    : List Char → List Char → Except String (List Char × List Char)
  | [],                  _   => .error s!"line {lineNo}: unterminated string for `{key}`"
  | '\\' :: c :: rest,   acc => scanString lineNo key rest (c :: '\\' :: acc)
  | '"' :: rest,         acc => .ok (acc.reverse, rest)
  | c :: rest,           acc => scanString lineNo key rest (c :: acc)

private def parseLine (lineNo : Nat) (rawStr : String) : Except String (Option (String × String)) := do
  let line := trim rawStr.toList
  match line with
  | []      => return none
  | '#' :: _ => return none
  | _ =>
    let (keyChars, afterEq) := line.span (· ≠ '=')
    match afterEq with
    | [] => .error s!"line {lineNo}: expected `key = \"value\"`, got `{String.ofList line}`"
    | _ :: rest =>
      let key := String.ofList (trim keyChars)
      if key.isEmpty then
        .error s!"line {lineNo}: empty key"
      else
        let rest := trim rest
        match rest with
        | '"' :: body =>
          let (rawVal, tail) ← scanString lineNo key body []
          let trailing := trim tail
          if trailing.isEmpty || trailing.head? = some '#' then
            let v ← unescape rawVal
            return some (key, v)
          else
            .error s!"line {lineNo}: unexpected trailing content after value for `{key}`"
        | _ =>
          .error s!"line {lineNo}: value for `{key}` must be a double-quoted string"

/-- Parse a string in our restricted TOML dialect. Order is preserved. -/
def parse (source : String) : Except String Table := do
  let mut out : Table := []
  let mut lineNo := 0
  for raw in source.splitOn "\n" do
    lineNo := lineNo + 1
    match ← parseLine lineNo raw with
    | none    => continue
    | some kv => out := out ++ [kv]
  return out

/-- Look up a key. Returns the first match. -/
def get? (t : Table) (k : String) : Option String :=
  t.find? (·.1 = k) |>.map (·.2)

/-- Required-key accessor; produces a clear error if absent. -/
def require (t : Table) (k : String) (file : String) : Except String String :=
  match get? t k with
  | some v => .ok v
  | none   => .error s!"{file}: missing required key `{k}`"

private def escapeOne (c : Char) : List Char :=
  match c with
  | '"'  => ['\\', '"']
  | '\\' => ['\\', '\\']
  | c    => [c]

private def escape (s : String) : String :=
  String.ofList (s.toList.flatMap escapeOne)

/-- Render a table as TOML. The exact format `parse` reads back. -/
def render (entries : Table) : String :=
  entries.foldl (init := "") fun acc (k, v) =>
    acc ++ s!"{k} = \"{escape v}\"\n"

end Verifier.TomlMini
