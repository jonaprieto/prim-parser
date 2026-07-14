import PrimParser
open Parser

/-! Single-parse binary for hyperfine: parse canada.json once with the SHALLOW
`Parser` backend, print the node count. Structural twin of `bench/JCanada.lean`
(the deep `G` backend) so the two are a like-for-like grammar comparison.

Difference that matters: the shallow backend parses `Text Char` (the 2.1MB file
decoded into a boxed `Array Char`), whereas the deep backend parses raw
`ByteArray`. That decode + boxed-char cost is exactly what this binary exposes. -/

@[inline] def cNumCh (c : Char) : Bool :=
  c.isDigit || c == '.' || c == '-' || c == '+' || c == 'e' || c == 'E'
@[inline] def cNotQuote (c : Char) : Bool := c != '\"'

def sJson : Parser Error conditional Nat :=
  fix fun self =>
    let jnum : Parser Error conditional Nat :=
      (fun _ => 1) <$>ᵍ takeWhile1 cNumCh
    let jstr : Parser Error conditional Nat := gdo
      char '\"'
      let _ ← takeWhile cNotQuote
      char '\"'
      return 1
    let jkw : Parser Error conditional Nat :=
      (fun _ => 1) <$>ᵍ takeWhile1 (·.isAlpha)
    let jarr : Parser Error conditional Nat := gdo
      char '['
      let xs ← sepBy (char ',') self
      whitespace
      char ']'
      return 1 + xs.foldl (· + ·) 0
    let jpair : Parser Error conditional Nat := gdo
      whitespace
      char '\"'
      let _ ← takeWhile cNotQuote
      char '\"'
      whitespace
      char ':'
      let v ← self
      return v
    let jobj : Parser Error conditional Nat := gdo
      char '{'
      let xs ← sepBy (char ',') jpair
      whitespace
      char '}'
      return 1 + xs.foldl (· + ·) 0
    -- dispatch on the first character (mirrors Examples/Json) to sidestep the
    -- grade algebra of a five-way `<|>` chain.
    gdo
      whitespace
      let c ← peek
      match c with
      | '{' => jobj
      | '[' => jarr
      | '\"' => jstr
      | 't' => jkw
      | 'f' => jkw
      | 'n' => jkw
      | _   => jnum
      grade_by by simp

@[noinline] def barrier {n} (_k : Nat) (t : Text n) : Text n := t

def main (args : List String) : IO Unit := do
  let s ← IO.FS.readFile "bench-data/canada.json"
  if args.contains "time" then
    let t := ofString s              -- decode once; time the parse only
    let mut best : Nat := 1 <<< 62
    for i in [0:100] do
      let t0 ← IO.monoNanosNow
      let n := (sJson.runResult? (barrier i t)).getD 0
      if n != 167179 then IO.eprintln "err"
      let t1 ← IO.monoNanosNow
      best := min best (t1 - t0)
    IO.println s!"count={(sJson.runResult? t).getD 0} parse_ms={(Float.ofNat best)/1e6}"
  else
    match sJson.runResult? (ofString s) with
    | some n => IO.println n
    | none   => IO.println "parse-failed"
