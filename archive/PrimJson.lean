import PrimParser
open Parser

/-- Full JSON node-count parser written in the shallow `PrimParser` combinators
(the original graded monad: `fix`, `gdo`, `<|>`/`oneOf`, `takeWhile`). Same
checksum as the deep-embedded / angstrom / megaparsec versions. -/
def jNodes : Parser Char Error conditional Nat :=
  fix fun v =>
    let jnum : Parser Char Error conditional Nat :=
      (fun _ => 1) <$>ᵍ takeWhile1 (fun c =>
        c.isDigit || c == '-' || c == '+' || c == '.' || c == 'e' || c == 'E')
    let jstr : Parser Char Error conditional Nat := gdo
      char '"'; takeWhile (· != '"'); char '"'; return 1
      grade_by by simp
    let jkw : Parser Char Error conditional Nat :=
      (fun _ => 1) <$>ᵍ takeWhile1 Char.isAlpha
    let jarr : Parser Char Error conditional Nat := gdo
      char '['; whitespace
      let xs ← sepBy (gdo char ','; whitespace) v
      whitespace; char ']'
      return (1 + xs.foldl (· + ·) 0)
      grade_by by simp
    let jpair : Parser Char Error conditional Nat := gdo
      whitespace; char '"'; takeWhile (· != '"'); char '"'; whitespace; char ':'
      let n ← v
      return n
      grade_by by simp
    let jobj : Parser Char Error conditional Nat := gdo
      char '{'; whitespace
      let xs ← sepBy (gdo char ','; whitespace) jpair
      whitespace; char '}'
      return (1 + xs.foldl (· + ·) 0)
      grade_by by simp
    gdo
      whitespace
      let r ← oneOf (jnum ::₁ [jstr, jkw, jarr, jobj])
      return r
      grade_by by simp

@[noinline] def countNodes (s : String) : Nat :=
  (jNodes.runResult? (ofString s)).getD 0

def main : IO Unit := do
  let canada ← IO.FS.readFile "bench-data/canada.json"
  IO.println s!"shallow PrimParser: canada.json {canada.length} bytes, nodes = {countNodes canada}"
  let ref ← IO.mkRef canada
  let mut best : Float := 1.0e9
  for _ in [0:20] do
    let s ← ref.get
    let t0 ← IO.monoNanosNow
    let _ ← IO.lazyPure (fun _ => countNodes s)
    let t1 ← IO.monoNanosNow
    let dt := (Float.ofNat (t1-t0))/1000000.0
    if dt < best then best := dt
  IO.println s!"  canada.json (shallow PrimParser): {best} ms/iter"
