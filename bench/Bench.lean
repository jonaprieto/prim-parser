import PrimParser
import Examples.Json
import Examples.Lambda
import BenchGen

-- prim side. lean4-parser side is BenchLp.lean: separate exe because both
-- libraries define `_root_.Parser` and can't share a module.

open Parser

def toText (s : String) : Text s.toList.length := ⟨s.toList, rfl⟩

def primInts : Parser Error flexible (List Nat) := sepBy (string ",") nat

def primSexp : Parser Error conditional Nat :=
  fix fun self =>
    let plist : Parser Error conditional Nat := gdo
      lexeme (char '(')
      let first ← self
      let rest ← many (gdo whitespace; self)
      lexeme (char ')')
      return first + rest.foldl (· + ·) 0
    let patom : Parser Error conditional Nat :=
      (fun _ => 1) <$>ᵍ takeWhile1 Char.isAlphanum
    patom <|> plist

def primCsv : Parser Error flexible Nat :=
  (fun rows => rows.foldl (fun a r => a + r.length) 0) <$>ᵍ
    sepBy (char '\n') (sepBy (char ',') nat)

def main : IO Unit := do
  let reps := 25
  let intsIn   ← prep "integers" (genInts 20000)
  let sexpIn   ← prep "sexp"     (genSexp 3 8)
  let csvIn    ← prep "csv"      (genCsv 4000 6)
  let jsonIn   ← prep "json"     (genJson 20000)
  let lambdaIn ← prep "lambda"   (genLambda 2000)
  IO.println "prim-parser:"
  let rows := #[
    ← benchOne "integers" intsIn   reps (fun _ => (primInts.runResult? (toText intsIn)).map (·.foldl (·+·) 0) |>.getD 0),
    ← benchOne "sexp"     sexpIn   reps (fun _ => (primSexp.runResult? (toText sexpIn)).getD 0),
    ← benchOne "csv"      csvIn    reps (fun _ => (primCsv.runResult? (toText csvIn)).getD 0),
    ← benchOne "json"     jsonIn   reps (fun _ => if (Json.json.runResult? (toText jsonIn)).isSome then 1 else 0),
    ← benchOne "lambda"   lambdaIn reps (fun _ => if (Term.term.runResult? (toText lambdaIn)).isSome then 1 else 0)]
  writeTsv "bench-prim.tsv" rows
