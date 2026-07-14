import Parser
import BenchGen

/-!
lean4-parser (`fgdorais/Parser`) side of the benchmark: the same-family baseline
(a pure monadic combinator library). Separate executable because it and prim-parser
both define `_root_.Parser`. Same grammars, same generated inputs. Run: `lake exe benchlp`.
-/

open Parser Parser.Char Parser.Char.ASCII

abbrev LP (α) := Parser Unit String.Slice Char α

def runArr (p : LP (Array Nat)) (s : String) : Nat :=
  match p.run s.toSlice with | .ok _ a => a.foldl (· + ·) 0 | _ => 0

def runChk (p : LP Nat) (s : String) : Nat :=
  match p.run s.toSlice with | .ok _ a => a | _ => 0

def ws : LP PUnit := Parser.dropMany whitespace

def lpInts : LP (Array Nat) := Parser.sepBy (Parser.token ',') parseNat

def lpCsv : LP Nat :=
  (fun rows => rows.foldl (fun a r => a + r.size) 0) <$>
    Parser.sepBy (Parser.token '\n') (Parser.sepBy (Parser.token ',') parseNat)

def lpJson : LP Nat := do
  let _ ← Parser.token '['
  let _ ← Parser.sepBy (Parser.token ',') parseNat
  let _ ← Parser.token ']'
  pure 1

mutual
partial def lpSexp : LP Nat := lpList <|> lpAtom
partial def lpAtom : LP Nat := do
  let _ ← Parser.takeMany1 alpha; ws; pure 1
partial def lpList : LP Nat := do
  let _ ← Parser.token '('; ws
  let cs ← Parser.takeMany lpSexp
  let _ ← Parser.token ')'; ws
  pure (cs.foldl (· + ·) 0)
end

mutual
partial def lpLam : LP Nat := lpLamAbs <|> lpVar
partial def lpVar : LP Nat := do
  let _ ← Parser.takeMany1 alpha; ws; pure 1
partial def lpLamAbs : LP Nat := do
  let _ ← Parser.token '\\'; ws
  let _ ← Parser.takeMany1 alpha; ws
  let _ ← Parser.token '.'; ws
  let b ← lpLam
  pure (b + 1)
end

def main : IO Unit := do
  let reps := 25
  let intsIn   ← prep "integers" (genInts 20000)
  let sexpIn   ← prep "sexp"     (genSexp 3 8)
  let csvIn    ← prep "csv"      (genCsv 4000 6)
  let jsonIn   ← prep "json"     (genJson 20000)
  let lambdaIn ← prep "lambda"   (genLambda 2000)
  IO.println "lean4-parser (fgdorais):"
  let rows := #[
    ← benchOne "integers" intsIn   reps (fun _ => runArr lpInts intsIn),
    ← benchOne "sexp"     sexpIn   reps (fun _ => runChk lpSexp sexpIn),
    ← benchOne "csv"      csvIn    reps (fun _ => runChk lpCsv csvIn),
    ← benchOne "json"     jsonIn   reps (fun _ => runChk lpJson jsonIn),
    ← benchOne "lambda"   lambdaIn reps (fun _ => runChk lpLam lambdaIn)]
  writeTsv "bench-lp.tsv" rows
