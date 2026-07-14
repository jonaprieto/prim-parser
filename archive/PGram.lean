import BenchGen
/-!
Prototype: deep-embedded grammar (data) + generic interpreter. Tests whether
grammar-as-data (built once, no per-node parser reconstruction) beats lean4-parser
on the recursive sexp grammar. TOTAL: the interpreter is structural recursion on a
fuel bound (= input size). Standalone prototype, not wired into the library yet.
-/

set_option linter.unusedVariables false

inductive Gram where
  | atom                 -- one or more alphanumerics -> counts 1
  | lit (c : Char)       -- match a single char -> counts 0
  | ws                   -- skip zero+ whitespace -> counts 0
  | recur                -- recurse into the top grammar
  | seq (a b : Gram)     -- a then b, sum the counts
  | alt (a b : Gram)     -- a, or b if a fails without a match
  | star (a : Gram)      -- a repeated zero+ times, sum the counts
  deriving Inhabited

@[inline] def isAlnum (c : Char) : Bool := c.isAlphanum

-- advance past chars satisfying `pred`; total by structural recursion on fuel
def scanPred (arr : Array Char) (pred : Char → Bool) : Nat → Nat → Nat
  | 0, o => o
  | fuel+1, o => if o < arr.size && pred arr[o]! then scanPred arr pred fuel (o+1) else o

-- returns (count, newOffset) on success, none on failure.
-- TOTAL: structural recursion on `fuel`; the top call passes `fuel = arr.size`,
-- a safe bound since every recursive step (`recur`, `star` iteration) consumes ≥1 char.
def Gram.run (arr : Array Char) (top : Gram) : Nat → Gram → Nat → Option (Nat × Nat)
  | 0, _, _ => none
  | fuel+1, g, off => match g with
    | .atom =>
      if off < arr.size && isAlnum arr[off]! then some (1, scanPred arr isAlnum arr.size (off+1))
      else none
    | .lit c => if off < arr.size && arr[off]! == c then some (0, off+1) else none
    | .ws => some (0, scanPred arr (·.isWhitespace) arr.size off)
    | .recur => Gram.run arr top fuel top off
    | .seq a b =>
      match Gram.run arr top fuel a off with
      | some (c1, o1) => match Gram.run arr top fuel b o1 with
        | some (c2, o2) => some (c1 + c2, o2)
        | none => none
      | none => none
    | .alt a b =>
      match Gram.run arr top fuel a off with
      | some r => some r
      | none => Gram.run arr top fuel b off
    | .star a =>
      match Gram.run arr top fuel a off with
      | some (c, o') =>
        if o' > off then match Gram.run arr top fuel (.star a) o' with
          | some (c2, o2) => some (c + c2, o2)
          | none => some (c, o')
        else some (c, o')
      | none => some (0, off)

open Gram in
-- sexp = atom | '(' ws self (ws self)* ')' ws     (matches primSexp / genSexp)
def sexpGram : Gram :=
  alt atom
    (seq (lit '(') (seq ws (seq recur (seq (star (seq ws recur)) (seq ws (lit ')'))))))

@[noinline] def countSexp (s : String) : Nat :=
  let arr := s.foldl (fun a c => a.push c) #[]
  match Gram.run arr sexpGram arr.size sexpGram 0 with
  | some (c, _) => c
  | none => 0

def main : IO Unit := do
  let ss ← prep "sexp" (genSexp 3 8)
  IO.println s!"checksum: {countSexp ss} (expect 6561)"
  let ref ← IO.mkRef ss
  let reps := 3000
  let t0 ← IO.monoNanosNow
  let mut a : Nat := 0
  for _ in [0:reps] do
    let s ← ref.get
    a := a + countSexp s
  let t1 ← IO.monoNanosNow
  IO.println s!"deep-embedded sexp (vs lp 2.23): {(Float.ofNat (t1-t0))/1000000.0/(Float.ofNat reps)} ms/iter (acc {a})"

#print axioms Gram.run
