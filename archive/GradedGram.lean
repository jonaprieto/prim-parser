import PrimParser
import BenchGen
open Parser

/-!
Graded, deep-embedded parser: the graded monad **reified as data**. `Gram` is
indexed by `Grade` exactly like the shallow `Parser`, so the grade discipline is
enforced at construction (an ill-graded grammar does not typecheck — e.g. `star`
demands an always-consuming body). A single total interpreter (`Gram.run`,
structural on a fuel bound = input size) walks the data. `ρ` is the result type of
the one fixpoint; `recur` refers back to it.

Same graded monad, different execution model: data + interpreter instead of
functions + `fix`. No per-node parser reconstruction, no `self`-closure.
-/

set_option linter.unusedVariables false

inductive Gram (ρ : Type) : Grade → Type → Type 1 where
  | pure {α} (a : α) : Gram ρ Grade.pure α
  | chars1 (f : Char → Bool) : Gram ρ conditional PUnit          -- one+ matching chars
  | chars0 (f : Char → Bool) : Gram ρ flexible PUnit             -- zero+ matching chars
  | lit (c : Char) : Gram ρ conditional PUnit                    -- a single char
  | map {g α β} (f : α → β) (a : Gram ρ g α) : Gram ρ g β
  | map2 {g g' α β γ} (f : α → β → γ) (a : Gram ρ g α) (b : Gram ρ g' β) : Gram ρ (g * g') γ
  | seqR {g g' α β} (a : Gram ρ g α) (b : Gram ρ g' β) : Gram ρ (g * g') β
  | seqL {g g' α β} (a : Gram ρ g α) (b : Gram ρ g' β) : Gram ρ (g * g') α
  | alt {g g' α} (a : Gram ρ g α) (b : Gram ρ g' α) : Gram ρ (g.choice g') α
  | star {ge α} (a : Gram ρ ⟨ge, always⟩ α) : Gram ρ flexible (List α)
  | recur : Gram ρ conditional ρ
  | natP : Gram ρ conditional Nat                               -- one+ digits, returns value

@[inline] def scanPred (arr : Array Char) (pred : Char → Bool) : Nat → Nat → Nat
  | 0, o => o
  | fuel+1, o => if o < arr.size && pred arr[o]! then scanPred arr pred fuel (o+1) else o

@[inline] def isDig (c : Char) : Bool := c.isDigit

def scanNat (arr : Array Char) (acc : Nat) : Nat → Nat → Nat × Nat
  | 0, o => (acc, o)
  | fuel+1, o =>
    if o < arr.size && isDig arr[o]! then scanNat arr (acc * 10 + (arr[o]!.toNat - 48)) fuel (o+1)
    else (acc, o)

-- Total interpreter: structural recursion on `fuel`. Returns (value, newOffset).
def Gram.run (arr : Array Char) {ρ} (top : Gram ρ conditional ρ)
    : Nat → {g : Grade} → {α : Type} → Gram ρ g α → Nat → Option (α × Nat)
  | 0, _, _, _, _ => none
  | fuel+1, g, α, gram, off => match gram with
    | .pure a => some (a, off)
    | .chars1 f =>
      if off < arr.size && f arr[off]! then some ((), scanPred arr f arr.size (off+1)) else none
    | .chars0 f => some ((), scanPred arr f arr.size off)
    | .lit c => if off < arr.size && arr[off]! == c then some ((), off+1) else none
    | .map f a => (Gram.run arr top fuel a off).map (fun (x, o) => (f x, o))
    | .map2 f a b => match Gram.run arr top fuel a off with
      | some (x, o1) => (Gram.run arr top fuel b o1).map (fun (y, o2) => (f x y, o2))
      | none => none
    | .seqR a b => match Gram.run arr top fuel a off with
      | some (_, o1) => Gram.run arr top fuel b o1
      | none => none
    | .seqL a b => match Gram.run arr top fuel a off with
      | some (x, o1) => (Gram.run arr top fuel b o1).map (fun (_, o2) => (x, o2))
      | none => none
    | .alt a b => match Gram.run arr top fuel a off with
      | some r => some r
      | none => Gram.run arr top fuel b off
    | .star a => match Gram.run arr top fuel a off with
      | some (x, o') =>
        if o' > off then match Gram.run arr top fuel (.star a) o' with
          | some (xs, o2) => some (x :: xs, o2)
          | none => some ([x], o')
        else some ([x], o')
      | none => some ([], off)
    | .recur => Gram.run arr top fuel top off
    | .natP =>
      if off < arr.size && isDig arr[off]! then some (scanNat arr 0 arr.size off) else none

-- sexp counting grammar, written with the graded combinators. `ρ = Nat`.
def sexpG : Gram Nat conditional Nat :=
  .alt
    (.map (fun _ => 1) (.chars1 Char.isAlphanum))
    (.map2 (fun first rest => first + rest.foldl (· + ·) 0)
      (.seqR (.lit '(') (.seqR (.chars0 Char.isWhitespace) .recur))
      (.seqL (.star (.seqR (.chars0 Char.isWhitespace) .recur))
             (.seqR (.chars0 Char.isWhitespace) (.lit ')'))))

@[inline] def ws : Gram Nat flexible PUnit := .chars0 Char.isWhitespace

-- integers: sum of comma-separated nats
def intsG : Gram Nat conditional Nat :=
  .map2 (fun x xs => x + xs.foldl (· + ·) 0) .natP (.star (.seqR (.lit ',') .natP))

-- csv: total cell count (rows separated by '\n', cells by ',')
def rowG : Gram Nat conditional Nat :=
  .map2 (fun _ xs => 1 + xs.length) .natP (.star (.seqR (.lit ',') .natP))
def csvG : Gram Nat conditional Nat :=
  .map2 (fun r rs => r + rs.foldl (· + ·) 0) rowG (.star (.seqR (.lit '\n') rowG))

-- json: validate a flat `[nat, nat, ...]` array, return 1 (matches lpJson)
def jsonG : Gram Nat conditional Nat :=
  .map (fun _ => 1)
    (.seqR (.seqR (.lit '[') ws)
      (.seqL (.map2 (fun _ _ => 0) .natP (.star (.seqR (.seqR (.lit ',') ws) .natP)))
             (.seqR ws (.lit ']'))))

-- lambda: count nodes in `\v. body | v`
def lamG : Gram Nat conditional Nat :=
  .alt
    (.map (fun _ => 1) (.seqL (.chars1 Char.isAlphanum) ws))
    (.map (fun n => n + 1)
      (.seqR (.lit '\\') (.seqR ws (.seqR (.chars1 Char.isAlphanum)
        (.seqR ws (.seqR (.lit '.') (.seqR ws .recur)))))))

-- words: whitespace-heavy, flat — count space-separated alnum tokens
def wordsG : Gram Nat conditional Nat :=
  .map2 (fun _ ws => 1 + ws.length) (.chars1 Char.isAlphanum)
    (.star (.seqR (.lit ' ') (.chars1 Char.isAlphanum)))

-- brackets: pure deep recursion — `B = nat | '[' B ']'`, returns nesting depth
def bracketsG : Gram Nat conditional Nat :=
  .alt (.map (fun _ => 0) .natP)
       (.map (fun d => d + 1) (.seqR (.lit '[') (.seqL .recur (.lit ']'))))

def genWordsS (n : Nat) : String := String.intercalate " " (List.replicate n "abc")
def genBracketsS (n : Nat) : String :=
  String.join (List.replicate n "[") ++ "0" ++ String.join (List.replicate n "]")

@[noinline] def runG (top : Gram Nat conditional Nat) (s : String) : Nat :=
  let arr := s.foldl (fun a c => a.push c) #[]
  -- fuel bounds total node-visits (<= gramSize * inputSize); surplus is unused, so
  -- a generous multiple keeps it total without affecting runtime.
  match Gram.run arr top (arr.size * 64 + 64) top 0 with
  | some (c, _) => c
  | none => 0

def benchG (label : String) (input : String) (top : Gram Nat conditional Nat) : IO Unit := do
  let ref ← IO.mkRef input
  let reps := 2000
  let t0 ← IO.monoNanosNow
  let mut a : Nat := 0
  for _ in [0:reps] do
    let s ← ref.get
    a := a + runG top s
  let t1 ← IO.monoNanosNow
  IO.println s!"  {label}: {(Float.ofNat (t1-t0))/1000000.0/(Float.ofNat reps)} ms/iter (chk {a / reps})"

def main : IO Unit := do
  let intsIn   ← prep "integers" (genInts 20000)
  let sexpIn   ← prep "sexp"     (genSexp 3 8)
  let csvIn    ← prep "csv"      (genCsv 4000 6)
  let jsonIn   ← prep "json"     (genJson 20000)
  let lambdaIn ← prep "lambda"   (genLambda 2000)
  IO.println "graded deep-embedded (total, grades enforced) vs lean4-parser (4.35 2.23 3.19 4.33 0.65):"
  benchG "integers" intsIn   intsG
  benchG "sexp    " sexpIn   sexpG
  benchG "csv     " csvIn    csvG
  benchG "json    " jsonIn   jsonG
  benchG "lambda  " lambdaIn lamG
  let wordsIn ← prep "words"    (genWordsS 30000)
  let brIn    ← prep "brackets" (genBracketsS 5000)
  benchG "words   " wordsIn wordsG
  benchG "brackets" brIn    bracketsG

#print axioms Gram.run
