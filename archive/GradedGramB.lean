import PrimParser
import BenchGen
open Parser

/-!
Byte-backed graded deep-embedded parser. Identical to `GradedGram` (grade-indexed
GADT, total fuel interpreter) but interprets over `ByteArray` (UInt8) instead of
`Array Char`. Lean stores `String` as UTF-8 internally, so `s.toUTF8` exposes the
bytes with no per-character decode — the same representation angstrom uses.
-/

set_option linter.unusedVariables false

@[inline] def bBetween (lo hi b : UInt8) : Bool := Nat.ble lo.toNat b.toNat && Nat.ble b.toNat hi.toNat
@[inline] def bDigit (b : UInt8) : Bool := bBetween 48 57 b
@[inline] def bAlnum (b : UInt8) : Bool := bDigit b || bBetween 65 90 b || bBetween 97 122 b
@[inline] def bWs (b : UInt8) : Bool := b == 32 || b == 10 || b == 9 || b == 13
-- number chars: digit . - + e E
@[inline] def bNumCh (b : UInt8) : Bool := bDigit b || b == 46 || b == 45 || b == 43 || b == 101 || b == 69
@[inline] def ch (c : Char) : UInt8 := UInt8.ofNat c.toNat

inductive GramB (ρ : Type) : Grade → Type → Type 1 where
  | pure {α} (a : α) : GramB ρ Grade.pure α
  | chars1 (f : UInt8 → Bool) : GramB ρ conditional PUnit
  | chars0 (f : UInt8 → Bool) : GramB ρ flexible PUnit
  | lit (c : UInt8) : GramB ρ conditional PUnit
  | map {g α β} (f : α → β) (a : GramB ρ g α) : GramB ρ g β
  | map2 {g g' α β γ} (f : α → β → γ) (a : GramB ρ g α) (b : GramB ρ g' β) : GramB ρ (g * g') γ
  | seqR {g g' α β} (a : GramB ρ g α) (b : GramB ρ g' β) : GramB ρ (g * g') β
  | seqL {g g' α β} (a : GramB ρ g α) (b : GramB ρ g' β) : GramB ρ (g * g') α
  | alt {g g' α} (a : GramB ρ g α) (b : GramB ρ g' α) : GramB ρ (g.choice g') α
  | star {ge α} (a : GramB ρ ⟨ge, always⟩ α) : GramB ρ flexible (List α)
  | recur : GramB ρ conditional ρ
  | natP : GramB ρ conditional Nat
  | jstr : GramB ρ conditional PUnit    -- JSON string "..." (no escapes; canada.json has none)
  | jnum : GramB ρ conditional PUnit    -- JSON number -?digits(.digits)?([eE][+-]?digits)?
  -- graded monadic bind: the continuation `k` is a closure, so this node is NOT
  -- pure data — it makes `GramB` a genuine graded monad (and pays a per-use cost).
  | bind {g g' α β} (m : GramB ρ g α) (k : α → GramB ρ g' β) : GramB ρ (g * g') β
  | takeN (n : Nat) : GramB ρ conditional PUnit   -- consume exactly n bytes (context-sensitive)

@[inline] def scanB (arr : ByteArray) (pred : UInt8 → Bool) : Nat → Nat → Nat
  | 0, o => o
  | fuel+1, o => if o < arr.size && pred (arr.get! o) then scanB arr pred fuel (o+1) else o

def scanNatB (arr : ByteArray) (acc : Nat) : Nat → Nat → Nat × Nat
  | 0, o => (acc, o)
  | fuel+1, o =>
    if o < arr.size && bDigit (arr.get! o) then
      scanNatB arr (acc * 10 + ((arr.get! o).toNat - 48)) fuel (o+1)
    else (acc, o)

def GramB.run (arr : ByteArray) {ρ} (top : GramB ρ conditional ρ)
    : Nat → {g : Grade} → {α : Type} → GramB ρ g α → Nat → Option (α × Nat)
  | 0, _, _, _, _ => none
  | fuel+1, g, α, gram, off => match gram with
    | .pure a => some (a, off)
    | .chars1 f =>
      if off < arr.size && f (arr.get! off) then some ((), scanB arr f arr.size (off+1)) else none
    | .chars0 f => some ((), scanB arr f arr.size off)
    | .lit c => if off < arr.size && arr.get! off == c then some ((), off+1) else none
    | .map f a => (GramB.run arr top fuel a off).map (fun (x, o) => (f x, o))
    | .map2 f a b => match GramB.run arr top fuel a off with
      | some (x, o1) => (GramB.run arr top fuel b o1).map (fun (y, o2) => (f x y, o2))
      | none => none
    | .seqR a b => match GramB.run arr top fuel a off with
      | some (_, o1) => GramB.run arr top fuel b o1
      | none => none
    | .seqL a b => match GramB.run arr top fuel a off with
      | some (x, o1) => (GramB.run arr top fuel b o1).map (fun (_, o2) => (x, o2))
      | none => none
    | .alt a b => match GramB.run arr top fuel a off with
      | some r => some r
      | none => GramB.run arr top fuel b off
    | .star a => match GramB.run arr top fuel a off with
      | some (x, o') =>
        if o' > off then match GramB.run arr top fuel (.star a) o' with
          | some (xs, o2) => some (x :: xs, o2)
          | none => some ([x], o')
        else some ([x], o')
      | none => some ([], off)
    | .recur => GramB.run arr top fuel top off
    | .natP => if off < arr.size && bDigit (arr.get! off) then some (scanNatB arr 0 arr.size off) else none
    | .jstr =>
      if off < arr.size && arr.get! off == 34 then         -- 34 = '"'
        let e := scanB arr (fun b => b != 34) arr.size (off+1)
        if e < arr.size then some ((), e+1) else none        -- consume closing quote
      else none
    | .jnum =>
      if off < arr.size && (bDigit (arr.get! off) || arr.get! off == 45) then
        some ((), scanB arr bNumCh arr.size off)
      else none
    | .bind m k => match GramB.run arr top fuel m off with
      | some (x, o1) => GramB.run arr top fuel (k x) o1
      | none => none
    | .takeN n => if Nat.ble (off + n) arr.size then some ((), off + n) else none

@[inline] def wsB : GramB Nat flexible PUnit := .chars0 bWs

def intsG : GramB Nat conditional Nat :=
  .map2 (fun x xs => x + xs.foldl (· + ·) 0) .natP (.star (.seqR (.lit (ch ',')) .natP))
def sexpG : GramB Nat conditional Nat :=
  .alt (.map (fun _ => 1) (.chars1 bAlnum))
    (.map2 (fun first rest => first + rest.foldl (· + ·) 0)
      (.seqR (.lit (ch '(')) (.seqR wsB .recur))
      (.seqL (.star (.seqR wsB .recur)) (.seqR wsB (.lit (ch ')')))))
def rowG : GramB Nat conditional Nat :=
  .map2 (fun _ xs => 1 + xs.length) .natP (.star (.seqR (.lit (ch ',')) .natP))
def csvG : GramB Nat conditional Nat :=
  .map2 (fun r rs => r + rs.foldl (· + ·) 0) rowG (.star (.seqR (.lit (ch '\n')) rowG))
def jsonG : GramB Nat conditional Nat :=
  .map (fun _ => 1)
    (.seqR (.seqR (.lit (ch '[')) wsB)
      (.seqL (.map2 (fun _ _ => 0) .natP (.star (.seqR (.seqR (.lit (ch ',')) wsB) .natP)))
             (.seqR wsB (.lit (ch ']')))))
def lamG : GramB Nat conditional Nat :=
  .alt (.map (fun _ => 1) (.seqL (.chars1 bAlnum) wsB))
    (.map (fun n => n + 1)
      (.seqR (.lit (ch '\\')) (.seqR wsB (.seqR (.chars1 bAlnum)
        (.seqR wsB (.seqR (.lit (ch '.')) (.seqR wsB .recur)))))))
def wordsG : GramB Nat conditional Nat :=
  .map2 (fun _ ws => 1 + ws.length) (.chars1 bAlnum) (.star (.seqR (.lit (ch ' ')) (.chars1 bAlnum)))
def bracketsG : GramB Nat conditional Nat :=
  .alt (.map (fun _ => 0) .natP)
       (.map (fun d => d + 1) (.seqR (.lit (ch '[')) (.seqL .recur (.lit (ch ']')))))

-- netstring: `LEN:DATA,` — LEN determines how many bytes DATA has. NEEDS bind
-- (the grammar for DATA depends on the parsed value LEN). Counts netstrings.
def netOne : GramB Nat conditional Nat :=
  .bind .natP (fun n => .seqR (.lit (ch ':')) (.seqR (.takeN n) (.map (fun _ => 1) (.lit (ch ',')))))
def netG : GramB Nat conditional Nat :=
  .map2 (fun x xs => x + xs.foldl (· + ·) 0) netOne (.star netOne)
def genNet (n : Nat) : String := String.join (List.replicate n "5:hello,")

-- Full RFC-8259 JSON: value = ws (number | string | keyword | array | object).
-- Returns the node count (every value counts 1). `recur` = the value itself.
def jsonV : GramB Nat conditional Nat :=
  let v : GramB Nat conditional Nat := .recur
  let arr' : GramB Nat conditional Nat :=
    .map (fun xs => 1 + xs.foldl (· + ·) 0)
      (.seqR (.lit (ch '['))
        (.seqL (.alt (.map2 (fun x xs => x :: xs) v (.star (.seqR (.lit (ch ',')) v)))
                     (.pure ([] : List Nat)))
               (.seqR wsB (.lit (ch ']')))))
  let pair' : GramB Nat conditional Nat :=
    .seqR wsB (.seqR .jstr (.seqR wsB (.seqR (.lit (ch ':')) v)))
  let obj' : GramB Nat conditional Nat :=
    .map (fun xs => 1 + xs.foldl (· + ·) 0)
      (.seqR (.lit (ch '{'))
        (.seqL (.alt (.map2 (fun x xs => x :: xs) pair' (.star (.seqR (.lit (ch ',')) pair')))
                     (.pure ([] : List Nat)))
               (.seqR wsB (.lit (ch '}')))))
  .seqR wsB
    (.alt (.map (fun _ => 1) .jnum)
      (.alt (.map (fun _ => 1) .jstr)
        (.alt (.map (fun _ => 1) (.chars1 bAlnum))
          (.alt arr' obj'))))

@[noinline] def runG (top : GramB Nat conditional Nat) (s : String) : Nat :=
  let arr := s.toUTF8
  match GramB.run arr top (arr.size * 64 + 64) top 0 with
  | some (c, _) => c
  | none => 0

def benchG (label : String) (input : String) (top : GramB Nat conditional Nat) : IO Unit := do
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
  let wordsIn  ← prep "words"    (String.intercalate " " (List.replicate 30000 "abc"))
  let brIn     ← prep "brackets" (String.join (List.replicate 5000 "[") ++ "0" ++ String.join (List.replicate 5000 "]"))
  IO.println "byte-backed graded deep-embedded (total, grades enforced):"
  benchG "integers" intsIn   intsG
  benchG "sexp    " sexpIn   sexpG
  benchG "csv     " csvIn    csvG
  benchG "json    " jsonIn   jsonG
  benchG "lambda  " lambdaIn lamG
  benchG "words   " wordsIn  wordsG
  benchG "brackets" brIn     bracketsG
  let netIn ← prep "net" (genNet 40000)
  benchG "netstr(bind)" netIn netG
  -- industrial: real 2.3MB canada.json (float-heavy GeoJSON, nativejson-benchmark)
  let canada ← IO.FS.readFile "bench-data/canada.json"
  IO.println s!"canada.json: {canada.length} bytes, node count = {runG jsonV canada}"
  let ref ← IO.mkRef canada
  let mut best : Float := 1.0e9
  for _ in [0:30] do
    let s ← ref.get
    let t0 ← IO.monoNanosNow
    let _ ← IO.lazyPure (fun _ => runG jsonV s)
    let t1 ← IO.monoNanosNow
    let dt := (Float.ofNat (t1-t0))/1000000.0
    if dt < best then best := dt
  IO.println s!"  canada.json (real JSON): {best} ms/iter"

#print axioms GramB.run
