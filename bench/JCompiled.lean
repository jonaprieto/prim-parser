import PrimParser.Graded
import PrimParser.GradedCompile
open Graded Byte

/-! Run the *deep* reified JSON grammar via `G.compile` into the fast byte backend.
Same node count (167179). Tests whether a compiled recursive grammar reaches byte
speed, or whether the recursion knot re-interprets (strict Lean can't memoize a
recursive value the way lazy Haskell can). -/

@[inline] def bNumCh (b : UInt8) : Bool := bDigit b || b == 46 || b == 45 || b == 43 || b == 101 || b == 69
@[inline] def notQuote (b : UInt8) : Bool := b != 34

@[inline] def gsepFold {ρ γ β ge ge' α} (f : β → α → β) (acc : β)
    (sep : G ρ ⟨ge', always⟩ γ) (p : G ρ ⟨ge, always⟩ α) :=
  G.alt (G.bind p (fun x => G.starFold f (f acc x) (G.seqR sep p))) (G.pure acc)

def gJson : G Nat conditional Nat :=
  let jnum : G Nat conditional Nat := (fun _ => 1) <$>ᵍ takeWhile1 bNumCh
  let jstr : G Nat conditional Nat := (fun _ => 1) <$>ᵍ (bchar '"' *>ᵍ takeWhile notQuote <*ᵍ bchar '"')
  let jkw  : G Nat conditional Nat := (fun _ => 1) <$>ᵍ takeWhile1 bAlpha
  let jarr : G Nat conditional Nat :=
    (fun n => 1 + n) <$>ᵍ (bchar '[' *>ᵍ gsepFold (· + ·) 0 (bchar ',') grecur <*ᵍ ws <*ᵍ bchar ']')
  let jpair : G Nat conditional Nat :=
    ws *>ᵍ bchar '"' *>ᵍ takeWhile notQuote *>ᵍ bchar '"' *>ᵍ ws *>ᵍ bchar ':' *>ᵍ grecur
  let jobj : G Nat conditional Nat :=
    (fun n => 1 + n) <$>ᵍ (bchar '{' *>ᵍ gsepFold (· + ·) 0 (bchar ',') jpair <*ᵍ ws <*ᵍ bchar '}')
  ws *>ᵍ (jnum <|>ᵍ jarr <|>ᵍ jobj <|>ᵍ jstr <|>ᵍ jkw)

/-- Run-level lazy knot: `recur` re-enters `compileRun`, so no construction loop —
but the grammar is re-compiled at each `recur`, so recursive grammars do NOT get the
memoized speedup (strict Lean can't tie a recursive *value* knot). -/
partial def compileRun (arr : ByteArray) (p : Nat) : Option (Nat × Nat) :=
  (G.compile ⟨compileRun⟩ gJson).run arr p

def crun (bytes : ByteArray) : Nat :=
  match compileRun bytes 0 with | some (n, _) => n | none => 0

@[noinline] def barrier (_k : Nat) (b : ByteArray) : ByteArray := b

def main (args : List String) : IO Unit := do
  let bytes ← IO.FS.readBinFile "bench-data/canada.json"
  if args.contains "time" then
    let mut best : Nat := 1 <<< 62
    for i in [0:100] do
      let t0 ← IO.monoNanosNow
      let n := crun (barrier i bytes)
      if n != 167179 then IO.eprintln s!"err {n}"
      let t1 ← IO.monoNanosNow
      best := min best (t1 - t0)
    IO.println s!"count={crun bytes} parse_ms={(Float.ofNat best)/1e6}"
  else
    IO.println (crun bytes)
