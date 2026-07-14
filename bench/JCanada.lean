import PrimParser.Graded
open Graded

/-! Single-parse binary for hyperfine: parse canada.json once with the graded
framework JSON grammar, print the node count. -/

@[inline] def bNumCh (b : UInt8) : Bool := bDigit b || b == 46 || b == 45 || b == 43 || b == 101 || b == 69
@[inline] def notQuote (b : UInt8) : Bool := b != 34

/-- `p` separated by `sep`, folding the results into `acc` with no intermediate
list (uses the `starFold` node). -/
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
  -- ordered choice tuned to frequency (numbers/arrays/objects dominate); all five
  -- branches remain, so any valid JSON still parses.
  ws *>ᵍ (jnum <|>ᵍ jarr <|>ᵍ jobj <|>ᵍ jstr <|>ᵍ jkw)

-- isolation probe: scan the whole file in ONE takeWhile (pure scanB throughput).
def gAll : G Nat conditional Nat := (fun _ => 1) <$>ᵍ takeWhile1 (fun _ => true)

def main (args : List String) : IO Unit := do
  -- read raw bytes straight into the byte parser (no String decode/re-encode),
  -- matching attoparsec/nom's raw ByteString/&[u8] input.
  let bytes ← IO.FS.readBinFile "bench-data/canada.json"
  if args.contains "scan" then
    let mut best : Nat := 1 <<< 62
    for _ in [0:100] do
      let t0 ← IO.monoNanosNow
      let n := (Graded.run gAll gAll bytes).getD 0
      let t1 ← IO.monoNanosNow
      if n == 0 then IO.eprintln "err"
      best := min best (t1 - t0)
    IO.println s!"scan_ms={(Float.ofNat best)/1e6}"
  else if args.contains "time" then
    -- in-process parse-only timing (best of 100), no process-startup/IO confound
    let mut best : Nat := 1 <<< 62
    for _ in [0:100] do
      let t0 ← IO.monoNanosNow
      let n := (Graded.run gJson gJson bytes).getD 0
      let t1 ← IO.monoNanosNow
      if n == 0 then IO.eprintln "err"
      best := min best (t1 - t0)
    IO.println s!"count={(Graded.run gJson gJson bytes).getD 0} parse_ms={(Float.ofNat best)/1e6}"
  else
    IO.println ((Graded.run gJson gJson bytes).getD 0)
