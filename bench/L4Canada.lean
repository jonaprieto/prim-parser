import Parser
open Parser Char

/-! canada.json node-count with lean4-parser (fgdorais/Parser), a Char-based
combinator library over `String.Slice`. Same node count (167179) as the other
baselines. -/

namespace L4
abbrev P := SimpleParser String.Slice Char

@[inline] def isNum (c : Char) : Bool :=
  c.isDigit || c == '-' || c == '+' || c == '.' || c == 'e' || c == 'E'

def ws : P Unit := dropMany (tokenFilter fun c => c == ' ' || c == '\n' || c == '\r' || c == '\t')
def numP : P Nat := do dropMany1 (tokenFilter isNum); pure 1
def strP : P Nat := do let _ ← char '"'; dropMany (tokenFilter (· != '"')); let _ ← char '"'; pure 1
def kwP  : P Nat := do dropMany1 (tokenFilter (·.isAlpha)); pure 1

mutual
partial def valP : P Nat := do
  ws
  let c ← peek
  if c == '[' then do
    let _ ← char '['
    let xs ← sepBy (char ',') valP
    ws; let _ ← char ']'
    return 1 + xs.foldl (· + ·) 0
  else if c == '{' then do
    let _ ← char '{'
    let xs ← sepBy (char ',') pairP
    ws; let _ ← char '}'
    return 1 + xs.foldl (· + ·) 0
  else if c == '"' then strP
  else if c.isAlpha then kwP
  else numP

partial def pairP : P Nat := do
  ws; let _ ← char '"'; dropMany (tokenFilter (· != '"')); let _ ← char '"'
  ws; let _ ← char ':'; valP
end

def run (s : String) : Nat :=
  match Parser.run (ws *> valP) s.toSlice with
  | .ok _ n => n
  | .error _ _ => 0
end L4

@[noinline] def barrier (_k : Nat) (s : String) : String := s

def main (args : List String) : IO Unit := do
  let s ← IO.FS.readFile "bench-data/canada.json"
  if args.contains "time" then
    let mut best : Nat := 1 <<< 62
    for i in [0:100] do
      let t0 ← IO.monoNanosNow
      let n := L4.run (barrier i s)
      if n != 167179 then IO.eprintln s!"err {n}"
      let t1 ← IO.monoNanosNow
      best := min best (t1 - t0)
    IO.println s!"count={L4.run s} parse_ms={(Float.ofNat best)/1e6}"
  else
    IO.println (L4.run s)
