/-! Lean byte-level recognizers for flatparse's `sexp` and `numeral-csv` benchmarks
(pure recognition, return Bool, no AST — matching flatparse's `Parser () ()`), on
the exact flatparse inputs. Position-threaded with a fail sentinel: allocation-free.
Grammars (from flatparse bench/FPBasic.hs):
  ws     = (' '|'\n')*
  sexp   = '(' ws sexp+ ')' ws | [A-Za-z]+ ws ;   src = sexp eof
  numcsv = [0-9]+ ws (',' ws [0-9]+ ws)* eof
-/

namespace FP

def SENT : Nat := 1 <<< 60
@[inline] def isWsC (b : UInt8) : Bool := b == 32 || b == 10
@[inline] def isAlphaC (b : UInt8) : Bool := (65 ≤ b && b ≤ 90) || (97 ≤ b && b ≤ 122)
@[inline] def isDig (b : UInt8) : Bool := 48 ≤ b && b ≤ 57

@[inline] partial def skipW (arr : ByteArray) (pred : UInt8 → Bool) (p : Nat) : Nat :=
  if h : p < arr.size then (if pred arr[p] then skipW arr pred (p + 1) else p) else p

mutual
partial def sexp (arr : ByteArray) (p : Nat) : Nat :=
  if h : p < arr.size then
    let b := arr[p]
    if b == 40 then                                   -- '('
      let p1 := skipW arr isWsC (p + 1)
      let q := sexp arr p1                             -- skipSome: first child (required)
      if q == SENT then SENT else
      let q2 := sexpMany arr q                         -- skipMany more children
      if h2 : q2 < arr.size then
        (if arr[q2] == 41 then skipW arr isWsC (q2 + 1) else SENT)  -- ')'
      else SENT
    else                                              -- ident = [A-Za-z]+ ws
      let e := skipW arr isAlphaC p
      if e == p then SENT else skipW arr isWsC e
  else SENT

partial def sexpMany (arr : ByteArray) (p : Nat) : Nat :=
  let q := sexp arr p
  if q == SENT then p else sexpMany arr q
end

def runSexp (arr : ByteArray) : Bool :=
  let q := sexp arr 0
  q != SENT && q == arr.size

partial def numcsvLoop (arr : ByteArray) (p : Nat) : Nat :=
  if h : p < arr.size then
    if arr[p] == 44 then                              -- ','
      let p := skipW arr isWsC (p + 1)
      let d := skipW arr isDig p
      if d == p then SENT else numcsvLoop arr (skipW arr isWsC d)
    else p
  else p

def runNumcsv (arr : ByteArray) : Bool :=
  let p := skipW arr isDig 0
  if p == 0 then false else
  let p := skipW arr isWsC p
  let q := numcsvLoop arr p
  q != SENT && q == arr.size

@[noinline] def barrier (_k : Nat) (b : ByteArray) : ByteArray := b
end FP

def timeIt (f : ByteArray → Bool) (bytes : ByteArray) : IO Unit := do
  let mut best : Nat := 1 <<< 62
  for i in [0:100] do
    let t0 ← IO.monoNanosNow
    let r := f (FP.barrier i bytes)
    if !r then IO.eprintln "err"
    let t1 ← IO.monoNanosNow
    best := min best (t1 - t0)
  IO.println s!"ok={f bytes} parse_ms={(Float.ofNat best)/1e6}"

def main (args : List String) : IO Unit := do
  let which := args.getD 0 "sexp"
  let (path, f) := if which == "numcsv" then ("bench-data/numcsv.txt", FP.runNumcsv)
                   else ("bench-data/sexp.txt", FP.runSexp)
  let bytes ← IO.FS.readBinFile path
  if args.contains "time" then timeIt f bytes else IO.println (f bytes)
