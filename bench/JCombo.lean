/-! Viability experiment for a compiled byte-combinator backend: the SAME packed
`UInt64` result as `jhand`, but expressed through a combinator abstraction
(`@[inline]` functions `ByteArray → Nat → UInt64`). If Lean fuses the combinators
into the grammar we keep jhand's speed; if the abstraction reintroduces overhead,
we learn the ceiling. Same JSON node count (167179) as every other baseline. -/

namespace JCombo

@[inline] def isWs (b : UInt8) : Bool := b == 32 || b == 10 || b == 9 || b == 13
@[inline] def isDigit (b : UInt8) : Bool := 48 ≤ b && b ≤ 57
@[inline] def isNumCh (b : UInt8) : Bool :=
  isDigit b || b == 46 || b == 45 || b == 43 || b == 101 || b == 69
@[inline] def isAlpha (b : UInt8) : Bool := (97 ≤ b && b ≤ 122) || (65 ≤ b && b ≤ 90)

@[inline] def FAIL : UInt64 := (1 : UInt64) <<< (63 : UInt64)
@[inline] def pk (pos cnt : Nat) : UInt64 := (pos.toUInt64 <<< (20 : UInt64)) ||| cnt.toUInt64
@[inline] def rpos (r : UInt64) : Nat := (r >>> (20 : UInt64)).toNat
@[inline] def rcnt (r : UInt64) : Nat := (r &&& (0xFFFFF : UInt64)).toNat
@[inline] def bad (r : UInt64) : Bool := (r &&& FAIL) != 0

/-- A byte parser producing a node-count: buffer + position → packed result. -/
abbrev BP := ByteArray → Nat → UInt64

@[inline] partial def scanWhile (arr : ByteArray) (p : UInt8 → Bool) (pos : Nat) : Nat :=
  if h : pos < arr.size then (if p arr[pos] then scanWhile arr p (pos + 1) else pos) else pos

-- combinators
@[inline] def bWs : BP := fun a p => pk (scanWhile a isWs p) 0
/-- skip leading ws, then run `p`. -/
@[inline] def lexed (p : BP) : BP := fun a pos => p a (scanWhile a isWs pos)
/-- expect literal byte `c`. -/
@[inline] def blit (c : UInt8) : BP := fun a p =>
  if h : p < a.size then (if a[p] == c then pk (p + 1) 0 else FAIL) else FAIL
/-- ordered choice keyed by the current byte's class isn't expressible generically;
`balt p q` tries `p`, then `q` at the same position. -/
@[inline] def balt (p q : BP) : BP := fun a pos =>
  let r := p a pos; if bad r then q a pos else r
/-- `p` then `q` sequential, summing counts. -/
@[inline] def bseq (p q : BP) : BP := fun a pos =>
  let r := p a pos; if bad r then FAIL else
    let s := q a (rpos r); if bad s then FAIL else pk (rpos s) (rcnt r + rcnt s)

/-- scan a scalar token (number / keyword / string body) → count 1. -/
@[inline] def bnum : BP := fun a p => pk (scanWhile a isNumCh p) 1
@[inline] def bkw  : BP := fun a p => pk (scanWhile a isAlpha p) 1
@[inline] def bstr : BP := fun a p =>
  if h : p < a.size then
    if a[p] == 34 then
      let q := scanWhile a (· != 34) (p + 1)
      if q < a.size then pk (q + 1) 1 else FAIL
    else FAIL
  else FAIL

/-- zero-or-more `elem` separated by byte `sep`, folding counts; then `close`. -/
@[inline] partial def bsepFoldClose (elem : BP) (sep close : UInt8) : ByteArray → Nat → Nat → UInt64 :=
  fun a pos acc =>
    let p := scanWhile a isWs pos
    if h : p < a.size then
      let b := a[p]
      if b == sep then
        let r := elem a (p + 1)
        if bad r then FAIL else bsepFoldClose elem sep close a (rpos r) (acc + rcnt r)
      else if b == close then pk (p + 1) acc
      else FAIL
    else FAIL

end JCombo

namespace JCombo
mutual
partial def pValue : BP := fun a pos0 =>
  let pos := scanWhile a isWs pos0
  if h : pos < a.size then
    let b := a[pos]
    if isNumCh b then bnum a pos
    else if b == 34 then bstr a pos
    else if b == 91 then pArr a (pos + 1)
    else if b == 123 then pObj a (pos + 1)
    else if isAlpha b then bkw a pos
    else FAIL
  else FAIL

partial def pArr : BP := fun a pos =>
  let r := pValue a pos
  if bad r then (blit 93 |> lexed) a pos |> fun c => if bad c then FAIL else pk (rpos c) 1
  else match bsepFoldClose pValue 44 93 a (rpos r) (1 + rcnt r) with
    | s => s

partial def pObj : BP := fun a pos =>
  let r := pMember a pos
  if bad r then (blit 125 |> lexed) a pos |> fun c => if bad c then FAIL else pk (rpos c) 1
  else bsepFoldClose pMember 44 125 a (rpos r) (1 + rcnt r)

partial def pMember : BP := fun a pos =>
  let p := scanWhile a isWs pos
  if h : p < a.size then
    if a[p] == 34 then
      let q := scanWhile a (· != 34) (p + 1)
      if q < a.size then
        let r := scanWhile a isWs (q + 1)
        if hr : r < a.size then
          if a[r] == 58 then pValue a (r + 1) else FAIL
        else FAIL
      else FAIL
    else FAIL
  else FAIL
end

def run (arr : ByteArray) : Nat := let r := pValue arr 0; if bad r then 0 else rcnt r
@[noinline] def barrier (_k : Nat) (b : ByteArray) : ByteArray := b
end JCombo

def main (args : List String) : IO Unit := do
  let bytes ← IO.FS.readBinFile "bench-data/canada.json"
  if args.contains "time" then
    let mut best : Nat := 1 <<< 62
    for i in [0:100] do
      let t0 ← IO.monoNanosNow
      let n := JCombo.run (JCombo.barrier i bytes)
      if n != 167179 then IO.eprintln "err"
      let t1 ← IO.monoNanosNow
      best := min best (t1 - t0)
    IO.println s!"count={JCombo.run bytes} parse_ms={(Float.ofNat best)/1e6}"
  else
    IO.println (JCombo.run bytes)
