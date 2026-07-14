/-! Prototype: a compiled, allocation-free byte-level JSON node-counter. Same node
count as `gJson` (scalars = 1, container = 1 + child values), over a raw `ByteArray`.
Results are packed into a single `UInt64` (position in the high bits, count in the
low 20, a fail bit at the top) so the hot path allocates nothing — the flatparse
technique. This is what a *compiled* byte-combinator backend would inline to. -/

namespace JHand

@[inline] def isWs (b : UInt8) : Bool := b == 32 || b == 10 || b == 9 || b == 13
@[inline] def isDigit (b : UInt8) : Bool := 48 ≤ b && b ≤ 57
@[inline] def isNumCh (b : UInt8) : Bool :=
  isDigit b || b == 46 || b == 45 || b == 43 || b == 101 || b == 69
@[inline] def isAlpha (b : UInt8) : Bool := (97 ≤ b && b ≤ 122) || (65 ≤ b && b ≤ 90)

-- Packed result: fail bit (63) | position (bits 20..) | count (bits 0..19).
@[inline] def FAIL : UInt64 := (1 : UInt64) <<< (63 : UInt64)
@[inline] def pk (pos cnt : Nat) : UInt64 := (pos.toUInt64 <<< (20 : UInt64)) ||| cnt.toUInt64
@[inline] def rpos (r : UInt64) : Nat := (r >>> (20 : UInt64)).toNat
@[inline] def rcnt (r : UInt64) : Nat := (r &&& (0xFFFFF : UInt64)).toNat
@[inline] def bad (r : UInt64) : Bool := (r &&& FAIL) != 0

@[inline] partial def scanWhile (arr : ByteArray) (p : UInt8 → Bool) (pos : Nat) : Nat :=
  if h : pos < arr.size then (if p arr[pos] then scanWhile arr p (pos + 1) else pos) else pos

mutual
partial def pValue (arr : ByteArray) (pos0 : Nat) : UInt64 :=
  let pos := scanWhile arr isWs pos0
  if h : pos < arr.size then
    let b := arr[pos]
    if isNumCh b then pk (scanWhile arr isNumCh (pos + 1)) 1
    else if b == 34 then
      let p := scanWhile arr (· != 34) (pos + 1)
      if p < arr.size then pk (p + 1) 1 else FAIL
    else if b == 91 then pArray arr (pos + 1)
    else if b == 123 then pObject arr (pos + 1)
    else if isAlpha b then pk (scanWhile arr isAlpha (pos + 1)) 1
    else FAIL
  else FAIL

partial def pArray (arr : ByteArray) (pos : Nat) : UInt64 :=
  let r := pValue arr pos
  if bad r then
    let p := scanWhile arr isWs pos
    if h : p < arr.size then (if arr[p] == 93 then pk (p + 1) 1 else FAIL) else FAIL
  else pArrayRest arr (rpos r) (1 + rcnt r)

partial def pArrayRest (arr : ByteArray) (pos : Nat) (acc : Nat) : UInt64 :=
  let p := scanWhile arr isWs pos
  if h : p < arr.size then
    let b := arr[p]
    if b == 44 then
      let r := pValue arr (p + 1)
      if bad r then FAIL else pArrayRest arr (rpos r) (acc + rcnt r)
    else if b == 93 then pk (p + 1) acc
    else FAIL
  else FAIL

partial def pObject (arr : ByteArray) (pos : Nat) : UInt64 :=
  let r := pMember arr pos
  if bad r then
    let p := scanWhile arr isWs pos
    if h : p < arr.size then (if arr[p] == 125 then pk (p + 1) 1 else FAIL) else FAIL
  else pObjectRest arr (rpos r) (1 + rcnt r)

partial def pObjectRest (arr : ByteArray) (pos : Nat) (acc : Nat) : UInt64 :=
  let p := scanWhile arr isWs pos
  if h : p < arr.size then
    let b := arr[p]
    if b == 44 then
      let r := pMember arr (p + 1)
      if bad r then FAIL else pObjectRest arr (rpos r) (acc + rcnt r)
    else if b == 125 then pk (p + 1) acc
    else FAIL
  else FAIL

partial def pMember (arr : ByteArray) (pos : Nat) : UInt64 :=
  let p := scanWhile arr isWs pos
  if h : p < arr.size then
    if arr[p] == 34 then
      let q := scanWhile arr (· != 34) (p + 1)
      if q < arr.size then
        let r := scanWhile arr isWs (q + 1)
        if hr : r < arr.size then
          if arr[r] == 58 then pValue arr (r + 1) else FAIL
        else FAIL
      else FAIL
    else FAIL
  else FAIL
end

def run (arr : ByteArray) : Nat :=
  let r := pValue arr 0
  if bad r then 0 else rcnt r

@[noinline] def barrier (_k : Nat) (b : ByteArray) : ByteArray := b

end JHand

def main (args : List String) : IO Unit := do
  let bytes ← IO.FS.readBinFile "bench-data/canada.json"
  if args.contains "time" then
    let mut best : Nat := 1 <<< 62
    for i in [0:100] do
      let t0 ← IO.monoNanosNow
      let n := JHand.run (JHand.barrier i bytes)
      if n != 167179 then IO.eprintln "err"
      let t1 ← IO.monoNanosNow
      best := min best (t1 - t0)
    IO.println s!"count={JHand.run bytes} parse_ms={(Float.ofNat best)/1e6}"
  else
    IO.println (JHand.run bytes)
