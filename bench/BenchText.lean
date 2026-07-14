import PrimParser
import BenchGen

/-!
Microbenchmark backing the `Text` design choice (Array+offset vs List).

`Text` stores input as a shared `Array Char` plus an offset. This measures the two
things that choice trades on, on the parser's hot path (walk every char once):

  1. construction   -- decode a `String` into Array (single pass) vs into a List
  2. traversal      -- fold over the whole input, Array vs List
  3. why the offset -- Array + per-step `drop` (copies the tail) is O(n^2);
                       the offset makes the same walk O(n). Strawman, small input.

Sequential scan is the tokenizer/`takeWhile` pattern; random peek-ahead (where a
contiguous Array wins even harder over a linked List) is not exercised here.

Run: `lake exe benchtext`.
-/

/-- Walk an `Array` once (contiguous, O(1) sequential index). The `Text` design. -/
@[noinline] def scanArr (arr : Array Char) : Nat := arr.foldl (fun a c => a + c.toNat) 0

/-- Walk a `List` once (linked, heap-chase per element). The alternative. -/
@[noinline] def scanList (l : List Char) : Nat := l.foldl (fun a c => a + c.toNat) 0

/-- Naive Array-without-offset: consume one char by copying the tail. O(n^2). -/
@[noinline] partial def scanArrDrop (arr : Array Char) : Nat :=
  if arr.size = 0 then 0 else arr[0]!.toNat + scanArrDrop (arr.drop 1)

/-- Peek `k` chars ahead at every position, advancing by one. Array indexes the
lookahead directly: O(1) per peek, O(n) total, independent of `k`. -/
@[noinline] def peekArr (arr : Array Char) (k : Nat) : Nat := Id.run do
  let mut acc := 0
  let n := arr.size
  for i in [0:n] do
    let j := i + k
    if j < n then acc := acc + arr[j]!.toNat
  acc

/-- Same peek, List cursor. Advancing is O(1) (`rest`), but each `k`-ahead peek
walks `k` nodes (`drop k`): O(k) per position, O(n*k) total. -/
@[noinline] partial def peekList (l : List Char) (k : Nat) (acc : Nat) : Nat :=
  match l with
  | [] => acc
  | _ :: rest =>
    let c := (l.drop k).head?.map Char.toNat |>.getD 0
    peekList rest k (acc + c)

def main : IO Unit := do
  let reps := 25
  -- Big input for the real question (Array+offset vs List).
  let src  ← prep "text-big"   (genInts 20000)
  -- Small input for the quadratic strawman, so it finishes.
  let smSrc ← prep "text-small" (genInts 3000)

  let arr   := decodeArr src        -- single-pass Array (what `ofString` builds)
  let lst   := src.toList           -- List alternative
  let smArr := decodeArr smSrc

  IO.println "Text backing: Array+offset vs List"
  let rows := #[
    -- construction: build the structure from a String
    ← benchOne "build Array"        src   reps (fun _ => (decodeArr src).size),
    ← benchOne "build List"         src   reps (fun _ => src.toList.length),
    -- traversal: walk the whole input once (decoded once, outside the loop)
    ← benchOne "walk Array"         src   reps (fun _ => scanArr arr),
    ← benchOne "walk List"          src   reps (fun _ => scanList lst),
    -- why the offset: same walk, Array+drop (O(n^2)) vs Array+offset, small input
    ← benchOne "walk Array+drop sm" smSrc reps (fun _ => scanArrDrop smArr),
    ← benchOne "walk Array sm"      smSrc reps (fun _ => scanArr smArr),
    -- peek-ahead: read k chars ahead at every position. Array O(1)/peek, List O(k).
    ← benchOne "peek Array k=1"     src   reps (fun _ => peekArr arr 1),
    ← benchOne "peek List  k=1"     src   reps (fun _ => peekList lst 1 0),
    ← benchOne "peek Array k=8"     src   reps (fun _ => peekArr arr 8),
    ← benchOne "peek List  k=8"     src   reps (fun _ => peekList lst 8 0),
    ← benchOne "peek Array k=64"    src   reps (fun _ => peekArr arr 64),
    ← benchOne "peek List  k=64"    src   reps (fun _ => peekList lst 64 0)]
  writeTsv "bench-text.tsv" rows
