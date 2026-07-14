import PrimParser.Basic

/-!
# PrimParser.Byte — a compiled, byte-level graded parser backend (start)

A third backend, motivated by the benchmarks: the reified deep interpreter pays a
per-node `Res` allocation (~2× attoparsec) and the shallow `Char` backend pays
boxed-`Char` + `Outcome`-per-combinator (~9× attoparsec). This one is **shallow**
(combinators are `@[inline]` functions the Lean compiler fuses into the grammar),
over a raw `ByteArray` with `Nat` positions, results as `Option (α × Nat)` — no
reified tree, no boxed `Char`, no witness-carrying `Outcome` at runtime.

The `Grade` index (error × consumption `Necessity`) is threaded through the
combinator types exactly as in `Parser`, so the same static discipline holds and
grades are erased at runtime.

Status vs the shallow backend's guarantees:
* **`LawfulGradedMonad` — proven** (below), as a *genuine class instance*, directly
  by funext (`BParser` is `Type 0` concrete, so no denotation/quotient needed —
  unlike the deep backend).
* **Total** — every combinator is a plain `def`; the scanners and the repetition
  core `foldFwd` recurse structurally on `arr.size - q` (the `q < q' ≤ size` guard
  makes progress explicit, so no consumption witness is needed for termination).
* Remaining: typed `ε` errors (currently failure is bare `none`), and the
  consumption-witness soundness (`run_consumes`-style) relating the grade to runtime.

Benchmark: the packed-`UInt64` specialization of this design (`bench/JCombo.lean`)
parses canada.json at 18.3 ms, under attoparsec's 19.5 ms; the polymorphic
`Option (α × Nat)` form here ties attoparsec (~19 ms) — Lean lacks GHC's unboxed
sums, so specialization is what buys the win.
-/

namespace Byte

/-- A byte-level parser with static grade `g`, producing `α`. `run` returns the
value and the new byte offset, or `none` on failure. -/
structure BParser (g : Grade) (α : Type) where
  run : ByteArray → Nat → Option (α × Nat)

instance {g : Grade} {α : Type} : Inhabited (BParser g α) := ⟨⟨fun _ _ => none⟩⟩

variable {g g' : Grade} {ge ge' gc gc' : Necessity} {α β : Type}

/-- Consume nothing, never fail. -/
@[inline] def pure (a : α) : BParser 1 α := ⟨fun _ p => some (a, p)⟩

/-- Always fail. -/
@[inline] def fail : BParser empty α := ⟨fun _ _ => none⟩

/-- Consume one byte satisfying `f`, or fail without consuming. -/
@[inline] def satisfy (f : UInt8 → Bool) : BParser conditional UInt8 :=
  ⟨fun arr p => if h : p < arr.size then (if f arr[p] then some (arr[p], p + 1) else none) else none⟩

/-- Match a specific byte. -/
@[inline] def byte (c : UInt8) : BParser conditional Unit :=
  ⟨fun arr p => if h : p < arr.size then (if arr[p] == c then some ((), p + 1) else none) else none⟩

/-- Map over the result (grade preserved). -/
@[inline] def map (h : α → β) (x : BParser g α) : BParser g β :=
  ⟨fun arr p => (x.run arr p).map fun (a, p') => (h a, p')⟩

/-- Sequence, keeping the right value; grades multiply. -/
@[inline] def seqR (x : BParser g α) (y : BParser g' β) : BParser (g * g') β :=
  ⟨fun arr p => match x.run arr p with | some (_, p') => y.run arr p' | none => none⟩

/-- Sequence, keeping the left value; grades multiply. -/
@[inline] def seqL (x : BParser g α) (y : BParser g' β) : BParser (g * g') α :=
  ⟨fun arr p => match x.run arr p with
    | some (a, p') => match y.run arr p' with | some (_, p'') => some (a, p'') | none => none
    | none => none⟩

/-- Ordered choice; grade follows `Grade.choice` (as in `Parser.choice`). -/
@[inline] def alt (x : BParser ⟨ge, gc⟩ α) (y : BParser ⟨ge', gc'⟩ α) :
    BParser ⟨ge ⊓ ge', ge.ite gc' gc⟩ α :=
  ⟨fun arr p => match x.run arr p with | some r => some r | none => y.run arr p⟩

/-- Scan forward while `f` holds. **Total** — structural on the measure
`arr.size - q` (each step advances one byte, bounded by `arr.size`). -/
def scanFwd (arr : ByteArray) (f : UInt8 → Bool) (q : Nat) : Nat :=
  if h : q < arr.size then (if f arr[q] then scanFwd arr f (q + 1) else q) else q
termination_by arr.size - q
decreasing_by omega

/-- Scan while `f` holds, returning the number of bytes consumed. Fast path. -/
@[inline] def takeWhile (f : UInt8 → Bool) : BParser flexible Nat :=
  ⟨fun arr p => let q := scanFwd arr f p; some (q - p, q)⟩

/-- One-or-more bytes satisfying `f`. -/
@[inline] def takeWhile1 (f : UInt8 → Bool) : BParser conditional Nat :=
  ⟨fun arr p =>
    if h : p < arr.size then
      if f arr[p] then (takeWhile f).run arr p else none
    else none⟩

/-- Total repetition core: fold `p`'s results into `a`, advancing while `p` succeeds
and strictly consumes (in bounds). **Total** — structural on `arr.size - q`; the
guard `q < q' ≤ arr.size` guarantees the measure drops, so no consumption witness is
needed (a well-behaved always-consuming `p` always takes the recursive branch). -/
def foldFwd {ge : Necessity} {α β : Type} (step : β → α → β) (p : BParser ⟨ge, always⟩ α)
    (arr : ByteArray) (a : β) (q : Nat) : β × Nat :=
  match p.run arr q with
  | some (x, q') =>
    if hq : q < q' ∧ q' ≤ arr.size then foldFwd step p arr (step a x) q' else (step a x, q')
  | none => (a, q)
termination_by arr.size - q
decreasing_by (obtain ⟨h1, h2⟩ := hq; omega)

/-- Fold `p` zero-or-more times into `acc` (no list). Total (see `foldFwd`). -/
@[inline] def foldMany (h : β → α → β) (acc : β) (p : BParser ⟨ge, always⟩ α) :
    BParser flexible β :=
  ⟨fun arr pos => some (foldFwd h p arr acc pos)⟩

/-- Monadic bind; grades multiply. -/
@[inline] def bind (x : BParser g α) (f : α → BParser g' β) : BParser (g * g') β :=
  ⟨fun arr p => match x.run arr p with | some (a, p') => (f a).run arr p' | none => none⟩

/-- Apply a binary function across two parses; grades multiply. -/
@[inline] def map2 {γ : Type} (f : α → β → γ) (x : BParser g α) (y : BParser g' β) : BParser (g * g') γ :=
  ⟨fun arr p => match x.run arr p with
    | some (a, p') => match y.run arr p' with | some (b, p'') => some (f a b, p'') | none => none
    | none => none⟩

/-- Fold decimal digits into `acc`. **Total** — structural on `arr.size - q`. -/
def natFwd (arr : ByteArray) (acc q : Nat) : Nat × Nat :=
  if h : q < arr.size then
    let b := arr[q]
    if 48 ≤ b && b ≤ 57 then natFwd arr (acc * 10 + (b.toNat - 48)) (q + 1) else (acc, q)
  else (acc, q)
termination_by arr.size - q
decreasing_by omega

@[inline] def nat : BParser conditional Nat :=
  ⟨fun arr p0 =>
    if h : p0 < arr.size then
      let b := arr[p0]; if 48 ≤ b && b ≤ 57 then some (natFwd arr 0 p0) else none
    else none⟩

/-- Consume exactly `n` bytes if available. -/
@[inline] def takeN (n : Nat) : BParser fallible Unit :=
  ⟨fun arr p => if p + n ≤ arr.size then some ((), p + n) else none⟩

/-- Zero-or-more `p` (always-consuming) into a list. Total (via `foldFwd`). -/
@[inline] def many (p : BParser ⟨ge, always⟩ α) : BParser flexible (List α) :=
  ⟨fun arr pos => let (xs, q) := foldFwd (fun acc x => x :: acc) p arr [] pos; some (xs.reverse, q)⟩

/-- Run on a whole `ByteArray` from offset 0. -/
@[inline] def run (p : BParser g α) (arr : ByteArray) : Option α :=
  (p.run arr 0).map (·.1)

/-! ### `BParser` is a genuine `LawfulGradedMonad`

Unlike the reified deep backend (`Type 1`, laws only up to denotation), `BParser`
is a `Type 0` `GradedType` with a concrete `run` function, so the graded-monad laws
hold **directly** by function extensionality. The grade is a phantom index (`run`'s
type ignores `g`), which trivializes the `≍` (cross-grade) laws. -/

@[ext] theorem ext {x y : BParser g α} (h : x.run = y.run) : x = y := by
  cases x; cases y; simp_all

/-- Transport a `run`-equality across a grade equality (grade is phantom). -/
theorem heq_of_run {i j : Grade} {x : BParser i α} {y : BParser j α}
    (hg : i = j) (h : x.run = y.run) : x ≍ y := by subst hg; exact heq_of_eq (ext h)

instance : GradedFunctor BParser where gmap := map
instance : GradedApplicative BParser where
  gpure := pure
  gseq f x := bind f (fun h => map h (x ()))
instance : GradedMonad BParser where gbind := bind

instance : LawfulGradedFunctor BParser where
  gmap_id x := by apply ext; funext arr p; simp [gmap, map]
  gmap_comp g h x := by
    apply ext; funext arr p; simp only [gmap, map, Option.map_map]; congr 1

instance : LawfulGradedApplicative BParser where
  gmap_gpure g x := by apply ext; funext arr p; simp [gmap, map, gpure, pure]
  gpure_gseq g x := by
    apply heq_of_run (one_mul _); funext arr p
    simp [gseq, gmap, bind, map, gpure, pure]
  gseq_gpure u x := by
    apply heq_of_run (mul_one _); funext arr p
    simp [gseq, gmap, bind, map, gpure, pure]; cases u.run arr p <;> simp
  gseq_assoc u v w := by
    apply heq_of_run (mul_assoc _ _ _); funext arr p
    simp only [gseq, gmap, bind, map]
    cases u.run arr p <;> simp
    cases v.run arr _ <;> simp
    cases w.run arr _ <;> simp

instance : LawfulGradedMonad BParser where
  gpure_gbind x f := by
    apply heq_of_run (one_mul _); funext arr p; simp [gbind, bind, gpure, pure]
  gbind_gpure x := by
    apply heq_of_run (mul_one _); funext arr p
    simp [gbind, bind, gpure, pure]; cases x.run arr p <;> simp
  gbind_assoc x f g := by
    apply heq_of_run (mul_assoc _ _ _); funext arr p
    simp only [gbind, bind]; cases x.run arr p <;> simp

end Byte

/-! ### Sanity: the byte backend parses. -/
section
open Byte

private def digits : BParser conditional Nat := takeWhile1 (fun b => 48 ≤ b && b ≤ 57)
private def sample := seqR (byte 40) (seqL digits (byte 41))   -- "(" digits ")"

#guard (run digits "123".toUTF8) == some 3        -- 3 digit bytes consumed
#guard (run sample "(42)".toUTF8) == some 2       -- 2 digit bytes inside parens
#guard (run sample "(42".toUTF8) == none          -- missing ')'
#guard (run (foldMany (· + ·) 0 digits) "".toUTF8) == some 0
end
