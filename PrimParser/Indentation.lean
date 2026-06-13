import PrimParser.Base

/-!
# Indentation

Support for indentation-sensitive parsing in the style of
*Indentation-Sensitive Parsing for Parsec* (Adams & Ağacan, Haskell '14).

Every consumed character has a column (1-based). Parsing carries a set `I` of
*allowable indentations*, represented as a half-open interval `[lo, hi)`;
by Theorem 1 of the paper, the relations in `Rel` only ever produce intervals.
A token at column `c` is admitted when `{i ∈ I | c ▷ i}` is non-empty (where
`▷` is the ambient token relation), and `I` is narrowed to that set.
-/

namespace Indentation

/-- A relation constraining the indentation of a sub-parse (or token) relative
to the indentation of its context. -/
inductive Rel where
  /-- Same indentation. -/
  | eq
  /-- Greater or equal indentation. -/
  | ge
  /-- Strictly greater indentation. -/
  | gt
  /-- Any indentation; disassociates a sub-parse from its context. -/
  | any
  deriving Repr, BEq, DecidableEq, Inhabited

/-- A set of allowable indentations: the half-open interval `[lo, hi)`,
where `hi = none` means unbounded. -/
structure Interval where
  lo : Nat := 0
  hi : Option Nat := none
  deriving Repr, BEq

namespace Interval

/-- The interval of all indentations. -/
abbrev all : Interval := {}

/-- The empty interval. -/
abbrev empty : Interval := {lo := 0, hi := some 0}

/-- The interval containing only `c`. -/
def singleton (c : Nat) : Interval := {lo := c, hi := some (c + 1)}

def isEmpty (i : Interval) : Bool :=
  match i.hi with
  | none => false
  | some h => h ≤ i.lo

def inter (i j : Interval) : Interval where
  lo := Nat.max i.lo j.lo
  hi := match i.hi, j.hi with
    | none, h => h
    | h, none => h
    | some a, some b => some (Nat.min a b)

def mem (c : Nat) (i : Interval) : Bool :=
  i.lo ≤ c && match i.hi with
    | none => true
    | some h => c < h

end Interval

namespace Rel

/-- Entry set `J = {j | ∃ i ∈ I, j ▷ i}`: the indentations at which a
sub-parse wrapped with relation `▷` may be attempted. -/
def entry (r : Rel) (i : Interval) : Interval :=
  if i.isEmpty then .empty else
  match r with
  | .eq => i
  | .any => .all
  | .ge => {lo := i.lo}
  | .gt => {lo := i.lo + 1}

/-- Exit set `I' = {i ∈ I | ∃ j ∈ J', j ▷ i}`: the indentations of the
context compatible with the indentations `J'` at which the sub-parse
actually succeeded. -/
def exit (r : Rel) (i j' : Interval) : Interval :=
  if j'.isEmpty then .empty else
  match r with
  | .eq => i.inter j'
  | .any => i
  | .ge =>
    match j'.hi with
    | none => i
    | some h => i.inter {hi := some h}
  | .gt =>
    match j'.hi with
    | none => i
    | some h => i.inter {hi := some (h - 1)}

end Rel

/-- Indentation state threaded through the input text. -/
structure State where
  /-- Allowable indentations of the current block. -/
  indents : Interval := {}
  /-- Set inside `absoluteIndentation` until the first token is consumed. -/
  absMode : Bool := false
  /-- Default relation applied at every consumed token. -/
  tokenRel : Rel := .any
  /-- Column (1-based) of the next character of the input. -/
  col : Nat := 1
  deriving Repr

namespace State

/-- Admit a token at the current column, narrowing the indentation set, or
return `none` if the token's column is not allowed. In absolute-alignment
mode the token must be at one of the allowed indentations exactly, which then
becomes the only allowed indentation; otherwise the token's column is related
to the indentation set by `tokenRel`. -/
def checkToken (s : State) : Option State :=
  if s.absMode then
    let i' := Rel.eq.exit s.indents (.singleton s.col)
    if i'.isEmpty then none else some {s with indents := i', absMode := false}
  else
    let i' := s.tokenRel.exit s.indents (.singleton s.col)
    if i'.isEmpty then none else some {s with indents := i'}

/-- Advance the column past character `c`. -/
def advance (c : Char) (s : State) : State :=
  {s with col := if c = '\n' then 1 else s.col + 1}

end State

end Indentation
