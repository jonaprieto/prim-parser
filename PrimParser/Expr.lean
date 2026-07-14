import PrimParser.Run

/-!
# Expression parser

A precedence-table expression parser in the style of megaparsec's
`makeExprParser`. Operators are grouped into precedence levels (highest first);
each level is left- or right-associative. Built from `chainl1` / `chainr1`, so
there is no left recursion. Fixed to the `conditional` grade to keep the grade
indices inferable.
-/

namespace Parser

variable {α : Type} {ge ge' : Necessity}

/-- Fold a collected `x op₁ y₁ op₂ y₂ ...` right-associatively. -/
private def rightFold (x : α) : List ((α → α → α) × α) → α
  | [] => x
  | (f, y) :: rest => f x (rightFold y rest)

/-- Parse `p` separated by right-associative operator `op`. -/
def chainr1 (op : Parser Error ⟨ge', always⟩ (α → α → α)) (p : Parser Error ⟨ge, always⟩ α)
    : Parser Error ⟨ge, always⟩ α := gdo
  let x ← p
  let rest ← many (gdo let f ← op; let y ← p; return (f, y))
  return rightFold x rest
  grade_by by simp

/-- A binary operator at the `conditional` grade. -/
abbrev BinOp (α : Type) := Parser Error conditional (α → α → α)

inductive Assoc | left | right

/-- One precedence level: an associativity and the operators sharing it. -/
structure Level (α : Type) where
  assoc : Assoc
  ops : NonEmptyList (BinOp α)

/-- Build an expression parser from a `term` parser and a precedence `table`
(highest precedence first). -/
def makeExprParser (term : Parser Error conditional α) (table : List (Level α))
    : Parser Error conditional α :=
  table.foldl (fun below lvl =>
    let opP := oneOf lvl.ops
    match lvl.assoc with
    | .left  => chainl1 opP below
    | .right => chainr1 opP below) term

private def arith : Parser Error conditional Nat :=
  makeExprParser nat
    [ { assoc := .left, ops := (gdo char '*'; return (· * ·)) ::₁ [] },
      { assoc := .left, ops := (gdo char '+'; return (· + ·)) ::₁ [] } ]

#guard arith.parse? "1+2*3" == some 7
#guard arith.parse? "2*3+1" == some 7
#guard arith.parseAll? "1+2+3" == some 6
#guard arith.parseAll? "2*3*4" == some 24

private def rpow : Parser Error conditional Nat :=
  makeExprParser digit [ { assoc := .right, ops := (gdo char '^'; return (· ^ ·)) ::₁ [] } ]

#guard rpow.parseAll? "2^3^2" == some 512   -- right assoc: 2^(3^2) = 2^9

end Parser
