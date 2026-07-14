/-
DISABLED: needs the `τ` token-type parameter, removed to minimize delta vs main.
Re-enable together with the τ generalization of `Text`/`Parser`.

import PrimParser

open Parser

/-! Parsing over a non-`Char` token stream (here `Nat`), via `ofArray` + the
generic primitives `anyToken` / `satisfyToken`. Same graded core, same proofs. -/

-- single token
#guard anyToken.runResult? (ofArray #[(10 : Nat), 20, 30]) == some 10
#guard (anyToken (τ := Nat)).runResult? (ofArray #[]) == none

-- generic satisfy + many over Nat tokens
#guard (many (satisfyToken (· < 100))).runResult? (ofArray #[(1 : Nat), 2, 3, 200])
    == some [1, 2, 3]

-- generic bind
#guard (gdo let a ← anyToken; let b ← anyToken; return a + b).runResult?
    (ofArray #[(5 : Nat), 7]) == some 12

-- a token stream of a custom inductive
inductive Tok | plus | num (v : Nat) deriving BEq, Repr
#guard (satisfyToken (· == Tok.plus)).runResult? (ofArray #[Tok.plus, Tok.num 3])
    == some Tok.plus

-/
