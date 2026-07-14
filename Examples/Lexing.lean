/-
DISABLED: needs the `τ` token-type parameter, removed to minimize delta vs main.
Re-enable together with the τ generalization of `Text`/`Parser`.

import PrimParser

open Parser

/-!
# Two-phase parsing over generic tokens

Phase 1 lexes a `String` into `Array Tok` with the character combinators.
Phase 2 parses that token stream with the *same* graded core, now at `τ := Tok`,
using `anyToken` / `satisfyToken`. Same proofs, different token type.
-/

inductive Tok | num (v : Nat) | plus | lpar | rpar
  deriving BEq, Repr

namespace Lexing

/-- One token (a number or a single-char symbol), plus trailing whitespace. -/
def oneTok : Parser Char Error conditional Tok :=
  lexeme (oneOf ((Tok.num <$>ᵍ nat) ::₁
    [Tok.plus <$ᵍ char '+', Tok.lpar <$ᵍ char '(', Tok.rpar <$ᵍ char ')']))

/-- Phase 1: lex a whole string into tokens (skipping leading whitespace). -/
def lex (s : String) : Option (List Tok) :=
  (gdo whitespace; many oneTok).parseAll? s

/-- Phase 2 building block: pull a `num` off the token stream. -/
def pNum : Parser Tok Error conditional Nat :=
  (anyToken : Parser Tok Error conditional Tok) >>=ᵍ fun t => match t with
    | Tok.num v => (ok v : Parser Tok Error fallible Nat)
    | _         => throw Error.fail

/-- `+` as a left-associative operator over tokens. -/
def pPlus : Parser Tok Error conditional (Nat → Nat → Nat) :=
  satisfyToken (· == Tok.plus) >>=ᵍ fun _ => (ok (· + ·) : Parser Tok Error fallible _)

/-- Phase 2: sum of `+`-separated numbers. -/
def pSum : Parser Tok Error conditional Nat := chainl1 pPlus pNum

/-- Full pipeline: lex then parse. -/
def eval (s : String) : Option Nat :=
  (lex s).bind fun toks => pSum.runResult? (ofArray toks.toArray)

#guard lex "1 + 22" == some [Tok.num 1, Tok.plus, Tok.num 22]
#guard eval "1 + 2 + 3" == some 6
#guard eval "42" == some 42
#guard eval "  10  +  5 " == some 15

end Lexing

-/
