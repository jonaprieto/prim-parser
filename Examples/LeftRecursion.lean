import PrimParser
open Parser

/-!
# Left recursion terminates with a wrong answer (a documented limitation)

Grammar, straight from a textbook BNF (left-associative `+`):

    sum ::= sum '+' digit | digit

Transcribe it *literally* into prim-parser. The recursive `sum` is the first
thing in the left alternative — classic left recursion. It typechecks at grade
`conditional`, `fix` accepts it, `lake build` is green. But it silently returns
the WRONG answer: it parses only the first digit and drops the rest, because the
`always`-consume grade proves termination, not guardedness, and the runtime fuel
guard turns the un-guarded `self` call into a failure that `<|>` backtracks past.

This is expected and **documented**: the prim-parser post states that a direct
left-recursive rule "loops forever in most parser libraries. prim-parser prevents
the loop, but the user must unfold the left recursion into an iterative form"
(https://draft.blog.janmasrovira.org/blog/prim-parser/). `sumGood` below is that
iterative form (`chainl1`, no left recursion). This example just makes the failure
mode concrete: same input, same types, silently different answers.
-/

private def txt (s : String) : Text s.toList.length := ofString s

/-- Left-recursive transcription. Typechecks; wrong at runtime. -/
def sumBad : Parser Error conditional Nat :=
  fix fun (sum : Parser Error conditional Nat) =>
    let lhs : Parser Error conditional Nat := gdo
      let a ← sum        -- <- `self` used before consuming: the trap
      char '+'
      let b ← digit
      return a + b
    (lhs <|> digit : Parser Error conditional Nat)

/-- Correct spelling: left-associative fold, no left recursion. -/
def sumGood : Parser Error conditional Nat :=
  chainl1 (gdo char '+'; return (· + ·)) digit

-- Same input, same types, silently different results:
#eval sumBad.runResult?  (txt "1+2")     -- some 1  ← WRONG (should be 3; dropped "+2")
#eval sumGood.runResult? (txt "1+2")     -- some 3  ← correct
#eval sumBad.runResult?  (txt "1+2+3")   -- some 1  ← WRONG (should be 6)
#eval sumGood.runResult? (txt "1+2+3")   -- some 6  ← correct
