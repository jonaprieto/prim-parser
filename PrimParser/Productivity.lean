import PrimParser.Basic

/-!
# Totality is not productivity

`fix` is total by construction (no `partial`): the `always`-consume grade forces
the input to shrink, so the recursion is well-founded on input length. But
`always`-consume on the *composite* body does **not** entail that the recursive
occurrence `self` is *guarded* by an already-consumed token. `fix` is really
**fuel-bounded general recursion** with fuel = remaining input size (see the guard
`if k ≤ n then go t' else throw` in `Parser.fix`), and fuel-based recursion turns
non-productivity into a silent premature failure rather than a compile-time error.

Concretely: a *left-recursive* body (using `self` before consuming) still typechecks
at grade `conditional`, `fix` accepts it, and the result is total — but it rejects
input a correct parser accepts, returning the `default` error via the fuel guard.

This is a **documented limitation, not a defect.** The prim-parser post is explicit
that a direct left-recursive rule such as `term ::= term '+' factor` "loops forever in
most parser libraries. prim-parser prevents the loop, but the user must unfold the left
recursion into an iterative form." The advertised guarantee is *termination*, and that is
exactly what holds. This file only makes the termination-without-productivity gap precise.
Source: https://draft.blog.janmasrovira.org/blog/prim-parser/

The principled alternative (a size-indexed / guarded `fix`, as in Allais' agdarsec, where
`self` is available only at a strictly smaller input size) makes left recursion a
*type* error. It is a redesign of the parser type, so it is not attempted here; this
file only pins the gap down as a theorem.

Note: the library's own recursive combinators (`manyTill`, `chainl1`, `many1`) are
written *guarded* — they consume via `p`/`op`/`anyChar` before touching `self` — so
the trap is latent, avoided by discipline rather than by the type system.
-/

namespace Parser

private def txt (s : String) : Text s.toList.length := ofString s

/-- A left-recursive body: `self` is used *before* any input is consumed. The grade is
still `conditional = ⟨possibly, always⟩`, so it typechecks and `fix` accepts it. -/
def leftRecBody (self : Parser Error conditional Char) : Parser Error conditional Char := gdo
  let _ ← self
  anyChar
  grade_by by simp

/-- `fix` accepts the left-recursive body: this definition elaborates and is total. -/
def leftRec : Parser Error conditional Char := fix leftRecBody

/-- **Totality ≠ productivity.** `fix leftRecBody` is total, yet on input `"a"` it
returns `none`, whereas the intended parse (`anyChar`) succeeds with `'a'`. The
`always`-consume grade proved *termination*, not *correctness*: it silently converts a
non-productive (left-recursive) definition into an always-failing parser. -/
theorem fix_not_productive :
    anyChar.runResult? (txt "a") = some 'a'
  ∧ leftRec.runResult? (txt "a") = none := by
  refine ⟨by decide, ?_⟩
  -- `fix` compiles to well-founded recursion, so the kernel will not reduce
  -- `leftRec.run` by itself. Unfold one step of `fix.go`; on this input the
  -- recursive branch is dead (guard `1 ≤ 0` is false), so `decide` finishes.
  simp only [leftRec, Parser.fix, Parser.runResult?]
  rw [Parser.fix.go.eq_def]
  decide

end Parser
