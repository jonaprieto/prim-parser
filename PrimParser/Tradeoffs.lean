import PrimParser.ChoiceAlgebra
import PrimParser.GradedDeep
import PrimParser.Productivity

/-!
# No free lunch: three mechanized impossibilities for graded parser combinators

The graded design is governed by fundamental tensions. Each is a *theorem*, not a
caveat — you cannot pay your way out. This module collects the three, proven
elsewhere, as one coherent map of the design space.

| you want | you give up | witness |
|----------|-------------|---------|
| a **principal** (tightest) grade for `<|>` | **associativity** of choice | `ChoiceAlgebra.no_tight_assoc` |
| a **fast** deep interpreter (fuel) | **lawfulness** (bind-associativity) | `Graded.PhaseE.fuel_not_monotone` |
| **totality** of `fix` (always-consume) | **productivity** (left recursion) | `fix_not_productive` |

1. **Precision ⟂ associativity.** The unique tightest sound grade for backtracking
   choice (`⊓` on errors, agreement on consumption — it makes "one infallible branch
   ⟹ infallible choice" a *type*) is non-associative. So no choice grade is both
   principal and a lawful graded-alternative. The standard additive grade regains
   associativity only by over-approximating.

2. **Fuel ⟂ laws.** The reified deep backend's fuel interpreter is not associative:
   the same grammar and input give different results at different fuel, because `alt`
   commits to its right branch when the left merely runs out of fuel. So the fast
   reified executor cannot be a `LawfulGradedMonad`; laws are recovered only by
   denoting into the structural shallow parser.

3. **Totality ⟂ productivity.** `fix` is total because the `always`-consume grade
   forces the input to shrink — but that proves *termination*, not *correctness*: a
   left-recursive body still typechecks and `fix` accepts it, silently turning
   non-productivity into an always-failing parser rather than a type error.

Together: **graded parsing is a lattice of impossibilities.** Positively, the same
grade algebra that forces these tensions also buys real precision — e.g. infallibility
inference through choice (item 1), which the standard graded-alternative cannot express.
-/

namespace Parser.Tradeoffs
open Parser

/-- (1) Precision excludes associativity — restated for the collection. -/
theorem precision_excludes_associativity {ch : ChoiceAlgebra.ChoiceGrade}
    (ht : ChoiceAlgebra.Tight ch) : ¬ ChoiceAlgebra.Assoc ch :=
  ChoiceAlgebra.no_tight_assoc ht

/-- (2) Fuel excludes lawfulness: the fuel interpreter is not monotone in fuel, so
bind-associativity fails for the reified deep backend. -/
def fuel_excludes_lawfulness := Graded.PhaseE.fuel_not_monotone

/-- (3) Totality excludes productivity: `fix` terminates on a left-recursive body but
returns `none` where the intended parse succeeds. -/
def totality_excludes_productivity := fix_not_productive

end Parser.Tradeoffs
