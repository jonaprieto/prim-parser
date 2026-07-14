import PrimParser.Basic

/-!
# The algebra of backtracking-choice grades: precision vs. associativity

This file isolates a metatheory result about the *grade* of the ordered-choice
combinator `p <|> q`. The standard `GradedAlternative` grades choice **additively**
(`i + j`); prim-parser grades it `⟨ge ⊓ ge', ge.ite gc' gc⟩` — meet on the error
dimension, a conditional on consumption. We show that this refined grade is the
unique **principal** (tightest sound) grade for backtracking choice, and that it is
**not associative** — hence there is *no* choice-grade that is both principal and
associative. Precision and the graded-alternative associativity law are incompatible.

`Byte.lean` and the parser combinators are untouched; this is pure grade algebra. -/

namespace Parser.ChoiceAlgebra
open Parser Necessity

/-- A candidate grade for `p <|> q`, computed from the two operand grades. -/
abbrev ChoiceGrade := Grade → Grade → Grade

/-- Associativity of a choice-grade (the `LawfulGradedAlternative` `gchoice_assoc`
obligation at the grade level). -/
def Assoc (ch : ChoiceGrade) : Prop := ∀ a b c, ch (ch a b) c = ch a (ch b c)

/-- The **semantic precision constraints** any tight sound grade for backtracking
choice must satisfy, read off the operational meaning of `p <|> q`:
* if `p` never fails, the choice commits to `p` (its grade **is** `p`'s);
* if `p` always fails, the choice is exactly `q`;
* if `p` may fail, errors are the meet (fails only if **both** fail) and consumption
  is the agreement of the two branches (`always`/`never` only if they concur, else
  `possibly`). -/
structure Tight (ch : ChoiceGrade) : Prop where
  commit_left  : ∀ ca b, ch ⟨never, ca⟩ b = ⟨never, ca⟩
  take_right   : ∀ ca b, ch ⟨always, ca⟩ b = b
  blend        : ∀ ca eb cb,
      ch ⟨possibly, ca⟩ ⟨eb, cb⟩ = ⟨possibly ⊓ eb, possibly.ite cb ca⟩

/-- The blend's consumption is exactly the branches' **agreement**: `cb` if the two
branches consume the same, else `possibly`. -/
theorem blend_is_agreement (cb ca : Necessity) :
    possibly.ite cb ca = if cb = ca then cb else possibly := Necessity.ite_possibly_cases cb ca

/-- **(B) prim-parser's `Grade.choice` is tight** — it realises exactly the principal
grade above. -/
theorem choice_tight : Tight Grade.choice where
  commit_left ca b  := by obtain ⟨e, c⟩ := b; simp [Grade.choice]
  take_right ca b   := by obtain ⟨e, c⟩ := b; simp [Grade.choice]
  blend ca eb cb    := by simp [Grade.choice]

/-- **Principality / uniqueness**: the tight grade is unique — any grade meeting the
semantic constraints equals `Grade.choice`. So the constraints pin the grade exactly;
there is one principal choice grade. -/
theorem tight_unique {ch : ChoiceGrade} (h : Tight ch) : ch = Grade.choice := by
  funext a b; obtain ⟨e, c⟩ := a
  cases e with
  | never => rw [h.commit_left]; obtain ⟨e', c'⟩ := b; simp [Grade.choice]
  | possibly => obtain ⟨e', c'⟩ := b; rw [h.blend]; simp [Grade.choice]
  | always => rw [h.take_right]; obtain ⟨e', c'⟩ := b; simp [Grade.choice]

/-- `Grade.choice` is **not associative** (the consumption dimension): a machine-checked
counterexample. With `a = ⟨possibly, always⟩`, `b = ⟨always, never⟩`, `c = ⟨possibly,
always⟩`, the left association consumes `possibly` while the right consumes `always`. -/
theorem choice_not_assoc : ¬ Assoc Grade.choice := by
  intro h
  have e := h ⟨possibly, always⟩ ⟨always, never⟩ ⟨possibly, always⟩
  simp [Grade.choice, Necessity.ite_possibly_cases] at e

/-- **(C) Impossibility: no principal choice grade is associative.** The tightest sound
grade for backtracking choice exists and is unique (`tight_unique`), and it is
non-associative (`choice_not_assoc`). Hence *any* grade precise enough to be principal
fails the graded-alternative associativity law: a graded parser cannot have both a
principal `<|>` grade and lawful alternation. Precision ⟂ associativity. -/
theorem no_tight_assoc {ch : ChoiceGrade} (ht : Tight ch) : ¬ Assoc ch := by
  rw [tight_unique ht]; exact choice_not_assoc

/-- Corollary: the additive graded-alternative grade (`i + j`, associative) is **not**
tight — it over-approximates. Any associative grade must be strictly coarser than the
principal one. -/
theorem assoc_not_tight {ch : ChoiceGrade} (ha : Assoc ch) : ¬ Tight ch :=
  fun ht => no_tight_assoc ht ha

/-! ### The semantic reading: precision makes the grade *incomplete* for choice
associativity. The obstruction above is not behavioural — the parser `<|>` really is
associative — it is that the precise grade cannot *witness* that fact. -/

variable {ε α : Type} {m : Nat} {ge gc ge' gc' : Necessity}

/-- Ordered choice is, at the value level, "first success". -/
theorem runResult_choice (p : Parser ε ⟨ge, gc⟩ α) (q : Parser ε ⟨ge', gc'⟩ α) (t : Text m) :
    (choice p q).runResult? t = ((p.runResult? t) <|> (q.runResult? t)) := by
  simp only [choice, Parser.runResult?]
  cases ge <;> cases ge' <;>
    simp only [Outcome.handle, Outcome.ofSuccess, Outcome.throwFailure] <;>
    (try cases hp : p.run t) <;> (try cases hq : q.run t) <;>
    simp_all [Outcome.handle, Outcome.ofSuccess, Outcome.throwFailure]

/-- **Behavioural associativity of `<|>`.** Both bracketings return the same value on
every input — choice is genuinely associative as a program. (Grade erased via
`runResult?`, since the two sides do not even share a grade type.) -/
theorem choice_run_assoc
    {ge'' gc'' : Necessity}
    (p : Parser ε ⟨ge, gc⟩ α) (q : Parser ε ⟨ge', gc'⟩ α) (r : Parser ε ⟨ge'', gc''⟩ α)
    (t : Text m) :
    (choice (choice p q) r).runResult? t = (choice p (choice q r)).runResult? t := by
  simp only [runResult_choice]; cases p.runResult? t <;> rfl

/-- **(C, semantic form) Precision ⟂ associativity, read as incompleteness.** The
parser `<|>` is behaviourally associative (`choice_run_assoc`), yet its two
bracketings carry *different grades* (`choice_not_assoc`). Hence the graded-alternative
associativity law is not even *statable* — the two sides inhabit different grade types.
The principal grade is a sound abstraction whose precision makes it **incomplete** for
the (true) associativity of choice: you cannot type what you can run. -/
theorem precision_incomplete_for_choice_assoc :
    -- behaviour: associative
    (∀ {ε α m ge gc ge' gc' ge'' gc''}
       (p : Parser ε ⟨ge, gc⟩ α) (q : Parser ε ⟨ge', gc'⟩ α) (r : Parser ε ⟨ge'', gc''⟩ α)
       (t : Text m),
       (choice (choice p q) r).runResult? t = (choice p (choice q r)).runResult? t)
    -- grade: not
    ∧ ¬ Assoc Grade.choice :=
  ⟨fun p q r t => choice_run_assoc p q r t, choice_not_assoc⟩

end Parser.ChoiceAlgebra
