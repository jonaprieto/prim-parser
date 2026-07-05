import PrimParser.Necessity

/-!
# PrimParser.Grade - the grade algebra

The `Grade` monoid (error + consumption `Necessity` pair).
-/

/-- A parser's static grade: whether it may/must produce errors and
whether it may/must consume input. -/
structure Grade where
  errors : Necessity
  consumes : Necessity
  deriving Repr

namespace Grade

/-- Consumes nothing, never fails: injects a value (`pure`/`return`). -/
abbrev pure : Grade where
  consumes := never
  errors := never

/-- Consumes nothing, may fail: pure lookahead / assertion. -/
abbrev lookahead : Grade where
  consumes := never
  errors := possibly

/-- Consumes nothing, always fails: the never-succeeding parser. -/
abbrev empty : Grade where
  consumes := never
  errors := always

/-- May consume, never fails: total, e.g. `many`/optional whitespace. -/
abbrev flexible : Grade where
  consumes := possibly
  errors := never

/-- May consume, may fail: the general case (most parsers). -/
abbrev fallible : Grade where
  consumes := possibly
  errors := possibly

/-- Always consumes, never fails: impossible, a parser must accept empty input. -/
abbrev impossible : Grade where
  consumes := always
  errors := never

/-- Always consumes on success, may fail: makes progress, e.g. single token. -/
abbrev conditional : Grade where
  consumes := always
  errors := possibly

@[simp] def max (a b : Grade) : Grade :=
  { errors := a.errors ⊔ b.errors, consumes := a.consumes ⊔ b.consumes }

instance : Max Grade where
  max := max

instance : Monoid Grade where
  mul := max
  mul_assoc a b c := by cases a; cases b; simp [HMul.hMul, Mul.mul]; grind
  one := pure
  one_mul a := by cases a; simp [HMul.hMul, Mul.mul, OfNat.ofNat, pure]
  mul_one a := by cases a; simp [HMul.hMul, Mul.mul, OfNat.ofNat, pure]

instance : Zero Grade where
  zero := empty

variable (g g' : Grade)

@[simp] theorem mul_mk : g * g' = max g g' := rfl

@[simp] theorem one_mk : (1 : Grade) = ⟨never, never⟩ := by
  simp [OfNat.ofNat, One.one]

@[simp] theorem mul_idem : g * g = g := by cases g ; simp

def choice (a b : Grade) : Grade where
  errors := a.errors ⊓ b.errors
  consumes := a.errors.ite b.consumes a.consumes

end Grade

export Grade (impossible conditional flexible fallible pure lookahead empty)
