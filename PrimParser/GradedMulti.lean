import PrimParser.Graded
open Graded

/-!
# Multi-recursion for the graded deep-embedded parser

`Graded.G` has a single fixpoint (`recur`). Real grammars need several
mutually-recursive non-terminals (expr / term / factor). `GM` generalizes `recur`
to `recur i`, referencing non-terminal `i` in an environment of grammar bodies
`bodies : Nat → GM conditional Nat`; the total fuel interpreter dispatches
`recur i` to `bodies i`. Non-terminals are `Nat`-typed here (evaluators/checksums),
which keeps the recursion mechanism uncluttered by a dependent type family.
-/

namespace GradedMulti

inductive GM : Grade → Type → Type 1 where
  | pure {α} (a : α) : GM Grade.pure α
  | lit (c : UInt8) : GM conditional PUnit
  | nat : GM conditional Nat
  | chars0 (f : UInt8 → Bool) : GM flexible PUnit
  | map {g α β} (f : α → β) (a : GM g α) : GM g β
  | map2 {g g' α β γ} (f : α → β → γ) (a : GM g α) (b : GM g' β) : GM (g * g') γ
  | seqR {g g' α β} (a : GM g α) (b : GM g' β) : GM (g * g') β
  | seqL {g g' α β} (a : GM g α) (b : GM g' β) : GM (g * g') α
  | alt {g g' α} (a : GM g α) (b : GM g' α) : GM (g.choice g') α
  | star {ge α} (a : GM ⟨ge, always⟩ α) : GM flexible (List α)
  | recur (i : Nat) : GM conditional Nat    -- reference non-terminal i

/-- Total fuel interpreter with an environment of mutually-recursive bodies. -/
def GM.run (arr : ByteArray) (bodies : Nat → GM conditional Nat)
    : Nat → {g : Grade} → {α : Type} → GM g α → Nat → Res α
  | 0, _, _, _, off => .err off
  | fuel+1, g, α, gram, off => match gram with
    | .pure a => .ok a off
    | .lit c => if off < arr.size && arr[off]! == c then .ok ⟨⟩ (off+1) else .err off
    | .nat => if off < arr.size && bDigit arr[off]! then let (v, o) := scanNatB arr 0 arr.size off; .ok v o else .err off
    | .chars0 f => .ok ⟨⟩ (scanB arr f arr.size off)
    | .map f a => match GM.run arr bodies fuel a off with | .ok x o => .ok (f x) o | .err e => .err e
    | .map2 f a b => match GM.run arr bodies fuel a off with
      | .ok x o1 => (match GM.run arr bodies fuel b o1 with | .ok y o2 => .ok (f x y) o2 | .err e => .err e)
      | .err e => .err e
    | .seqR a b => match GM.run arr bodies fuel a off with | .ok _ o1 => GM.run arr bodies fuel b o1 | .err e => .err e
    | .seqL a b => match GM.run arr bodies fuel a off with
      | .ok x o1 => (match GM.run arr bodies fuel b o1 with | .ok _ o2 => .ok x o2 | .err e => .err e)
      | .err e => .err e
    | .alt a b => match GM.run arr bodies fuel a off with
      | .ok x o => .ok x o
      | .err _ => GM.run arr bodies fuel b off
    | .star a => match GM.run arr bodies fuel a off with
      | .ok x o' =>
        if o' > off then (match GM.run arr bodies fuel (.star a) o' with
          | .ok xs o2 => .ok (x :: xs) o2 | .err _ => .ok [x] o')
        else .ok [x] o'
      | .err _ => .ok [] off
    | .recur i => GM.run arr bodies fuel (bodies i) off

/-! ### Arithmetic: mutually-recursive expr / term / factor, evaluated. -/

-- expr = term ('+' term)* summed
def exprB : GM conditional Nat :=
  .map2 (fun t ts => t + ts.foldl (· + ·) 0) (.recur 1) (.star (.seqR (.lit (ch '+')) (.recur 1)))
-- term = factor ('*' factor)* multiplied
def termB : GM conditional Nat :=
  .map2 (fun f fs => fs.foldl (· * ·) f) (.recur 2) (.star (.seqR (.lit (ch '*')) (.recur 2)))
-- factor = nat | '(' expr ')'
def factorB : GM conditional Nat :=
  .alt .nat (.seqR (.lit (ch '(')) (.seqL (.recur 0) (.lit (ch ')'))))

def bodies : Nat → GM conditional Nat
  | 0 => exprB | 1 => termB | 2 => factorB | _ => .nat

def evalArith (s : String) : Nat :=
  let arr := s.toUTF8
  match GM.run arr bodies (arr.size * 64 + 64) exprB 0 with
  | .ok v _ => v | .err _ => 0

end GradedMulti

-- self-tests: mutual recursion with precedence + parenthesization
#guard GradedMulti.evalArith "2+3*4" == 14        -- 2 + (3*4)
#guard GradedMulti.evalArith "(2+3)*4" == 20      -- (2+3) * 4
#guard GradedMulti.evalArith "2*3+4*5" == 26      -- (2*3) + (4*5)
#guard GradedMulti.evalArith "((1+2)*(3+4))" == 21