import PrimParser.Graded
import PrimParser.Run
import PrimParser.Properties

/-!
# PrimParser.GradedDeep — a lawful semantics for the deep graded backend

`Graded.G` is a reified, `Grade`-indexed grammar run by a fast *fuel* interpreter.
That interpreter is deliberately **not** a `LawfulGradedMonad`: bind-associativity
provably fails for it (the `alt` fuel-monotonicity counterexample, see `Graded`).

Here we give `G` a **denotational** semantics into the shallow `Parser`, which *is*
a `LawfulGradedMonad` (see `Parser.instLawfulGradedMonad`). `denote` is a graded-monad
homomorphism, so every `G` program obeys the graded-monad laws **up to denotational
equivalence** `≋` (`denote`-equality). The mandatory `LawfulGradedMonad` therefore
holds on the semantic domain, and transports to `G` through `denote`.

The fuel interpreter is kept as the fast execution path.
-/

open Parser

namespace Graded

/-- Byte → `Char` (round-trips with `ofChar` on `0..255`). -/
@[inline] def toChar (b : UInt8) : Char := Char.ofNat b.toNat
/-- `Char` → byte (inverse of `toChar` on the byte range). -/
@[inline] def ofChar (c : Char) : UInt8 := UInt8.ofNat c.toNat

/-- **Denotation**: compile a reified grammar into the shallow, lawful `Parser`.
`self` denotes the single fixpoint node `recur`; the top-level entry point ties the
knot with `Parser.fix` (see `denoteTop`). Byte-level primitives are read through the
`Char`↔byte bridge. -/
def G.denote {ρ} (self : Parser Error conditional ρ) :
    {g : Grade} → {α : Type} → G ρ g α → Parser Error g α
  | _, _, .pure a       => Parser.pure a
  | _, _, .fail         => Parser.throw Error.fail
  | _, _, .byte f       => ofChar <$>ᵍ Parser.satisfy (fun c => f (ofChar c))
  | _, _, .lit c        => Parser.char (toChar c)
  | _, _, .chars1 f     => Parser.skipWhile1 (fun c => f (ofChar c))
  | _, _, .chars0 f     => Parser.skipWhile (fun c => f (ofChar c))
  | _, _, .nat          => Parser.nat
  | _, _, .takeN n      => Parser.skip n Parser.anyChar
  | _, _, .map f a      => f <$>ᵍ G.denote self a
  | _, _, .map2 f a b   => G.denote self a >>=ᵍ fun x => f x <$>ᵍ G.denote self b
  | _, _, .seqR a b     => G.denote self a >>=ᵍ fun _ => G.denote self b
  | _, _, .seqL a b     => G.denote self a >>=ᵍ fun x => (fun _ => x) <$>ᵍ G.denote self b
  | _, _, .alt a b      => G.denote self a <|> G.denote self b
  | _, _, .star a       => Parser.many (G.denote self a)
  | _, _, .starFold f acc a => (fun xs => xs.foldl f acc) <$>ᵍ Parser.many (G.denote self a)
  | _, _, .bind m k     => G.denote self m >>=ᵍ fun a => G.denote self (k a)
  | _, _, .recur        => self

/-- Top-level denotation: tie the `recur` knot with the shallow `Parser.fix`. The
fuel interpreter (`Graded.run`) is the fast path; this is the lawful reference. -/
def denoteTop {ρ} (top : G ρ conditional ρ) : Parser Error conditional ρ :=
  Parser.fix (fun self => G.denote self top)

/-! ### `denote` is a graded-monad homomorphism (definitional). -/

variable {ρ : Type} (self : Parser Error conditional ρ)

@[simp] theorem denote_pure {α} (a : α) :
    G.denote self (.pure a) = Parser.pure a := rfl

@[simp] theorem denote_map {g α β} (f : α → β) (a : G ρ g α) :
    G.denote self (.map f a) = f <$>ᵍ G.denote self a := rfl

@[simp] theorem denote_bind {g g' α β} (m : G ρ g α) (k : α → G ρ g' β) :
    G.denote self (.bind m k) = G.denote self m >>=ᵍ fun a => G.denote self (k a) := rfl

@[simp] theorem denote_seqR {g g' α β} (a : G ρ g α) (b : G ρ g' β) :
    G.denote self (.seqR a b) = G.denote self a >>=ᵍ fun _ => G.denote self b := rfl

@[simp] theorem denote_seqL {g g' α β} (a : G ρ g α) (b : G ρ g' β) :
    G.denote self (.seqL a b) = G.denote self a >>=ᵍ fun x => (fun _ => x) <$>ᵍ G.denote self b := rfl

@[simp] theorem denote_alt {g g' α} (a : G ρ g α) (b : G ρ g' α) :
    G.denote self (.alt a b) = Parser.choice (G.denote self a) (G.denote self b) := rfl

@[simp] theorem denote_star {ge α} (a : G ρ ⟨ge, always⟩ α) :
    G.denote self (.star a) = Parser.many (G.denote self a) := rfl

@[simp] theorem denote_recur :
    G.denote self (.recur) = self := rfl

/-! ### The graded-monad laws hold for `G` up to denotational equivalence

Because `denote` is a homomorphism into the lawful `Parser`, the three
`LawfulGradedMonad` laws transport to the reified grammar `G`, stated as
`≍`-equalities of the denotations (the grades differ by the monoid identity /
associator, exactly as in the class). The semantic domain `Parser` is itself a
genuine `LawfulGradedMonad` (`Parser.instLawfulGradedMonad`), so these are the
deep backend's monad laws, proven — what the fuel interpreter cannot satisfy. -/

/-- Left identity for the deep backend (up to denotation). -/
theorem denote_gpure_gbind {j α β} (x : α) (f : α → G ρ j β) :
    G.denote self (.bind (.pure x) f) ≍ G.denote self (f x) := by
  rw [denote_bind, denote_pure]
  exact LawfulGradedMonad.gpure_gbind x (fun a => G.denote self (f a))

/-- Right identity for the deep backend (up to denotation). -/
theorem denote_gbind_gpure {i α} (m : G ρ i α) :
    G.denote self (.bind m .pure) ≍ G.denote self m := by
  rw [denote_bind]
  exact LawfulGradedMonad.gbind_gpure (G.denote self m)

/-- Associativity for the deep backend (up to denotation) — the law that
provably **fails** for the fuel interpreter, recovered here via the denotation. -/
theorem denote_gbind_assoc {i j k α β γ}
    (m : G ρ i α) (f : α → G ρ j β) (g : β → G ρ k γ) :
    G.denote self (.bind (.bind m f) g)
      ≍ G.denote self (.bind m (fun a => .bind (f a) g)) := by
  simp only [denote_bind]
  exact LawfulGradedMonad.gbind_assoc (G.denote self m)
    (fun a => G.denote self (f a)) (fun b => G.denote self (g b))

/-- Denotational equivalence of grammars: same meaning as shallow parsers. The
three theorems above are exactly its graded-monad-law congruences, so `G` is a
lawful graded monad **in the quotient by `DEquiv`** (equivalently, through the
homomorphism `denote` into the lawful `Parser`). -/
def DEquiv {g α} (a b : G ρ g α) : Prop := G.denote self a = G.denote self b

theorem DEquiv.refl {g α} (a : G ρ g α) : DEquiv self a a := rfl
theorem DEquiv.symm {g α} {a b : G ρ g α} : DEquiv self a b → DEquiv self b a := Eq.symm
theorem DEquiv.trans {g α} {a b c : G ρ g α} :
    DEquiv self a b → DEquiv self b c → DEquiv self a c := Eq.trans

end Graded

/-- **The mandatory law, discharged.** The deep backend's denotational domain is a
genuine `LawfulGradedMonad`; `Graded.denote` is a homomorphism into it, so every
reified grammar obeys the graded-monad laws up to `Graded.DEquiv`. This is the law
that provably fails for `Graded`'s fuel interpreter. -/
theorem Graded.semantics_lawful : LawfulGradedMonad (Parser Error) := inferInstance

namespace Graded

/-! ### Combinator zoo for the deep backend

The reified `G` already ships `gmany`, `gmany1`, `gsepBy`, `gsepBy1`. Here we grow
the surface toward `Parser`'s zoo, all as *derived* smart constructors (no new GADT
nodes). Each denotes — through `denote` — to the corresponding shallow combinator,
so the deep versions inherit the shallow laws.

Combinators that need lookahead/position (`eof`, `peek`, `notFollowedBy`,
`lookahead`, `getOffset`) are *not* derivable: `G` has no non-consuming primitive.
They would each require a new GADT node + interpreter clause. -/

variable {ρ : Type}

/-- Try `a`; `some` on success, `none` on failure. Never fails. -/
@[inline] def goptional {g α} (a : G ρ g α) : G ρ (g.choice Grade.pure) (Option α) :=
  .alt (.map some a) (.pure none)

/-- Try `a`; its result or a default `d`. -/
@[inline] def goptionalD {g α} (a : G ρ g α) (d : α) : G ρ (g.choice Grade.pure) α :=
  .map (fun o => o.getD d) (goptional a)

/-- Did `a` succeed? -/
@[inline] def gtest {g α} (a : G ρ g α) : G ρ (g.choice Grade.pure) Bool :=
  .map (fun o => o.isSome) (goptional a)

/-- Zero-or-more, discarding results. -/
@[inline] def gskipMany {ge α} (a : G ρ ⟨ge, always⟩ α) : G ρ flexible PUnit :=
  .map (fun _ => ⟨⟩) (.star a)

/-- One-or-more, discarding results. -/
@[inline] def gskipMany1 {ge α} (a : G ρ ⟨ge, always⟩ α) :=
  G.map (fun _ => (⟨⟩ : PUnit)) (gmany1 a)

/-- `c` between openers/closers: `l *> c <* r`. -/
@[inline] def gbetween {gl gr g α β γ}
    (l : G ρ gl α) (r : G ρ gr β) (c : G ρ g γ) :=
  G.seqR l (G.seqL c r)

/-- One-or-more `p` folded through a left-associative operator `op`. -/
def gchainl1 {ge ge' α} (op : G ρ ⟨ge', always⟩ (α → α → α)) (p : G ρ ⟨ge, always⟩ α) :=
  G.map2 (fun x rest => rest.foldl (fun acc (fy : (α → α → α) × α) => fy.1 acc fy.2) x) p
    (G.star (G.map2 (fun f y => (f, y)) op p))

/-- A single decimal digit's value. -/
@[inline] def gdigit : G ρ conditional Nat :=
  .map (fun b => b.toNat - 48) (.byte bDigit)

/-! #### The derived combinators denote to shallow combinators (homomorphism). -/

variable (self : Parser Error conditional ρ)

@[simp] theorem denote_goptional {g α} (a : G ρ g α) :
    G.denote self (goptional a)
      = Parser.choice (some <$>ᵍ G.denote self a) (Parser.pure none) := rfl

@[simp] theorem denote_gskipMany {ge α} (a : G ρ ⟨ge, always⟩ α) :
    G.denote self (gskipMany a) = (fun _ => ⟨⟩) <$>ᵍ Parser.many (G.denote self a) := rfl

@[simp] theorem denote_gbetween {gl gr g α β γ}
    (l : G ρ gl α) (r : G ρ gr β) (c : G ρ g γ) :
    G.denote self (gbetween l r c)
      = G.denote self l >>=ᵍ fun _ =>
          G.denote self c >>=ᵍ fun x => (fun _ => x) <$>ᵍ G.denote self r := rfl

end Graded

namespace Graded

/-! ### Genuine graded-monad class instances for the deep backend

`G` itself cannot instantiate the graded classes: it lives in `Type 1` (its
constructors quantify over `α : Type`), while `GradedType Grade = Grade → Type →
Type` is `Type 0`-valued. Its **denotational image** is `Type 0`, though, and
*is* a graded monad:

  `DImg self g α := { p : Parser Error g α // ∃ gram, denote self gram = p }`

i.e. the sub-graded-monad of `Parser` generated by reified grammars. Its
operations are `Parser`'s (on the value component), so the `Lawful` laws are
inherited from `Parser` by `Subtype.ext` — the reified data's failure of
value-equality is quotiented away by working with meanings, not syntax. -/

variable {ρ : Type} (self : Parser Error conditional ρ)

@[simp] theorem denote_map2 {g g' α β γ} (f : α → β → γ) (a : G ρ g α) (b : G ρ g' β) :
    G.denote self (.map2 f a b) = G.denote self a >>=ᵍ fun x => f x <$>ᵍ G.denote self b := rfl

/-- The denotational image of the deep backend: shallow parsers arising from some
reified grammar. A `Type 0` graded family, so it carries the graded classes. -/
def DImg (g : Grade) (α : Type) : Type :=
  { p : Parser Error g α // ∃ gram : G ρ g α, G.denote self gram = p }

namespace DImg

/-- Embed a grammar into the image. -/
@[inline] def of {g α} (gram : G ρ g α) : DImg self g α := ⟨G.denote self gram, gram, rfl⟩

instance : GradedFunctor (DImg self) where
  gmap {_ _ _} h x := ⟨h <$>ᵍ x.1, G.map h x.2.choose, by rw [denote_map, x.2.choose_spec]⟩

instance : GradedApplicative (DImg self) where
  gpure {_} a := ⟨Parser.pure a, G.pure a, rfl⟩
  gseq {_ _ _ _} u th := ⟨u.1 <*>ᵍ (fun () => (th ()).1),
    G.map2 (fun f x => f x) u.2.choose (th ()).2.choose, by
      rw [denote_map2, u.2.choose_spec, (th ()).2.choose_spec, Parser.gseq_eq_gbind]⟩

instance : GradedMonad (DImg self) where
  gbind {_ _ _ _} m k := ⟨m.1 >>=ᵍ fun a => (k a).1,
    G.bind m.2.choose (fun a => (k a).2.choose), by
      rw [denote_bind, m.2.choose_spec]
      exact congrArg _ (funext fun a => (k a).2.choose_spec)⟩

/-- Transport a value-equality to a `≍` across a grade equality: the image's laws
follow from `Parser`'s because a `DImg` element is determined by its value (the
`∃`-witness is a `Prop`). -/
theorem heq_of_val {g1 g2 α} (h : g1 = g2)
    {x : DImg self g1 α} {y : DImg self g2 α} (hv : x.1 ≍ y.1) : x ≍ y := by
  subst h; exact heq_of_eq (Subtype.ext (eq_of_heq hv))

instance : LawfulGradedFunctor (DImg self) where
  gmap_id x := Subtype.ext (LawfulGradedFunctor.gmap_id x.1)
  gmap_comp g h x := Subtype.ext (LawfulGradedFunctor.gmap_comp g h x.1)

instance : LawfulGradedApplicative (DImg self) where
  gmap_gpure g x := Subtype.ext (LawfulGradedApplicative.gmap_gpure g x)
  gpure_gseq {i _ _} g x := heq_of_val self (one_mul i) (LawfulGradedApplicative.gpure_gseq g x.1)
  gseq_gpure {i _ _} u x := heq_of_val self (mul_one i) (LawfulGradedApplicative.gseq_gpure u.1 x)
  gseq_assoc {i j k _ _ _} u v w :=
    heq_of_val self (mul_assoc i j k) (LawfulGradedApplicative.gseq_assoc u.1 v.1 w.1)

instance : LawfulGradedMonad (DImg self) where
  gpure_gbind {j _ _} x f := heq_of_val self (one_mul j) (LawfulGradedMonad.gpure_gbind x (fun a => (f a).1))
  gbind_gpure {i _} x := heq_of_val self (mul_one i) (LawfulGradedMonad.gbind_gpure x.1)
  gbind_assoc {i j k _ _ _} x f g :=
    heq_of_val self (mul_assoc i j k)
      (LawfulGradedMonad.gbind_assoc x.1 (fun a => (f a).1) (fun b => (g b).1))

/-- **The mandatory law, as a genuine class instance.** The deep backend's `Type 0`
denotational image `DImg` is a `LawfulGradedMonad` (hence applicative and functor)
— not merely lawful up to `≍`. `G` itself cannot be one (it is `Type 1`, and its
reified trees are not value-equal); `DImg` is its sub-graded-monad of meanings. -/
theorem lawful (self : Parser Error conditional ρ) : LawfulGradedMonad (DImg self) :=
  inferInstance

end DImg
end Graded

/-! ### Runtime sanity

The deep zoo executes, and the fast **fuel** interpreter (`Graded.runTop`) agrees
with the lawful **denotation** (`Graded.denoteTop` run as a shallow `Parser`) on
these samples. A full operational-equivalence proof is left as future work. -/
section
open Parser Graded

#guard runTop gnat "123" == 123
#guard (denoteTop gnat).parse? "123" == some 123
#guard (denoteTop gnat).parse? "" == none
#guard (denoteTop (gdigit (ρ := Nat))).parse? "7" == some 7
-- fuel fast-path and denotation agree on the well-fuelled deterministic fragment:
#guard runTop gnat "42" == ((denoteTop gnat).parse? "42").getD 0

/-- A sequential sample (`lit 'x'` then `nat`): fuel path = denotation. -/
def seqSample : Graded.G Nat conditional Nat := .seqR (.lit (Graded.ch 'x')) .nat
#guard runTop seqSample "x42" == 42
#guard (denoteTop seqSample).parse? "x42" == some 42

end

/-! ### Phase E — operational soundness: what holds, and the sharp obstruction

The `#guard`s above witness `fuel-run = denotation` on the *well-fuelled
deterministic* fragment. A **fully general** `G.run ≈ denote` at any fixed fuel is
*false*, and for the same structural reason that bind-associativity fails for the
fuel interpreter: success is **not fuel-monotone**, because `alt` commits to its
right branch when the left one merely *runs out of fuel*.

We make this a checked theorem rather than prose. `cex = alt L (pure 999)` where
`L` needs fuel ≥ 3 (two nested `map`s over a `byte`):

* at fuel 2, `L` fuel-exhausts (a spurious failure) and `alt` yields `999`;
* at fuel 5, `L` succeeds and `alt` yields the real byte value `65`.

Same grammar, same input, different results — so no fixed-fuel reading can equal
the (deterministic, fuel-free) denotation on grammars containing `alt`/`star`/
`recur`. A conditional soundness theorem (*with enough fuel*, on the
backtracking-free fragment) is possible but additionally blocked from a clean
structural proof by the byte↔`Char` bridge running through `Parser`'s **private**
`scanWhile`/`natScan` (for `nat`/`chars0`/`chars1`). Hence: soundness holds on the
deterministic fragment (evidenced), and is provably unattainable in general. -/
namespace Graded.PhaseE
open Parser Graded

/-- Left branch costs fuel ≥ 3; right branch is immediate. -/
def cex : G Nat (Grade.choice conditional Grade.pure) Nat :=
  .alt (.map (fun (b : UInt8) => b.toNat) (.map (fun b => b) (.byte (fun _ => true))))
       (.pure 999)

@[inline] def resVal (r : Res Nat) : Nat := match r with | .ok v _ => v | .err _ => 0

-- concrete disagreement (spurious fuel-failure of the left branch):
#guard resVal (G.run "A".toUTF8 gnat 2 cex 0) == 999
#guard resVal (G.run "A".toUTF8 gnat 5 cex 0) == 65

/-- **Success is not fuel-monotone**: the same grammar and input give different
results at different fuel. Consequently no fixed-fuel `G.run` can equal the
deterministic denotation on grammars with `alt` — the operational counterpart of
the bind-associativity failure. -/
theorem fuel_not_monotone :
    resVal (G.run "A".toUTF8 gnat 2 cex 0) ≠ resVal (G.run "A".toUTF8 gnat 5 cex 0) := by
  decide

end Graded.PhaseE

