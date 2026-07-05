import PrimParser.Basic

/-!
# PrimParser Lawfulness Proofs

Lawful instances for `Success`, `Outcome`, and `Parser`:
`LawfulFunctor`, `LawfulGradedFunctor`, `LawfulGradedApplicative`, `LawfulGradedMonad`.
-/

namespace Parser

variable
  {α β γ ε : Type}
  {n : Nat}
  {g : Grade}
  {ge gc : Necessity}

instance : LawfulFunctor (Success n gc) where
  map_const := rfl
  id_map x := by cases x; rfl
  comp_map g h x := by cases x; rfl

instance : LawfulFunctor (Outcome ε n g) where
  map_const := by simp [Functor.mapConst, Functor.map]
  id_map x := by
    rcases g with ⟨ge, gc⟩; cases ge <;> simp [Outcome] at x
    · apply id_map x
    · simp [Functor.map]
    · apply id_map x
  comp_map {α} β γ f h x := by
    rcases g with ⟨ge, gc⟩; cases ge <;> simp [Outcome] at x
    · cases x <;> simp [Functor.map, Sum.bind]
    · simp [Functor.map]
    · apply comp_map f h x

instance : LawfulGradedFunctor (Success n) where
  gmap_id x := by cases x; rfl
  gmap_comp g h x := by cases x; rfl

instance : LawfulGradedFunctor (Parser ε) where
  gmap_comp := by intro g _ _ _ f h p; simp [GradedFunctor.gmap]; ext n t; congr
  gmap_id := by intro g α ⟨p⟩; simp [GradedFunctor.gmap]

theorem gbind_assoc
  {ge1 gc1 ge2 gc2 ge3 gc3 : Necessity}
  (p1 : Parser ε ⟨ge1, gc1⟩ α)
  (p2 : α → Parser ε ⟨ge2, gc2⟩ β)
  (p3 : β → Parser ε ⟨ge3, gc3⟩ γ)
  : (p1 >>=ᵍ p2 >>=ᵍ p3) ≍ (p1 >>=ᵍ fun a => p2 a >>=ᵍ p3) := by
  obtain ⟨p⟩ := p1
  cases ge1
  · case possibly =>
    simp [gbind, bind]
    congr 1
    · grind
    · refine Function.hfunext rfl ?_; intro _ _ .rfl
      refine Function.hfunext rfl ?_; intro t _ .rfl
      cases ge2 <;> simp
      · cases p t <;> simp [Outcome.throwFailure, Success.bindParser]
        · cases ge3 <;> simp <;> congr 2 <;> apply max_assoc
        · next v =>
          cases ge3 <;> simp
          · cases p2 v.result |>.run v.restText <;> simp [Success.seq]
            · congr 2; apply max_assoc
            · next v =>
              cases p3 v.result |>.run v.restText <;> simp
              · congr 2; apply max_assoc
              · congr 2
                · apply max_assoc
                · apply max_assoc
                · apply proof_irrel_heq
          · cases p2 v.result |>.run v.restText <;> simp [Success.seq]
            · congr
          · cases p2 v.result |>.run v.restText <;> simp [Success.seq]
            · congr 2; apply max_assoc
            · congr 2
              · apply max_assoc
              · apply max_assoc
              · apply proof_irrel_heq
      · cases p t <;> simp [Outcome.throwFailure, Success.bindParser]
      · cases p t <;> simp [Outcome.throwFailure, Success.bindParser]
        · cases ge3 <;> simp <;> congr 2 <;> apply max_assoc
        · next v =>
          cases ge3 <;> simp [Success.seq]
          · case possibly =>
            cases p3 (p2 v.result |>.run v.restText).result |>.run
              (p2 v.result |>.run v.restText).restText <;> simp
            · congr 2; apply max_assoc
            · congr 2
              · apply max_assoc
              · apply max_assoc
              · apply proof_irrel_heq
          · case always => congr
          · case never =>
            congr 2
            · apply max_assoc
            · apply max_assoc
            · apply proof_irrel_heq
  · case always => simp [gbind, bind]; congr 1; grind
  · case never =>
    simp [gbind, bind]
    congr 1
    · grind
    · cases ge2 <;> simp
      · case possibly =>
        refine Function.hfunext rfl ?_; intro _ _ .rfl
        refine Function.hfunext rfl ?_; intro t _ .rfl
        simp [Success.bindParser, Success.seq]
        cases ge3 <;> simp
        · case possibly =>
          cases p2 (p t).result |>.run (p t).restText <;> simp [Outcome.throwFailure]
          · congr 2; cases gc1 <;> cases gc2 <;> cases gc3 <;> simp
          · next v =>
            cases p3 v.result |>.run v.restText <;> simp
              <;> congr 2 <;> cases gc1 <;> cases gc2 <;> cases gc3 <;> simp
        · case always =>
          cases p2 (p t).result |>.run (p t).restText <;> simp
          · rfl
          · rfl
        · case never =>
          cases p2 (p t).result |>.run (p t).restText <;> simp [Outcome.throwFailure]
          · congr 2; cases gc1 <;> cases gc2 <;> cases gc3 <;> simp
          · congr 2 <;> · cases gc1 <;> cases gc2 <;> cases gc3 <;> simp
      · case always => ext n a; simp [Success.bindParser]
      · case never =>
        cases ge3
        · case possibly =>
          refine Function.hfunext rfl ?_; intro _ _ .rfl
          refine Function.hfunext rfl ?_; intro t _ .rfl
          simp [Success.bindParser, Success.seq]
          cases p3 (p2 (p t).result |>.run (p t).restText).result |>.run
            (p2 (p t).result |>.run (p t).restText).restText <;> simp
          · congr 1; cases gc1 <;> cases gc2 <;> cases gc3 <;> simp
          · congr 1 <;> cases gc1 <;> cases gc2 <;> cases gc3 <;> simp
        · case always =>
          simp [Success.bindParser, Success.seq]
          ext; congr
        · case never =>
          simp [Success.bindParser, Success.seq]
          refine Function.hfunext rfl ?_; intro _ _ .rfl
          refine Function.hfunext rfl ?_; intro _ _ .rfl
          congr 1
          · cases gc1 <;> cases gc2 <;> cases gc3 <;> simp
          · apply proof_irrel_heq

set_option pp.explicit true
instance : LawfulGradedApplicative (Parser ε) where
  gmap_gpure := by intro _ _ _ _; congr
  gpure_gseq := by
    intro ⟨ge, gc⟩ α β f ⟨p⟩
    simp [GradedFunctor.gmap, GradedApplicative.gseq, bind, gpure]
    ext n t
    simp [Success.bindParser]
    cases ge <;> simp
    · cases p t <;> simp
      · simp! [Functor.map]
      · simp [Functor.map, Sum.bind, Success.seq]
    · cases p t; simp [Functor.map, Success.seq]

  gseq_gpure := by
    intro ⟨ge, gc⟩ α β ⟨p⟩ a
    cases ge <;> cases gc <;> simp [GradedFunctor.gmap, GradedApplicative.gseq, bind, gpure] <;> funext n t
      <;> simp [Functor.map, Success.bindParser, Success.seq, Outcome.throwFailure, Sum.bind]
      <;> cases p t <;> simp

  gseq_assoc := by
    intro ⟨ge1, gc1⟩ ⟨ge2, gc2⟩ ⟨ge3, gc3⟩ α β γ ⟨p1⟩ ⟨p2⟩ ⟨p3⟩
    cases ge1
    · case possibly =>
      simp [GradedApplicative.gseq, bind]
      congr 1
      · grind
      · refine Function.hfunext rfl ?_; intro _ _ .rfl
        refine Function.hfunext rfl ?_; intro t1 t2 .rfl
        cases ge2 <;> simp [GradedFunctor.gmap, Functor.map, Sum.bind]
        · cases p1 t1 <;> simp [Outcome.throwFailure, Success.bindParser]
          · cases ge3 <;> simp <;> congr 2 <;> apply max_assoc
          · next v =>
            cases ge3 <;> simp
            · case possibly =>
              cases p2 (Success.restText v) <;> simp [Success.seq]
              · congr 2; apply max_assoc
              · next v =>
                cases p3 (Success.restText v) <;> simp
                · congr 2; apply max_assoc
                · congr 2
                  · apply max_assoc
                  · apply max_assoc
                  · apply proof_irrel_heq
            · case always =>
                cases p2 (Success.restText v) <;> simp [Success.seq]; congr
            · case never =>
              cases p2 (Success.restText v) <;> simp [Success.seq]
              · congr 2; apply max_assoc
              · congr 2
                · apply max_assoc
                · apply max_assoc
                · apply proof_irrel_heq
        · cases p1 t1 <;> simp [Outcome.throwFailure, Success.bindParser]
        · cases p1 t1 <;> simp [Outcome.throwFailure, Success.bindParser]
          · cases ge3 <;> simp <;> congr 2 <;> apply max_assoc
          · next v =>
            cases ge3 <;> simp [Success.seq]
            · case possibly =>
              cases p3 (Success.restText (p2 (Success.restText v))) <;> simp
              · congr 2; apply max_assoc
              · congr 2
                · apply max_assoc
                · apply max_assoc
                · apply proof_irrel_heq
            · case always => congr
            · case never =>
              congr 2
              · apply max_assoc
              · apply max_assoc
              · apply proof_irrel_heq
    · case always => simp [GradedApplicative.gseq, bind]; congr 1; grind
    · case never =>
      simp [GradedApplicative.gseq, bind]
      congr 1
      · grind
      · cases ge2 <;> simp
        · case possibly =>
          refine Function.hfunext rfl ?_; intro _ _ .rfl
          refine Function.hfunext rfl ?_; intro t1 t2 .rfl
          simp [GradedFunctor.gmap, Functor.map, Success.bindParser, Sum.bind, Success.seq]
          cases ge3 <;> simp
          · case possibly =>
            cases p2 (Success.restText (p1 t1)) <;> simp [Outcome.throwFailure]
            · congr 2; cases gc1 <;> cases gc2 <;> cases gc3 <;> simp
            · next v =>
              cases p3 (Success.restText v) <;> simp
                <;> congr 2 <;> cases gc1 <;> cases gc2 <;> cases gc3 <;> simp
          · case always =>
            cases p2 (Success.restText (p1 t1)) <;> simp
            · rfl
            · rfl
          · case never =>
            cases p2 (Success.restText (p1 t1)) <;> simp [Outcome.throwFailure]
            · congr 2; cases gc1 <;> cases gc2 <;> cases gc3 <;> simp
            · congr 2 <;> · cases gc1 <;> cases gc2 <;> cases gc3 <;> simp
        · case always => ext n a; simp [GradedFunctor.gmap, Functor.map, Success.bindParser]
        · case never =>
          cases ge3
          · case possibly =>
            refine Function.hfunext rfl ?_; intro _ _ .rfl
            refine Function.hfunext rfl ?_; intro t1 t2 .rfl
            simp [GradedFunctor.gmap, Functor.map, Success.bindParser, Sum.bind, Success.seq]
            cases p3 (Success.restText (p2 (Success.restText (p1 t1)))) <;> simp
            · congr 1; cases gc1 <;> cases gc2 <;> cases gc3 <;> simp
            · congr 1 <;> cases gc1 <;> cases gc2 <;> cases gc3 <;> simp
          · case always =>
            simp [GradedFunctor.gmap, Functor.map, Success.bindParser]
            ext n t; congr
          · case never =>
            simp [Success.bindParser, Success.seq, Functor.map, GradedFunctor.gmap]
            refine Function.hfunext rfl ?_; intro _ _ .rfl
            refine Function.hfunext rfl ?_; intro _ _ .rfl
            congr 1
            · cases gc1 <;> cases gc2 <;> cases gc3 <;> simp
            · apply proof_irrel_heq

instance : LawfulGradedMonad (Parser ε) where
  gpure_gbind := by
    intro ⟨ge, gc⟩ _ _ a f
    cases ge <;> simp [gpure, gbind, bind, Success.bindParser, Success.seq] <;> try (rcases f a with ⟨run'⟩; simp)
    · ext n t; cases run' t; simp; congr 2
    · congr

  gbind_gpure := by
    intro ⟨ge, gc⟩ _ ⟨p⟩
    simp [gpure, gbind, bind]
    congr 1
    · simp [OfNat.ofNat, One.one]
    · refine Function.hfunext rfl ?_; intro _ _ .rfl
      refine Function.hfunext rfl ?_; intro t _ .rfl
      cases ge <;> simp [Outcome.throwFailure, Success.bindParser, Success.seq]
      · case possibly =>
        cases p t <;> simp
        · congr 2; simp [OfNat.ofNat, One.one]
        · congr 2
          · simp [OfNat.ofNat, One.one]
          · simp [OfNat.ofNat, One.one]
          · apply proof_irrel_heq
      · case never =>
        cases p t; simp
        congr
        · simp [OfNat.ofNat, One.one]
        · apply proof_irrel_heq

  gbind_assoc := Parser.gbind_assoc

end Parser
