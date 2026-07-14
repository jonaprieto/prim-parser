import PrimParser.Basic
open Parser

/-!
# PrimParser.Graded — deep-embedded graded-monad parser framework

A second backend for the graded monad, living alongside the shallow `Parser`. The
grammar is **reified as data** (`G`, a `Grade`-indexed GADT) and executed by one
**total** fuel interpreter. The applicative fragment is pure data (fast); `gbind`
adds a genuine graded monadic bind (closure, pay-per-use). Byte-backed
(`ByteArray`) — the same representation angstrom uses.

The grade discipline is enforced at construction (an ill-graded grammar does not
typecheck — e.g. `gmany` demands an always-consuming body). Totality is by
structural recursion on a fuel bound.
-/

namespace Graded

@[inline] def bBetween (lo hi b : UInt8) : Bool := Nat.ble lo.toNat b.toNat && Nat.ble b.toNat hi.toNat
@[inline] def bDigit (b : UInt8) : Bool := bBetween 48 57 b
@[inline] def bAlnum (b : UInt8) : Bool := bDigit b || bBetween 65 90 b || bBetween 97 122 b
@[inline] def bAlpha (b : UInt8) : Bool := bBetween 65 90 b || bBetween 97 122 b
@[inline] def bWs (b : UInt8) : Bool := b == 32 || b == 10 || b == 9 || b == 13
@[inline] def ch (c : Char) : UInt8 := UInt8.ofNat c.toNat

/-- A reified graded parser producing `α`, with static grade `g`. `ρ` is the result
type of the single fixpoint the grammar recurses into (`recur`). -/
inductive G (ρ : Type) : Grade → Type → Type 1 where
  | pure {α} (a : α) : G ρ Grade.pure α
  | fail {α} : G ρ empty α
  | byte (f : UInt8 → Bool) : G ρ conditional UInt8            -- one byte satisfying f
  | lit (c : UInt8) : G ρ conditional PUnit
  | chars1 (f : UInt8 → Bool) : G ρ conditional PUnit          -- one+ matching bytes (skip)
  | chars0 (f : UInt8 → Bool) : G ρ flexible PUnit             -- zero+ matching bytes (skip)
  | nat : G ρ conditional Nat
  | takeN (n : Nat) : G ρ fallible PUnit                       -- up to n bytes (may consume 0; context-sensitive)
  | map {g α β} (f : α → β) (a : G ρ g α) : G ρ g β
  | map2 {g g' α β γ} (f : α → β → γ) (a : G ρ g α) (b : G ρ g' β) : G ρ (g * g') γ
  | seqR {g g' α β} (a : G ρ g α) (b : G ρ g' β) : G ρ (g * g') β
  | seqL {g g' α β} (a : G ρ g α) (b : G ρ g' β) : G ρ (g * g') α
  | alt {g g' α} (a : G ρ g α) (b : G ρ g' α) : G ρ (g.choice g') α
  | star {ge α} (a : G ρ ⟨ge, always⟩ α) : G ρ flexible (List α)
  | starFold {ge α β} (f : β → α → β) (acc : β) (a : G ρ ⟨ge, always⟩ α) : G ρ flexible β  -- fold `a*` into `acc`, no list
  | bind {g g' α β} (m : G ρ g α) (k : α → G ρ g' β) : G ρ (g * g') β   -- graded monadic bind
  | recur : G ρ conditional ρ

/-- Interpreter result: success with new position, or failure with the furthest
byte position reached (for error messages). -/
inductive Res (α : Type) where
  | ok (val : α) (pos : Nat) : Res α
  | err (furthest : Nat) : Res α

@[inline] def scanB (arr : ByteArray) (pred : UInt8 → Bool) : Nat → Nat → Nat
  | 0, o => o
  | fuel+1, o => if o < arr.size && pred arr[o]! then scanB arr pred fuel (o+1) else o

def scanNatB (arr : ByteArray) (acc : Nat) : Nat → Nat → Nat × Nat
  | 0, o => (acc, o)
  | fuel+1, o =>
    if o < arr.size && bDigit arr[o]! then scanNatB arr (acc*10 + (arr[o]!.toNat - 48)) fuel (o+1)
    else (acc, o)

/-- Total fuel interpreter (structural recursion on `fuel`). -/
def G.run (arr : ByteArray) {ρ} (top : G ρ conditional ρ)
    : Nat → {g : Grade} → {α : Type} → G ρ g α → Nat → Res α
  | 0, _, _, _, off => .err off
  | fuel+1, g, α, gram, off => match gram with
    | .pure a => .ok a off
    | .fail => .err off
    | .byte f => if off < arr.size && f arr[off]! then .ok arr[off]! (off+1) else .err off
    | .lit c => if off < arr.size && arr[off]! == c then .ok ⟨⟩ (off+1) else .err off
    | .chars1 f => if off < arr.size && f arr[off]! then .ok ⟨⟩ (scanB arr f arr.size (off+1)) else .err off
    | .chars0 f => .ok ⟨⟩ (scanB arr f arr.size off)
    | .nat => if off < arr.size && bDigit arr[off]! then let (v, o) := scanNatB arr 0 arr.size off; .ok v o else .err off
    | .takeN n => if Nat.ble (off + n) arr.size then .ok ⟨⟩ (off + n) else .err off
    | .map f a => match G.run arr top fuel a off with | .ok x o => .ok (f x) o | .err e => .err e
    | .map2 f a b => match G.run arr top fuel a off with
      | .ok x o1 => (match G.run arr top fuel b o1 with | .ok y o2 => .ok (f x y) o2 | .err e => .err e)
      | .err e => .err e
    | .seqR a b => match G.run arr top fuel a off with | .ok _ o1 => G.run arr top fuel b o1 | .err e => .err e
    | .seqL a b => match G.run arr top fuel a off with
      | .ok x o1 => (match G.run arr top fuel b o1 with | .ok _ o2 => .ok x o2 | .err e => .err e)
      | .err e => .err e
    | .alt a b => match G.run arr top fuel a off with
      | .ok x o => .ok x o
      | .err e1 => (match G.run arr top fuel b off with | .ok x o => .ok x o | .err e2 => .err (Nat.max e1 e2))
    | .star a =>
      match G.run arr top fuel a off with
      | .ok x o' =>
        if o' > off then (match G.run arr top fuel (.star a) o' with
          | .ok xs o2 => .ok (x :: xs) o2 | .err _ => .ok [x] o')
        else .ok [x] o'
      | .err _ => .ok [] off
    | .starFold f acc a =>
      match G.run arr top fuel a off with
      | .ok x o' =>
        let acc' := f acc x
        if o' > off then G.run arr top fuel (.starFold f acc' a) o' else .ok acc' o'
      | .err _ => .ok acc off
    | .bind m k => match G.run arr top fuel m off with | .ok x o1 => G.run arr top fuel (k x) o1 | .err e => .err e
    | .recur => G.run arr top fuel top off

/-! ### Grade soundness

`run_mono`: the interpreter never rewinds. `run_consumes`: a grammar whose grade
claims `always`-consume really does advance the position on success — the property
that makes the grade *sound* (not merely enforced at composition). -/

theorem scanB_ge (arr : ByteArray) (f : UInt8 → Bool) :
    ∀ (fuel o : Nat), o ≤ scanB arr f fuel o := by
  intro fuel
  induction fuel with
  | zero => intro o; simp [scanB]
  | succ fuel ih =>
    intro o
    simp only [scanB]
    split
    · have := ih (o+1); omega
    · omega

theorem scanNatB_ge (arr : ByteArray) :
    ∀ (fuel acc o : Nat), o ≤ (scanNatB arr acc fuel o).2 := by
  intro fuel
  induction fuel with
  | zero => intro acc o; simp [scanNatB]
  | succ fuel ih =>
    intro acc o
    simp only [scanNatB]
    split
    · have := ih (acc*10 + (arr[o]!.toNat - 48)) (o+1); omega
    · simp

/-- On success, the position only advances (all grades). -/
theorem run_mono (arr : ByteArray) {ρ} (top : G ρ conditional ρ) :
    ∀ (fuel : Nat) {g : Grade} {α : Type} (gram : G ρ g α) (off v o'),
      G.run arr top fuel gram off = .ok v o' → off ≤ o' := by
  intro fuel
  induction fuel with
  | zero => intro g α gram off v o' h; simp [G.run] at h
  | succ fuel ih =>
    intro g α gram off v o' h
    cases gram with
    | pure a => simp only [G.run] at h; injection h with _ ho; omega
    | fail => simp [G.run] at h
    | byte f =>
      simp only [G.run] at h; split at h
      · injection h with _ ho; omega
      · simp at h
    | lit c =>
      simp only [G.run] at h; split at h
      · injection h with _ ho; omega
      · simp at h
    | chars1 f =>
      simp only [G.run] at h; split at h
      · injection h with _ ho; have := scanB_ge arr f arr.size (off+1); omega
      · simp at h
    | chars0 f =>
      simp only [G.run] at h; injection h with _ ho
      have := scanB_ge arr f arr.size off; omega
    | nat =>
      simp only [G.run] at h; split at h
      · injection h with _ ho; have := scanNatB_ge arr arr.size 0 off; omega
      · simp at h
    | takeN n =>
      simp only [G.run] at h; split at h
      · injection h with _ ho; omega
      · simp at h
    | map f a =>
      simp only [G.run] at h
      cases hi : G.run arr top fuel a off with
      | ok x o => simp only [hi] at h; injection h with _ ho; have := ih a off x o hi; omega
      | err e => simp [hi] at h
    | map2 f a b =>
      simp only [G.run] at h
      cases hia : G.run arr top fuel a off with
      | ok x o1 =>
        simp only [hia] at h
        cases hib : G.run arr top fuel b o1 with
        | ok y o2 => simp only [hib] at h; injection h with _ ho
                     have := ih a off x o1 hia; have := ih b o1 y o2 hib; omega
        | err e => simp [hib] at h
      | err e => simp [hia] at h
    | seqR a b =>
      simp only [G.run] at h
      cases hia : G.run arr top fuel a off with
      | ok x o1 => simp only [hia] at h; have := ih a off x o1 hia; have := ih b o1 v o' h; omega
      | err e => simp [hia] at h
    | seqL a b =>
      simp only [G.run] at h
      cases hia : G.run arr top fuel a off with
      | ok x o1 =>
        simp only [hia] at h
        cases hib : G.run arr top fuel b o1 with
        | ok y o2 => simp only [hib] at h; injection h with _ ho
                     have := ih a off x o1 hia; have := ih b o1 y o2 hib; omega
        | err e => simp [hib] at h
      | err e => simp [hia] at h
    | alt a b =>
      simp only [G.run] at h
      cases hia : G.run arr top fuel a off with
      | ok x o => simp only [hia] at h; injection h with _ ho; have := ih a off x o hia; omega
      | err e1 =>
        simp only [hia] at h
        cases hib : G.run arr top fuel b off with
        | ok y o => simp only [hib] at h; injection h with _ ho; have := ih b off y o hib; omega
        | err e2 => simp [hib] at h
    | star a =>
      simp only [G.run] at h
      cases hia : G.run arr top fuel a off with
      | ok x o2 =>
        simp only [hia] at h
        have hax := ih a off x o2 hia
        split at h
        · cases hib : G.run arr top fuel (G.star a) o2 with
          | ok xs o3 => simp only [hib] at h; injection h with _ ho
                        have := ih (G.star a) o2 xs o3 hib; omega
          | err e => simp only [hib] at h; injection h with _ ho; omega
        · injection h with _ ho; omega
      | err e => simp only [hia] at h; injection h with _ ho; omega
    | starFold f acc a =>
      simp only [G.run] at h
      cases hia : G.run arr top fuel a off with
      | ok x o2 =>
        simp only [hia] at h
        have hax := ih a off x o2 hia
        split at h
        · have := ih (G.starFold f (f acc x) a) o2 v o' h; omega
        · injection h with _ ho; omega
      | err e => simp only [hia] at h; injection h with _ ho; omega
    | bind m k =>
      simp only [G.run] at h
      cases him : G.run arr top fuel m off with
      | ok x o1 => simp only [him] at h; have := ih m off x o1 him; have := ih (k x) o1 v o' h; omega
      | err e => simp [him] at h
    | recur => simp only [G.run] at h; exact ih top off v o' h

theorem gmul_err (a b : Grade) : (a * b).errors = a.errors ⊔ b.errors := by cases a; cases b; simp
theorem gmul_con (a b : Grade) : (a * b).consumes = a.consumes ⊔ b.consumes := by cases a; cases b; simp
theorem gchoice_err (a b : Grade) : (a.choice b).errors = a.errors ⊓ b.errors := by
  cases a; cases b; simp [Grade.choice]
theorem gchoice_con (a b : Grade) : (a.choice b).consumes = a.errors.ite b.consumes a.consumes := by
  cases a; cases b; simp [Grade.choice]

/-- Error-grade soundness: a grammar whose grade claims `always`-error never
succeeds (returns `.err`). Needed for the `alt` case of consume-soundness. -/
theorem run_err (arr : ByteArray) {ρ} (top : G ρ conditional ρ) :
    ∀ (fuel : Nat) {g : Grade} {α : Type} (gram : G ρ g α) (off : Nat),
      g.errors = always → ∃ e, G.run arr top fuel gram off = .err e := by
  intro fuel
  induction fuel with
  | zero => intro g α gram off _; exact ⟨off, by simp [G.run]⟩
  | succ fuel ih =>
    intro g α gram off he
    cases gram with
    | pure a => exact absurd he (by decide)
    | fail => exact ⟨off, by simp [G.run]⟩
    | byte f => exact absurd he (by decide)
    | lit c => exact absurd he (by decide)
    | chars1 f => exact absurd he (by decide)
    | chars0 f => exact absurd he (by decide)
    | nat => exact absurd he (by decide)
    | takeN n => exact absurd he (by decide)
    | star a => exact absurd he (by decide)
    | starFold f acc a => exact absurd he (by decide)
    | recur => exact absurd he (by decide)
    | map f a => obtain ⟨e, hae⟩ := ih a off he; exact ⟨e, by simp only [G.run, hae]⟩
    | map2 f a b =>
      rw [gmul_err, Necessity.max_always] at he
      rcases he with hga | hgb
      · obtain ⟨e, hae⟩ := ih a off hga; exact ⟨e, by simp only [G.run, hae]⟩
      · cases hia : G.run arr top fuel a off with
        | ok x o1 => obtain ⟨e, hbe⟩ := ih b o1 hgb; exact ⟨e, by simp only [G.run, hia, hbe]⟩
        | err e => exact ⟨e, by simp only [G.run, hia]⟩
    | seqR a b =>
      rw [gmul_err, Necessity.max_always] at he
      rcases he with hga | hgb
      · obtain ⟨e, hae⟩ := ih a off hga; exact ⟨e, by simp only [G.run, hae]⟩
      · cases hia : G.run arr top fuel a off with
        | ok x o1 => obtain ⟨e, hbe⟩ := ih b o1 hgb; exact ⟨e, by simp only [G.run, hia, hbe]⟩
        | err e => exact ⟨e, by simp only [G.run, hia]⟩
    | seqL a b =>
      rw [gmul_err, Necessity.max_always] at he
      rcases he with hga | hgb
      · obtain ⟨e, hae⟩ := ih a off hga; exact ⟨e, by simp only [G.run, hae]⟩
      · cases hia : G.run arr top fuel a off with
        | ok x o1 => obtain ⟨e, hbe⟩ := ih b o1 hgb; exact ⟨e, by simp only [G.run, hia, hbe]⟩
        | err e => exact ⟨e, by simp only [G.run, hia]⟩
    | bind m k =>
      rw [gmul_err, Necessity.max_always] at he
      rcases he with hgm | hgk
      · obtain ⟨e, hme⟩ := ih m off hgm; exact ⟨e, by simp only [G.run, hme]⟩
      · cases him : G.run arr top fuel m off with
        | ok x o1 => obtain ⟨e, hke⟩ := ih (k x) o1 hgk; exact ⟨e, by simp only [G.run, him, hke]⟩
        | err e => exact ⟨e, by simp only [G.run, him]⟩
    | alt a b =>
      rw [gchoice_err, Necessity.min_always] at he
      obtain ⟨hga, hgb⟩ := he
      obtain ⟨e1, hae⟩ := ih a off hga
      obtain ⟨e2, hbe⟩ := ih b off hgb
      exact ⟨Nat.max e1 e2, by simp only [G.run, hae, hbe]⟩

theorem scanNatB_gt (arr : ByteArray) :
    ∀ (fuel acc off : Nat), 0 < fuel → off < arr.size → bDigit arr[off]! = true →
      off < (scanNatB arr acc fuel off).2 := by
  intro fuel acc off hfuel hlt hd
  cases fuel with
  | zero => omega
  | succ f =>
    simp only [scanNatB]
    split
    · have := scanNatB_ge arr f (acc*10 + (arr[off]!.toNat - 48)) (off+1); omega
    · rename_i hcond; simp_all

/-- Grade-level: the impossible grade is not produced by `*` from non-impossible
factors. Pure `Necessity` case analysis. -/
theorem mul_not_imp (ga gb : Grade) :
    ¬(ga.errors = never ∧ ga.consumes = always) → ¬(gb.errors = never ∧ gb.consumes = always) →
    ¬((ga * gb).errors = never ∧ (ga * gb).consumes = always) := by
  obtain ⟨e1, c1⟩ := ga; obtain ⟨e2, c2⟩ := gb
  simp only [gmul_err, gmul_con]
  cases e1 <;> cases c1 <;> cases e2 <;> cases c2 <;> decide

/-- Grade-level: same for `choice`. -/
theorem choice_not_imp (ga gb : Grade) :
    ¬(ga.errors = never ∧ ga.consumes = always) → ¬(gb.errors = never ∧ gb.consumes = always) →
    ¬((ga.choice gb).errors = never ∧ (ga.choice gb).consumes = always) := by
  obtain ⟨e1, c1⟩ := ga; obtain ⟨e2, c2⟩ := gb
  simp only [gchoice_err, gchoice_con]
  cases e1 <;> cases c1 <;> cases e2 <;> cases c2 <;> decide

/-- A never-error grammar produces an inhabited type (it must yield a value). -/
theorem nonempty_never {ρ} : ∀ {g : Grade} {α : Type} (gram : G ρ g α),
    g.errors = never → Nonempty α := by
  intro g α gram
  induction gram with
  | pure a => intro _; exact ⟨a⟩
  | fail => intro he; exact absurd he (by decide)
  | byte f => intro he; exact absurd he (by decide)
  | lit c => intro he; exact absurd he (by decide)
  | chars1 f => intro he; exact absurd he (by decide)
  | chars0 f => intro _; exact ⟨⟨⟩⟩
  | nat => intro he; exact absurd he (by decide)
  | takeN n => intro he; exact absurd he (by decide)
  | star a _ => intro _; exact ⟨[]⟩
  | starFold f acc a _ => intro _; exact ⟨acc⟩
  | recur => intro he; exact absurd he (by decide)
  | map f a iha => intro he; exact (iha he).map f
  | map2 f a b iha ihb =>
    intro he
    rw [gmul_err, Necessity.max_never] at he
    haveI := iha he.1; haveI := ihb he.2; exact ⟨f (Classical.arbitrary _) (Classical.arbitrary _)⟩
  | seqR a b iha ihb => intro he; rw [gmul_err, Necessity.max_never] at he; exact ihb he.2
  | seqL a b iha ihb => intro he; rw [gmul_err, Necessity.max_never] at he; exact iha he.1
  | alt a b iha ihb =>
    intro he
    rw [gchoice_err, Necessity.min_never] at he
    rcases he with h | h
    · exact iha h
    · exact ihb h
  | bind m k ihm ihk =>
    intro he
    rw [gmul_err, Necessity.max_never] at he
    haveI := ihm he.1; exact ihk (Classical.arbitrary _) he.2

/-- No grammar has the impossible grade `⟨never, always⟩` (never fails yet always
consumes). Rules out the degenerate `alt` corner in consume-soundness. -/
theorem no_imp {ρ} : ∀ {g : Grade} {α : Type} (gram : G ρ g α),
    ¬(g.errors = never ∧ g.consumes = always) := by
  intro g α gram
  induction gram with
  | pure a => rintro ⟨_, hc⟩; exact absurd hc (by decide)
  | fail => rintro ⟨he, _⟩; exact absurd he (by decide)
  | byte f => rintro ⟨he, _⟩; exact absurd he (by decide)
  | lit c => rintro ⟨he, _⟩; exact absurd he (by decide)
  | chars1 f => rintro ⟨he, _⟩; exact absurd he (by decide)
  | chars0 f => rintro ⟨_, hc⟩; exact absurd hc (by decide)
  | nat => rintro ⟨he, _⟩; exact absurd he (by decide)
  | takeN n => rintro ⟨he, _⟩; exact absurd he (by decide)
  | star a _ => rintro ⟨_, hc⟩; exact absurd hc (by decide)
  | starFold f acc a _ => rintro ⟨_, hc⟩; exact absurd hc (by decide)
  | recur => rintro ⟨he, _⟩; exact absurd he (by decide)
  | map f a iha => exact iha
  | map2 f a b iha ihb => exact mul_not_imp _ _ iha ihb
  | seqR a b iha ihb => exact mul_not_imp _ _ iha ihb
  | seqL a b iha ihb => exact mul_not_imp _ _ iha ihb
  | alt a b iha ihb => exact choice_not_imp _ _ iha ihb
  | bind m k ihm ihk =>
    rintro ⟨he, hc⟩
    rw [gmul_err, Necessity.max_never] at he
    rw [gmul_con, Necessity.max_always] at hc
    obtain ⟨hme, hke⟩ := he
    rcases hc with hmc | hkc
    · exact ihm ⟨hme, hmc⟩
    · haveI := nonempty_never m hme; exact ihk (Classical.arbitrary _) ⟨hke, hkc⟩

theorem choice_con_ok (ga gb : Grade) (hne : ga.errors ≠ always) :
    (ga.choice gb).consumes = always → ga.consumes = always := by
  obtain ⟨e1, c1⟩ := ga; obtain ⟨e2, c2⟩ := gb
  simp only [gchoice_con]; cases e1 <;> cases c1 <;> cases e2 <;> cases c2 <;> simp_all <;> decide

theorem choice_con_err (ga gb : Grade) (hni : ¬(ga.errors = never ∧ ga.consumes = always)) :
    (ga.choice gb).consumes = always → gb.consumes = always := by
  obtain ⟨e1, c1⟩ := ga; obtain ⟨e2, c2⟩ := gb
  simp only [gchoice_con]; cases e1 <;> cases c1 <;> cases e2 <;> cases c2 <;> simp_all <;> decide

/-- **Consume soundness**: a grammar whose grade claims `always`-consume really
advances the position on success. Together with `run_mono` this makes the
consumption grade sound w.r.t. runtime, not merely enforced at composition. -/
theorem run_consumes (arr : ByteArray) {ρ} (top : G ρ conditional ρ) :
    ∀ (fuel : Nat) {g : Grade} {α : Type} (gram : G ρ g α) (off v o'),
      G.run arr top fuel gram off = .ok v o' → g.consumes = always → off < o' := by
  intro fuel
  induction fuel with
  | zero => intro g α gram off v o' h _; simp [G.run] at h
  | succ fuel ih =>
    intro g α gram off v o' h hc
    cases gram with
    | pure a => exact absurd hc (by decide)
    | fail => simp [G.run] at h
    | byte f => simp only [G.run] at h; split at h
                · injection h with _ ho; omega
                · simp at h
    | lit c => simp only [G.run] at h; split at h
               · injection h with _ ho; omega
               · simp at h
    | chars1 f => simp only [G.run] at h; split at h
                  · injection h with _ ho; have := scanB_ge arr f arr.size (off+1); omega
                  · simp at h
    | chars0 f => exact absurd hc (by decide)
    | nat => simp only [G.run] at h; split at h
             · rename_i hcond
               rw [Bool.and_eq_true, decide_eq_true_eq] at hcond
               obtain ⟨hsz, hdd⟩ := hcond
               injection h with _ ho
               have := scanNatB_gt arr arr.size 0 off (by omega) hsz hdd
               omega
             · simp at h
    | takeN n => exact absurd hc (by decide)
    | star a => exact absurd hc (by decide)
    | starFold f acc a => exact absurd hc (by decide)
    | recur => simp only [G.run] at h; exact ih top off v o' h (by decide)
    | map f a => simp only [G.run] at h
                 cases hi : G.run arr top fuel a off with
                 | ok x o => simp only [hi] at h; injection h with _ ho; have := ih a off x o hi hc; omega
                 | err e => simp [hi] at h
    | map2 f a b =>
      rw [gmul_con, Necessity.max_always] at hc
      simp only [G.run] at h
      cases hia : G.run arr top fuel a off with
      | ok x o1 =>
        simp only [hia] at h
        cases hib : G.run arr top fuel b o1 with
        | ok y o2 => simp only [hib] at h; injection h with _ ho
                     rcases hc with hca | hcb
                     · have := ih a off x o1 hia hca; have := run_mono arr top fuel b o1 y o2 hib; omega
                     · have := run_mono arr top fuel a off x o1 hia; have := ih b o1 y o2 hib hcb; omega
        | err e => simp [hib] at h
      | err e => simp [hia] at h
    | seqR a b =>
      rw [gmul_con, Necessity.max_always] at hc
      simp only [G.run] at h
      cases hia : G.run arr top fuel a off with
      | ok x o1 =>
        simp only [hia] at h
        rcases hc with hca | hcb
        · have := ih a off x o1 hia hca; have := run_mono arr top fuel b o1 v o' h; omega
        · have := run_mono arr top fuel a off x o1 hia; have := ih b o1 v o' h hcb; omega
      | err e => simp [hia] at h
    | seqL a b =>
      rw [gmul_con, Necessity.max_always] at hc
      simp only [G.run] at h
      cases hia : G.run arr top fuel a off with
      | ok x o1 =>
        simp only [hia] at h
        cases hib : G.run arr top fuel b o1 with
        | ok y o2 => simp only [hib] at h; injection h with _ ho
                     rcases hc with hca | hcb
                     · have := ih a off x o1 hia hca; have := run_mono arr top fuel b o1 y o2 hib; omega
                     · have := run_mono arr top fuel a off x o1 hia; have := ih b o1 y o2 hib hcb; omega
        | err e => simp [hib] at h
      | err e => simp [hia] at h
    | bind m k =>
      rw [gmul_con, Necessity.max_always] at hc
      simp only [G.run] at h
      cases him : G.run arr top fuel m off with
      | ok x o1 =>
        simp only [him] at h
        rcases hc with hcm | hck
        · have := ih m off x o1 him hcm; have := run_mono arr top fuel (k x) o1 v o' h; omega
        · have := run_mono arr top fuel m off x o1 him; have := ih (k x) o1 v o' h hck; omega
      | err e => simp [him] at h
    | alt a b =>
      simp only [G.run] at h
      cases hia : G.run arr top fuel a off with
      | ok x o =>
        simp only [hia] at h; injection h with _ ho
        have hstrict : off < o := by
          apply ih a off x o hia
          apply choice_con_ok _ _ _ hc
          intro hh
          obtain ⟨e, he⟩ := run_err arr top fuel a off hh
          rw [he] at hia; simp at hia
        omega
      | err e1 =>
        simp only [hia] at h
        cases hib : G.run arr top fuel b off with
        | ok y o => simp only [hib] at h; injection h with _ ho
                    have := ih b off y o hib (choice_con_err _ _ (no_imp a) hc); omega
        | err e2 => simp [hib] at h

/-! ### Monad / functor laws

The fuel interpreter charges one unit of fuel per node, so the identity/functor
laws below hold with the fuel bookkeeping made explicit (`fuel+1` on the composite
side collapses the eliminated node).

**Associativity provably does NOT hold for this fuel backend**, and the obstruction
is genuine, not a missing lemma: (1) the two associations `(m >>= k) >>= k'` and
`m >>= (fun x => k x >>= k')` nest the `bind` nodes differently, so their
sub-parsers receive different fuel; and (2) worse, success is *not* fuel-monotone
because of `alt` — if `a` fails by fuel exhaustion at `n` but succeeds at `n+1`,
then `alt a b` flips from `b`'s result to `a`'s when fuel is added. So there is no
fixed fuel offset making the two sides equal, and no "sufficient fuel" limit that
is stable. Clean equational laws require the *size-indexed* interpreter (the shallow
`Parser`, whose recursion is structural on the actual input, so fuel never runs
short); that is the price this fast fuel backend pays for its speed. The grade
*soundness* results above, by contrast, hold unconditionally — they only talk about
what a single successful run consumed. -/

/-- Left identity: `bind (pure a) k` = `k a` (the `bind`/`pure` nodes cost one fuel). -/
theorem law_bind_pure_l (arr : ByteArray) {ρ} (top : G ρ conditional ρ) {gk α β}
    (a : α) (k : α → G ρ gk β) (off fuel : Nat) :
    G.run arr top (fuel+1) (G.bind (G.pure a) k) off = G.run arr top fuel (k a) off := by
  cases fuel with
  | zero => simp [G.run]
  | succ m => simp [G.run]

/-- Right identity: `bind m pure` = `m`. -/
theorem law_bind_pure_r (arr : ByteArray) {ρ} (top : G ρ conditional ρ) {gm α}
    (m : G ρ gm α) (off fuel : Nat) :
    G.run arr top (fuel+1) (G.bind m G.pure) off = G.run arr top fuel m off := by
  simp only [G.run]
  cases hm : G.run arr top fuel m off with
  | ok x o1 =>
    have hne : fuel ≠ 0 := by rintro rfl; simp [G.run] at hm
    obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hne
    simp [G.run]
  | err e => simp

/-- Functor identity: `map id a` = `a`. -/
theorem law_map_id (arr : ByteArray) {ρ} (top : G ρ conditional ρ) {ga α}
    (a : G ρ ga α) (off fuel : Nat) :
    G.run arr top (fuel+1) (G.map id a) off = G.run arr top fuel a off := by
  simp only [G.run]
  cases G.run arr top fuel a off <;> simp

/-! ### Combinator surface (users write these, never the raw GADT). -/

@[inline] def gpure {ρ α} (a : α) : G ρ Grade.pure α := .pure a
@[inline] def anyByte {ρ} : G ρ conditional UInt8 := .byte (fun _ => true)
@[inline] def satisfy {ρ} (f : UInt8 → Bool) : G ρ conditional UInt8 := .byte f
@[inline] def bchar {ρ} (c : Char) : G ρ conditional PUnit := .lit (ch c)
@[inline] def takeWhile1 {ρ} (f : UInt8 → Bool) : G ρ conditional PUnit := .chars1 f
@[inline] def takeWhile {ρ} (f : UInt8 → Bool) : G ρ flexible PUnit := .chars0 f
@[inline] def gnat {ρ} : G ρ conditional Nat := .nat
@[inline] def ws {ρ} : G ρ flexible PUnit := .chars0 bWs
@[inline] def grecur {ρ} : G ρ conditional ρ := .recur

/-- Graded functor / applicative / alternative / monad operators. -/
scoped infixr:100 " <$>ᵍ " => G.map
@[inline] def gmap2 {ρ g g' α β γ} (f : α → β → γ) (a : G ρ g α) (b : G ρ g' β) : G ρ (g*g') γ := .map2 f a b
scoped infixl:60 " <*ᵍ "  => G.seqL
scoped infixl:60 " *>ᵍ "  => G.seqR
scoped infixr:20 " <|>ᵍ " => G.alt
scoped infixl:55 " >>=ᵍ " => G.bind
@[inline] def gmany {ρ ge α} (a : G ρ ⟨ge, always⟩ α) : G ρ flexible (List α) := .star a

/-- One or more `a`, always-consuming. -/
@[inline] def gmany1 {ρ ge α} (a : G ρ ⟨ge, always⟩ α) :=
  G.map2 (fun x xs => x :: xs) a (G.star a)

/-- `p` separated by `sep`, one or more. -/
@[inline] def gsepBy1 {ρ ge ge' α β} (sep : G ρ ⟨ge', always⟩ β) (p : G ρ ⟨ge, always⟩ α) :=
  G.map2 (fun x xs => x :: xs) p (G.star (G.seqR sep p))

/-- `p` separated by `sep`, zero or more. -/
@[inline] def gsepBy {ρ ge ge' α β} (sep : G ρ ⟨ge', always⟩ β) (p : G ρ ⟨ge, always⟩ α) :=
  G.alt (G.map2 (fun x xs => x :: xs) p (G.star (G.seqR sep p))) (G.pure (α := List α) [])

/-! ### Entry points. -/

/-- Fast run: `some (value, consumedAll?)` or `none`. Fuel bounds node visits. -/
@[inline] def run {ρ α} (top : G ρ conditional ρ) (g : G ρ conditional α) (arr : ByteArray) : Option α :=
  match G.run arr top (arr.size * 64 + 64) g 0 with
  | .ok v _ => some v
  | .err _ => none

/-- Parse a `String` (decoded to its UTF-8 bytes for free), reporting the failure
byte position on error. -/
def parse {ρ} (top : G ρ conditional ρ) (s : String) : Except String ρ :=
  let arr := s.toUTF8
  match G.run arr top (arr.size * 64 + 64) top 0 with
  | .ok v pos => if pos ≥ arr.size then .ok v else .error s!"unexpected trailing input at byte {pos}"
  | .err e => .error s!"parse error at byte {e}"

/-- Run a self-contained grammar (its own `top`) for a checksum. -/
@[inline] def runTop (top : G Nat conditional Nat) (s : String) : Nat :=
  (run top top s.toUTF8).getD 0

/-! ### `gdo` do-notation for the graded monad

`gdo (x ← p) rest` desugars to `p >>=ᵍ fun x => rest`; chain by nesting for several
binds. Non-binding steps use `*>ᵍ`/`<*ᵍ`. The grades are computed by the
constructors, so a `gdo` block is graded automatically. -/
end Graded

/-- `gletm n ⟵ p ⨾ rest` = graded monadic bind (`p >>=ᵍ fun n => rest`). -/
macro "gletm " x:ident " ⟵ " e:term " ⨾ " r:term : term =>
  `(Graded.G.bind $e (fun $x => $r))
