module

public import ConLeche.Model.Env.Laws
import ConLeche.Verify.InferLemmas
import ConLeche.Verify.Denote.Lemmas

public section

/-!
# A rule's law along a fitted telescope

A rule's law (`RuleLaw`) speaks of its statement's sides as closed terms (`ruleSides`): the
functions `fun xs => l`, `fun xs => r` inhabit `∀ xs, A`, and `fun xs => A` inhabits
`∀ xs, Sort u`.  A firing reads the statement at fitted arguments (`TeleFitPA`).  The readings of
the statement and of its sides share their binder domains (`SidesT`, `sidesT_of_denote`), so the
law crosses the fit one binder at a time, by β in the model (`app_lamV`), down to the residual
`Eq` spine: both sides inhabit `A` and `A` inhabits the equation's universe (`sidesT_fit`).
-/

namespace ConLeche.Model
open ConLeche.Semantics ConLeche.SetModel ConLeche.Term ConLeche.Verify SetTheory

open ConLeche (Env Expr Name Level)

universe w

variable {V : Type w} [SetTheory V]

/-- **The readings of a rule's statement and of its sides**: an `Eq` spine with its type, sides
and universe, under common binder domains. -/
inductive SidesT (n : Nat) : Term → Term → Term → Term → Term → Term → Prop where
  | eq {E A l r : Term} : SidesT n (.app (.app (.app E A) l) r) A l r A (.sort n)
  | pi {d b P L R LA PU : Term} : SidesT n b P L R LA PU →
      SidesT n (.pi d b) (.pi d P) (.lam d L) (.lam d R) (.lam d LA) (.pi d PU)

/-- The relation survives a substitution. -/
theorem SidesT.inst {n : Nat} (a : Term) :
    ∀ {t P L R LA PU : Term} (k : Nat), SidesT n t P L R LA PU →
      SidesT n (t.inst a k) (P.inst a k) (L.inst a k) (R.inst a k) (LA.inst a k) (PU.inst a k)
  | _, _, _, _, _, _, _, .eq => by simp only [Term.inst]; exact .eq
  | _, _, _, _, _, _, k, .pi h => by simp only [Term.inst]; exact .pi (SidesT.inst a (k + 1) h)

/-- One binder of the law at a fitting argument. -/
theorem mem_lam_pi {ρ : Nat → V} {d L P a : Term} (ha : interp V ρ a ∈ˢ interp V ρ d)
    (h : interp V ρ (.lam d L) ∈ˢ interp V ρ (.pi d P)) :
    interp V ρ (L.inst a) ∈ˢ interp V ρ (P.inst a) := by
  rw [interp_lam, interp_pi] at h
  have happ := app_mem_piV h ha
  rw [app_lamV ha] at happ
  rw [interp_inst0, interp_inst0]
  exact happ

/-- **The law along a fitted telescope**: at the residual `Eq` spine, both sides inhabit its
type, and the type inhabits the equation's universe. -/
theorem sidesT_fit {n : Nat} {ρ : Nat → V} :
    ∀ {t : Term} {vs : List Term} {rest : Term}, TeleFitPA V ρ t vs rest →
      ∀ {P L R LA PU : Term}, SidesT n t P L R LA PU →
      interp V ρ L ∈ˢ interp V ρ P → interp V ρ R ∈ˢ interp V ρ P →
      interp V ρ LA ∈ˢ interp V ρ PU →
      ∀ {E A l r : Term}, rest = .app (.app (.app E A) l) r →
        interp V ρ l ∈ˢ interp V ρ A ∧ interp V ρ r ∈ˢ interp V ρ A ∧
          interp V ρ A ∈ˢ interp V ρ (.sort n) := by
  intro t vs rest h
  induction h with
  | nil =>
    intro P L R LA PU hs hL hR hA E A l r hrest
    subst hrest
    cases hs
    exact ⟨hL, hR, hA⟩
  | @cons D B rest' a as ha _ ih =>
    intro P L R LA PU hs hL hR hA E A l r hrest
    cases hs with
    | pi hs' =>
      exact ih (hs'.inst a 0) (mem_lam_pi ha hL) (mem_lam_pi ha hR) (mem_lam_pi ha hA) hrest

/-- **The readings of a statement and of its sides are related** (`SidesT`), at the universe
the statement's `Eq` reads at. -/
theorem sidesT_of_denote {acval : Name → (Name → Nat) → Term} {env : Env} {ψ : Name → Nat} :
    ∀ (n : Nat) (T : Expr), (ConLeche.ruleTele T).1 = n →
      ∀ {P L R LA PU : Expr} {v : Level}, ConLeche.ruleSides T = some (P, L, R, LA, PU) →
      ConLeche.ruleLevel T = some v →
      ∀ {d : Nat} {ta pa la ra laa pua : Term},
        denote acval env ψ d T = some ta → denote acval env ψ d P = some pa →
        denote acval env ψ d L = some la → denote acval env ψ d R = some ra →
        denote acval env ψ d LA = some laa → denote acval env ψ d PU = some pua →
        SidesT (v.eval ψ) ta pa la ra laa pua := by
  intro n
  induction n with
  | zero =>
    intro T hn P L R LA PU v hs hv d ta pa la ra laa pua hT hP hL hR hLA hPU
    match T, hn, hs, hT, hv with
    | .forallE ty b, hn, _, _, _ => simp [ConLeche.ruleTele] at hn
    | .app (.app (.app (.const eqn [v']) A) l) r, _, hs, hT, hv =>
      simp only [ConLeche.ruleSides, ConLeche.eqSpine?, Option.map_some, Option.some.injEq,
        Prod.mk.injEq] at hs
      obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hs
      obtain ⟨g₂, ra', hg₂, hra', rfl⟩ := denote_app_inv hT
      obtain ⟨g₁, la', hg₁, hla', rfl⟩ := denote_app_inv hg₂
      obtain ⟨Ea, Aa, hEa, hAa, rfl⟩ := denote_app_inv hg₁
      obtain rfl := Option.some.inj (hP.symm.trans hAa)
      obtain rfl := Option.some.inj (hL.symm.trans hla')
      obtain rfl := Option.some.inj (hR.symm.trans hra')
      obtain rfl := Option.some.inj (hLA.symm.trans hAa)
      simp only [ConLeche.ruleLevel, ConLeche.eqSpine?, Option.map_some, Option.some.injEq] at hv
      subst hv
      rw [denote_sort] at hPU
      obtain rfl := Option.some.inj hPU.symm
      exact .eq
  | succ n ih =>
    intro T hn P L R LA PU v hs hv d ta pa la ra laa pua hT hP hL hR hLA hPU
    match T, hn, hs, hT, hv with
    | .app (.app (.app (.const _ [_]) _) _) _, hn, _, _, _ => simp [ConLeche.ruleTele] at hn
    | .forallE ty b, hn, hs, hT, hv =>
      simp only [ConLeche.ruleSides, Option.map_eq_some_iff] at hs
      obtain ⟨⟨P', L', R', LA', PU'⟩, hb, he⟩ := hs
      obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ : Expr.forallE ty P' = P ∧ Expr.lam ty L' = L ∧
          Expr.lam ty R' = R ∧ Expr.lam ty LA' = LA ∧ Expr.forallE ty PU' = PU := by
        simpa using he
      have hn' : (ConLeche.ruleTele b).1 = n := by simpa [ConLeche.ruleTele] using hn
      obtain ⟨hbi, hbn⟩ := ConLeche.ruleSides_instantiate1 (.fvar d ty) b 0 hb
      obtain ⟨tya, ba, htya, hba, rfl⟩ := denote_forallE_inv hT
      obtain ⟨tya₁, pa', htya₁, hpa', rfl⟩ := denote_forallE_inv hP
      obtain ⟨tya₂, la', htya₂, hla', rfl⟩ := denote_lam_inv hL
      obtain ⟨tya₃, ra', htya₃, hra', rfl⟩ := denote_lam_inv hR
      obtain ⟨tya₄, laa', htya₄, hlaa', rfl⟩ := denote_lam_inv hLA
      obtain ⟨tya₅, pua', htya₅, hpua', rfl⟩ := denote_forallE_inv hPU
      obtain rfl := Option.some.inj (htya₁.symm.trans htya)
      obtain rfl := Option.some.inj (htya₂.symm.trans htya)
      obtain rfl := Option.some.inj (htya₃.symm.trans htya)
      obtain rfl := Option.some.inj (htya₄.symm.trans htya)
      obtain rfl := Option.some.inj (htya₅.symm.trans htya)
      have hvb : ConLeche.ruleLevel (b.instantiate1 (.fvar d ty)) = some v := by
        rw [ConLeche.ruleLevel_instantiate1 _ b 0 hb]; exact hv
      exact .pi (ih _ (hbn.trans hn') hbi hvb hba hpa' hla' hra' hlaa' hpua')

end ConLeche.Model
