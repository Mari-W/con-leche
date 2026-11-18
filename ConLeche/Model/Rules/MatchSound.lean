module

public import ConLeche.Model.Rules.Motive
import ConLeche.Model.Rules.DefEqSoundKit
import ConLeche.Model.CtxOkKit

public section

/-!
# The soundness of a rewrite rule's match

`MatchRel env d P e l` relates a term `e` to the instance `l` of a rule's left side, position by
position (`ruleMatchM`).  Its claim: off the point, the two read equal.  The spine shares the
head, so at `f a` against `f' a'` the functions read equal (by induction), and where `f a` is not
the point neither is `f`, so `⟦f⟧` is a graph.  Both applications are graded, so their
application clauses (`AppliesTo`) put `⟦a⟧` and `⟦a'⟧` in the graph's one domain, a type, whose
members are all the point or none (`IsTy.eq_of_ne_pt`).  That leaves the argument's claim off
the point, from the reduction (`RedSem`) and the inner match.

The claims carry the whole term `E` the match started from, whose leaves cover every subterm the
match produces, and the pool `P` of instance subterms produced before the position.
-/

namespace ConLeche.Model.Rules
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory

open ConLeche (Env Expr Name)
open ConLeche.Rules

universe w

variable {V : Type w} [SetTheory V] {env : Env} {m : EnvModel V env}
  {φ : Name → Nat}

/-- The pool of a match position: framed, inside the whole term's leaves, and read. -/
@[expose] def PoolOk (m : EnvModel V env) (φ : Name → Nat) (d : Nat) (E : Expr)
    (P : List Expr) : Prop :=
  ∀ q ∈ P, Frame d q ∧ LeavesSub q E ∧ ∃ qa, denote m.acval env φ d q = some qa

/-- **`MatchRel`'s motive**: the instance is framed, inside the whole term's leaves and read, and
where both sides are graded and the term is not the point, the two are equal. -/
@[expose] def MatchRelSem (m : EnvModel V env) (φ : Name → Nat) (d : Nat) (P : List Expr)
    (e e' : Expr) : Prop :=
  ∀ {E : Expr} {Δa : List Term} {ea : Term},
    Frame d e → LeavesSub e E → CtxOkS m φ d Δa E → PoolOk m φ d E P →
    denote m.acval env φ d e = some ea →
    Frame d e' ∧ LeavesSub e' E ∧
      ∃ ea', denote m.acval env φ d e' = some ea' ∧
        ∀ ρ : Nat → V, Sat V Δa ρ → LeavesGr m φ d E ρ →
          WellDenoted V ρ ea → WellDenoted V ρ ea' → interp V ρ ea ≠ pt →
          interp V ρ ea = interp V ρ ea'

/-- **`MatchArg`'s motive**: `MatchRelSem` where neither side is the point. -/
@[expose] def MatchArgSem (m : EnvModel V env) (φ : Name → Nat) (d : Nat) (P : List Expr)
    (e e' : Expr) : Prop :=
  ∀ {E : Expr} {Δa : List Term} {ea : Term},
    Frame d e → LeavesSub e E → CtxOkS m φ d Δa E → PoolOk m φ d E P →
    denote m.acval env φ d e = some ea →
    Frame d e' ∧ LeavesSub e' E ∧
      ∃ ea', denote m.acval env φ d e' = some ea' ∧
        ∀ ρ : Nat → V, Sat V Δa ρ → LeavesGr m φ d E ρ →
          WellDenoted V ρ ea → WellDenoted V ρ ea' → interp V ρ ea ≠ pt →
          interp V ρ ea' ≠ pt → interp V ρ ea = interp V ρ ea'

theorem MatchRel.refl_sound {d : Nat} {P : List Expr} {e : Expr} :
    MatchRelSem m φ d P e e := by
  intro E Δa ea hf hsub _ _ hea
  exact ⟨hf, hsub, ea, hea, fun _ _ _ _ _ _ => rfl⟩

/-- The spine: the functions read equal, and the arguments lie in the one domain of the graph
the function reads as. -/
theorem MatchRel.app_sound {d : Nat} {P : List Expr} {f f' a a' : Expr}
    (hf : MatchRelSem m φ d P f f') (ha : MatchArgSem m φ d (f' :: P) a a') :
    MatchRelSem m φ d P (.app f a) (.app f' a') := by
  intro E Δa ea hfr hsub hC hP hea
  have hsubf : LeavesSub f E := fun l hl => hsub l (by simp [Expr.fvarLeaves, hl])
  have hsuba : LeavesSub a E := fun l hl => hsub l (by simp [Expr.fvarLeaves, hl])
  obtain ⟨fa, aa, hfa, haa, rfl⟩ := denote_app_inv hea
  obtain ⟨hff', hsf', fa', hfa', hsemf⟩ := hf hfr.app_fn hsubf hC hP hfa
  have hP' : PoolOk m φ d E (f' :: P) := by
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact ⟨hff', hsf', fa', hfa'⟩
    · exact hP q hq
  obtain ⟨hfa'', hsa', aa', haa', hsema⟩ := ha hfr.app_arg hsuba hC hP' haa
  have hfr' : Frame d (.app f' a') := by
    obtain ⟨hw1, hb1, hl1⟩ := hff'
    obtain ⟨hw2, hb2, hl2⟩ := hfa''
    refine ⟨by simp only [Expr.WScoped]; exact ⟨hw1, hw2⟩,
      by simp only [Expr.looseBVarsBounded, Bool.and_eq_true]; exact ⟨hb1, hb2⟩, fun l hl => ?_⟩
    simp only [Expr.fvarLeaves, List.mem_append] at hl
    rcases hl with hl | hl
    · exact hl1 l hl
    · exact hl2 l hl
  refine ⟨hfr', fun l hl => ?_, .app fa' aa', by rw [denote_app, hfa', haa']; rfl,
    fun ρ hρ hL hg hg' hne => ?_⟩
  · simp only [Expr.fvarLeaves, List.mem_append] at hl
    rcases hl with hl | hl
    · exact hsf' l hl
    · exact hsa' l hl
  rw [WellDenoted_app] at hg hg'
  obtain ⟨hgf, hga, hap⟩ := hg
  obtain ⟨hgf', hga', hap'⟩ := hg'
  have hnf : interp V ρ fa ≠ pt := by
    intro h; apply hne; rw [interp_app, h, app_pt]
  have heqf := hsemf ρ hρ hL hgf hgf' hnf
  rcases hap with hpt | ⟨F, A, hF, hA, hmem⟩
  · exact absurd hpt hnf
  rw [← heqf, hF] at hap'
  obtain ⟨-, hmem'⟩ := appliesTo_graph.mp hap'
  have heqa : interp V ρ aa = interp V ρ aa' :=
    IsTy.eq_of_ne_pt hA hmem hmem' fun h₁ h₂ => hsema ρ hρ hL hga hga' h₁ h₂
  rw [interp_app, interp_app, heqf, heqa]

/-- An argument whose spine matches. -/
theorem MatchArg.spine_sound {d : Nat} {P : List Expr} {a a' : Expr}
    (h : MatchRelSem m φ d P a a') : MatchArgSem m φ d P a a' := by
  intro E Δa ea hf hsub hC hP hea
  obtain ⟨hf', hsub', ea', hea', hs⟩ := h hf hsub hC hP hea
  exact ⟨hf', hsub', ea', hea', fun ρ hρ hL hg hg' hne _ => hs ρ hρ hL hg hg' hne⟩

/-- An argument that matches after a reduction (the retry on `whnf`): equal to its reduct off
the point (`RedSem`), and the reduct equal to the instance by the inner match. -/
theorem MatchArg.red_sound {d : Nat} {P : List Expr} {a a'' a' : Expr}
    (hr : RedSem m φ d a a'') (hm : MatchRelSem m φ d P a'' a') : MatchArgSem m φ d P a a' := by
  intro E Δa ea hf hsub hC hP hea
  obtain ⟨hf'', hsub'', ea'', hea'', hsr⟩ := hr hf (hC.of_subset hsub) hea
  obtain ⟨hf', hsub', ea', hea', hsm⟩ :=
    hm hf'' (fun l hl => hsub l (hsub'' l hl)) hC hP hea''
  refine ⟨hf', hsub', ea', hea', fun ρ hρ hL hg hg' hne _ => ?_⟩
  obtain ⟨hg'', heq⟩ := hsr ρ hρ (hL.of_subset hsub) hg hne
  exact heq.trans (hsm ρ hρ hL hg'' hg' (heq ▸ hne))

end ConLeche.Model.Rules
