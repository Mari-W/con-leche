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

/-- A subterm of the application tree inherits the leaves, the scoping
and the reading of the whole. -/
theorem appSubterms_pkg {d : Nat} :
    ∀ (e : Expr) {x : Expr}, x ∈ ConLeche.appSubterms e →
      (∀ y ∈ x.fvarLeaves, y ∈ e.fvarLeaves) ∧
      (Expr.WScoped d e → Expr.WScoped d x) ∧
      (e.looseBVarsBounded 0 = true → x.looseBVarsBounded 0 = true) ∧
      (∀ {ea : Term}, denote m.acval env φ d e = some ea →
        ∃ v, denote m.acval env φ d x = some v) := by
  intro e
  induction e with
  | app f a ihf iha =>
    intro x hx
    simp only [ConLeche.appSubterms, List.mem_cons, List.mem_append] at hx
    rcases hx with rfl | hx | hx
    · exact ⟨fun _ h => h, id, id, fun h => ⟨_, h⟩⟩
    · obtain ⟨hl, hw, hb, hd⟩ := ihf hx
      refine ⟨fun y hy => ?_, fun h => hw ?_, fun h => hb ?_, fun h => ?_⟩
      · rw [Expr.fvarLeaves]; exact List.mem_append_left _ (hl y hy)
      · simp only [Expr.WScoped] at h; exact h.1
      · simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at h; exact h.1
      · obtain ⟨fa, aa, hfa, -, -⟩ := denote_app_inv h
        exact hd hfa
    · obtain ⟨hl, hw, hb, hd⟩ := iha hx
      refine ⟨fun y hy => ?_, fun h => hw ?_, fun h => hb ?_, fun h => ?_⟩
      · rw [Expr.fvarLeaves]; exact List.mem_append_right _ (hl y hy)
      · simp only [Expr.WScoped] at h; exact h.2
      · simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at h; exact h.2
      · obtain ⟨fa, aa, -, haa, -⟩ := denote_app_inv h
        exact hd haa
  | _ =>
    intro x hx
    simp only [ConLeche.appSubterms, List.mem_singleton] at hx
    subst hx
    exact ⟨fun _ h => h, id, id, fun h => ⟨_, h⟩⟩

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

/-- A repeated pattern variable: the instance's subterm is the variable's binding, a subterm of the
application tree of a pool term, so it is framed, inside the whole term's leaves and read, and
the definitional equality gives the claim. -/
theorem MatchArg.defeq_sound {d : Nat} {P : List Expr} {a a' : Expr}
    (hd : DefEqSem m φ d a' a) (hp : ∃ q ∈ P, a' ∈ ConLeche.appSubterms q) :
    MatchArgSem m φ d P a a' := by
  intro E Δa ea hf hsub hC hP hea
  obtain ⟨q, hq, hx⟩ := hp
  obtain ⟨hfq, hsq, qa, hqa⟩ := hP q hq
  obtain ⟨hl, hw, hb, hden⟩ := appSubterms_pkg (m := m) (φ := φ) (d := d) q hx
  obtain ⟨ea', hea'⟩ := hden hqa
  have hf' : Frame d a' := ⟨hw hfq.1, hb hfq.2.1, fun y hy => hfq.2.2 y (hl y hy)⟩
  have hsub' : LeavesSub a' E := fun y hy => hsq y (hl y hy)
  refine ⟨hf', hsub', ea', hea', fun ρ hρ hL hg hg' hne hne' => ?_⟩
  exact (hd hf' hf (hC.of_subset hsub') (hC.of_subset hsub) hea' hea ρ hρ (hL.of_subset hsub')
    (hL.of_subset hsub) hg' hg hne' hne).symm

/-! ### The view and the instance (task r13)

A rule fires when its matched view equals the instance of the left side up to the official form
of the constants' levels (`Expr.levelFormEq`).  Levels of the same official form evaluate the
same (`Level.substFn_formsEq`), so the two read as the same term, and they share their leaves,
their scoping and their bound variables. -/

/-- The view and the instance share their leaves. -/
theorem levelFormEq_fvarLeaves : ∀ {a b : Expr}, a.levelFormEq b = true →
    a.fvarLeaves = b.fvarLeaves :=
  Expr.levelFormEq_rec (P := fun a b => a.fvarLeaves = b.fvarLeaves) (fun _ => rfl)
    (fun f x g y hf hx => by simp only [Expr.fvarLeaves, hf, hx])
    (fun _ _ _ _ => by simp only [Expr.fvarLeaves]) _ _

/-- The view and the instance share their scoping. -/
theorem levelFormEq_WScoped {d : Nat} : ∀ {a b : Expr}, a.levelFormEq b = true →
    (Expr.WScoped d a ↔ Expr.WScoped d b) :=
  Expr.levelFormEq_rec (P := fun a b => Expr.WScoped d a ↔ Expr.WScoped d b) (fun _ => .rfl)
    (fun f x g y hf hx => by simp only [Expr.WScoped, hf, hx])
    (fun _ _ _ _ => by simp only [Expr.WScoped]) _ _

/-- The view and the instance share their bound variables. -/
theorem levelFormEq_looseBVarsBounded {k : Nat} : ∀ {a b : Expr}, a.levelFormEq b = true →
    a.looseBVarsBounded k = b.looseBVarsBounded k :=
  Expr.levelFormEq_rec (P := fun a b => a.looseBVarsBounded k = b.looseBVarsBounded k)
    (fun _ => rfl) (fun f x g y hf hx => by simp only [Expr.looseBVarsBounded, hf, hx])
    (fun _ _ _ _ => by simp only [Expr.looseBVarsBounded]) _ _

/-- The view and the instance read the same. -/
theorem levelFormEq_denote {d : Nat} : ∀ {a b : Expr}, a.levelFormEq b = true →
    denote m.acval env φ d a = denote m.acval env φ d b :=
  Expr.levelFormEq_rec (P := fun a b => denote m.acval env φ d a = denote m.acval env φ d b)
    (fun _ => rfl) (fun f x g y hf hx => by rw [denote_app, denote_app, hf, hx])
    (fun c ls ls' h => by
      have hk := fun ks => Level.substFn_formsEq φ ks h
      simp only [denote, Level.formsEq_length h, hk]) _ _

/-- **A match that ends at a view of the instance is a match of the instance.** -/
theorem MatchRelSem.of_levelFormEq {d : Nat} {P : List Expr} {e e₁ l : Expr}
    (h : MatchRelSem m φ d P e e₁) (hl : e₁.levelFormEq l = true) :
    MatchRelSem m φ d P e l := by
  intro E Δa ea hf hsub hC hP hea
  obtain ⟨⟨hw, hb, hlb⟩, hsub', ea', hea', hs⟩ := h hf hsub hC hP hea
  have hleaves := levelFormEq_fvarLeaves hl
  refine ⟨⟨(levelFormEq_WScoped hl).mp hw, (levelFormEq_looseBVarsBounded hl) ▸ hb, ?_⟩,
    fun y hy => hsub' y (hleaves ▸ hy), ea',
    (levelFormEq_denote (m := m) (φ := φ) (d := d) hl).symm.trans hea', hs⟩
  intro y hy
  exact hlb y (hleaves ▸ hy)

end ConLeche.Model.Rules
