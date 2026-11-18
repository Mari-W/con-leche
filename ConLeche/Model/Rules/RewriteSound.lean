module

public import ConLeche.Model.Rules.Inputs
import ConLeche.Model.Rules.IotaSoundKit
import ConLeche.Model.CtxOkKit
import ConLeche.Model.WellDenotedTransport
import ConLeche.Verify.Denote.Inst
import ConLeche.Verify.Leaves
import ConLeche.Model.Rules.RuleLawKit
import ConLeche.Model.Reading.Levels
public import ConLeche.Model.Rules.MatchSound

public section

/-!
# The soundness of a user rewrite rule

`Red.rewrite` fires a stored theorem `h : ∀ xs, @Eq A l r` on a term `e`
that matches the instance `l` of the left side (`MatchRel`), on arguments
found in `l`'s application tree.  The match equates `e` with `l` off the
point (`MatchRel.app_sound`), so the rule's equation of `l` and `r` is one
of `e` and `r`.  The theorem's leaf inhabits
its type's reading (`const_ty`), the certificate fits the arguments to
its telescope, so the residual `Eq` spine's reading is inhabited.  The
rule's law, installed at its registration (`RuleLaw`) and read along the
fit (`sidesT_fit`), puts `A` in its universe and both sides in `A`, so
`eq_law` reads the spine as `eqv ⟦l⟧ ⟦r⟧`, and an inhabitant of it
equates the sides (`eq_of_mem_eqv`).
-/

namespace ConLeche.Model.Rules
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory

open ConLeche (Env Expr Name Level ConstantVal)
open ConLeche.Rules

universe w

variable {V : Type w} [SetTheory V] {env : Env} {m : EnvModel V env}
  {φ : Name → Nat}

/-! ## The left side's application tree -/

theorem self_mem_appSubterms (e : Expr) : e ∈ ConLeche.appSubterms e := by
  cases e <;> simp [ConLeche.appSubterms]

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

/-- A subterm of the application tree is framed and in context where
the whole is. -/
theorem appSubterms_frame {d : Nat} {Δa : List Term} {e x : Expr}
    (hx : x ∈ ConLeche.appSubterms e) (hf : Frame d e) (hC : CtxOkS m φ d Δa e) :
    Frame d x ∧ CtxOkS m φ d Δa x := by
  obtain ⟨hl, hw, hb, -⟩ := appSubterms_pkg (m := m) (φ := φ) (d := d) e hx
  exact ⟨⟨hw hf.1, hb hf.2.1, fun y hy => hf.2.2 y (hl y hy)⟩, hC.of_subset hl⟩

/-- Every expression of a list that reads gives a read spine. -/
theorem denoteSpine_of_forall {acval : Name → (Name → Nat) → Term} {d : Nat} :
    ∀ (as : List Expr), (∀ x ∈ as, ∃ v, denote acval env φ d x = some v) →
      ∃ vs, DenoteSpine acval env φ d as vs
  | [], _ => ⟨[], .nil⟩
  | a :: as, h => by
    obtain ⟨v, hv⟩ := h a List.mem_cons_self
    obtain ⟨vs, hvs⟩ := denoteSpine_of_forall as fun x hx => h x (List.mem_cons_of_mem a hx)
    exact ⟨v :: vs, .cons hv hvs⟩

/-! ## The telescope -/

/-- **A `∀`-telescope's residual reads** where the telescope and the
arguments do (`teleFitPA_residualK` without the fit). -/
theorem denote_piResidual_exists {acval : Name → (Name → Nat) → Term}
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (k : Nat),
      (acval n ψ).liftN 1 k = acval n ψ)
    (hainst : ∀ (n : Name) (ψ : Name → Nat) (y : Term) (k : Nat),
      (acval n ψ).inst y k = acval n ψ)
    {d : Nat} :
    ∀ (args : List Expr) {ty rest : Expr} {Ta : Term} {vs : List Term},
      ConLeche.piResidual ty args = some rest →
      Expr.WScoped d ty →
      (∀ a ∈ args, Expr.WScoped d a ∧ a.looseBVarsBounded 0 = true) →
      denote acval env φ d ty = some Ta →
      DenoteSpine acval env φ d args vs →
      ∃ restA, denote acval env φ d rest = some restA := by
  intro args
  induction args with
  | nil =>
    intro ty rest Ta vs hpr _ _ hty _
    obtain rfl : rest = ty := (Option.some.inj hpr).symm
    exact ⟨Ta, hty⟩
  | cons a as ih =>
    intro ty rest Ta vs hpr hwty hargs hty hsp
    match ty, hpr, hwty, hty with
    | .bvar _, hpr, _, _ => exact nomatch hpr
    | .fvar _ _, hpr, _, _ => exact nomatch hpr
    | .sort _, hpr, _, _ => exact nomatch hpr
    | .const _ _, hpr, _, _ => exact nomatch hpr
    | .app _ _, hpr, _, _ => exact nomatch hpr
    | .lam _ _, hpr, _, _ => exact nomatch hpr
    | .letE _ _ _, hpr, _, _ => exact nomatch hpr
    | .lit _, hpr, _, _ => exact nomatch hpr
    | .proj _ _ _, hpr, _, _ => exact nomatch hpr
    | .forallE dom body, hpr, hwty, hty => ?_
    cases hsp with | @cons _ va _ vs' ha hsp' => ?_
    obtain ⟨hwa, hba⟩ := hargs a List.mem_cons_self
    obtain ⟨hdomw, hbodyw⟩ : Expr.WScoped d dom ∧ Expr.WScoped d body := by
      simpa [Expr.WScoped] using hwty
    obtain ⟨doma, bodya, hdoma, hbodya, rfl⟩ := denote_forallE_inv hty
    have hbody' : denote acval env φ d (body.instantiate1 a)
        = some (bodya.inst va) := by
      rw [denote_beta hacl hainst (ty := dom)
        hbodyw.fvarsBelow hwa hba ha 0, hbodya]
      rfl
    exact ih hpr (Expr.WScoped.instantiate1_gen hwa 0 hbodyw)
      (fun x hx => hargs x (List.mem_cons_of_mem a hx)) hbody' hsp'

/-- **A fitted telescope's residual is inhabited** where the telescope
is: apply an inhabitant along the fit. -/
theorem teleFitPA_inhabited {ρ : Nat → V} :
    ∀ {T : Term} {vs : List Term} {rest : Term},
      TeleFitPA V ρ T vs rest → ∀ {f : V}, f ∈ˢ interp V ρ T →
        ∃ y : V, y ∈ˢ interp V ρ rest := by
  intro T vs rest h
  induction h with
  | nil => intro f hf; exact ⟨f, hf⟩
  | @cons A B rest' a as hmem _ ih =>
    intro f hf
    rw [interp_pi] at hf
    have happ := app_mem_piV hf hmem
    rw [← interp_inst0] at happ
    exact ih happ

/-! ## The rule -/

/-- A rule in force at a head is one the rules name. -/
theorem ruleNamed_of_rulesFor {h c : Name} (hmem : h ∈ env.rulesFor c) : RuleNamed env h := by
  unfold Env.rulesFor at hmem
  obtain ⟨e, he, hsome⟩ := List.mem_filterMap.mp hmem
  refine .inr ⟨e, he, ?_⟩
  split at hsome
  · exact Option.some.inj hsome
  · exact nomatch hsome

/-- **A user rewrite rule**, at the conditional motive.  The match equates the term with the
instance `l` of the left side off the point (`MatchRelSem`).  The rule's law (`RuleLaw`), read
along the certificate's fit (`sidesT_fit`), puts both sides in `A` and `A` in the equation's
universe, so `eq_law` reads the residual spine as `eqv ⟦l⟧ ⟦r⟧`, whose inhabitant equates the
sides. -/
theorem Red.rewrite_sound (hin : RulesInputs V m φ) {d : Nat} {h : Name}
    {cv : ConstantVal} {us : List Level} {args : List Expr} {u : Level}
    {A l r e : Expr} {c : Name} {ls : List Level}
    (hthm : env.find? h = some (.thmInfo cv))
    (hus : us.length = cv.levelParams.length)
    (hcerts : CertsFSem m φ d (cv.type.instantiateLevelParams cv.levelParams us) args)
    (hres : ConLeche.piResidual (cv.type.instantiateLevelParams cv.levelParams us) args
      = some (.app (.app (.app (.const eqName [u]) A) l) r))
    (_hhead : e.getAppFn = .const c ls)
    (hmatch : MatchRelSem m φ d [] e l)
    (hsub : ∀ x ∈ args, x ∈ ConLeche.appSubterms l)
    (hleaves : ∀ x ∈ r.fvarLeaves, x ∈ l.fvarLeaves)
    (hmem : h ∈ env.rulesFor c) :
    RedSem m φ d e r := by
  intro hfe Δa ee hCe hee
  obtain ⟨hfl, hLS, ea, hea, hsem⟩ := hmatch hfe (fun _ h => h) hCe
    (fun _ hq => nomatch hq) hee
  have hCl : CtxOkS m φ d Δa l := hCe.of_subset hLS
  -- the theorem's stored type: closed, read, graded, inhabited
  obtain ⟨ta, hTd, hTok, hTmem, hnfT, hbdT⟩ :=
    constTy_pkg (ci := .thmInfo cv) hin.const_ty hthm hus
  obtain ⟨hfT, hCT⟩ := frame_of_not_hasFvar (m := m) (φ := φ) hnfT hbdT hCl.1
  -- the arguments are subterms of the left side
  have hfargs : ∀ x ∈ args, Frame d x ∧ CtxOkS m φ d Δa x :=
    fun x hx => appSubterms_frame (hsub x hx) hfl hCl
  have hlargs : ∀ x ∈ args, ∀ y ∈ x.fvarLeaves, y ∈ l.fvarLeaves :=
    fun x hx => (appSubterms_pkg (m := m) (φ := φ) (d := d) l (hsub x hx)).1
  obtain ⟨vs, hsp⟩ := denoteSpine_of_forall args fun x hx =>
    (appSubterms_pkg (m := m) (φ := φ) (d := d) l (hsub x hx)).2.2.2 hea
  -- the residual `Eq` spine: framed, in context, read
  obtain ⟨hfR, hCR⟩ := piResidual_frameK hres hfT hCT hfargs
  obtain ⟨RA, hRA⟩ := denote_piResidual_exists m.acval_closed (acval_inst_self m) args
    hres hfT.1 (fun x hx => ⟨(hfargs x hx).1.1, (hfargs x hx).1.2.1⟩) (hTd d) hsp
  obtain ⟨g₂, ra, hg₂, hra, rfl⟩ := denote_app_inv hRA
  obtain ⟨g₁, la, hg₁, hla, rfl⟩ := denote_app_inv hg₂
  obtain ⟨Ea, Aa, hEa, hAa, rfl⟩ := denote_app_inv hg₁
  obtain rfl : la = ea := Option.some.inj (hla.symm.trans hea)
  have hrR : r ∈ ConLeche.appSubterms (.app (.app (.app (.const eqName [u]) A) l) r) := by
    simp only [ConLeche.appSubterms, List.mem_cons, List.mem_append]
    exact Or.inr (Or.inr (self_mem_appSubterms r))
  obtain ⟨hfr, -⟩ := appSubterms_frame hrR hfR hCR
  -- the stored `Eq` and its level
  obtain ⟨ci, hfE, hlenE, rfl⟩ : ∃ ci, env.find? eqName = some ci ∧
      [u].length = ci.toConstantVal.levelParams.length ∧
      Ea = m.acval eqName (Level.substFn φ ci.toConstantVal.levelParams [u]) := by
    rw [denote] at hEa
    cases hf : env.find? eqName with
    | none => rw [hf] at hEa; exact nomatch hEa
    | some ci =>
      rw [hf] at hEa
      simp only at hEa
      split at hEa
      · exact ⟨ci, rfl, by assumption, (Option.some.inj hEa).symm⟩
      · exact nomatch hEa
  obtain ⟨p, hp⟩ : ∃ p, ci.toConstantVal.levelParams = [p] := by
    match hps : ci.toConstantVal.levelParams, hlenE with
    | [p], _ => exact ⟨p, rfl⟩
  have hψp : Level.substFn φ [p] [u] p = u.eval φ := by
    simp [Level.substFn]
  have hlaw := (hin.eq_law ci p hfE hp (Level.substFn φ [p] [u])).1
  -- the rule's law, at the levels and the depth of the firing
  obtain ⟨cv', hf', hsome, hlawR⟩ := hin.rule_law h (ruleNamed_of_rulesFor hmem)
  rw [hthm] at hf'
  obtain rfl : cv = cv' := by simpa using hf'
  obtain ⟨⟨P, L, R, LA, PU⟩, hsides⟩ := Option.isSome_iff_exists.mp hsome
  obtain ⟨v, hv⟩ := ConLeche.ruleLevel_of_ruleSides _ hsides
  obtain ⟨pa, la', ra', laa, pua, hpa, hla', hra', hlaa, hpua, hlawρ⟩ :=
    hlawR P L R LA PU hsides (Level.substFn φ cv.levelParams us) d
  have hsides' := ConLeche.ruleSides_instantiateLevelParams cv.levelParams us _ hsides
  have hv' := ConLeche.ruleLevel_instantiateLevelParams cv.levelParams us _ hv
  have hinst : ∀ (X : Expr) (xa : Term),
      denote m.acval env (Level.substFn φ cv.levelParams us) d X = some xa →
      denote m.acval env φ d (X.instantiateLevelParams cv.levelParams us) = some xa :=
    fun X xa hx => (denotePInstLevels m φ cv.levelParams us d X).trans hx
  have hST := sidesT_of_denote (acval := m.acval) (env := env) (ψ := φ) _ _ rfl hsides' hv'
    (hTd d) (hinst P pa hpa) (hinst L la' hla') (hinst R ra' hra') (hinst LA laa hlaa)
    (hinst PU pua hpua)
  have hu : u = Level.subst cv.levelParams us v :=
    ConLeche.piResidual_ruleLevel args _ hsides' hv' hres
  refine ⟨hfr, fun x hx => hLS x (hleaves x hx), ra, hra, fun ρ hρ hLe hge hne => ?_⟩
  have hLl : LeavesGr m φ d l ρ := hLe.of_subset hLS
  have hLargs : ∀ x ∈ args, LeavesGr m φ d x ρ :=
    fun x hx => hLl.of_subset (hlargs x hx)
  have hLT : LeavesGr m φ d (cv.type.instantiateLevelParams cv.levelParams us) ρ :=
    LeavesGr.of_fvarLeaves_nil (ConLeche.Expr.fvarLeaves_eq_nil_of_not_hasFvar hnfT)
  -- the certificate's fit, at the residual's reading
  obtain ⟨resta, hcs⟩ := hcerts hfT hCT (hTd d) hfargs hsp
  obtain ⟨-, hfit, hwres⟩ := hcs ρ hρ hLT hLargs (hTok ρ)
  have hresta := teleFitPA_residualK m.acval_closed (acval_inst_self m) args hres hfT.1
    (fun x hx => ⟨(hfargs x hx).1.1, (hfargs x hx).1.2.1⟩) (hTd d) hsp hfit
  rw [hRA] at hresta
  obtain rfl := Option.some.inj hresta
  have hgr : WellDenoted V ρ ra := by
    rw [WellDenoted_app] at hwres
    exact hwres.2.1
  have hgl : WellDenoted V ρ la := by
    rw [WellDenoted_app, WellDenoted_app] at hwres
    exact hwres.1.2.1
  obtain ⟨hlmem, hrmem, hAmem⟩ :=
    sidesT_fit hfit hST (hlawρ ρ).1 (hlawρ ρ).2.1 (hlawρ ρ).2.2 rfl
  obtain ⟨y, hy⟩ := teleFitPA_inhabited hfit (hTmem ρ)
  simp only [interp_app] at hy
  rw [hp] at hy
  have hAu : interp V ρ Aa ∈ˢ (univ (Level.substFn φ [p] [u] p) : V) := by
    rw [hψp, hu]
    simpa [interp_sort] using hAmem
  rw [hlaw ρ _ _ _ hAu hlmem hrmem] at hy
  exact ⟨hgr, (hsem ρ hρ hLe hge hgl hne).trans (eq_of_mem_eqv hy)⟩

end ConLeche.Model.Rules
