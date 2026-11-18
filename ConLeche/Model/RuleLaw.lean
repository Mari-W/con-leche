module

import ConLeche.Model.Capstone
import ConLeche.Verify.Denote.Closed
public import ConLeche.Semantics.DeclRun
public import ConLeche.Model.Env.EnvModelM

public section

/-!
# A rule's law, from its registration's runs

`ruleLaw_of_run`: a registration's recorded runs (`RuleLawRun`) give the rule's law
(`RuleLaw`) at the registration's carrier.  Each of the three typings is `harvestDefn`'s
membership argument at a closed term (`mem_of_runs`): the inferred type holds the term, the
declared type is a type by its sort run, and the conversion run equates the two types, which
are both types and so neither is the point.
-/

namespace ConLeche.Model
open ConLeche.Semantics ConLeche.SetModel ConLeche.Term ConLeche.Verify SetTheory

open ConLeche (Env Expr Name Level ConstantInfo inferTypeCore isDefEqCore)

universe w

variable {V : Type w} [SetTheory V] {env : Env} {F : Nat}

/-- **A closed term inhabits a declared type** where its inferred type converts to it and the
declared type is a type (`harvestDefn`'s membership). -/
theorem mem_of_runs (mp : EnvModelM V env) {v T vt sT : Expr} {u : Level}
    (hvf : v.hasFvar = false) (hvb : v.looseBVarsBounded 0 = true)
    (hTf : T.hasFvar = false) (hTb : T.looseBVarsBounded 0 = true)
    (hvrun : inferTypeCore .verified false env F 0 v = .ok vt)
    (hvde : isDefEqCore .verified false env F 0 vt T = .ok true)
    (hst : inferTypeCore .verified false env F 0 T = .ok sT)
    (hens : ConLeche.ensureSortCore .verified false env F 0 sT = .ok u) (ψ : Name → Nat) :
    ∃ va ta, denote mp.base2.acval env ψ 0 v = some va ∧
      denote mp.base2.acval env ψ 0 T = some ta ∧
      ∀ ρ : Nat → V, interp V ρ va ∈ˢ interp V ρ ta := by
  have hwv : Expr.WScoped 0 v := Expr.WScoped.of_not_hasFvar hvf
  have hnlv : v.fvarLeaves = [] := Expr.fvarLeaves_eq_nil_of_not_hasFvar hvf
  have hLv : Expr.LeavesBounded v := fun l hl => by rw [hnlv] at hl; exact absurd hl List.not_mem_nil
  have hwt : Expr.WScoped 0 T := Expr.WScoped.of_not_hasFvar hTf
  have hnlt : T.fvarLeaves = [] := Expr.fvarLeaves_eq_nil_of_not_hasFvar hTf
  have hLt : Expr.LeavesBounded T := fun l hl => by rw [hnlt] at hl; exact absurd hl List.not_mem_nil
  obtain ⟨va, hva⟩ := acceptedReads_of mp.base2 ψ hvrun hwv hvb hLv
  obtain ⟨ta, hta⟩ := acceptedReads_of mp.base2 ψ hst hwt hTb hLt
  have hclaims := checkSoundAt (V := V) (Rules.RulesInputs.ofSem mp ψ) F
  have hreads : InferReads mp.base2 ψ F := inferReads_of (Rules.RulesInputs.ofSem mp ψ)
  obtain ⟨-, ihw, ihd, ihi⟩ := hclaims
  obtain ⟨vta, hvta⟩ := hreads hvrun hwv hvb hLv (CtxOk.nil hnlv) hva
  obtain ⟨sta, hsta⟩ := hreads hst hwt hTb hLt (CtxOk.nil hnlt) hta
  have hrV := ihi hvrun hwv hvb hLv (CtxOk.nil hnlv) hva hvta
  have hrT := ihi hst hwt hTb hLt (CtxOk.nil hnlt) hta hsta
  refine ⟨va, ta, hva, hta, fun ρ => ?_⟩
  have hTaTy : IsTy (interp V ρ ta) :=
    IsTy_of_mem_univ ((sortSemAt_of_claims ihw ihi hreads)
      (CtxOk.nil hnlt) hwt hTb hLt hst (ConLeche.ensureSortCore_inv hens) hta ρ (Sat_nil V ρ)).2
  have hwvt : Expr.WScoped 0 vt := inferTypeCore_WScoped mp.base2.wf F hvrun hwv
  have hbvt : vt.looseBVarsBounded 0 = true := inferTypeCore_looseBVars mp.base2.wf F hvrun hwv hvb hLv
  have hnlvt : vt.fvarLeaves = [] := by
    have hsub := inferTypeCore_fvarLeaves mp.base2.wf F hvrun hwv
    cases hh : vt.fvarLeaves with
    | nil => rfl
    | cons l ls =>
      have := hsub l (by rw [hh]; exact List.mem_cons_self ..)
      rw [hnlv] at this
      exact absurd this List.not_mem_nil
  have hLvt : Expr.LeavesBounded vt := fun l hl => by rw [hnlvt] at hl; exact absurd hl List.not_mem_nil
  obtain ⟨-, hrTv, hrMv⟩ := hrV
  obtain ⟨htE, -, -⟩ := hrT
  have heq : interp V ρ vta = interp V ρ ta :=
    eq_of_IsTy_of_ne_pt (hrTv ρ (Sat_nil V ρ)).2 hTaTy
      (ihd hvde hwvt hbvt hLvt hwt hTb hLt (CtxOk.nil hnlvt) (CtxOk.nil hnlt) hvta hta
        (fun σ hσ => (hrTv σ hσ).1) htE ρ (Sat_nil V ρ))
  rw [← heq]
  exact hrMv ρ (Sat_nil V ρ)

/-- A closed term's reading at depth `0` is its reading at every depth. -/
theorem denote_all_depths (mp : EnvModelM V env) {e : Expr} {ea : Term} {ψ : Name → Nat}
    (hf : e.hasFvar = false) (hb : e.looseBVarsBounded 0 = true)
    (h : denote mp.base2.acval env ψ 0 e = some ea) (d : Nat) :
    denote mp.base2.acval env ψ d e = some ea :=
  denote_depth_of_closed mp.base2.acval_closed hf
    (fun k => denote_liftN_eq_self mp.base2.cval_closed hf hb h 1 k) h d

/-- **A rule's law, from its registration's runs** (`RuleLawRun`). -/
theorem ruleLaw_of_run (mp : EnvModelM V env) {thm : Name} (hrun : RuleLawRun F env thm) :
    ∃ cv, env.find? thm = some (.thmInfo cv) ∧ (ConLeche.ruleSides cv.type).isSome = true ∧
      RuleLaw V mp.base2 cv.type := by
  obtain ⟨cv, P, L, R, LA, PU, hf, hs, ⟨sPU, v, hsPU, hv⟩, ⟨sP, u, hsP, hu⟩, ⟨tA, htA, hdA⟩,
    ⟨tL, htL, hdL⟩, ⟨tR, htR, hdR⟩⟩ := hrun
  have hwf := mp.base2.wf.consts _ (ConLeche.Env.find?_mem hf)
  obtain ⟨fP, fL, fR, fLA, fPU⟩ := ConLeche.ruleSides_hasFvar hs hwf.1
  obtain ⟨bP, bL, bR, bLA, bPU⟩ := ConLeche.ruleSides_looseBVarsBounded hs hwf.2.2.2.1
  refine ⟨cv, hf, by rw [hs]; rfl, fun P' L' R' LA' PU' hs' ψ d => ?_⟩
  rw [hs] at hs'
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ : P = P' ∧ L = L' ∧ R = R' ∧ LA = LA' ∧ PU = PU' := by
    simpa using hs'
  obtain ⟨la, pa, hla, hpa, hmL⟩ := mem_of_runs mp fL bL fP bP htL hdL hsP hu ψ
  obtain ⟨ra, pa', hra, hpa', hmR⟩ := mem_of_runs mp fR bR fP bP htR hdR hsP hu ψ
  obtain ⟨laa, pua, hlaa, hpua, hmA⟩ := mem_of_runs mp fLA bLA fPU bPU htA hdA hsPU hv ψ
  obtain rfl : pa' = pa := Option.some.inj (hpa'.symm.trans hpa)
  exact ⟨pa', la, ra, laa, pua, denote_all_depths mp fP bP hpa' d, denote_all_depths mp fL bL hla d,
    denote_all_depths mp fR bR hra d, denote_all_depths mp fLA bLA hlaa d,
    denote_all_depths mp fPU bPU hpua d, fun ρ => ⟨hmL ρ, hmR ρ, hmA ρ⟩⟩

end ConLeche.Model
