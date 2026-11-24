module

public import ConLeche.Model.Rules.Inputs
import ConLeche.Model.Rules.IotaSoundKit
import ConLeche.Model.Rules.RedSoundKit
import ConLeche.Model.CtxOkKit
import ConLeche.Verify.Denote.Inst

public section

/-!
# The soundness of a rule firing's certificate (`CertsR`)

`CertsR` is `CertsF` with one more step, `head`: a slot whose argument is the fired term's own
argument at position `j`, where the head's telescope along the term's first `j` arguments has the
binder's domain, runs no inference.  A reduction claims nothing of a term that is the point, so
`CertsRSem` may assume the term graded and not the point.  Then every prefix of its spine is a
graph, its head's reading lies in the head's type (`ConstType`), and the application clause of the
prefix that ends at position `j` puts the argument in the domain there (`headSlot_mem`), as
`teleFitPA_of_peel_ne_pt` does for a whole spine.  That domain is the binder's, so the slot fits.
-/

namespace ConLeche.Model.Rules
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory

open ConLeche (Env Expr Name Level)
open ConLeche.Rules

universe w

variable {V : Type w} [SetTheory V] {env : Env} {m : EnvModel V env}
  {φ : Name → Nat}

/-- **A graded spine that is not the point puts its argument at a head slot in the slot's
domain**: the telescope peeled along the arguments before the slot (`piResidual`) is a `∀` whose
domain reads, and the argument's reading is graded and lies in that domain. -/
theorem headSlot_mem {ρ : Nat → V} {d : Nat} :
    ∀ (as : List Expr) {bs : List Expr} {a' T ty body : Expr} {Ta f : Term} {vsAll : List Term},
      ConLeche.piResidual T as = some (.forallE ty body) →
      Expr.WScoped d T →
      (∀ a ∈ as, Expr.WScoped d a ∧ a.looseBVarsBounded 0 = true) →
      denote m.acval env φ d T = some Ta →
      DenoteSpine m.acval env φ d (as ++ a' :: bs) vsAll →
      WellDenoted V ρ Ta → interp V ρ f ∈ˢ interp V ρ Ta →
      WellDenoted V ρ (Term.mkAppN f vsAll) → interp V ρ (Term.mkAppN f vsAll) ≠ pt →
      ∃ tya xa, denote m.acval env φ d ty = some tya ∧ denote m.acval env φ d a' = some xa ∧
        WellDenoted V ρ xa ∧ interp V ρ xa ∈ˢ interp V ρ tya := by
  intro as
  induction as with
  | nil =>
    intro bs a' T ty body Ta f vsAll hpr _ _ hTa hsp hT hmem hg hne
    obtain rfl : T = .forallE ty body := Option.some.inj hpr
    obtain ⟨doma, bodya, hdoma, -, rfl⟩ := denote_forallE_inv hTa
    cases hsp with | @cons _ xa _ ys hxa _ =>
    have hg' : WellDenoted V ρ (Term.mkAppN (.app f xa) ys) := hg
    have hne' : interp V ρ (Term.mkAppN (.app f xa) ys) ≠ pt := hne
    have happ : WellDenoted V ρ (.app f xa) := mkAppN_head ys hg'
    have hfne : interp V ρ f ≠ pt := by
      intro h0
      exact hne' (interp_mkAppN_of_pt (by rw [interp_app, h0, app_pt]) ys)
    have hmem' := hmem
    rw [interp_pi] at hmem'
    exact ⟨doma, xa, hdoma, hxa, happ.app_arg,
      happ.app_clause.mem (mem_piSet_of_mem_piV hmem' hfne)⟩
  | cons a as ih =>
    intro bs a' T ty body Ta f vsAll hpr hwT hargs hTa hsp hT hmem hg hne
    match T, hpr, hwT, hTa with
    | .bvar _, hpr, _, _ => exact nomatch hpr
    | .fvar _ _, hpr, _, _ => exact nomatch hpr
    | .sort _, hpr, _, _ => exact nomatch hpr
    | .const _ _, hpr, _, _ => exact nomatch hpr
    | .app _ _, hpr, _, _ => exact nomatch hpr
    | .lam _ _, hpr, _, _ => exact nomatch hpr
    | .letE _ _ _, hpr, _, _ => exact nomatch hpr
    | .lit _, hpr, _, _ => exact nomatch hpr
    | .proj _ _ _, hpr, _, _ => exact nomatch hpr
    | .forallE dom b, hpr, hwT, hTa => ?_
    obtain ⟨doma, bodya, hdoma, hbodya, rfl⟩ := denote_forallE_inv hTa
    cases hsp with | @cons _ va _ vs' hva hsp' =>
    obtain ⟨hwa, hba⟩ := hargs a List.mem_cons_self
    obtain ⟨-, hbw⟩ : Expr.WScoped d dom ∧ Expr.WScoped d b := by
      simpa [Expr.WScoped] using hwT
    have hg' : WellDenoted V ρ (Term.mkAppN (.app f va) vs') := hg
    have hne' : interp V ρ (Term.mkAppN (.app f va) vs') ≠ pt := hne
    have happ : WellDenoted V ρ (.app f va) := mkAppN_head vs' hg'
    have hfne : interp V ρ f ≠ pt := by
      intro h0
      exact hne' (interp_mkAppN_of_pt (by rw [interp_app, h0, app_pt]) vs')
    have hmem' := hmem
    rw [interp_pi] at hmem'
    have hxA : interp V ρ va ∈ˢ interp V ρ doma :=
      happ.app_clause.mem (mem_piSet_of_mem_piV hmem' hfne)
    have hBx : WellDenoted V ρ (bodya.inst va) :=
      (WellDenoted_inst0 _ happ.app_arg).mpr (hT.pi_body _ hxA)
    have hmemB : interp V ρ (.app f va) ∈ˢ interp V ρ (bodya.inst va) := by
      rw [interp_inst0, interp_app]
      exact app_mem_piV hmem' hxA
    have hbody' : denote m.acval env φ d (b.instantiate1 a) = some (bodya.inst va) := by
      rw [denote_beta m.acval_closed (acval_inst_self m)
        (ty := dom) hbw.fvarsBelow hwa hba hva 0, hbodya]
      rfl
    exact ih hpr (Expr.WScoped.instantiate1_gen hwa 0 hbw)
      (fun x hx => hargs x (List.mem_cons_of_mem a hx)) hbody' hsp' hBx hmemB hg' hne'

theorem CertsR.nil_sound {d : Nat} {e T : Expr} : CertsRSem m φ d e T [] := by
  intro _ _ Δa Ta ea vs _ _ _ _ _ hsp
  cases hsp
  exact ⟨Ta, fun _ _ _ _ _ hgT _ _ => ⟨by simp, .nil, hgT⟩⟩

/-- The step shared by both kinds of slot: from the slot's grading and membership at each
valuation, the fit of the rest gives the fit of the whole. -/
theorem CertsR.step_sound {d : Nat} {e ty body arg : Expr} {rest : List Expr}
    (hrest : CertsRSem m φ d e (body.instantiate1 arg) rest)
    (hslot : ∀ {Δa : List Term} {ea aa doma : Term}, Frame d arg → CtxOkS m φ d Δa arg →
      Frame d e → CtxOkS m φ d Δa e →
      denote m.acval env φ d e = some ea → denote m.acval env φ d arg = some aa →
      denote m.acval env φ d ty = some doma → CtxOkS m φ d Δa ty → Frame d ty →
      ∀ ρ : Nat → V, Sat V Δa ρ → LeavesGr m φ d arg ρ → LeavesGr m φ d e ρ →
        LeavesGr m φ d ty ρ → WellDenotedTy V ρ doma →
        WellDenoted V ρ ea → interp V ρ ea ≠ pt →
        WellDenoted V ρ aa ∧ interp V ρ aa ∈ˢ interp V ρ doma) :
    CertsRSem m φ d e (.forallE ty body) (arg :: rest) := by
  intro hfT hfe Δa Ta ea vs hCT hCe hTa hea hargs hsp
  obtain ⟨hwty, hbty, hLbty⟩ := hfT
  obtain ⟨hdomw, hbodyw⟩ : Expr.WScoped d ty ∧ Expr.WScoped d body := by
    simpa [Expr.WScoped] using hwty
  obtain ⟨hdomb, hbodyb⟩ :
      ty.looseBVarsBounded 0 = true ∧ Expr.looseBVarsBounded 1 body = true := by
    simpa [Expr.looseBVarsBounded, Bool.and_eq_true] using hbty
  have hLbdom : Expr.LeavesBounded ty := fun l hl =>
    hLbty l (by simp [Expr.fvarLeaves, hl])
  have hCdom : CtxOkS m φ d Δa ty := hCT.forallE_ty
  obtain ⟨doma, bodya, hdoma, hbodya, rfl⟩ := denote_forallE_inv hTa
  cases hsp with | @cons _ aa _ vs' haa hsp' =>
  obtain ⟨hfarg, hCarg⟩ := hargs arg List.mem_cons_self
  obtain ⟨hwa, hba, hLa⟩ := hfarg
  have hbody' : denote m.acval env φ d (body.instantiate1 arg)
      = some (bodya.inst aa) := by
    rw [denote_beta m.acval_closed (acval_inst_self m)
      (ty := ty) hbodyw.fvarsBelow hwa hba haa 0, hbodya]
    rfl
  have hLbbody : Expr.LeavesBounded (body.instantiate1 arg) := by
    intro l hl
    rcases ConLeche.Expr.fvarLeaves_instantiate1 body 0 hl with hl' | hl'
    · exact hLbty l (by simp [Expr.fvarLeaves, hl'])
    · exact hLa l hl'
  have hsubBody : ∀ l ∈ (body.instantiate1 arg).fvarLeaves,
      l ∈ (Expr.forallE ty body).fvarLeaves ∨ l ∈ arg.fvarLeaves := by
    intro l hl
    rcases ConLeche.Expr.fvarLeaves_instantiate1 body 0 hl with hl' | hl'
    · exact Or.inl (by simp [Expr.fvarLeaves, hl'])
    · exact Or.inr hl'
  have hCbody : CtxOkS m φ d Δa (body.instantiate1 arg) := by
    refine ⟨hCT.1, fun l hl => ?_⟩
    rcases hsubBody l hl with hl' | hl'
    · exact hCT.2 l hl'
    · exact hCarg.2 l hl'
  obtain ⟨resta, hfit⟩ :=
    hrest ⟨ConLeche.Expr.WScoped.instantiate1_gen hwa 0 hbodyw,
        ConLeche.Expr.looseBVarsBounded_instantiate1_gen hba hbodyb, hLbbody⟩
      hfe hCbody hCe hbody' hea (fun x hx => hargs x (List.mem_cons_of_mem arg hx)) hsp'
  refine ⟨resta, fun ρ hρ hLT hLe hLargs hgT hge hne => ?_⟩
  have hLarg : LeavesGr m φ d arg ρ := hLargs arg List.mem_cons_self
  have hokDom : WellDenotedTy V ρ doma := hgT.pi_dom
  obtain ⟨hokA, hmemA⟩ := hslot ⟨hwa, hba, hLa⟩ hCarg hfe hCe hea haa hdoma hCdom
    ⟨hdomw, hdomb, hLbdom⟩ ρ hρ hLarg hLe hLT.forallE_ty hokDom hge hne
  have hokBody : WellDenoted V ρ (bodya.inst aa) :=
    (WellDenoted_inst0 _ hokA).mpr (hgT.pi_body _ hmemA)
  have hLbody : LeavesGr m φ d (body.instantiate1 arg) ρ := by
    intro l hl
    rcases hsubBody l hl with hl' | hl'
    · exact hLT l hl'
    · exact hLarg l hl'
  obtain ⟨hgvs', hfit', hgresta⟩ := hfit ρ hρ hLbody hLe
    (fun x hx => hLargs x (List.mem_cons_of_mem arg hx)) hokBody hge hne
  refine ⟨fun x hx => ?_, .cons hmemA hfit', hgresta⟩
  rcases List.mem_cons.mp hx with rfl | hx'
  · exact hokA
  · exact hgvs' x hx'

/-- **The certified slot**: the full-grade inference establishes the argument's grading and its
membership in its inferred type, a type equal to the binder's domain (`CertsF.cert_sound`). -/
theorem CertsR.cert_sound {d : Nat} {e ty body arg ta : Expr} {rest : List Expr}
    (hta : InferSemFull m φ d arg ta) (hd : DefEqSem m φ d ta ty)
    (hrest : CertsRSem m φ d e (body.instantiate1 arg) rest) :
    CertsRSem m φ d e (.forallE ty body) (arg :: rest) := by
  refine CertsR.step_sound hrest ?_
  intro Δa ea aa doma hfarg hCarg _ _ _ haa hdoma hCdom hfdom ρ hρ hLarg _ hLdom hokDom _ _
  obtain ⟨hfta, hsubta, taA, htaA, hA⟩ := hta hfarg hCarg haa
  obtain ⟨hokA, hgtaA, hmem⟩ := hA ρ hρ hLarg
  have heq := hd hfta hfdom (hCarg.of_subset hsubta) hCdom
    htaA hdoma ρ hρ (hLarg.of_subset hsubta) hLdom hgtaA.1 hokDom.1
    hgtaA.ne_pt hokDom.ne_pt
  exact ⟨hokA, heq ▸ hmem⟩

/-- **The head slot**: the fired term is graded and not the point, so the prefix of its spine
that ends at the slot is a graph application, and its application clause puts the argument in the
head's domain there (`headSlot_mem`), which is the binder's. -/
theorem CertsR.head_sound (hin : RulesInputs V m φ) {d : Nat} {e T ty body arg : Expr}
    {rest : List Expr} {j : Nat}
    (hT : ConLeche.headTypeOf env.find? e = some T) (harg : e.getAppArgs[j]? = some arg)
    (hdom : ConLeche.teleDomAt T e.getAppArgs j = some ty)
    (hrest : CertsRSem m φ d e (body.instantiate1 arg) rest) :
    CertsRSem m φ d e (.forallE ty body) (arg :: rest) := by
  refine CertsR.step_sound hrest ?_
  intro Δa ea aa doma _ _ hfe hCe hea haa hdoma _ _ ρ _ _ _ _ _ hge hne
  -- the head: a stored constant at its levels, whose type `T` reads and holds its reading
  unfold ConLeche.headTypeOf at hT
  split at hT
  next c ls hfn =>
    split at hT
    next ci hf =>
      split at hT
      next hlen =>
        obtain rfl := (Option.some.inj hT).symm
        have hea' := hea
        rw [show e = Expr.mkAppN e.getAppFn e.getAppArgs from
          (ConLeche.Expr.mkAppN_getApp e).symm, hfn] at hea'
        obtain ⟨vc, xs, hvc, hspx, rfl⟩ := denote_mkAppN_inv hea'
        rw [denote_const hf hlen] at hvc
        obtain rfl := (Option.some.inj hvc).symm
        obtain ⟨ta, hTd, hTok, hTmem, hnfT, hbdT⟩ := constTy_pkg hin.const_ty hf hlen
        obtain ⟨hfT, -⟩ := frame_of_not_hasFvar (m := m) (φ := φ) hnfT hbdT hCe.1
        -- the spine split at the slot
        have hj : j < e.getAppArgs.length := by
          obtain ⟨h, -⟩ := List.getElem?_eq_some_iff.mp harg; exact h
        have hsplit : e.getAppArgs
            = e.getAppArgs.take j ++ arg :: e.getAppArgs.drop (j + 1) := by
          obtain ⟨_, hx⟩ := List.getElem?_eq_some_iff.mp harg
          have h1 := (List.take_append_drop j e.getAppArgs).symm
          rw [List.drop_eq_getElem_cons hj, hx] at h1
          exact h1
        unfold ConLeche.teleDomAt at hdom
        split at hdom
        next dom body' hres =>
          obtain rfl := Option.some.inj hdom
          have hfr := frame_spine hfe hCe
          rw [hsplit] at hspx
          obtain ⟨tya, xa, htya, hxa, hgx, hmx⟩ := headSlot_mem (m := m) (φ := φ) (ρ := ρ)
            (e.getAppArgs.take j) hres hfT.1
            (fun x hx => ⟨(hfr x (List.mem_of_mem_take hx)).1.1,
              (hfr x (List.mem_of_mem_take hx)).1.2.1⟩) (hTd d) hspx (hTok ρ) (hTmem ρ) hge hne
          obtain rfl : xa = aa := Option.some.inj (hxa.symm.trans haa)
          obtain rfl : tya = doma := Option.some.inj (htya.symm.trans hdoma)
          exact ⟨hgx, hmx⟩
        next => exact nomatch hdom
      next => exact nomatch hT
    next => exact nomatch hT
  next => exact nomatch hT

end ConLeche.Model.Rules
