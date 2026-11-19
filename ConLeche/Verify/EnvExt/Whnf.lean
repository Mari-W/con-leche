module

public import ConLeche.Verify.EnvExt.Rel
public import ConLeche.Verify.InferLemmas
import ConLeche.Verify.IotaReduct

/-!
# A run does not see an extension of the environment: head normalization and inference (task #480)
-/

@[expose] public section

namespace ConLeche.Verify

open ConLeche

variable {env₁ env₂ : Env} {r₂ r₁ : CoreFns CheckM}

/-- What an optional result carries. -/
abbrev ResO (env : Env) (o : Option Expr) : Prop := ∀ x, o = some x → Res env x

theorem resO_none {env : Env} : ResO env none := fun _ h => nomatch h

theorem natOpResult_cases {c : Name} {a b : Nat} {x : Expr} (h : natOpResult c a b = some x) :
    (∃ n, x = .lit (.natVal n)) ∨
      ((c = natBeqName ∨ c = natBleName) ∧
        (x = .const boolTrueName [] ∨ x = .const boolFalseName [])) := by
  have key : ∀ {G : Prop} {q : Prop} [Decidable q] {u v : Option Expr},
      (q → u = some x → G) → (¬q → v = some x → G) → (if q then u else v) = some x → G := by
    intro G q _ u v h₁ h₂ he
    by_cases hq : q
    · exact h₁ hq (by simpa only [hq, ↓reduceIte] using he)
    · exact h₂ hq (by simpa only [hq, ↓reduceIte] using he)
  have hbool : ∀ q [Decidable q], ((if q then boolTrueName else boolFalseName) = boolTrueName ∨
      (if q then boolTrueName else boolFalseName) = boolFalseName) := by
    intro q _
    by_cases hq : q <;> simp [hq]
  unfold natOpResult at h
  revert h
  repeat' refine key (fun hq => ?_) (fun hq => ?_)
  all_goals
    intro h
    first
    | (obtain rfl := Option.some.inj h; exact .inl ⟨_, rfl⟩)
    | (obtain rfl := Option.some.inj h
       rcases hbool (a = b) with he | he
       · exact .inr ⟨.inl hq, .inl (by rw [he])⟩
       · exact .inr ⟨.inl hq, .inr (by rw [he])⟩)
    | (obtain rfl := Option.some.inj h
       rcases hbool (a ≤ b) with he | he
       · exact .inr ⟨.inr hq, .inl (by rw [he])⟩
       · exact .inr ⟨.inr hq, .inr (by rw [he])⟩)
    | simp at h

theorem nat_of_rawNatLit {w : Expr} {n : Nat} (hw : Res env₁ w) (h : rawNatLit? w = some n) :
    (env₁.find? natName).isSome = true ∨ (env₁.find? natZeroName).isSome = true ∨
      (env₁.find? natSuccName).isSome = true := by
  cases w with
  | lit l =>
    cases l with
    | natVal m =>
      simp only [Res, Expr.constsResolve, Bool.and_eq_true] at hw
      exact .inl hw.1.1
    | strVal _ => exact nomatch h
  | const c us =>
    cases us with
    | nil =>
      simp only [rawNatLit?] at h
      split at h
      · rename_i hc
        subst hc
        exact .inr (.inl (res_const.mp hw))
      · exact nomatch h
    | cons _ _ => exact nomatch h
  | _ => exact nomatch h

theorem natOpName_of_bin {c : Name}
    (h : c = natAddName ∨ c = natSubName ∨ c = natMulName ∨
        c = natPowName ∨ c = natBeqName ∨ c = natBleName ∨
        c = natDivName ∨ c = natModName ∨ c = natGcdName ∨
        c = natLandName ∨ c = natLorName ∨ c = natXorName ∨
        c = natShiftLeftName ∨ c = natShiftRightName) : natOpName c = true := by
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    decide

theorem res_natOpResult (hf : StoredFacts env₁) {c : Name} {a b : Nat} {x : Expr}
    (hs : isDefinitionAt env₁ c = true)
    (hn : (env₁.find? natName).isSome = true ∨ (env₁.find? natZeroName).isSome = true ∨
      (env₁.find? natSuccName).isSome = true)
    (h : natOpResult c a b = some x) : Res env₁ x := by
  rcases natOpResult_cases h with ⟨n, rfl⟩ | ⟨hc, hx⟩
  · exact res_natLit hf hn n
  · obtain ⟨ht, hfa⟩ := hf.boolCtors (by rcases hc with rfl | rfl; exact .inl hs; exact .inr hs)
    rcases hx with rfl | rfl
    · exact res_const.mpr ht
    · exact res_const.mpr hfa

theorem andRescueSlots_ext (hx : EnvExt env₁ env₂) (hA : (env₁.find? andName).isSome = true)
    (ctor : Name) (nP : Nat) : andRescueSlots env₂ ctor nP = andRescueSlots env₁ ctor nP := by
  unfold andRescueSlots andRescueSlotsOf
  simp only [hx.findProj hA]

theorem res_openPisAtFvars : ∀ (n : Nat) {e : Expr} (i : Nat) {fvs : List Expr} {b : Expr},
    Res env₁ e → openPisAtFvars n e i = some (fvs, b) → ∀ x ∈ fvs, Res env₁ x
  | 0, _, _, _, _, _, h => by
    simp only [openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at h
    intro x hx
    rw [← h.1] at hx
    exact nomatch hx
  | n + 1, e, i, fvs, b, he, h => by
    cases e with
    | forallE dom body =>
      obtain ⟨hd, hb⟩ := res_forall.mp he
      simp only [openPisAtFvars] at h
      split at h
      · rename_i fvs' e' heq
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact res_fvar.mpr hd
        · exact res_openPisAtFvars n (i + 1) (res_open hd hb) heq x hx
      · exact nomatch h
    | _ => simp [openPisAtFvars] at h

theorem projGuardRows_ext (hx : EnvExt env₁ env₂) {entry : ProjEntry}
    (hc : (env₁.find? entry.ctor).isSome = true) (us : List Level) :
    projGuardRows env₂.find? entry us = projGuardRows env₁.find? entry us := by
  unfold projGuardRows
  rw [hx.find_of_isSome hc]

/-- What an opening leaves resolves. -/
theorem res_openPisAtFvars_body : ∀ (n : Nat) {e : Expr} (i : Nat) {fvs : List Expr} {b : Expr},
    Res env₁ e → openPisAtFvars n e i = some (fvs, b) → Res env₁ b
  | 0, _, _, _, _, he, h => by
    simp only [openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.2]; exact he
  | n + 1, e, i, fvs, b, he, h => by
    cases e with
    | forallE dom body =>
      obtain ⟨hd, hb⟩ := res_forall.mp he
      simp only [openPisAtFvars] at h
      split at h
      · rename_i fvs' e' heq
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        exact res_openPisAtFvars_body n (i + 1) (res_open hd hb) heq
      · exact nomatch h
    | _ => simp [openPisAtFvars] at h

/-- The rows of the field loop resolve. -/
theorem res_projGuardRowsGo : ∀ (k : Nat) {d : Nat} {r : Expr} {rows : List (Nat × Expr)},
    Res env₁ r → projGuardRowsGo k d r = some rows → ∀ row ∈ rows, Res env₁ row.2
  | 0, d, .forallE dom body, rows, he, h => by
    obtain ⟨hd, -⟩ := res_forall.mp he
    simp only [projGuardRowsGo, Option.some.injEq] at h
    subst h
    intro row hrow
    rcases List.mem_singleton.mp hrow with rfl
    exact hd
  | k + 1, d, .forallE dom body, rows, he, h => by
    obtain ⟨hd, hb⟩ := res_forall.mp he
    simp only [projGuardRowsGo] at h
    split at h
    · revert h
      cases hrec : projGuardRowsGo k (d + 1) (body.instantiate1 (.fvar d dom)) with
      | none => intro h; exact nomatch h
      | some rows' =>
        intro h
        simp only [Option.some.injEq] at h
        subst h
        intro row hrow
        rcases List.mem_cons.mp hrow with rfl | hrow
        · exact hd
        · exact res_projGuardRowsGo k (res_open hd hb) hrec row hrow
    · exact res_projGuardRowsGo k hb h
  | 0, _, .bvar _, _, _, h | 0, _, .fvar .., _, _, h | 0, _, .sort _, _, _, h
  | 0, _, .const .., _, _, h | 0, _, .app .., _, _, h | 0, _, .lam .., _, _, h
  | 0, _, .letE .., _, _, h | 0, _, .lit _, _, _, h | 0, _, .proj .., _, _, h
  | _ + 1, _, .bvar _, _, _, h | _ + 1, _, .fvar .., _, _, h | _ + 1, _, .sort _, _, _, h
  | _ + 1, _, .const .., _, _, h | _ + 1, _, .app .., _, _, h | _ + 1, _, .lam .., _, _, h
  | _ + 1, _, .letE .., _, _, h | _ + 1, _, .lit _, _, _, h | _ + 1, _, .proj .., _, _, h => by
    simp [projGuardRowsGo] at h

theorem res_projGuardRows (hf : StoredFacts env₁) {entry : ProjEntry} {us : List Level}
    {rows : List (Nat × Expr)} (h : projGuardRows env₁.find? entry us = some rows) :
    ∀ row ∈ rows, Res env₁ row.2 := by
  unfold projGuardRows at h
  cases hc : env₁.find? entry.ctor with
  | none => rw [hc] at h; exact nomatch h
  | some ci =>
    rw [hc] at h
    dsimp only at h
    split at h
    · rename_i fvs r heq
      have hty := res_inst ci.toConstantVal.levelParams us (hf.type hc)
      exact res_projGuardRowsGo _ (res_openPisAtFvars_body _ 0 hty heq) h
    · exact nomatch h

/-- A rule's comparands at resolved arguments. -/
theorem res_recFireComparands {rl : RecRule} (hrw : ∀ lvls pins, RecRule.fire rl = .nested lvls pins →
      ∀ p ∈ pins, Res env₁ p) {cnP rP : Nat} {lps : List Name} {us : List Level}
    {cvjLps : List Name} {args : List Expr} (hargs : ∀ a ∈ args, Res env₁ a) :
    ∀ a ∈ (recFireComparands rl cnP lps us cvjLps args rP).2, Res env₁ a := by
  unfold recFireComparands
  cases hf : RecRule.fire rl with
  | nested lvls pins =>
    intro a ha
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
    exact res_instSpine _ (res_inst _ _ (hrw lvls pins hf p hp)) (res_take hargs _)
  | plain => exact res_take hargs _
  | levels lvls => exact res_take hargs _

section Bodies

variable (K : KR env₁ r₂ r₁) (d : Nat) (hx : EnvExt env₁ env₂)
include K hx

theorem majorToCtor_rel (mode : CheckMode) (name : Name) (isK : Bool) {rules : List RecRule}
    {major : Expr} (hrc : ∀ rl ∈ rules, (env₁.find? rl.ctor).isSome = true)
    (hm : Res env₁ major) :
    Rel (Res env₁) (majorToCtor mode r₂ env₂ d name isK rules major)
      (majorToCtor mode r₁ env₁ d name isK rules major) := by
  unfold majorToCtor
  rw [isCtorApp_ext hx hm]
  refine Rel.ite (fun _ => Rel.ok hm) fun _ => ?_
  cases rules with
  | nil => exact Rel.ok hm
  | cons rl rest =>
    cases rest with
    | cons _ _ => exact Rel.ok hm
    | nil =>
      dsimp only
      have hs := hrc rl List.mem_cons_self
      rw [hx.find_of_isSome hs]
      cases hf : env₁.find? rl.ctor with
      | none => exact Rel.ok hm
      | some ci =>
        cases ci with
        | ctorInfo cvj cnP cnF T =>
          dsimp only
          have hty : Res env₁ cvj.type := hx.facts.type hf
          obtain ⟨us₀, hft⟩ := hx.facts.wf.ctorHead hf
          have hT := res_head (res_piResult hty) hft
          rw [hx.find_of_isSome hT]
          cases hfT : env₁.find? T with
          | none => exact Rel.ok hm
          | some ci' =>
            cases ci' with
            | indInfo cvT caps =>
              dsimp only
              have hTy : Res env₁ cvT.type := hx.facts.type hfT
              refine Rel.ite (fun _ => ?_) fun _ => ?_
              · -- K
                refine Rel.bind (K.inferIO d hm) fun ti hti =>
                  Rel.bind (K.whnf d hti) fun tmaj htm => ?_
                cases hfa : tmaj.getAppFn with
                | const T' ust =>
                  dsimp only
                  refine Rel.ite (fun _ => Rel.ite (fun _ => ?_) fun _ => Rel.ok hm)
                    fun _ => Rel.ok hm
                  have hfab : Res env₁ (Expr.mkAppN (.const rl.ctor ust)
                      (tmaj.getAppArgs.take cnP)) :=
                    res_mkAppN (res_const.mpr hs) (res_take (res_getAppArgs htm) _)
                  refine Rel.ite (fun _ => ?_) fun _ => Rel.ok hm
                  refine Rel.bind (K.inferIO d hfab) fun tf htf =>
                    Rel.bind (K.defeq d htm htf) fun v _ => ?_
                  refine Rel.iteB v (fun _ => ?_) fun _ => Rel.ok hm
                  refine Rel.bind (Q := TT) (Rel.ite (fun _ => proofIrrel_rel K d hfab hm)
                    fun _ => Rel.ok trivial) fun v' _ => ?_
                  exact Rel.iteB v' (fun _ => Rel.ok hfab) fun _ => Rel.ok hm
                | _ => exact Rel.ok hm
              rw [hx.table T hT]
              cases he : etaRescueTable? (env₁.findTable? T) rl.ctor cvj cvT caps with
              | some tbl =>
                -- η
                dsimp only
                obtain ⟨-, -, hec, -⟩ := etaRescueTable?_inv he
                refine Rel.bind (K.inferIO d hm) fun ti hti =>
                  Rel.bind (K.whnf d hti) fun tmaj htm => ?_
                cases hfa : tmaj.getAppFn with
                | const T' ust =>
                  dsimp only
                  refine Rel.ite (fun _ => ?_) fun _ => Rel.ok hm
                  refine Rel.bind (familyNeverZeroAt_rel K hTy) fun v _ => ?_
                  refine Rel.iteB v (fun _ => ?_) fun _ => Rel.ok hm
                  have hfab : Res env₁ (Expr.mkAppN (.const tbl.ctor ust)
                      (etaFabArgsE T tmaj.getAppArgs major tbl.numFields)) := by
                    refine res_mkAppN (res_const.mpr (by rw [hec]; exact hs)) fun a ha => ?_
                    rcases List.mem_append.mp ha with ha | ha
                    · exact res_getAppArgs htm a ha
                    · exact res_etaProjs hT hm _ a ha
                  exact Rel.ite (fun _ => Rel.ok hfab) fun _ => Rel.ok hm
                | _ => exact Rel.ok hm
              | none =>
              dsimp only
              refine Rel.ite (fun hA => ?_) fun _ => Rel.ok hm
              · -- `And`
                have hAs : (env₁.find? andName).isSome = true := hA ▸ hT
                refine Rel.bind (K.inferIO d hm) fun ti hti =>
                  Rel.bind (K.whnf d hti) fun tmaj htm => ?_
                cases hfa : tmaj.getAppFn with
                | const T' ust =>
                  dsimp only
                  rw [andRescueSlots_ext hx hAs]
                  refine Rel.ite (fun _ => ?_) fun _ => Rel.ok hm
                  have hfab : Res env₁ (Expr.mkAppN (.const rl.ctor ust)
                      (tmaj.getAppArgs ++ [.proj T 0 major, .proj T 1 major])) := by
                    refine res_mkAppN (res_const.mpr hs) fun a ha => ?_
                    rcases List.mem_append.mp ha with ha | ha
                    · exact res_getAppArgs htm a ha
                    · simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
                      rcases ha with rfl | rfl <;> exact res_proj.mpr ⟨hT, hm⟩
                  refine Rel.ite (fun _ => ?_) fun _ => Rel.ok hm
                  refine Rel.bind (K.inferIO d hfab) fun tf htf =>
                    Rel.bind (K.defeq d htm htf) fun v _ => ?_
                  refine Rel.iteB v (fun _ => ?_) fun _ => Rel.ok hm
                  refine Rel.bind (Q := TT) (Rel.ite (fun _ => proofIrrel_rel K d hfab hm)
                    fun _ => Rel.ok trivial) fun v' _ => ?_
                  exact Rel.iteB v' (fun _ => Rel.ok hfab) fun _ => Rel.ok hm
                | _ => exact Rel.ok hm
            | _ => exact Rel.ok hm
        | _ => exact Rel.ok hm

theorem litMajorToCtor_rel {e : Expr} (he : Res env₁ e) :
    Rel (Res env₁) (litMajorToCtor r₂ env₂ d e) (litMajorToCtor r₁ env₁ d e) := by
  by_cases hs : ∃ s, e = .lit (.strVal s)
  · obtain ⟨s, rfl⟩ := hs
    simp only [litMajorToCtor]
    rw [strLit_of_res hx he]
    exact Rel.ite (fun _ => K.whnf d (res_strLitToConstructor he)) fun _ => Rel.ok he
  · have h₁ : ∀ env r, litMajorToCtor (m := CheckM) r env d e = .ok (litToCtorIfNat env e) := by
      intro env r
      cases e with
      | lit l =>
        cases l with
        | natVal _ => rfl
        | strVal s => exact absurd ⟨s, rfl⟩ hs
      | _ => rfl
    rw [h₁, h₁, litToCtorIfNat_ext hx he]
    exact Rel.ok (res_litToCtorIfNat he)

theorem projLitToCtor_rel {e : Expr} (he : Res env₁ e) :
    Rel (Res env₁) (projLitToCtor r₂ env₂ d e) (projLitToCtor r₁ env₁ d e) := by
  by_cases hs : ∃ s, e = .lit (.strVal s)
  · obtain ⟨s, rfl⟩ := hs
    simp only [projLitToCtor]
    rw [strLit_of_res hx he]
    exact Rel.ite (fun _ => K.whnf d (res_strLitToConstructor he)) fun _ => Rel.ok he
  · have h₁ : ∀ env r, projLitToCtor (m := CheckM) r env d e = .ok e := by
      intro env r
      cases e with
      | lit l =>
        cases l with
        | natVal _ => rfl
        | strVal s => exact absurd ⟨s, rfl⟩ hs
      | _ => rfl
    rw [h₁, h₁]
    exact Rel.ok he

/-- The non-K major's tail, past the rescue on the major as found. -/
theorem prepareTail_rel (mode : CheckMode) (name : Name) (isK : Bool) {rules : List RecRule}
    {mE : Expr} (hrc : ∀ rl ∈ rules, (env₁.find? rl.ctor).isSome = true)
    (hmE : Res env₁ mE) :
    Rel (Res env₁)
      (if (isCtorApp env₂ mE && !mE.isNatSuccApp) = true then pure mE else do
        let major₀ ← r₂.whnf d mE
        let major₁ ← litMajorToCtor r₂ env₂ d major₀
        majorToCtor mode r₂ env₂ d name isK rules major₁)
      (if (isCtorApp env₁ mE && !mE.isNatSuccApp) = true then pure mE else do
        let major₀ ← r₁.whnf d mE
        let major₁ ← litMajorToCtor r₁ env₁ d major₀
        majorToCtor mode r₁ env₁ d name isK rules major₁) := by
  rw [isCtorApp_ext hx hmE]
  refine Rel.ite (fun _ => Rel.ok hmE) fun _ => ?_
  exact Rel.bind (K.whnf d hmE) fun m₀ hm₀ => Rel.bind (litMajorToCtor_rel K d hx hm₀) fun m₁ hm₁ =>
    majorToCtor_rel K d hx mode name isK hrc hm₁

theorem prepareMajor_rel (mode : CheckMode) (name : Name) (isK : Bool) {rules : List RecRule}
    {major : Expr} (hrc : ∀ rl ∈ rules, (env₁.find? rl.ctor).isSome = true)
    (hm : Res env₁ major) :
    Rel (Res env₁) (prepareMajor mode r₂ env₂ d name isK rules major)
      (prepareMajor mode r₁ env₁ d name isK rules major) := by
  unfold prepareMajor
  refine Rel.ite (fun _ => ?_) fun _ => ?_
  · refine Rel.bind (majorToCtor_rel K d hx mode name isK hrc hm) fun mk hmk => ?_
    rw [isCtorApp_ext hx hmk]
    exact Rel.ite (fun _ => litMajorToCtor_rel K d hx hmk) fun _ => Rel.ok hmk
  · dsimp only
    refine Rel.ite (fun _ => prepareTail_rel K d hx mode name isK hrc hm) fun _ =>
      Rel.bind (majorToCtor_rel K d hx mode name isK hrc hm) fun mE hmE =>
        prepareTail_rel K d hx mode name isK hrc hmE

theorem reduceNat_rel {e : Expr} (he : Res env₁ e) :
    Rel (ResO env₁) (reduceNat r₂ env₂ d e) (reduceNat r₁ env₁ d e) := by
  match e, he with
  | .bvar _, _ | .fvar _ _, _ | .sort _, _ | .lam _ _, _ | .forallE _ _, _
  | .letE _ _ _, _ | .lit _, _ | .proj _ _ _, _ | .const _ _, _ => exact Rel.ok resO_none
  | .app f a, he =>
    obtain ⟨hf, ha⟩ := res_app.mp he
    match f, hf with
    | .bvar _, _ | .fvar _ _, _ | .sort _, _ | .lam _ _, _ | .forallE _ _, _
    | .letE _ _ _, _ | .lit _, _ | .proj _ _ _, _ => exact Rel.ok resO_none
    | .const c us, hf =>
      match us with
      | _ :: _ => exact Rel.ok resO_none
      | [] =>
        have hc := res_const.mp hf
        simp only [reduceNat]
        by_cases hs : c = natSuccName
        · subst hs
          rw [natLit_ext hx (.inr (.inr hc))]
          refine Rel.ite (fun _ => ?_) fun _ => Rel.ok resO_none
          refine Rel.bind (K.whnf d ha) fun w hw => ?_
          cases hr : rawNatLit? w with
          | none => exact Rel.ok resO_none
          | some n =>
            exact Rel.ok fun x h => (Option.some.inj h) ▸ res_natLit hx.facts
              (nat_of_rawNatLit hw hr) (n + 1)
        · simp only [hs, false_and, ↓reduceIte]
          exact Rel.ok resO_none
    | .app f' a', hf =>
      match f', hf with
      | .bvar _, _ | .fvar _ _, _ | .sort _, _ | .lam _ _, _ | .forallE _ _, _
      | .letE _ _ _, _ | .lit _, _ | .proj _ _ _, _ | .app _ _, _ => exact Rel.ok resO_none
      | .const c us, hf =>
        match us with
        | _ :: _ => exact Rel.ok resO_none
        | [] =>
          obtain ⟨hcf, ha'⟩ := res_app.mp hf
          have hc := res_const.mp hcf
          simp only [reduceNat]
          refine Rel.ite (fun hop => ?_) fun _ => Rel.ok resO_none
          · refine Rel.bind (K.whnf d ha') fun w₁ hw₁ => ?_
            cases hr₁ : rawNatLit? w₁ with
            | none => exact Rel.ok resO_none
            | some n₁ =>
              dsimp only
              refine Rel.bind (K.whnf d ha) fun w₂ _ => ?_
              cases rawNatLit? w₂ with
              | none => exact Rel.ok resO_none
              | some n₂ =>
                exact Rel.ok fun x h => res_natOpResult hx.facts
                  (hx.facts.opDefn c (natOpName_of_bin hop) hc)
                  (nat_of_rawNatLit hw₁ hr₁) h

theorem iotaRec_rel (mode : CheckMode) {e : Expr} (he : Res env₁ e) :
    Rel (ResO env₁) (iotaRec mode r₂ env₂ d e) (iotaRec mode r₁ env₁ d e) := by
  unfold iotaRec
  cases hfn : e.getAppFn with
  | const c us =>
    dsimp only
    rw [hx.find_of_isSome (res_head he hfn)]
    cases hfc : env₁.find? c with
    | none => exact Rel.ok resO_none
    | some ci =>
      cases ci with
      | recInfo cv mI rP isK rules =>
        dsimp only
        have hargs := res_getAppArgs he
        refine Rel.ite (fun _ => ?_) fun _ => Rel.ok resO_none
        have hrc : ∀ rl ∈ rules, (env₁.find? rl.ctor).isSome = true := fun rl hrl => by
          obtain ⟨cvj, cnP, cnF, _, h⟩ := hx.facts.recCtors c cv mI rP isK rules hfc rl hrl
          exact res_of_find h
        refine Rel.bind (prepareMajor_rel K d hx mode c isK hrc
          (res_getD hargs res_bvar)) fun major hmaj => ?_
        cases hfm : major.getAppFn with
        | const cj usj =>
          dsimp only
          rw [hx.find_of_isSome (res_head hmaj hfm)]
          cases hfj : env₁.find? cj with
          | none => exact Rel.ok resO_none
          | some cj' =>
            cases cj' with
            | ctorInfo cvj cnP cnF induct =>
              dsimp only
              have hty : Res env₁ cvj.type := hx.facts.type hfj
              have hTs : (env₁.find? induct).isSome = true :=
                let ⟨_, hh⟩ := hx.facts.wf.ctorHead hfj
                res_head (res_piResult hty) hh
              cases hrl : rules.find? (fun r' => r'.ctor == cj) with
              | none => exact Rel.ok resO_none
              | some rl =>
                dsimp only
                have hrm : rl ∈ rules := List.mem_of_find?_eq_some hrl
                have hmargs := res_getAppArgs hmaj
                refine Rel.ite (fun _ => ?_) fun _ => Rel.ok resO_none
                have hcmp := res_recFireComparands (rl := rl) (env₁ := env₁) (cnP := cnP) (rP := rP)
                  (lps := cv.levelParams) (us := us) (cvjLps := cvj.levelParams)
                  (fun lvls pins hfi p hp => by
                    obtain ⟨-, -, hpins, -⟩ := ((hx.facts.wf.consts _ (Env.find?_mem hfc)).2.2.2.2.2
                      cv mI rP isK rules rfl rl hrm).2.2.2.2 lvls pins hfi
                    exact (hpins p hp).2.2.1) hargs
                have hres : Res env₁ (rl.iotaReduct cv.levelParams us rP
                    (e.getAppArgs.take rP ++ major.getAppArgs.drop cnP)) := by
                  rw [RecRule.iotaReduct_eq_instSpine]
                  refine res_instSpine _ (res_inst _ _
                    (Expr.constsResolve_lamBody _ (hx.facts.rhs hfc hrm))) fun a ha => ?_
                  rcases List.mem_append.mp ha with ha | ha
                  · exact res_take hargs _ a ha
                  · exact res_drop hmargs _ a ha
                refine Rel.bind (Q := TT) (Rel.ite (fun _ => ?_) fun _ => Rel.ok trivial) fun v _ =>
                  Rel.iteB v (fun _ => Rel.ok fun x h => (Option.some.inj h) ▸ hres)
                    fun _ => Rel.ok resO_none
                refine Rel.bind (iotaCaseAt_rel K hx isK hTs _) fun c3 _ => ?_
                refine Rel.iteB c3 (fun _ => ?_) fun _ => Rel.ok trivial
                refine Rel.bind Rel.triv fun v₁ _ => ?_
                refine Rel.iteB v₁ (fun _ => ?_) fun _ => Rel.ok trivial
                refine Rel.bind (defEqList_rel K d _ _ (res_take hmargs _) hcmp) fun v₂ _ => ?_
                refine Rel.iteB v₂ (fun _ => ?_) fun _ => Rel.ok trivial
                have htyI := res_inst cvj.levelParams usj hty
                refine Rel.bind (iotaCertsFull_rel K d _ _ htyI hmargs) fun v₃ _ => ?_
                refine Rel.iteB v₃ (fun _ => ?_) fun _ => Rel.ok trivial
                exact iotaIndexOk_rel K d _ _ _ htyI hmargs (res_drop (res_take hargs _) _)
            | _ => exact Rel.ok resO_none
        | _ => exact Rel.ok resO_none
      | _ => exact Rel.ok resO_none
  | _ => exact Rel.ok resO_none

theorem reduceProjCore_rel (mode : CheckMode) {sn : Name} (i : Nat) {c : Expr}
    (hsn : (env₁.find? sn).isSome = true) (hc : Res env₁ c) :
    Rel (ResO env₁) (reduceProjCore mode r₂ env₂ d sn i c) (reduceProjCore mode r₁ env₁ d sn i c) := by
  unfold reduceProjCore
  refine Rel.bind (projLitToCtor_rel K d hx hc) fun c' hc' => ?_
  rw [hx.findProj hsn]
  cases env₁.findProj? sn i with
  | none => exact Rel.ok resO_none
  | some entry =>
    dsimp only
    cases hfn : c'.getAppFn with
    | const k us =>
      dsimp only
      refine Rel.ite (fun _ => ?_) fun _ => Rel.ok resO_none
      have hcert : projCertAt env₂ mode.verifiedChecks k c'.getAppArgs =
          projCertAt env₁ mode.verifiedChecks k c'.getAppArgs := by
        unfold projCertAt projCert
        rw [hx.find_of_isSome (res_head hc' hfn)]
      rw [hcert]
      exact Rel.ite (fun _ => Rel.ok fun x h =>
        (Option.some.inj h) ▸ res_getD (res_getAppArgs hc') res_bvar) fun _ => Rel.ok resO_none
    | _ => exact Rel.ok resO_none

theorem ruleRetry_rel {a : Expr} (ha : Res env₁ a) :
    Rel (Res env₁) (ruleRetry r₂ env₂ d a) (ruleRetry r₁ env₁ d a) := by
  unfold ruleRetry
  refine Rel.bind (K.whnf d ha) fun w hw => ?_
  rw [litToCtorIfNat_ext hx hw]
  exact Rel.ok (res_litToCtorIfNat hw)

/-- What a rule's match hands on: the matched view and the slots' bindings resolve. -/
abbrev ResM (env : Env) (o : Option ((List (Option Expr) × List (Option Level)) × Expr)) : Prop :=
  ∀ st x, o = some (st, x) → Res env x ∧ SlotsP (Res env) st

omit hx in
/-- A variable position: a repeated variable's comparison runs on resolved terms. -/
theorem ruleBindVar_rel (n k : Nat) (st : List (Option Expr) × List (Option Level)) {a : Expr}
    (hst : SlotsP (Res env₁) st) (ha : Res env₁ a) :
    Rel (ResM env₁) (ruleBindVar r₂ d n k st a) (ruleBindVar r₁ d n k st a) := by
  unfold ruleBindVar
  rcases hs : ruleSlot? n k st.1 with _ | (_ | e')
  · exact Rel.ok fun _ _ h => nomatch h
  · refine Rel.ok fun st' x h => ?_
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨ha, hst.set ha _⟩
  · have he' : Res env₁ e' := hst e' (ruleSlot?_mem hs)
    have hok : ResM env₁ (some (st, e')) := fun st' x h => by
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨he', hst⟩
    refine Rel.ite (fun _ => Rel.ok hok) fun _ => Rel.bind (K.defeq d he' ha) fun v _ => ?_
    exact Rel.iteB v (fun _ => Rel.ok hok) fun _ => Rel.ok fun _ _ h => nomatch h

theorem ruleMatchM_rel (n : Nat) (lps : List Name) :
    ∀ (pat : Expr) (st : List (Option Expr) × List (Option Level)) {e : Expr},
      SlotsP (Res env₁) st → Res env₁ e →
      Rel (ResM env₁) (ruleMatchM r₂ env₂ d n lps pat st e) (ruleMatchM r₁ env₁ d n lps pat st e) := by
  intro pat
  induction pat with
  | app f p ihf ihp =>
    intro st e hst he
    cases e with
    | app f' a =>
      obtain ⟨hf', ha⟩ := res_app.mp he
      simp only [ruleMatchM]
      refine Rel.bind (ihf st hst hf') fun o ho => ?_
      cases o with
      | none => exact Rel.ok fun _ _ h => nomatch h
      | some sf =>
        obtain ⟨st₁, f₁⟩ := sf
        obtain ⟨hf₁, hst₁⟩ := ho _ _ rfl
        refine Rel.bind (Q := ResM env₁) ?_ fun o' ho' => ?_
        · unfold ruleArgStep
          split
          · exact ruleBindVar_rel K d n _ st₁ hst₁ ha
          · unfold ruleOrRetry
            refine Rel.bind (ihp st₁ hst₁ ha) fun o ho => ?_
            cases o with
            | some y => exact Rel.ok ho
            | none => exact Rel.bind (ruleRetry_rel K d hx ha) fun a' ha' => ihp st₁ hst₁ ha'
        · cases o' with
          | none => exact Rel.ok fun _ _ h => nomatch h
          | some sa =>
            obtain ⟨st₂, a₁⟩ := sa
            refine Rel.ok fun st' x h => ?_
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            obtain ⟨ha₁, hst₂⟩ := ho' _ _ rfl
            exact ⟨res_app.mpr ⟨hf₁, ha₁⟩, hst₂⟩
    | _ => exact Rel.ok fun _ _ h => nomatch h
  | const c ls =>
    intro st e hst he
    obtain ⟨sl, lv⟩ := st
    cases e with
    | const c' ls' =>
      simp only [ruleMatchM]
      refine Rel.ok fun st' x h => ?_
      split at h
      · obtain ⟨lv', -, h⟩ := Option.map_eq_some_iff.mp h
        simp only [Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨he, hst⟩
      · exact nomatch h
    | _ => exact Rel.ok fun _ _ h => nomatch h
  | _ => intro st e _ he; exact Rel.ok fun _ _ h => nomatch h

/-- What the match's arguments hand on: the matched view resolves. -/
abbrev ResA (env : Env) (o : Option (List Expr × List Level × Expr)) : Prop :=
  ∀ args us x, o = some (args, us, x) → Res env x

theorem ruleArgsM_rel (cv : ConstantVal) {e : Expr} (he : Res env₁ e) :
    Rel (ResA env₁) (ruleArgsM r₂ env₂ d cv e) (ruleArgsM r₁ env₁ d cv e) := by
  unfold ruleArgsM
  split
  · refine Rel.bind (ruleMatchM_rel K d hx _ _ _ _ (SlotsP.replicate _ _ _) he) fun o ho => ?_
    cases o with
    | none => exact Rel.ok fun _ _ _ h => nomatch h
    | some x =>
      obtain ⟨⟨sl, lv⟩, e₁⟩ := x
      dsimp only
      split
      · refine Rel.ok fun args us x h => ?_
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, -, rfl⟩ := h
        exact (ho _ _ rfl).1
      · exact Rel.ok fun _ _ _ h => nomatch h
  · exact Rel.ok fun _ _ _ h => nomatch h

/-- **A rule's firing at an extension is its firing at the prefix**: the theorem is the
prefix's, every run of the firing is on resolved terms, and the right side resolves. -/
theorem rewriteAttempt_rel {e : Expr} (he : Res env₁ e) {t : Name}
    (ht : (env₁.find? t).isSome = true) :
    Rel (ResO env₁) (rewriteAttempt r₂ env₂ d e t) (rewriteAttempt r₁ env₁ d e t) := by
  unfold rewriteAttempt rewriteFire
  rw [hx.find_of_isSome ht]
  cases hft : env₁.find? t with
  | none => exact Rel.ok resO_none
  | some ci =>
    cases ci
    case thmInfo cv =>
      try dsimp only
      refine Rel.bind (ruleArgsM_rel K d hx cv he) fun o ho => ?_
      cases o with
      | none => exact Rel.ok resO_none
      | some au =>
        obtain ⟨args, us, e₁⟩ := au
        have he₁ := ho _ _ _ rfl
        try dsimp only
        have hT : Res env₁ (cv.type.instantiateLevelParams cv.levelParams us) :=
          res_inst _ _ (hx.facts.type hft)
        split
        · rename_i eqn u A l rhs hres
          rw [bind_eqSpine?_eq_some] at hres
          · refine Rel.ite (fun hchk => ?_) fun _ => Rel.ok resO_none
            obtain ⟨-, -, -, hsub, -⟩ := hchk
            have hargs : ∀ a ∈ args, Res env₁ a := fun a ha => res_appSubterms e₁ (hsub a ha) he₁
            have hR := res_piResidual hT hargs hres
            have hA : Res env₁ A := (res_app.mp (res_app.mp (res_app.mp hR).1).1).2
            have hr : Res env₁ rhs := (res_app.mp hR).2
            refine Rel.bind (iotaCertsFull_rel K d _ args hT hargs) fun b _ => ?_
            refine Rel.iteB b (fun _ => Rel.ok fun x hxe => ?_) fun _ => Rel.ok resO_none
            obtain rfl := Option.some.inj hxe
            exact hr
        · exact Rel.ok resO_none
    all_goals exact Rel.ok resO_none

/-- A rule at the prefix of its arity, at an extension, is its firing at the prefix. -/
theorem rewriteAt_rel {t : Name} (ht : (env₁.find? t).isSome = true) :
    ∀ {e : Expr}, Res env₁ e →
      Rel (ResO env₁) (rewriteAt r₂ env₂ d t e) (rewriteAt r₁ env₁ d t e)
  | .app f a, he => by
    rw [rewriteAt, rewriteAt]
    refine Rel.bind (rewriteAttempt_rel K d hx he ht) fun o ho => ?_
    cases o with
    | some e₂ => exact Rel.ok ho
    | none =>
      obtain ⟨hf, ha⟩ := res_app.mp he
      refine Rel.bind (rewriteAt_rel ht hf) fun o' ho' => ?_
      cases o' with
      | some f₂ =>
        exact Rel.ok fun x h => (Option.some.inj h) ▸ res_app.mpr ⟨ho' f₂ rfl, ha⟩
      | none => exact Rel.ok resO_none
  | .bvar _, he | .sort _, he | .const .., he | .fvar .., he | .forallE .., he | .lam .., he
  | .letE .., he | .lit _, he | .proj .., he => by
    rw [rewriteAt_nonApp _ _ _ _ (by intro _ _ hh; cases hh),
      rewriteAt_nonApp _ _ _ _ (by intro _ _ hh; cases hh)]
    exact rewriteAttempt_rel K d hx he ht

/-- What a rule firing hands on. -/
abbrev ResOR (env : Env) (o : Option (Name × Expr)) : Prop := ∀ t x, o = some (t, x) → Res env x

theorem rewriteRules_rel {e : Expr} (he : Res env₁ e) :
    ∀ ts : List Name, (∀ t ∈ ts, (env₁.find? t).isSome = true) →
      Rel (ResOR env₁) (rewriteRules r₂ env₂ d e ts) (rewriteRules r₁ env₁ d e ts)
  | [], _ => Rel.ok fun _ _ h => nomatch h
  | t :: ts, hts => by
    unfold rewriteRules
    refine Rel.bind (rewriteAt_rel K d hx (hts t List.mem_cons_self) he) fun o ho => ?_
    cases o with
    | some e₂ =>
      exact Rel.ok fun t' x h => by
        obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj h)
        exact ho _ rfl
    | none =>
      exact rewriteRules_rel he ts fun t' ht' => hts t' (List.mem_cons_of_mem _ ht')

theorem rewriteStep_rel (stuck : Bool) {e : Expr} (he : Res env₁ e) :
    Rel (ResOR env₁) (rewriteStep r₂ env₂ d stuck e) (rewriteStep r₁ env₁ d stuck e) := by
  unfold rewriteStep
  split
  · rename_i c ls hfn
    rw [hx.rules c, unfoldableHead_ext hx he]
    refine Rel.ite (fun _ => Rel.ok fun _ _ h => nomatch h) fun _ => ?_
    exact rewriteRules_rel K d hx he _ fun t ht => find_of_mem_rulesFor ht
  · exact Rel.ok fun _ _ h => nomatch h

/-- The rules fired again, at an extension, are the prefix's. -/
theorem fireMore_rel : ∀ (k : Nat) {e : Expr}, Res env₁ e →
    Rel (Res env₁) (fireMore r₂ env₂ d k e) (fireMore r₁ env₁ d k e)
  | 0, _, he => Rel.ok he
  | k + 1, e, he => by
    unfold fireMore
    refine Rel.bind (rewriteStep_rel K d hx false he) fun ro hro => ?_
    cases ro with
    | some te => exact fireMore_rel k (hro te.1 te.2 rfl)
    | none => exact Rel.ok he

theorem originFire_rel {o : Option Expr} {e : Expr} (ho : OriginP (Res env₁) o)
    (he : Res env₁ e) :
    Rel (ResOR env₁) (originFire r₂ env₂ d o e) (originFire r₁ env₁ d o e) := by
  unfold originFire
  cases o with
  | none => exact Rel.ok fun _ _ h => nomatch h
  | some o' =>
    dsimp only
    rw [isStuckResult_ext hx he]
    refine Rel.ite (fun _ => ?_) fun _ => Rel.ok fun _ _ h => nomatch h
    refine Rel.bind (rewriteStep_rel K d hx true (ho _ rfl)) fun ro hro => ?_
    cases ro with
    | some te =>
      refine Rel.bind (fireMore_rel K d hx _ (hro te.1 te.2 rfl)) fun e₃ he₃ => ?_
      exact Rel.ok fun t x h => by
        obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj h)
        exact he₃
    | none => exact Rel.ok fun _ _ h => nomatch h

/-- ι at the prefix of the recursor's arity, at an extension, is the prefix's. -/
theorem iotaAt_rel (mode : CheckMode) : ∀ {e : Expr}, Res env₁ e →
    Rel (ResO env₁) (iotaAt mode r₂ env₂ d e) (iotaAt mode r₁ env₁ d e)
  | .app f a, he => by
    rw [iotaAt, iotaAt]
    refine Rel.bind (iotaRec_rel K d hx mode he) fun o ho => ?_
    cases o with
    | some e₂ => exact Rel.ok ho
    | none =>
      obtain ⟨hf, ha⟩ := res_app.mp he
      refine Rel.bind (iotaAt_rel mode hf) fun o' ho' => ?_
      cases o' with
      | some f₂ =>
        exact Rel.ok fun x h => (Option.some.inj h) ▸ res_app.mpr ⟨ho' f₂ rfl, ha⟩
      | none => exact Rel.ok resO_none
  | .bvar _, he | .sort _, he | .const .., he | .fvar .., he | .forallE .., he | .lam .., he
  | .letE .., he | .lit _, he | .proj .., he => by
    rw [iotaAt_nonApp _ _ _ (by intro _ _ hh; cases hh),
      iotaAt_nonApp _ _ _ (by intro _ _ hh; cases hh)]
    exact iotaRec_rel K d hx mode he

theorem iotaThenRule_rel (mode : CheckMode) {e : Expr} (he : Res env₁ e) :
    Rel (ResO env₁) (iotaThenRule mode r₂ env₂ d e) (iotaThenRule mode r₁ env₁ d e) := by
  unfold iotaThenRule
  refine Rel.bind (iotaAt_rel K d hx mode he) fun o ho => ?_
  cases o with
  | some e'' => exact Rel.ok ho
  | none =>
    refine Rel.bind (rewriteStep_rel K d hx false he) fun ro hro => ?_
    cases ro with
    | some te =>
      refine Rel.bind (fireMore_rel K d hx _ (hro te.1 te.2 rfl)) fun e₃ he₃ => ?_
      exact Rel.ok fun x h => (Option.some.inj h) ▸ he₃
    | none => exact Rel.ok resO_none

theorem whnfCoreBody_rel (mode : CheckMode) (c : Bool) {e : Expr} (he : Res env₁ e) :
    Rel (Res env₁) (whnfCoreBody mode r₂ env₂ c d e) (whnfCoreBody mode r₁ env₁ c d e) := by
  match e, he with
  | .sort _, he | .fvar _ _, he | .forallE _ _, he | .lam _ _, he
  | .lit _, he => exact Rel.ok he
  | .const n us, he =>
    refine Rel.bind (rewriteStep_rel K d hx false he) fun ro hro => ?_
    cases ro with
    | some te =>
      exact Rel.bind (fireMore_rel K d hx _ (hro te.1 te.2 rfl)) fun e₃ he₃ => K.whnfCore c d he₃
    | none => exact Rel.ok he
  | .bvar _, _ => exact Rel.err _
  | .letE _ v b, he =>
    obtain ⟨-, hv, hb⟩ := res_let.mp he
    exact K.whnfCore c d (res_instantiate1 hv b 0 hb)
  | .app f a, he =>
    have hP : AppClosed (Res env₁) := fun _ _ => res_app
    refine Rel.bind (K.whnfCore c d (hP.getAppFn he)) fun v hv => ?_
    cases v
    case lam t body =>
      dsimp only
      cases hargs : (Expr.app f a).getAppArgs with
      | nil => exact Rel.ok he
      | cons a₁ rest =>
        exact K.whnfCore c d (hP.beta (fun hl ha => res_instantiate1 ha body 0 (res_lam.mp hl).2)
          hargs he hv)
    all_goals
      dsimp only
      refine Rel.ite (fun _ => ?_) fun _ => K.whnfCore c d (hP.mkAppN hv (hP.getAppArgs he))
      refine Rel.bind (iotaThenRule_rel K d hx mode he) fun o ho => ?_
      cases o with
      | none => exact Rel.ok he
      | some e'' => exact K.whnfCore c d (ho _ rfl)
  | .proj sn i pe, he =>
    obtain ⟨hsn, hpe⟩ := res_proj.mp he
    have hrest : ∀ c', Res env₁ c' → Rel (Res env₁)
        (do match ← reduceProjCore mode r₂ env₂ d sn i c' with
          | some m' => r₂.whnfCore c d m'
          | none => pure (.proj sn i pe))
        (do match ← reduceProjCore mode r₁ env₁ d sn i c' with
          | some m' => r₁.whnfCore c d m'
          | none => pure (.proj sn i pe)) := by
      intro c' hc'
      refine Rel.bind (reduceProjCore_rel K d hx mode i hsn hc') fun o ho => ?_
      cases o with
      | none => exact Rel.ok he
      | some m' => exact K.whnfCore c d (ho _ rfl)
    cases c with
    | true => exact Rel.bind (K.whnfCore true d hpe) hrest
    | false => exact Rel.bind (K.whnf d hpe) hrest

theorem whnfLoop_rel : ∀ (n : Nat) {o : Option Expr} {e : Expr}, OriginP (Res env₁) o →
    Res env₁ e → Rel (Res env₁) (whnfLoop r₂ env₂ d n o e) (whnfLoop r₁ env₁ d n o e)
  | 0, _, _, _, _ => Rel.err _
  | n + 1, o, e, hor, he => by
    simp only [whnfLoop, whnfStep, whnfFix]
    refine Rel.bind (K.whnfCore false d he) fun e₁ he₁ => ?_
    refine Rel.bind (reduceNat_rel K d hx he₁) fun o' ho => ?_
    cases o' with
    | some e₂ =>
      dsimp only
      split
      · exact Rel.ok (ho _ rfl)
      · exact whnfLoop_rel n hor (ho _ rfl)
    | none =>
      dsimp only
      rw [unfoldDefinition_ext hx he₁, noteOrigin_ext hx he₁]
      cases hu : unfoldDefinition env₁ e₁ with
      | none =>
        dsimp only
        refine Rel.bind (originFire_rel K d hx hor he₁) fun ro hro => ?_
        cases ro with
        | none => exact Rel.ok he₁
        | some te => exact whnfLoop_rel n (OriginP.none _) (hro te.1 te.2 rfl)
      | some e₂ => exact whnfLoop_rel n (hor.note he₁) (res_unfoldDefinition hx he₁ hu)

omit hx in
theorem ensureSort_rel {e : Expr} (he : Res env₁ e) :
    Rel TT (ensureSort r₂ env₂ d e) (ensureSort r₁ env₁ d e) := by
  unfold ensureSort
  refine Rel.bind (K.whnf d he) fun w _ => ?_
  cases w <;> first | exact Rel.ok trivial | exact Rel.err _

end Bodies

theorem checkGuardRows_rel (K : KR env₁ r₂ r₁) {inf₂ inf₁ : Nat → Expr → CheckM Expr}
    (hinf : ∀ d {e}, Res env₁ e → Rel (Res env₁) (inf₂ d e) (inf₁ d e)) (guardSort : Level) :
    ∀ (rows : List (Nat × Expr)), (∀ row ∈ rows, Res env₁ row.2) →
      Rel TT (checkGuardRows inf₂ r₂.whnf guardSort rows) (checkGuardRows inf₁ r₁.whnf guardSort rows)
  | [], _ => Rel.ok trivial
  | (d, dom) :: rest, h => by
    simp only [checkGuardRows]
    have hd : Res env₁ dom := h (d, dom) List.mem_cons_self
    refine Rel.bind (hinf d hd) fun t ht => Rel.bind (K.whnf d ht) fun w _ => ?_
    cases w with
    | sort u =>
      dsimp only
      have hr := checkGuardRows_rel K hinf guardSort rest
        (fun row hrow => h row (List.mem_cons_of_mem _ hrow))
      refine Rel.ite (fun _ => hr) fun _ => Rel.err _
    | _ => exact Rel.err _

theorem projGuardSort_rel (K : KR env₁ r₂ r₁) {cvT : ConstantVal} {caps : IndCaps} {us : List Level}
    (hT : Res env₁ cvT.type) :
    Rel TT (projGuardSort r₂.whnf cvT caps us) (projGuardSort r₁.whnf cvT caps us) := by
  unfold projGuardSort
  split
  · exact Rel.ok trivial
  · refine Rel.bind (formerSortLoop_rel K _ 0 (res_inst _ _ hT)) fun w _ => ?_
    cases w with
    | some s => exact Rel.ok trivial
    | none => exact Rel.err _

theorem checkProjGuard_rel (K : KR env₁ r₂ r₁) (hx : EnvExt env₁ env₂)
    {inf₂ inf₁ : Nat → Expr → CheckM Expr}
    (hinf : ∀ d {e}, Res env₁ e → Rel (Res env₁) (inf₂ d e) (inf₁ d e)) {T : Name} {i : Nat}
    {entry : ProjEntry} (hfp : env₁.findProj? T i = some entry) (us : List Level) :
    Rel TT (checkProjGuard inf₂ r₂.whnf env₂ entry us) (checkProjGuard inf₁ r₁.whnf env₁ entry us) := by
  unfold checkProjGuard
  have hst : (env₁.find? entry.structName).isSome = true := by
    obtain ⟨tbl, hT, -, rfl⟩ := Env.findProj?_some hfp
    exact (hx.facts.wf.table hT).1
  rw [hx.find_of_isSome hst, projGuardRows_ext hx (hx.facts.entryCtors hfp)]
  cases hfs : env₁.find? entry.structName with
  | none => exact Rel.err _
  | some ci =>
    cases ci with
    | indInfo cvT caps =>
      dsimp only
      refine Rel.bind (projGuardSort_rel K (hx.facts.type hfs)) fun o _ => ?_
      cases o with
      | none => exact Rel.ok trivial
      | some guardSort =>
        dsimp only
        cases hr : projGuardRows env₁.find? entry us with
        | none => exact Rel.err _
        | some rows => exact checkGuardRows_rel K hinf guardSort rows (res_projGuardRows hx.facts hr)
    | _ => exact Rel.err _

/-- A `.const` node's type. -/
theorem inferConst_rel (hx : EnvExt env₁ env₂) {n : Name} {us : List Level}
    (hn : (env₁.find? n).isSome = true) :
    Rel (Res env₁)
      (match env₂.find? n with
       | none => throw (unknownConstError n)
       | some ci => do
          let cv := ci.toConstantVal
          unless us.length = cv.levelParams.length do
            throw (.invalid s!"incorrect number of universe levels for {n}")
          pure (cv.type.instantiateLevelParams cv.levelParams us))
      (match env₁.find? n with
       | none => throw (unknownConstError n)
       | some ci => do
          let cv := ci.toConstantVal
          unless us.length = cv.levelParams.length do
            throw (.invalid s!"incorrect number of universe levels for {n}")
          pure (cv.type.instantiateLevelParams cv.levelParams us)) := by
  rw [hx.find_of_isSome hn]
  cases hf : env₁.find? n with
  | none => exact Rel.err _
  | some ci =>
    dsimp only
    refine Rel.ite (fun _ => Rel.ok (res_inst _ _ (hx.facts.type hf))) fun _ => ?_
    exact Rel.bind (Q := TT) (Rel.err _) fun _ _ => Rel.ok (res_inst _ _ (hx.facts.type hf))

/-- A `.proj` node's type at its inferred subject type. -/
theorem res_typeAt (hf : StoredFacts env₁) {T : Name} {i : Nat} {entry : ProjEntry}
    (hfp : env₁.findProj? T i = some entry) (us : List Level) {targs : List Expr} {pe : Expr}
    (hlen : targs.length = entry.numParams) (ht : ∀ a ∈ targs, Res env₁ a) (hpe : Res env₁ pe) :
    Res env₁ (entry.typeAt us targs pe) := by
  rw [ProjEntry.typeAt_eq_instSpine entry us hlen pe]
  refine res_instSpine _ (res_inst _ _ (hf.entryBody hfp)) fun a ha => ?_
  rcases List.mem_append.mp ha with ha | ha
  · exact ht a ha
  · rw [List.mem_singleton.mp ha]; exact hpe

section Infer

variable (K : KR env₁ r₂ r₁) (hx : EnvExt env₁ env₂)
include K hx

theorem inferBody_rel (d : Nat) {e : Expr} (he : Res env₁ e) :
    Rel (Res env₁) (inferBody r₂ env₂ d e) (inferBody r₁ env₁ d e) := by
  match e, he with
  | .sort _, _ => exact Rel.ok res_sort
  | .bvar _, _ => exact Rel.err _
  | .fvar idx ty, he =>
    exact Rel.ite (fun _ => Rel.ok (res_fvar.mp he)) fun _ => Rel.err _
  | .const n us, he => exact inferConst_rel hx (res_const.mp he)
  | .lit (.natVal v), he =>
    simp only [inferBody]
    rw [natLit_of_res hx he]
    simp only [Res, Expr.constsResolve, Bool.and_eq_true] at he
    exact Rel.ite (fun _ => Rel.ok (res_const.mpr he.1.1)) fun _ => Rel.err _
  | .lit (.strVal v), he =>
    simp only [inferBody]
    rw [strLit_of_res hx he]
    simp only [Res, Expr.constsResolve, Bool.and_eq_true] at he
    exact Rel.ite (fun _ => Rel.ok (res_const.mpr he.1.1.1.1.1.1.2)) fun _ => Rel.err _
  | .forallE ty body, he =>
    obtain ⟨ht, hb⟩ := res_forall.mp he
    refine Rel.bind (K.infer d ht) fun s hs => Rel.bind (K.whnf d hs) fun w _ => ?_
    cases w with
    | sort u =>
      refine Rel.bind (K.infer (d + 1) (res_open ht hb)) fun t' ht' => ?_
      exact Rel.bind (ensureSort_rel K (d + 1) ht') fun v _ => Rel.ok res_sort
    | _ => exact Rel.err _
  | .lam ty body, he =>
    obtain ⟨ht, hb⟩ := res_lam.mp he
    refine Rel.bind (K.infer d ht) fun s hs => Rel.bind (K.whnf d hs) fun w _ => ?_
    cases w with
    | sort u =>
      exact Rel.bind (K.infer (d + 1) (res_open ht hb)) fun bt hbt =>
        Rel.ok (res_forall.mpr ⟨ht, res_abstract1 d bt 0 hbt⟩)
    | _ => exact Rel.err _
  | .app f a, he =>
    obtain ⟨hf, ha⟩ := res_app.mp he
    refine Rel.bind (K.infer d hf) fun tf htf => Rel.bind (K.whnf d htf) fun w hw => ?_
    cases w with
    | forallE ty body =>
      obtain ⟨hty, hbody⟩ := res_forall.mp hw
      refine Rel.bind (K.infer d ha) fun ta hta => ?_
      have hdef : Rel TT (defeqArg r₂ d a ta ty) (defeqArg r₁ d a ta ty) := by
        unfold defeqArg
        exact Rel.ite (fun _ => K.defeqE d hta hty) fun _ => K.defeq d hta hty
      refine Rel.bind hdef fun v _ => ?_
      dsimp only
      cases v
      · exact Rel.err _
      · exact Rel.ok (res_instantiate1 ha body 0 hbody)
    | _ => exact Rel.err _
  | .proj sn i pe, he =>
    obtain ⟨-, hpe⟩ := res_proj.mp he
    refine Rel.bind (K.infer d hpe) fun s hs => Rel.bind (K.whnf d hs) fun te hte => ?_
    cases hfn : te.getAppFn with
    | const T us =>
      dsimp only
      rw [hx.findProj (res_head hte hfn)]
      cases hfp : env₁.findProj? T i with
      | none => exact Rel.err _
      | some entry =>
        dsimp only
        refine Rel.ite (fun h => ?_) fun _ => Rel.err _
        refine Rel.bind (checkProjGuard_rel K hx K.inferIO hfp us) fun _ _ => ?_
        exact Rel.ok (res_typeAt hx.facts hfp us h.2.1 (res_getAppArgs hte) hpe)
    | _ => exact Rel.err _
  | .letE ty v b, he =>
    obtain ⟨hty, hv, hb⟩ := res_let.mp he
    refine Rel.bind (K.infer d hty) fun s hs => Rel.bind (ensureSort_rel K d hs) fun _ _ => ?_
    refine Rel.bind (K.infer d hv) fun tv htv => Rel.bind (K.defeq d htv hty) fun w _ => ?_
    dsimp only
    cases w
    · exact Rel.err _
    · exact K.infer d (res_instantiate1 hv b 0 hb)

theorem inferBodyIO_rel (d : Nat) {e : Expr} (he : Res env₁ e) :
    Rel (Res env₁) (inferBodyIO r₂.ioView env₂ d e) (inferBodyIO r₁.ioView env₁ d e) := by
  have KI := K.ioView
  match e, he with
  | .sort _, _ => exact Rel.ok res_sort
  | .bvar _, _ => exact Rel.err _
  | .fvar idx ty, he =>
    exact Rel.ite (fun _ => Rel.ok (res_fvar.mp he)) fun _ => Rel.err _
  | .const n us, he => exact inferConst_rel hx (res_const.mp he)
  | .lit (.natVal v), he =>
    simp only [inferBodyIO]
    rw [natLit_of_res hx he]
    simp only [Res, Expr.constsResolve, Bool.and_eq_true] at he
    exact Rel.ite (fun _ => Rel.ok (res_const.mpr he.1.1)) fun _ => Rel.err _
  | .lit (.strVal v), he =>
    simp only [inferBodyIO]
    rw [strLit_of_res hx he]
    simp only [Res, Expr.constsResolve, Bool.and_eq_true] at he
    exact Rel.ite (fun _ => Rel.ok (res_const.mpr he.1.1.1.1.1.1.2)) fun _ => Rel.err _
  | .forallE ty body, he =>
    obtain ⟨ht, hb⟩ := res_forall.mp he
    refine Rel.bind (KI.infer d ht) fun s hs => Rel.bind (KI.whnf d hs) fun w _ => ?_
    cases w with
    | sort u =>
      refine Rel.bind (KI.infer (d + 1) (res_open ht hb)) fun t' ht' => ?_
      exact Rel.bind (ensureSort_rel KI (d + 1) ht') fun v _ => Rel.ok res_sort
    | _ => exact Rel.err _
  | .lam ty body, he =>
    obtain ⟨ht, hb⟩ := res_lam.mp he
    exact Rel.bind (KI.infer (d + 1) (res_open ht hb)) fun bt hbt =>
      Rel.ok (res_forall.mpr ⟨ht, res_abstract1 d bt 0 hbt⟩)
  | .app f a, he =>
    obtain ⟨hf, ha⟩ := res_app.mp he
    refine Rel.bind (KI.infer d hf) fun tf htf => Rel.bind (KI.whnf d htf) fun w hw => ?_
    cases w with
    | forallE ty body => exact Rel.ok (res_instantiate1 ha body 0 (res_forall.mp hw).2)
    | _ => exact Rel.err _
  | .proj sn i pe, he =>
    obtain ⟨-, hpe⟩ := res_proj.mp he
    refine Rel.bind (KI.infer d hpe) fun s hs => Rel.bind (KI.whnf d hs) fun te hte => ?_
    cases hfn : te.getAppFn with
    | const T us =>
      dsimp only
      rw [hx.findProj (res_head hte hfn)]
      cases hfp : env₁.findProj? T i with
      | none => exact Rel.err _
      | some entry =>
        dsimp only
        refine Rel.ite (fun h => ?_) fun _ => Rel.err _
        refine Rel.bind (checkProjGuard_rel KI hx KI.infer hfp us) fun _ _ => ?_
        exact Rel.ok (res_typeAt hx.facts hfp us h.2.1 (res_getAppArgs hte) hpe)
    | _ => exact Rel.err _
  | .letE ty v b, he =>
    obtain ⟨-, hv, hb⟩ := res_let.mp he
    exact KI.infer d (res_instantiate1 hv b 0 hb)

end Infer

end ConLeche.Verify
