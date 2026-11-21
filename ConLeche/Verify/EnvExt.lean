module

public import ConLeche.Verify.EnvExt.Whnf
public import ConLeche.Kernel.Inductives.BlockTail

/-!
# A run does not see an extension of the environment (task #480)

**The knot theorem**: `env₂` extends `env₁`, `e` resolves in `env₁`, and the fuelled knot at the
two environments is one run on `e`, at every entry point and every fuel, and what it returns
resolves in `env₁` (`knot_ext`).  What the knot reads past the term in hand is `StoredFacts`:
every read is of a constant of a resolved term, of a stored term, or of a name such a constant's
record gives.  `reducedFormer_ext` is the consequence for a former: its reduct at an extension is the reduct
at the prefix, syntactically.
-/

@[expose] public section

namespace ConLeche.Verify

open ConLeche

variable {env₁ env₂ : Env} {r₂ r₁ : CoreFns CheckM}

/-- What a lazy-delta step hands on resolves. -/
def DeltaRes (env : Env) : DeltaStep → Prop
  | .cont a b _ _ => Res env a ∧ Res env b
  | _ => True

/-- What the lazy-delta loop hands on resolves. -/
def LazyResRes (env : Env) : LazyRes → Prop
  | .unknown oa ob a b => Res env a ∧ Res env b ∧ OriginP (Res env) oa ∧ OriginP (Res env) ob
  | _ => True

theorem res_natPred {x e : Expr} (he : Res env₁ e) (h : e.natPred? = some x) : Res env₁ x := by
  cases e with
  | lit l =>
    cases l with
    | natVal n =>
      cases n with
      | zero => exact nomatch h
      | succ k =>
        obtain rfl := Option.some.inj h
        simpa [Res, Expr.constsResolve] using he
    | strVal _ => exact nomatch h
  | app f a =>
    cases f with
    | const c us =>
      cases us with
      | nil =>
        simp only [Expr.natPred?] at h
        split at h
        · obtain rfl := Option.some.inj h
          exact (res_app.mp he).2
        · exact nomatch h
      | cons _ _ => simp [Expr.natPred?] at h
    | _ => simp [Expr.natPred?] at h
  | _ => exact nomatch h

theorem res_binderPair {lam : Bool} {a b t₁ b₁ t₂ b₂ : Expr} (ha : Res env₁ a) (hb : Res env₁ b)
    (h : Expr.binderPair? lam a b = some (t₁, b₁, t₂, b₂)) :
    Res env₁ t₁ ∧ Res env₁ b₁ ∧ Res env₁ t₂ ∧ Res env₁ b₂ := by
  cases lam <;> cases a <;> cases b <;>
    simp only [Expr.binderPair?, reduceCtorEq, Option.some.injEq, Prod.mk.injEq] at h <;>
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h
  · exact ⟨(res_forall.mp ha).1, (res_forall.mp ha).2, (res_forall.mp hb).1, (res_forall.mp hb).2⟩
  · exact ⟨(res_lam.mp ha).1, (res_lam.mp ha).2, (res_lam.mp hb).1, (res_lam.mp hb).2⟩

section Bodies

variable (K : KR env₁ r₂ r₁) (d : Nat) (mode : CheckMode)
include K

theorem defeqSpine_rel {a b : Expr} (ha : Res env₁ a) (hb : Res env₁ b) :
    Rel TT (defeqSpine r₂ env₂ d a b) (defeqSpine r₁ env₁ d a b) := by
  unfold defeqSpine
  cases a.getAppFn with
  | const n us =>
    cases b.getAppFn with
    | const n' us' =>
      dsimp only
      refine Rel.ite (fun _ => ?_) fun _ => Rel.ok trivial
      cases Level.isEquivList us us' with
      | none => exact Rel.ok trivial
      | some v =>
        cases v with
        | false => exact Rel.ok trivial
        | true =>
          exact defEqList_rel K d _ _ (fun x hx => res_getAppArgs ha x (List.mem_reverse.mp hx))
            (fun x hx => res_getAppArgs hb x (List.mem_reverse.mp hx))
    | _ => exact Rel.ok trivial
  | _ => exact Rel.ok trivial

theorem defeqBindersInner_rel (lam : Bool) {b₁ b₂ : Expr} (h₁ : Res env₁ b₁)
    (h₂ : Res env₁ b₂) :
    Rel TT (defeqBindersInner mode r₂ lam d b₁ b₂) (defeqBindersInner mode r₁ lam d b₁ b₂) := by
  unfold defeqBindersInner
  refine Rel.bind (K.defeq (d + 1) h₁ h₂) fun v _ => ?_
  refine Rel.iteB v (fun _ => ?_) fun _ => Rel.ok trivial
  dsimp only
  refine Rel.ite (fun _ => ?_) fun _ => Rel.ok trivial
  refine Rel.bind (K.infer (d + 1) h₁) fun t₁ ht₁ => Rel.bind (K.infer (d + 1) h₂) fun t₂ ht₂ =>
    Rel.bind (K.defeq (d + 1) ht₁ ht₂) fun v' _ => ?_
  exact Rel.iteB v' (fun _ => Rel.ok trivial) fun _ => Rel.ok trivial

theorem defeqDomain_rel {fvs : List Expr} {ty₁ ty₂ dom₂ : Expr} (hfv : ∀ v ∈ fvs, Res env₁ v)
    (h₁ : Res env₁ ty₁) (hd : Res env₁ dom₂) :
    Rel TT (defeqDomain r₂ d fvs ty₁ ty₂ dom₂) (defeqDomain r₁ d fvs ty₁ ty₂ dom₂) := by
  unfold defeqDomain
  exact Rel.ite (fun _ => Rel.ok trivial) fun _ => K.defeq d (res_instantiateList hfv 0 h₁) hd

omit K in
theorem defeqBinders_rel (K : KR env₁ r₂ r₁) (mode : CheckMode) (lam : Bool) :
    ∀ (fuel d : Nat) {fvs : List Expr} {ty₁ body₁ ty₂ body₂ : Expr}, (∀ v ∈ fvs, Res env₁ v) →
      Res env₁ ty₁ → Res env₁ body₁ → Res env₁ ty₂ → Res env₁ body₂ →
      Rel TT (defeqBinders mode r₂ lam fuel d fvs ty₁ body₁ ty₂ body₂)
        (defeqBinders mode r₁ lam fuel d fvs ty₁ body₁ ty₂ body₂)
  | fuel, d, fvs, ty₁, body₁, ty₂, body₂, hfv, h₁, hb₁, h₂, hb₂ => by
    unfold defeqBinders
    have hd₂ : Res env₁ (ty₂.instantiateList fvs) := res_instantiateList hfv 0 h₂
    refine Rel.bind (defeqDomain_rel K d hfv h₁ hd₂) fun v _ => ?_
    refine Rel.iteB v (fun _ => ?_) fun _ => Rel.ok trivial
    have hfv' : ∀ v ∈ Expr.fvar d (ty₂.instantiateList fvs) :: fvs, Res env₁ v := by
      intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact res_fvar.mpr hd₂
      · exact hfv v hv
    have ho₁ := res_instantiateList hfv' 0 hb₁
    have ho₂ := res_instantiateList hfv' 0 hb₂
    dsimp only
    cases fuel with
    | zero => exact defeqBindersInner_rel K d mode lam ho₁ ho₂
    | succ fuel =>
      cases hp : Expr.binderPair? lam body₁ body₂ with
      | none => exact defeqBindersInner_rel K d mode lam ho₁ ho₂
      | some q =>
        obtain ⟨ty₁', body₁', ty₂', body₂'⟩ := q
        dsimp only
        obtain ⟨h₃, h₄, h₅, h₆⟩ := res_binderPair hb₁ hb₂ hp
        exact defeqBinders_rel K mode lam fuel (d + 1) hfv' h₃ h₄ h₅ h₆

theorem quickDefEq_rel {a b : Expr} (ha : Res env₁ a) (hb : Res env₁ b) :
    Rel TT (quickDefEq mode r₂ d a b) (quickDefEq mode r₁ d a b) := by
  unfold quickDefEq
  refine Rel.ite (fun _ => Rel.ok trivial) fun _ => ?_
  cases a <;> cases b <;> first
    | exact Rel.ok trivial
    | exact Rel.bind Rel.triv fun _ _ => Rel.ok trivial
    | exact Rel.bind (defeqBinders_rel K mode true _ d (fun _ h => nomatch h)
        (res_lam.mp ha).1 (res_lam.mp ha).2 (res_lam.mp hb).1 (res_lam.mp hb).2)
        fun _ _ => Rel.ok trivial
    | exact Rel.bind (defeqBinders_rel K mode false _ d (fun _ h => nomatch h)
        (res_forall.mp ha).1 (res_forall.mp ha).2 (res_forall.mp hb).1 (res_forall.mp hb).2)
        fun _ _ => Rel.ok trivial

theorem defeqOffset_rel {a b : Expr} (ha : Res env₁ a) (hb : Res env₁ b) :
    Rel TT (defeqOffset r₂ d a b) (defeqOffset r₁ d a b) := by
  unfold defeqOffset
  refine Rel.ite (fun _ => Rel.ok trivial) fun _ => Rel.ite (fun _ => Rel.ok trivial) fun _ => ?_
  cases hpa : a.natPred? with
  | none => exact Rel.ok trivial
  | some x =>
    cases hpb : b.natPred? with
    | none => exact Rel.ok trivial
    | some y =>
      exact Rel.bind (K.defeq d (res_natPred ha hpa) (res_natPred hb hpb)) fun _ _ => Rel.ok trivial

theorem tryUnfoldProjApp_rel {e : Expr} (he : Res env₁ e) :
    Rel (ResO env₁) (tryUnfoldProjApp r₂ d e) (tryUnfoldProjApp r₁ d e) := by
  unfold tryUnfoldProjApp
  refine Rel.ite (fun _ => ?_) fun _ => Rel.ok resO_none
  refine Rel.bind (K.whnfCore false d he) fun e' he' => ?_
  exact Rel.ite (fun _ => Rel.ok resO_none) fun _ =>
    Rel.ok fun x h => (Option.some.inj h) ▸ he'

theorem deltaQuick_rel {a b : Expr} (ha : Res env₁ a) (hb : Res env₁ b) (fa fb : Bool) :
    Rel (DeltaRes env₁) (deltaQuick mode r₂ d a b fa fb) (deltaQuick mode r₁ d a b fa fb) := by
  unfold deltaQuick
  refine Rel.bind (quickDefEq_rel K d mode ha hb) fun o _ => ?_
  cases o with
  | none => exact Rel.ok ⟨ha, hb⟩
  | some v => cases v <;> exact Rel.ok trivial

variable (hx : EnvExt env₁ env₂)
include hx

/-- What a lazy step hands on resolves. -/
abbrev ResU (env : Env) (o : Option (Expr × Bool)) : Prop := ∀ x f, o = some (x, f) → Res env x

/-- What both sides' step hands on resolves. -/
abbrev ResB (env : Env) (o : Option (Expr × Expr × Bool)) : Prop :=
  ∀ x y f, o = some (x, y, f) → Res env x ∧ Res env y

/-- One side's lazy step, at an extension, is the prefix's. -/
theorem lazyUnfold_rel {a : Expr} (ha : Res env₁ a) :
    Rel (ResU env₁) (lazyUnfold r₂ env₂ d a) (lazyUnfold r₁ env₁ d a) := by
  unfold lazyUnfold
  refine Rel.bind (preFire_rel K d hx ha) fun o ho => ?_
  cases o with
  | some te =>
    exact Rel.bind (K.whnfCore true d (ho te.1 te.2 rfl)) fun a₃ ha₃ =>
      Rel.ok fun x f h => by obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj h); exact ha₃
  | none =>
    dsimp only
    rw [unfoldDefinition_ext hx ha]
    cases hu : unfoldDefinition env₁ a with
    | none => exact Rel.ok fun _ _ h => nomatch h
    | some a₂ =>
      exact Rel.bind (K.whnfCore true d (res_unfoldDefinition hx ha hu)) fun a₃ ha₃ =>
        Rel.ok fun x f h => by obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj h); exact ha₃

theorem lazyBothUnfold_rel {a b : Expr} (ha : Res env₁ a) (hb : Res env₁ b) :
    Rel (ResB env₁) (lazyBothUnfold r₂ env₂ d a b) (lazyBothUnfold r₁ env₁ d a b) := by
  unfold lazyBothUnfold
  rw [unfoldDefinition_ext hx ha, unfoldDefinition_ext hx hb]
  cases hua : unfoldDefinition env₁ a with
  | none => exact Rel.ok fun _ _ _ h => nomatch h
  | some a₂ =>
    cases hub : unfoldDefinition env₁ b with
    | none => exact Rel.ok fun _ _ _ h => nomatch h
    | some b₂ =>
      exact Rel.bind (K.whnfCore true d (res_unfoldDefinition hx ha hua)) fun a₃ ha₃ =>
        Rel.bind (K.whnfCore true d (res_unfoldDefinition hx hb hub)) fun b₃ hb₃ =>
          Rel.ok fun x y f h => by
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, -⟩ := h
            exact ⟨ha₃, hb₃⟩

theorem lazyBoth_rel {a b : Expr} (ha : Res env₁ a) (hb : Res env₁ b) :
    Rel (ResB env₁) (lazyBoth r₂ env₂ d a b) (lazyBoth r₁ env₁ d a b) := by
  unfold lazyBoth
  refine Rel.bind (preFire_rel K d hx ha) fun o ho => ?_
  cases o with
  | some te =>
    refine Rel.bind (preFire_rel K d hx hb) fun o' ho' => ?_
    cases o' with
    | some te' =>
      exact Rel.bind (K.whnfCore true d (ho te.1 te.2 rfl)) fun a₃ ha₃ =>
        Rel.bind (K.whnfCore true d (ho' te'.1 te'.2 rfl)) fun b₃ hb₃ =>
          Rel.ok fun x y f h => by
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, -⟩ := h
            exact ⟨ha₃, hb₃⟩
    | none => exact lazyBothUnfold_rel K d hx ha hb
  | none => exact lazyBothUnfold_rel K d hx ha hb

theorem lazyDeltaStep_rel {a b : Expr} (ha : Res env₁ a) (hb : Res env₁ b) :
    Rel (DeltaRes env₁) (lazyDeltaStep mode r₂ env₂ d a b) (lazyDeltaStep mode r₁ env₁ d a b) := by
  unfold lazyDeltaStep
  rw [unfoldableHead_ext hx ha, unfoldableHead_ext hx hb]
  cases unfoldableHead env₁ a with
  | false =>
    cases unfoldableHead env₁ b with
    | false => exact Rel.ok trivial
    | true =>
      refine Rel.bind (tryUnfoldProjApp_rel K d ha) fun o ho => ?_
      cases o with
      | some a₂ => exact deltaQuick_rel K d mode (ho _ rfl) hb _ _
      | none =>
        refine Rel.bind (lazyUnfold_rel K d hx hb) fun o ho => ?_
        cases o with
        | none => exact Rel.ok trivial
        | some p => obtain ⟨b₃, f⟩ := p; exact deltaQuick_rel K d mode ha (ho b₃ f rfl) _ _
  | true =>
    cases unfoldableHead env₁ b with
    | false =>
      refine Rel.bind (tryUnfoldProjApp_rel K d hb) fun o ho => ?_
      cases o with
      | some b₂ => exact deltaQuick_rel K d mode ha (ho _ rfl) _ _
      | none =>
        refine Rel.bind (lazyUnfold_rel K d hx ha) fun o ho => ?_
        cases o with
        | none => exact Rel.ok trivial
        | some p => obtain ⟨a₃, f⟩ := p; exact deltaQuick_rel K d mode (ho a₃ f rfl) hb _ _
    | true =>
      dsimp only
      rw [headHint_ext hx ha, headHint_ext hx hb]
      have hUa : Rel (DeltaRes env₁)
          (do match ← lazyUnfold r₂ env₂ d a with
            | some (a₃, fa) => deltaQuick mode r₂ d a₃ b fa false
            | none => pure .unknown)
          (do match ← lazyUnfold r₁ env₁ d a with
            | some (a₃, fa) => deltaQuick mode r₁ d a₃ b fa false
            | none => pure .unknown) := by
        refine Rel.bind (lazyUnfold_rel K d hx ha) fun o ho => ?_
        cases o with
        | none => exact Rel.ok trivial
        | some p => obtain ⟨a₃, f⟩ := p; exact deltaQuick_rel K d mode (ho a₃ f rfl) hb _ _
      have hUb : Rel (DeltaRes env₁)
          (do match ← lazyUnfold r₂ env₂ d b with
            | some (b₃, fb) => deltaQuick mode r₂ d a b₃ false fb
            | none => pure .unknown)
          (do match ← lazyUnfold r₁ env₁ d b with
            | some (b₃, fb) => deltaQuick mode r₁ d a b₃ false fb
            | none => pure .unknown) := by
        refine Rel.bind (lazyUnfold_rel K d hx hb) fun o ho => ?_
        cases o with
        | none => exact Rel.ok trivial
        | some p => obtain ⟨b₃, f⟩ := p; exact deltaQuick_rel K d mode ha (ho b₃ f rfl) _ _
      refine Rel.ite (fun _ => hUa) fun _ => Rel.ite (fun _ => hUb) fun _ => ?_
      refine Rel.ite (fun _ => ?_) fun _ => ?_
      · refine Rel.bind (lazyUnfold_rel K d hx ha) fun o ho => ?_
        cases o with
        | none => exact Rel.ok trivial
        | some p =>
          obtain ⟨a₃, f⟩ := p
          refine Rel.bind (lazyUnfold_rel K d hx hb) fun o' ho' => ?_
          cases o' with
          | none => exact Rel.ok trivial
          | some p' =>
            obtain ⟨b₃, f'⟩ := p'
            exact deltaQuick_rel K d mode (ho a₃ f rfl) (ho' b₃ f' rfl) _ _
      refine Rel.bind (Q := TT) (Rel.ite (fun _ => defeqSpine_rel K d ha hb)
        fun _ => Rel.ok trivial) fun v _ => ?_
      refine Rel.iteB v (fun _ => Rel.ok trivial) fun _ => ?_
      refine Rel.bind (lazyBoth_rel K d hx ha hb) fun o ho => ?_
      cases o with
      | none => exact Rel.ok trivial
      | some p =>
        obtain ⟨a₃, b₃, f⟩ := p
        exact deltaQuick_rel K d mode (ho a₃ b₃ f rfl).1 (ho a₃ b₃ f rfl).2 _ _

omit K hx in
theorem lazyDeltaReduction_rel (K : KR env₁ r₂ r₁) (d : Nat) (mode : CheckMode)
    (hx : EnvExt env₁ env₂) (eager : Bool) :
    ∀ (n : Nat) {oa ob : Option Expr} {a b : Expr}, OriginP (Res env₁) oa →
      OriginP (Res env₁) ob → Res env₁ a → Res env₁ b →
      Rel (LazyResRes env₁) (lazyDeltaReduction mode eager r₂ env₂ d n oa ob a b)
        (lazyDeltaReduction mode eager r₁ env₁ d n oa ob a b)
  | 0, _, _, _, _, _, _, _, _ => Rel.err _
  | n + 1, oa, ob, a, b, hoa, hob, ha, hb => by
    simp only [lazyDeltaReduction]
    refine Rel.bind (defeqOffset_rel K d ha hb) fun o _ => ?_
    cases o with
    | some v => exact Rel.ok trivial
    | none =>
      dsimp only
      refine Rel.bind (Q := ResO env₁) (Rel.ite (fun _ => reduceNat_rel K d hx ha)
        fun _ => Rel.ok resO_none) fun o ho => ?_
      cases o with
      | some a₂ =>
        exact Rel.bind (K.defeq d (ho _ rfl) hb) fun _ _ => Rel.ok trivial
      | none =>
        dsimp only
        refine Rel.bind (Q := ResO env₁) (Rel.ite (fun _ => reduceNat_rel K d hx hb)
          fun _ => Rel.ok resO_none) fun o' ho' => ?_
        cases o' with
        | some b₂ =>
          exact Rel.bind (K.defeq d ha (ho' _ rfl)) fun _ _ => Rel.ok trivial
        | none =>
          dsimp only
          refine Rel.bind (lazyDeltaStep_rel K d mode hx ha hb) fun st hst => ?_
          cases st with
          | cont a' b' fa fb =>
            dsimp only
            rw [noteOrigin_ext hx hst.1, noteOrigin_ext hx hst.2]
            exact lazyDeltaReduction_rel K d mode hx eager n ((hoa.drop fa a).note hst.1)
              ((hob.drop fb b).note hst.2) hst.1 hst.2
          | eq => exact Rel.ok trivial
          | diff => exact Rel.ok trivial
          | unknown => exact Rel.ok ⟨ha, hb, hoa, hob⟩

omit K hx in
theorem lazyDeltaProjReduction_rel (K : KR env₁ r₂ r₁) (d : Nat) (mode : CheckMode)
    (hx : EnvExt env₁ env₂) {sn : Name} (i : Nat) (hsn : (env₁.find? sn).isSome = true) :
    ∀ (n : Nat) {a b : Expr}, Res env₁ a → Res env₁ b →
      Rel TT (lazyDeltaProjReduction mode r₂ env₂ d sn i n a b)
        (lazyDeltaProjReduction mode r₁ env₁ d sn i n a b)
  | 0, _, _, _, _ => Rel.err _
  | n + 1, a, b, ha, hb => by
    simp only [lazyDeltaProjReduction]
    have htail : Rel TT
        (do match ← reduceProjCore mode r₂ env₂ d sn i a with
          | some x =>
            match ← reduceProjCore mode r₂ env₂ d sn i b with
            | some y => r₂.defeq d x y
            | none => r₂.defeq d a b
          | none => r₂.defeq d a b)
        (do match ← reduceProjCore mode r₁ env₁ d sn i a with
          | some x =>
            match ← reduceProjCore mode r₁ env₁ d sn i b with
            | some y => r₁.defeq d x y
            | none => r₁.defeq d a b
          | none => r₁.defeq d a b) := by
      refine Rel.bind (reduceProjCore_rel K d hx mode i hsn ha) fun o ho => ?_
      cases o with
      | none => exact K.defeq d ha hb
      | some x =>
        refine Rel.bind (reduceProjCore_rel K d hx mode i hsn hb) fun o' ho' => ?_
        cases o' with
        | none => exact K.defeq d ha hb
        | some y => exact K.defeq d (ho _ rfl) (ho' _ rfl)
    refine Rel.bind (lazyDeltaStep_rel K d mode hx ha hb) fun st hst => ?_
    cases st with
    | cont a' b' _ _ => exact lazyDeltaProjReduction_rel K d mode hx i hsn n hst.1 hst.2
    | eq => exact Rel.ok trivial
    | diff => exact htail
    | unknown => exact htail

theorem defeqProjPair_rel {a b : Expr} (ha : Res env₁ a) (hb : Res env₁ b) :
    Rel TT (defeqProjPair mode r₂ env₂ d a b) (defeqProjPair mode r₁ env₁ d a b) := by
  unfold defeqProjPair
  cases a <;> cases b <;> first
    | exact Rel.ok trivial
    | exact Rel.ite (fun _ => lazyDeltaProjReduction_rel K d mode hx _ (res_proj.mp ha).1 _
        (res_proj.mp ha).2 (res_proj.mp hb).2) fun _ => Rel.ok trivial

theorem defeqStuck_rel {a b : Expr} (ha : Res env₁ a) (hb : Res env₁ b) :
    Rel TT (defeqStuck mode r₂ env₂ d a b) (defeqStuck mode r₁ env₁ d a b) := by
  have hst := fun {a b : Expr} (ha : Res env₁ a) (hb : Res env₁ b) => stuckIrrel_rel K d hx ha hb
  have hlam : ∀ {t body c : Expr} (_ : Res env₁ t) (_ : Res env₁ body) (_ : Res env₁ c),
      Rel TT (do
          if ← etaCert mode r₂ env₂ d t body c then pure true
          else stuckIrrel r₂ env₂ d (.lam t body) c)
        (do
          if ← etaCert mode r₁ env₁ d t body c then pure true
          else stuckIrrel r₁ env₁ d (.lam t body) c) := fun ht hbo hc =>
    Rel.bind (etaCert_rel K d mode ht hbo hc) fun v _ =>
      Rel.iteB v (fun _ => Rel.ok trivial) fun _ => hst (res_lam.mpr ⟨ht, hbo⟩) hc
  have hlam' : ∀ {t body c : Expr} (_ : Res env₁ t) (_ : Res env₁ body) (_ : Res env₁ c),
      Rel TT (do
          if ← etaCert mode r₂ env₂ d t body c then pure true
          else stuckIrrel r₂ env₂ d c (.lam t body))
        (do
          if ← etaCert mode r₁ env₁ d t body c then pure true
          else stuckIrrel r₁ env₁ d c (.lam t body)) := fun ht hbo hc =>
    Rel.bind (etaCert_rel K d mode ht hbo hc) fun v _ =>
      Rel.iteB v (fun _ => Rel.ok trivial) fun _ => hst hc (res_lam.mpr ⟨ht, hbo⟩)
  unfold defeqStuck
  cases a with
  | lit l =>
    cases b with
    | app f x =>
      cases l with
      | natVal _ => exact hst ha hb
      | strVal st =>
        cases f with
        | const cO usO =>
          dsimp only
          rw [strLit_of_res hx ha]
          exact Rel.ite (fun _ => K.defeq d (res_strLitToConstructor ha) hb) fun _ => hst ha hb
        | _ => exact hst ha hb
    | lam t body => exact hlam' (res_lam.mp hb).1 (res_lam.mp hb).2 ha
    | _ => exact hst ha hb
  | app f x =>
    cases b with
    | lit l =>
      cases l with
      | natVal _ => exact hst ha hb
      | strVal st =>
        cases f with
        | const cO usO =>
          dsimp only
          rw [strLit_of_res hx hb]
          exact Rel.ite (fun _ => K.defeq d ha (res_strLitToConstructor hb)) fun _ => hst ha hb
        | _ => exact hst ha hb
    | app f₂ x₂ =>
      dsimp only
      refine Rel.ite (fun _ => ?_) fun _ => hst ha hb
      refine Rel.bind (K.defeq d (res_getAppFn ha) (res_getAppFn hb)) fun v _ => ?_
      refine Rel.iteB v (fun _ => ?_) fun _ => hst ha hb
      refine Rel.bind (defEqList_rel K d _ _ (res_getAppArgs ha) (res_getAppArgs hb)) fun v' _ => ?_
      exact Rel.iteB v' (fun _ => Rel.ok trivial) fun _ => hst ha hb
    | lam t body => exact hlam' (res_lam.mp hb).1 (res_lam.mp hb).2 ha
    | _ => exact hst ha hb
  | fvar i ty₁ =>
    cases b with
    | fvar j ty₂ => exact Rel.ite (fun _ => Rel.ok trivial) fun _ => hst ha hb
    | lam t body => exact hlam' (res_lam.mp hb).1 (res_lam.mp hb).2 ha
    | _ => exact hst ha hb
  | const n us =>
    cases b with
    | const n' us' =>
      dsimp only
      refine Rel.ite (fun _ => ?_) fun _ => hst ha hb
      refine Rel.bind Rel.triv fun v _ => ?_
      exact Rel.iteB v (fun _ => Rel.ok trivial) fun _ => hst ha hb
    | lam t body => exact hlam' (res_lam.mp hb).1 (res_lam.mp hb).2 ha
    | _ => exact hst ha hb
  | lam t body =>
    exact hlam (res_lam.mp ha).1 (res_lam.mp ha).2 hb
  | _ =>
    cases b with
    | lam t body => exact hlam' (res_lam.mp hb).1 (res_lam.mp hb).2 ha
    | _ => exact hst ha hb

theorem rulesLast_rel {oa ob : Option Expr} {a b : Expr} (hoa : OriginP (Res env₁) oa)
    (hob : OriginP (Res env₁) ob) (ha : Res env₁ a) (hb : Res env₁ b) :
    Rel TT (rulesLast r₂ env₂ d oa ob a b) (rulesLast r₁ env₁ d oa ob a b) := by
  unfold rulesLast
  refine Rel.bind (originFire_rel K d hx hoa ha) fun ra hra => ?_
  refine Rel.bind (originFire_rel K d hx hob hb) fun rb hrb => ?_
  rcases ra with _ | ⟨t, a₂⟩ <;> rcases rb with _ | ⟨t', b₂⟩
  · exact Rel.ok trivial
  · exact K.defeq d ha (hrb _ _ rfl)
  · exact K.defeq d (hra _ _ rfl) hb
  · exact K.defeq d (hra _ _ rfl) (hrb _ _ rfl)

theorem defeqLazy_rel (eager : Bool) {a b : Expr} (ha : Res env₁ a) (hb : Res env₁ b) :
    Rel TT (defeqLazy mode eager r₂ env₂ d a b) (defeqLazy mode eager r₁ env₁ d a b) := by
  unfold defeqLazy
  refine Rel.bind (quickDefEq_rel K d mode ha hb) fun o _ => ?_
  cases o with
  | some v => exact Rel.ok trivial
  | none =>
    dsimp only
    refine Rel.bind (propIrrel_rel K d hx ha hb) fun p _ => ?_
    refine Rel.iteB p (fun _ => Rel.ok trivial) fun _ => ?_
    refine Rel.bind (K.whnfCore true d ha) fun a' ha' => Rel.bind (K.whnfCore true d hb) fun b' hb' => ?_
    refine Rel.bind (quickDefEq_rel K d mode ha' hb') fun o' _ => ?_
    cases o' with
    | some v => exact Rel.ok trivial
    | none =>
      dsimp only
      rw [noteOrigin_ext hx ha', noteOrigin_ext hx hb']
      refine Rel.bind (lazyDeltaReduction_rel K d mode hx eager _
        ((OriginP.none _).note ha') ((OriginP.none _).note hb') ha' hb') fun lz hlz => ?_
      cases lz with
      | verdict v => exact Rel.ok trivial
      | unknown oa ob a₁ b₁ =>
        obtain ⟨ha₁, hb₁, hoa, hob⟩ := hlz
        dsimp only
        have hrl := rulesLast_rel K d hx hoa hob ha₁ hb₁
        refine Rel.bind (defeqProjPair_rel K d mode hx ha₁ hb₁) fun q _ => ?_
        refine Rel.iteB q (fun _ => Rel.ok trivial) fun _ => ?_
        refine Rel.ite (fun _ => Rel.bind (defeqStuck_rel K d mode hx ha₁ hb₁) fun v _ =>
          Rel.iteB v (fun _ => Rel.ok trivial) fun _ => hrl) fun _ => ?_
        refine Rel.bind (K.whnfCore false d ha₁) fun a₂ ha₂ =>
          Rel.bind (K.whnfCore false d hb₁) fun b₂ hb₂ => ?_
        exact Rel.ite (fun _ => Rel.bind (defeqStuck_rel K d mode hx ha₁ hb₁) fun v _ =>
            Rel.iteB v (fun _ => Rel.ok trivial) fun _ => hrl)
          fun _ => Rel.bind (K.defeq d ha₂ hb₂) fun v _ =>
            Rel.iteB v (fun _ => Rel.ok trivial) fun _ => hrl

theorem defeqBody_rel (eager : Bool) {a b : Expr} (ha : Res env₁ a) (hb : Res env₁ b) :
    Rel TT (defeqBody mode eager r₂ env₂ d a b) (defeqBody mode eager r₁ env₁ d a b) := by
  unfold defeqBody
  refine Rel.ite (fun _ => Rel.ok trivial) fun _ => ?_
  rw [ctorTargetFor_ext hx hb, ctorTargetFor_ext hx ha]
  split
  · refine Rel.bind (K.whnf d ha) fun w hw => ?_
    rw [ctorHeadAgainst_ext hx hw]
    split
    · exact defeqLazy_rel K d mode hx eager hw hb
    · exact Rel.ok trivial
    · exact defeqLazy_rel K d mode hx eager ha hb
  · split
    · refine Rel.bind (K.whnf d hb) fun w hw => ?_
      rw [ctorHeadAgainst_ext hx hw]
      split
      · exact defeqLazy_rel K d mode hx eager ha hw
      · exact Rel.ok trivial
      · exact defeqLazy_rel K d mode hx eager ha hb
    · exact defeqLazy_rel K d mode hx eager ha hb

end Bodies

/-! ## The knot -/

/-- **The knot theorem.**  At every fuel and at either flag, the knot at an extension is the knot
at `env₁` on terms resolving in `env₁`. -/
theorem knot_ext (mode : CheckMode) (hx : EnvExt env₁ env₂) :
    ∀ (fuel : Nat) (eager : Bool),
      KR env₁ (pureFns mode eager env₂ fuel) (pureFns mode eager env₁ fuel)
  | 0, _ =>
    { whnfCore := fun _ _ _ _ => Rel.err _
      whnf := fun _ _ _ => Rel.err _
      infer := fun _ _ _ => Rel.err _
      inferIO := fun _ _ _ => Rel.err _
      defeq := fun _ _ _ _ _ => Rel.err _
      defeqE := fun _ _ _ _ _ => Rel.err _ }
  | fuel + 1, eager =>
    have K := knot_ext mode hx fuel eager
    have KE := knot_ext mode hx fuel true
    { whnfCore := fun c d _ he => whnfCoreBody_rel K d hx mode c he
      whnf := fun d _ he => whnfLoop_rel K d hx _ (OriginP.none _) he
      infer := fun d _ he => inferBody_rel K hx d he
      inferIO := fun d _ he => inferBodyIO_rel K hx d he
      defeq := fun d _ _ ha hb => defeqBody_rel K d mode hx eager ha hb
      defeqE := fun d _ _ ha hb => defeqBody_rel KE d mode hx true ha hb }

/-- The checker operations' `whnf` at an extension is the one at the prefix, on a resolved term. -/
theorem fueledOps_whnf_ext (hx : EnvExt env₁ env₂) (F i : Nat) {e : Expr} (he : Res env₁ e) :
    (fueledOps .verified F).whnf env₂ i e = (fueledOps .verified F).whnf env₁ i e ∧
      ∀ w, (fueledOps .verified F).whnf env₁ i e = .ok w → Res env₁ w := by
  obtain ⟨hw, hP⟩ := (knot_ext .verified hx F false).whnf i he
  rw [whnf_def, whnf_def] at hw
  rw [whnf_def] at hP
  exact ⟨hw, hP⟩

/-- The telescope walk of a former, at an extension. -/
theorem whnfTelescope_ext (hx : EnvExt env₁ env₂) (F : Nat) (n : Nat) :
    ∀ (i : Nat) {e : Expr}, Res env₁ e →
      whnfTelescope (fueledOps .verified F) env₂ i n e =
        whnfTelescope (fueledOps .verified F) env₁ i n e := by
  induction n with
  | zero =>
    intro i e he
    unfold whnfTelescope
    rw [(fueledOps_whnf_ext hx F i he).1]
  | succ n ih =>
    intro i e he
    unfold whnfTelescope
    obtain ⟨hw, hP⟩ := fueledOps_whnf_ext hx F i he
    rw [hw]
    -- Each arm reduces the bind before closing: a bare `rfl` would leave the kernel comparing the
    -- two continuations, whose recursive calls differ in the environment, and it would unfold the
    -- whole knot to compare them.
    cases hr : (fueledOps .verified F).whnf env₁ i e with
    | error _ => simp only [bind, Except.bind]
    | ok w =>
      have hres : Res env₁ w := hP w hr
      cases w with
      | forallE dom body =>
        obtain ⟨hd, hb⟩ := res_forall.mp hres
        simp only [bind, Except.bind]
        rw [ih (i + 1) (res_open (d := i) hd hb)]
      | _ => simp only [bind, Except.bind]

/-- **A former's reduct at an extension is the one at the prefix.** -/
theorem reducedFormer_ext {envB env : Env} (hx : EnvExt envB env)
    {cv : ConstantVal} {n F : Nat} {f : ConstantVal} (hr : cv.type.constsResolve envB = true)
    (h : reducedFormer (fueledOps .verified F) envB cv n = .ok f) :
    reducedFormer (fueledOps .verified F) env cv n = .ok f := by
  unfold reducedFormer at h ⊢
  rw [whnfTelescope_ext hx F n 0 hr]
  exact h

end ConLeche.Verify
