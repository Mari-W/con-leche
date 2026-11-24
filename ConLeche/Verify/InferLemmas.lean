module

public import ConLeche.Verify.Mono
import ConLeche.Kernel.TypeChecker
import ConLeche.Verify.Shift
import ConLeche.Verify.InstLevels
public import ConLeche.Verify.EnvWF
import ConLeche.Verify.Knot
public import ConLeche.Verify.StrLitExpr
import ConLeche.Verify.InstList
public import ConLeche.Verify.InstSpine
import ConLeche.Verify.IotaReduct

public section

/-!
# Preservation and inversion lemmas for the checker core

Under environment well-formedness (`EnvWF`), reduction preserves the
syntactic invariants the model soundness proofs thread (well-scopedness
here; the free-variable leaf closure in `ConLeche.Verify.InferLeaves`),
and the new mutual-core branches get inversion lemmas so the many
consumers don't re-destructure the do-chains.
-/

set_option linter.unusedSimpArgs false

namespace ConLeche

variable {mode : CheckMode} {eager : Bool}

open Expr

/-! ## Inversion lemmas -/

/-- An application's argument list is never empty. -/
theorem getAppArgs_app_ne_nil (f a : Expr) : (Expr.app f a).getAppArgs ≠ [] := by
  simp [Expr.getAppArgs]

set_option linter.unusedSimpArgs false in
/-- Inversion for `whnfCore` on applications, taken as a whole spine: the spine head
normalized to a λ and the spine's first argument met it (uniform β, no certificate), or it is
its own head normal form and ι or a rule fired at the whole spine (`iotaThenRule`) or the spine
is stuck, or it reduced to something else and head normalization went on at the spine
re-assembled. -/
theorem whnf_app_inv {env : Env} {fuel d : Nat} {f a e' : Expr} {c : Bool}
    (h : whnfCore mode eager env (fuel + 1) d (.app f a) c = .ok e') :
    ∃ v, whnfCore mode eager env fuel d (Expr.app f a).getAppFn c = .ok v ∧
      ((∃ ty body a₁ rest, v = .lam ty body ∧ (Expr.app f a).getAppArgs = a₁ :: rest ∧
          whnfCore mode eager env fuel d (Expr.mkAppN (body.instantiate1 a₁) rest) c = .ok e') ∨
        (v = (Expr.app f a).getAppFn ∧
          ((∃ e'', iotaThenRule mode (pureFns mode eager env fuel) env d (.app f a)
              = .ok (some e'') ∧
            whnfCore mode eager env fuel d e'' c = .ok e') ∨
           (iotaThenRule mode (pureFns mode eager env fuel) env d (.app f a) = .ok none ∧
            e' = .app f a))) ∨
        ((∀ ty body, v ≠ .lam ty body) ∧ v ≠ (Expr.app f a).getAppFn ∧
          whnfCore mode eager env fuel d (Expr.mkAppN v (Expr.app f a).getAppArgs) c
            = .ok e')) := by
  rw [whnfCore_succ] at h
  simp only [whnfCoreBody, Bind.bind, Except.bind] at h
  simp only [whnfCore_def] at h
  cases hwf : whnfCore mode eager env fuel d (Expr.app f a).getAppFn c with
  | error err => rw [hwf] at h; exact nomatch h
  | ok v =>
  rw [hwf] at h
  dsimp only at h
  refine ⟨v, rfl, ?_⟩
  split at h
  · rename_i ty body
    refine Or.inl ⟨ty, body, ?_⟩
    cases hargs : (Expr.app f a).getAppArgs with
    | nil => exact absurd hargs (getAppArgs_app_ne_nil f a)
    | cons a₁ rest =>
      rw [hargs] at h
      exact ⟨a₁, rest, rfl, rfl, h⟩
  · rename_i hv
    by_cases hvh : v = (Expr.app f a).getAppFn
    · rw [ite_eq_left hvh] at h
      refine Or.inr (Or.inl ⟨hvh, ?_⟩)
      cases hio : iotaThenRule mode (pureFns mode eager env fuel) env d (.app f a) with
      | error err => rw [hio] at h; exact nomatch h
      | ok o =>
        rw [hio] at h
        dsimp only at h
        cases o with
        | some e'' => exact Or.inl ⟨e'', rfl, h⟩
        | none =>
          simp only [pure, Except.pure, Except.ok.injEq] at h
          exact Or.inr ⟨rfl, h.symm⟩
    · rw [ite_eq_right hvh] at h
      exact Or.inr (Or.inr ⟨fun ty body hh => hv ty body hh, hvh, h⟩)

/-- The `Eq` spine's parts are the spine's. -/
theorem eqSpine?_eq_some {R A l rhs : Expr} {eqn : Name} {u : Level} :
    eqSpine? R = some (eqn, u, A, l, rhs) ↔ R = .app (.app (.app (.const eqn [u]) A) l) rhs := by
  constructor
  · intro h
    unfold eqSpine? at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
      rfl
    · exact nomatch h
  · rintro rfl
    rfl

/-- **A rule's sides keep a property that binders and applications split** (`ruleSides`): a
property `Q k` of the statement that holds of a binder exactly where it holds of its domain at
`k` and of its body at `s k`, of an application exactly where it holds of both parts, and of
every sort, holds of the five sides. -/
theorem ruleSides_keep (Q : Nat → Expr → Prop) (s : Nat → Nat)
    (hpi : ∀ k ty b, Q k (.forallE ty b) ↔ Q k ty ∧ Q (s k) b)
    (hlam : ∀ k ty b, Q k (.lam ty b) ↔ Q k ty ∧ Q (s k) b)
    (happ : ∀ k f a, Q k (.app f a) ↔ Q k f ∧ Q k a) (hsort : ∀ k u, Q k (.sort u)) :
    ∀ (T : Expr) (k : Nat) {P L R LA PU : Expr}, ruleSides T = some (P, L, R, LA, PU) → Q k T →
      Q k P ∧ Q k L ∧ Q k R ∧ Q k LA ∧ Q k PU := by
  intro T
  induction T with
  | forallE ty b _ ihb =>
    intro k P L R LA PU h hQ
    simp only [ruleSides, Option.map_eq_some_iff] at h
    obtain ⟨⟨P', L', R', LA', PU'⟩, hb, he⟩ := h
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ : Expr.forallE ty P' = P ∧ Expr.lam ty L' = L ∧
        Expr.lam ty R' = R ∧ Expr.lam ty LA' = LA ∧ Expr.forallE ty PU' = PU := by
      simpa using he
    obtain ⟨hty, hbQ⟩ := (hpi k ty b).mp hQ
    obtain ⟨h1, h2, h3, h4, h5⟩ := ihb (s k) hb hbQ
    exact ⟨(hpi k ty P').mpr ⟨hty, h1⟩, (hlam k ty L').mpr ⟨hty, h2⟩, (hlam k ty R').mpr ⟨hty, h3⟩,
      (hlam k ty LA').mpr ⟨hty, h4⟩, (hpi k ty PU').mpr ⟨hty, h5⟩⟩
  | _ =>
    intro k P L R LA PU h hQ
    simp only [ruleSides, Option.map_eq_some_iff] at h
    obtain ⟨⟨eqn, u, A, l, r⟩, hsp, he⟩ := h
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ : A = P ∧ l = L ∧ r = R ∧ A = LA ∧ Expr.sort u = PU := by
      simpa using he
    rw [eqSpine?_eq_some] at hsp
    rw [hsp] at hQ
    obtain ⟨h1, hr⟩ := (happ _ _ _).mp hQ
    obtain ⟨h2, hl⟩ := (happ _ _ _).mp h1
    have hA := ((happ _ _ _).mp h2).2
    exact ⟨hA, hl, hr, hA, hsort k u⟩

theorem ruleSides_WScoped {T P L R LA PU : Expr} {d : Nat}
    (h : ruleSides T = some (P, L, R, LA, PU)) (hw : Expr.WScoped d T) :
    Expr.WScoped d P ∧ Expr.WScoped d L ∧ Expr.WScoped d R ∧ Expr.WScoped d LA ∧
      Expr.WScoped d PU :=
  ruleSides_keep (fun k e => Expr.WScoped k e) id (fun _ _ _ => by simp [Expr.WScoped])
    (fun _ _ _ => by simp [Expr.WScoped]) (fun _ _ _ => by simp [Expr.WScoped])
    (fun _ _ => by simp [Expr.WScoped]) T d h hw

theorem ruleSides_looseBVarsBounded {T P L R LA PU : Expr} {k : Nat}
    (h : ruleSides T = some (P, L, R, LA, PU)) (hb : T.looseBVarsBounded k = true) :
    P.looseBVarsBounded k = true ∧ L.looseBVarsBounded k = true ∧
      R.looseBVarsBounded k = true ∧ LA.looseBVarsBounded k = true ∧
      PU.looseBVarsBounded k = true :=
  ruleSides_keep (fun k e => e.looseBVarsBounded k = true) (· + 1)
    (fun _ _ _ => by simp [Expr.looseBVarsBounded]) (fun _ _ _ => by simp [Expr.looseBVarsBounded])
    (fun _ _ _ => by simp [Expr.looseBVarsBounded]) (fun _ _ => by simp [Expr.looseBVarsBounded])
    T k h hb

theorem ruleSides_hasFvar {T P L R LA PU : Expr} (h : ruleSides T = some (P, L, R, LA, PU))
    (hf : T.hasFvar = false) :
    P.hasFvar = false ∧ L.hasFvar = false ∧ R.hasFvar = false ∧ LA.hasFvar = false ∧
      PU.hasFvar = false :=
  ruleSides_keep (fun _ e => e.hasFvar = false) id (fun _ _ _ => by simp [Expr.hasFvar])
    (fun _ _ _ => by simp [Expr.hasFvar]) (fun _ _ _ => by simp [Expr.hasFvar])
    (fun _ _ => by simp [Expr.hasFvar]) T 0 h hf

theorem ruleSides_constsResolve {T P L R LA PU : Expr} {env : Env}
    (h : ruleSides T = some (P, L, R, LA, PU)) (hr : T.constsResolve env = true) :
    P.constsResolve env = true ∧ L.constsResolve env = true ∧ R.constsResolve env = true ∧
      LA.constsResolve env = true ∧ PU.constsResolve env = true :=
  ruleSides_keep (fun _ e => e.constsResolve env = true) id
    (fun _ _ _ => by simp [Expr.constsResolve]) (fun _ _ _ => by simp [Expr.constsResolve])
    (fun _ _ _ => by simp [Expr.constsResolve]) (fun _ _ => by simp [Expr.constsResolve]) T 0 h hr

/-- The universe of a rule statement's `Eq` spine, under its binders. -/
@[expose] def ruleLevel : Expr → Option Level
  | .forallE _ b => ruleLevel b
  | e => (eqSpine? e).map fun (_, u, _, _, _) => u

/-- A rule's sides commute with instantiating its universe parameters. -/
theorem ruleSides_instantiateLevelParams (ks : List Name) (us : List Level) :
    ∀ (T : Expr) {P L R LA PU : Expr}, ruleSides T = some (P, L, R, LA, PU) →
      ruleSides (T.instantiateLevelParams ks us) = some (P.instantiateLevelParams ks us,
        L.instantiateLevelParams ks us, R.instantiateLevelParams ks us,
        LA.instantiateLevelParams ks us, PU.instantiateLevelParams ks us) := by
  intro T
  induction T with
  | forallE ty b _ ihb =>
    intro P L R LA PU h
    simp only [ruleSides, Option.map_eq_some_iff] at h
    obtain ⟨⟨P', L', R', LA', PU'⟩, hb, he⟩ := h
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ : Expr.forallE ty P' = P ∧ Expr.lam ty L' = L ∧
        Expr.lam ty R' = R ∧ Expr.lam ty LA' = LA ∧ Expr.forallE ty PU' = PU := by
      simpa using he
    simp only [Expr.instantiateLevelParams, ruleSides, ihb hb, Option.map_some]
  | _ =>
    intro P L R LA PU h
    simp only [ruleSides, Option.map_eq_some_iff] at h
    obtain ⟨⟨eqn, u, A, l, r⟩, hsp, he⟩ := h
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ : A = P ∧ l = L ∧ r = R ∧ A = LA ∧ Expr.sort u = PU := by
      simpa using he
    rw [eqSpine?_eq_some] at hsp
    rw [hsp]
    simp [Expr.instantiateLevelParams, ruleSides, eqSpine?]

/-- A rule statement's universe commutes with instantiating its universe parameters. -/
theorem ruleLevel_instantiateLevelParams (ks : List Name) (us : List Level) :
    ∀ (T : Expr) {v : Level}, ruleLevel T = some v →
      ruleLevel (T.instantiateLevelParams ks us) = some (Level.subst ks us v) := by
  intro T
  induction T with
  | forallE ty b _ ihb => intro v h; exact ihb h
  | app f a _ _ =>
    intro v h
    simp only [ruleLevel, Option.map_eq_some_iff] at h
    obtain ⟨⟨eqn, u, A, l, r⟩, hsp, rfl⟩ := h
    rw [eqSpine?_eq_some] at hsp
    rw [hsp]
    simp [Expr.instantiateLevelParams, ruleLevel, eqSpine?]
  | _ => intro v h; simp [ruleLevel, eqSpine?] at h

/-- A statement with sides has a universe. -/
theorem ruleLevel_of_ruleSides :
    ∀ (T : Expr) {P L R LA PU : Expr}, ruleSides T = some (P, L, R, LA, PU) →
      ∃ v, ruleLevel T = some v := by
  intro T
  induction T with
  | forallE ty b _ ihb =>
    intro P L R LA PU h
    simp only [ruleSides, Option.map_eq_some_iff] at h
    obtain ⟨⟨P', L', R', LA', PU'⟩, hb, -⟩ := h
    exact ihb hb
  | _ =>
    intro P L R LA PU h
    simp only [ruleSides, Option.map_eq_some_iff] at h
    obtain ⟨⟨eqn, u, A, l, r⟩, hsp, -⟩ := h
    exact ⟨u, by simp [ruleLevel, hsp]⟩

/-- A rule's sides commute with instantiating a bound variable. -/
theorem ruleSides_instantiate1 (v : Expr) :
    ∀ (T : Expr) (k : Nat) {P L R LA PU : Expr}, ruleSides T = some (P, L, R, LA, PU) →
      ruleSides (T.instantiate1 v k) = some (P.instantiate1 v k, L.instantiate1 v k,
        R.instantiate1 v k, LA.instantiate1 v k, PU.instantiate1 v k) ∧
      (ruleTele (T.instantiate1 v k)).1 = (ruleTele T).1 := by
  intro T
  induction T with
  | forallE ty b _ ihb =>
    intro k P L R LA PU h
    simp only [ruleSides, Option.map_eq_some_iff] at h
    obtain ⟨⟨P', L', R', LA', PU'⟩, hb, he⟩ := h
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ : Expr.forallE ty P' = P ∧ Expr.lam ty L' = L ∧
        Expr.lam ty R' = R ∧ Expr.lam ty LA' = LA ∧ Expr.forallE ty PU' = PU := by
      simpa using he
    obtain ⟨h1, h2⟩ := ihb (k + 1) hb
    refine ⟨?_, ?_⟩
    · simp only [Expr.instantiate1, ruleSides, h1, Option.map_some]
    · simp only [Expr.instantiate1, ruleTele, h2]
  | _ =>
    intro k P L R LA PU h
    simp only [ruleSides, Option.map_eq_some_iff] at h
    obtain ⟨⟨eqn, u, A, l, r⟩, hsp, he⟩ := h
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ : A = P ∧ l = L ∧ r = R ∧ A = LA ∧ Expr.sort u = PU := by
      simpa using he
    rw [eqSpine?_eq_some] at hsp
    rw [hsp]
    exact ⟨by simp [Expr.instantiate1, ruleSides, eqSpine?], by simp [Expr.instantiate1, ruleTele]⟩

/-- A rule statement's universe survives instantiating a bound variable. -/
theorem ruleLevel_instantiate1 (v : Expr) :
    ∀ (T : Expr) (k : Nat) {P L R LA PU : Expr}, ruleSides T = some (P, L, R, LA, PU) →
      ruleLevel (T.instantiate1 v k) = ruleLevel T := by
  intro T
  induction T with
  | forallE ty b _ ihb =>
    intro k P L R LA PU h
    simp only [ruleSides, Option.map_eq_some_iff] at h
    obtain ⟨⟨P', L', R', LA', PU'⟩, hb, -⟩ := h
    simp only [Expr.instantiate1, ruleLevel]
    exact ihb (k + 1) hb
  | _ =>
    intro k P L R LA PU h
    simp only [ruleSides, Option.map_eq_some_iff] at h
    obtain ⟨⟨eqn, u, A, l, r⟩, hsp, -⟩ := h
    rw [eqSpine?_eq_some] at hsp
    rw [hsp]
    simp [Expr.instantiate1, ruleLevel, eqSpine?]

/-- **The residual's universe is the statement's**: a statement with sides, peeled along its
arguments down to an `Eq` spine, reads that spine at its own universe. -/
theorem piResidual_ruleLevel :
    ∀ (args : List Expr) (T : Expr) {P L R LA PU : Expr} {v u : Level} {A l r : Expr} {en : Name},
      ruleSides T = some (P, L, R, LA, PU) → ruleLevel T = some v →
      piResidual T args = some (.app (.app (.app (.const en [u]) A) l) r) → u = v := by
  intro args
  induction args with
  | nil =>
    intro T P L R LA PU v u A l r en _ hv hr
    obtain rfl := Option.some.inj hr
    simpa [ruleLevel, eqSpine?] using hv
  | cons a as ih =>
    intro T P L R LA PU v u A l r en hs hv hr
    cases T with
    | forallE ty b =>
      simp only [ruleSides, Option.map_eq_some_iff] at hs
      obtain ⟨⟨P', L', R', LA', PU'⟩, hb, -⟩ := hs
      obtain ⟨hbi, -⟩ := ruleSides_instantiate1 a b 0 hb
      exact ih (b.instantiate1 a) hbi (by rw [ruleLevel_instantiate1 a b 0 hb]; exact hv) hr
    | _ => all_goals simp [piResidual] at hr

theorem bind_eqSpine?_eq_some {o : Option Expr} {A l rhs : Expr} {eqn : Name} {u : Level} :
    o.bind eqSpine? = some (eqn, u, A, l, rhs) ↔
      o = some (.app (.app (.app (.const eqn [u]) A) l) rhs) := by
  cases o with
  | none => simp
  | some R => simpa using eqSpine?_eq_some

theorem bindM_ok {α β : Type} {x : CheckM α} {f : α → CheckM β} {b : β}
    (h : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases hx : x with
  | error e => rw [hx] at h; exact nomatch h
  | ok a => rw [hx] at h; exact ⟨a, rfl, h⟩

/-- **What a rule's match keeps**: a property of terms that holds of an application exactly when
it holds of both parts, and that a term's retry (`ruleRetry`) keeps, holds of the matched view and
of every binding of the slots where it holds of the term and of the bindings before. -/
structure MatchPres (r : CoreFns CheckM) (env : Env) (d : Nat) (Q : Expr → Prop) : Prop where
  app : ∀ {f a}, Q (.app f a) ↔ Q f ∧ Q a
  retry : ∀ {a w}, r.whnf d a = .ok w → Q a → Q (litToCtor env w)

/-- **The slot invariant** of a rule's match: every binding of the binder slots has `Q`. -/
@[expose] def SlotsP (Q : Expr → Prop) (st : List (Option Expr) × List (Option Level)) : Prop :=
  ∀ x, some x ∈ st.1 → Q x

theorem SlotsP.set {Q : Expr → Prop} {st : List (Option Expr) × List (Option Level)} {a : Expr}
    (h : SlotsP Q st) (ha : Q a) (i : Nat) : SlotsP Q (st.1.set i (some a), st.2) := by
  intro x hx
  rcases List.mem_or_eq_of_mem_set hx with hx | hx
  · exact h x hx
  · exact (Option.some.inj hx) ▸ ha

theorem SlotsP.lv {Q : Expr → Prop} {sl : List (Option Expr)} {lv lv' : List (Option Level)}
    (h : SlotsP Q (sl, lv)) : SlotsP Q (sl, lv') := h

theorem SlotsP.replicate (Q : Expr → Prop) (n : Nat) (lv : List (Option Level)) :
    SlotsP Q (List.replicate n none, lv) := by
  intro x hx
  exact nomatch (List.eq_of_mem_replicate hx)

theorem some_mem_of_getD_none {l : List (Option Expr)} {i : Nat} {x : Expr}
    (h : l.getD i none = some x) : some x ∈ l := by
  rw [List.getD_eq_getElem?_getD] at h
  cases hh : l[i]? with
  | none => rw [hh] at h; exact nomatch h
  | some y =>
    rw [hh] at h
    exact (show y = some x from h) ▸ List.mem_of_getElem? hh

theorem ruleSlot?_mem {n k : Nat} {sl : List (Option Expr)} {e' : Expr}
    (h : ruleSlot? n k sl = some (some e')) : some e' ∈ sl := by
  unfold ruleSlot? at h
  split at h
  · exact some_mem_of_getD_none (Option.some.inj h)
  · exact nomatch h

/-- **A variable position, read back**: a fresh binding of the argument, or a binding already in
the slots, syntactically or definitionally equal to the argument, the state unchanged. -/
theorem ruleBindVar_inv {r : CoreFns CheckM} {d n k : Nat}
    {st st' : List (Option Expr) × List (Option Level)} {a a₁ : Expr}
    (h : ruleBindVar r d n k st a = .ok (some (st', a₁))) :
    (st' = (st.1.set (n - 1 - k) (some a), st.2) ∧ a₁ = a) ∨
      (st' = st ∧ some a₁ ∈ st.1 ∧ (a₁ = a ∨ r.defeq d a₁ a = .ok true)) := by
  unfold ruleBindVar at h
  split at h
  · exact nomatch h
  · simp only [pure, Except.pure, Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
    exact Or.inl ⟨h.1.symm, h.2.symm⟩
  · rename_i e' hs
    have hmem : some e' ∈ st.1 := ruleSlot?_mem hs
    split at h
    · rename_i heq
      simp only [pure, Except.pure, Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact Or.inr ⟨rfl, hmem, Or.inl heq⟩
    · obtain ⟨b, hb, h⟩ := bindM_ok h
      cases b with
      | false => simp [pure, Except.pure] at h
      | true =>
        simp only [↓reduceIte, pure, Except.pure, Except.ok.injEq, Option.some.injEq,
          Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact Or.inr ⟨rfl, hmem, Or.inr hb⟩

/-- A variable position keeps the slot invariant, and its matched view has the property. -/
theorem ruleBindVar_pres {r : CoreFns CheckM} {d n k : Nat} {Q : Expr → Prop}
    {st st' : List (Option Expr) × List (Option Level)} {a a₁ : Expr}
    (hst : SlotsP Q st) (ha : Q a) (h : ruleBindVar r d n k st a = .ok (some (st', a₁))) :
    Q a₁ ∧ SlotsP Q st' := by
  rcases ruleBindVar_inv h with ⟨rfl, rfl⟩ | ⟨rfl, hmem, -⟩
  · exact ⟨ha, hst.set ha _⟩
  · exact ⟨hst _ hmem, hst⟩

theorem ruleArgStep_pres {r : CoreFns CheckM} {env : Env} {d n : Nat} {Q : Expr → Prop}
    (hQ : MatchPres r env d Q)
    {k : Expr → CheckM (Option ((List (Option Expr) × List (Option Level)) × Expr))}
    {p a a₁ : Expr} {st st' : List (Option Expr) × List (Option Level)}
    (hk : ∀ {x st' x₁}, Q x → k x = .ok (some (st', x₁)) → Q x₁ ∧ SlotsP Q st')
    (hst : SlotsP Q st) (ha : Q a)
    (h : ruleArgStep r env d n k p st a = .ok (some (st', a₁))) : Q a₁ ∧ SlotsP Q st' := by
  unfold ruleArgStep at h
  split at h
  · exact ruleBindVar_pres hst ha h
  · unfold ruleOrRetry at h
    obtain ⟨o, ho, h⟩ := bindM_ok h
    cases o with
    | some x =>
      simp only [pure, Except.pure, Except.ok.injEq] at h
      obtain rfl := Option.some.inj h; exact hk ha ho
    | none =>
      obtain ⟨a', ha', h⟩ := bindM_ok h
      unfold ruleRetry at ha'
      obtain ⟨w, hw, ha'⟩ := bindM_ok ha'
      simp only [pure, Except.pure, Except.ok.injEq] at ha'
      subst ha'
      exact hk (hQ.retry hw ha) h

theorem ruleMatchM_pres {r : CoreFns CheckM} {env : Env} {d n : Nat} {lps : List Name}
    {Q : Expr → Prop} (hQ : MatchPres r env d Q) :
    ∀ (pat : Expr) {st st' : List (Option Expr) × List (Option Level)} {e e₁ : Expr},
      SlotsP Q st → Q e →
      ruleMatchM r env d n lps pat st e = .ok (some (st', e₁)) → Q e₁ ∧ SlotsP Q st' := by
  intro pat
  induction pat with
  | app f p ihf ihp =>
    intro st st' e e₁ hst he h
    cases e with
    | app f' a =>
      obtain ⟨hf', ha⟩ := hQ.app.mp he
      simp only [ruleMatchM] at h
      obtain ⟨o, ho, h⟩ := bindM_ok h
      cases o with
      | none => simp [pure, Except.pure] at h
      | some sf =>
        obtain ⟨st₁, f₁⟩ := sf
        obtain ⟨hf₁, hst₁⟩ := ihf hst hf' ho
        obtain ⟨o', ho', h⟩ := bindM_ok h
        cases o' with
        | none => simp [pure, Except.pure] at h
        | some sa =>
          obtain ⟨st₂, a₁⟩ := sa
          simp only [pure, Except.pure, Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨ha₁, hst₂⟩ := ruleArgStep_pres hQ (fun hx h => ihp hst₁ hx h) hst₁ ha ho'
          exact ⟨hQ.app.mpr ⟨hf₁, ha₁⟩, hst₂⟩
    | _ => simp [ruleMatchM, pure, Except.pure] at h
  | const c ls =>
    intro st st' e e₁ hst he h
    obtain ⟨sl, lv⟩ := st
    cases e with
    | const c' ls' =>
      simp only [ruleMatchM, pure, Except.pure, Except.ok.injEq] at h
      split at h
      · obtain ⟨lv', -, h⟩ := Option.map_eq_some_iff.mp h
        simp only [Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨he, hst⟩
      · exact nomatch h
    | _ => simp [ruleMatchM, pure, Except.pure] at h
  | _ => intro st st' e e₁ _ _ h; simp [ruleMatchM, pure, Except.pure] at h

/-- The match's arguments and levels, with the matched view of the term. -/
theorem ruleArgsM_inv {r : CoreFns CheckM} {env : Env} {d : Nat} {cv : ConstantVal}
    {e e₁ : Expr} {args : List Expr} {us : List Level}
    (h : ruleArgsM r env d cv e = .ok (some (args, us, e₁))) :
    ∃ l₀ st', ruleMatchM r env d (ruleTele cv.type).1 cv.levelParams l₀
        (List.replicate (ruleTele cv.type).1 none,
          List.replicate cv.levelParams.length none) e = .ok (some (st', e₁)) := by
  unfold ruleArgsM at h
  split at h
  · obtain ⟨o, ho, h⟩ := bindM_ok h
    cases o with
    | none => simp [pure, Except.pure] at h
    | some x =>
      obtain ⟨⟨sl, lv⟩, e₁'⟩ := x
      dsimp only at h
      split at h
      · simp only [pure, Except.pure, Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, -, rfl⟩ := h
        exact ⟨_, _, ho⟩
      · simp [pure, Except.pure] at h
  · simp [pure, Except.pure] at h

theorem ruleArgsM_pres {r : CoreFns CheckM} {env : Env} {d : Nat} {cv : ConstantVal}
    {e e₁ : Expr} {args : List Expr} {us : List Level} {Q : Expr → Prop}
    (hQ : MatchPres r env d Q) (h : ruleArgsM r env d cv e = .ok (some (args, us, e₁)))
    (he : Q e) : Q e₁ := by
  obtain ⟨l₀, st', hm⟩ := ruleArgsM_inv h
  exact (ruleMatchM_pres hQ l₀ (SlotsP.replicate Q _ _) he hm).1

/-- **Inversion for a rule firing**: the firing's checks, read back, at the matched view `e₁`
of the term and the instance `l` of the left side. -/
theorem rewriteAttempt_inv {r : CoreFns CheckM} {env : Env} {d : Nat} {e e₂ : Expr} {t : Name}
    (h : rewriteAttempt r env d e t = .ok (some e₂)) :
    ∃ (cv : ConstantVal) (args : List Expr) (us : List Level) (u : Level) (A : Expr) (c : Name)
      (ls : List Level) (e₁ l : Expr),
      env.find? t = some (.thmInfo cv) ∧
      ruleArgsM r env d cv e = .ok (some (args, us, e₁)) ∧
      piResidual (cv.type.instantiateLevelParams cv.levelParams us) args
        = some (.app (.app (.app (.const eqName [u]) A) l) e₂) ∧
      e₁.getAppFn = .const c ls ∧ us.length = cv.levelParams.length ∧
      (∀ x ∈ args, x ∈ appSubterms e₁) ∧
      ruleCerts r env d e.getAppArgs (headTypeOf env.find? e)
        (cv.type.instantiateLevelParams cv.levelParams us) args = .ok true ∧
      e₁.levelFormEq l = true := by
  unfold rewriteAttempt rewriteFire at h
  split at h
  · rename_i cv hfind
    obtain ⟨o, ho, h⟩ := bindM_ok h
    cases o with
    | none => simp [pure, Except.pure] at h
    | some x =>
      obtain ⟨args, us, e₁⟩ := x
      dsimp only at h
      split at h
      · rename_i eqn u A l rhs hres
        rw [bind_eqSpine?_eq_some] at hres
        split at h
        · rename_i hchk
          obtain ⟨rfl, hlen, hle, hsub, hcst⟩ := hchk
          obtain ⟨c, ls, hhead⟩ : ∃ c ls, e₁.getAppFn = .const c ls := by
            revert hcst
            cases e₁.getAppFn <;> simp [Expr.isConstB]
          obtain ⟨b, hcert, h⟩ := bindM_ok h
          split at h
          · rename_i hb
            obtain rfl : rhs = e₂ := by simpa [pure, Except.pure] using h
            exact ⟨cv, args, us, u, A, c, ls, e₁, l, hfind, ho, hres, hhead, hlen, hsub,
              by rw [hcert, hb], hle⟩
          · simp [pure, Except.pure] at h
        · simp [pure, Except.pure] at h
      · simp [pure, Except.pure] at h
  · simp [pure, Except.pure] at h

/-- `levelFormEq` off the application and constant pairs is equality. -/
theorem Expr.levelFormEq_other {a b : Expr}
    (h1 : ∀ f x g y, a = .app f x → b = .app g y → False)
    (h2 : ∀ c ls c' ls', a = .const c ls → b = .const c' ls' → False) :
    a.levelFormEq b = decide (a = b) := by
  unfold Expr.levelFormEq
  split
  · exact (h1 _ _ _ _ rfl rfl).elim
  · exact (h2 _ _ _ _ rfl rfl).elim
  · rfl

/-- **Induction on `levelFormEq`**: a relation that is reflexive, closed under application and
relates constants of the same name at levels of the same official forms holds of every pair
`levelFormEq` accepts. -/
theorem Expr.levelFormEq_rec {P : Expr → Expr → Prop} (hrefl : ∀ e, P e e)
    (happ : ∀ f x g y, P f g → P x y → P (.app f x) (.app g y))
    (hconst : ∀ c ls ls', Level.formsEq ls ls' = true → P (.const c ls) (.const c ls')) :
    ∀ (a b : Expr), a.levelFormEq b = true → P a b := by
  have hother : ∀ {a b : Expr}, (∀ f x g y, a = .app f x → b = .app g y → False) →
      (∀ c ls c' ls', a = .const c ls → b = .const c' ls' → False) →
      a.levelFormEq b = true → P a b := by
    intro a b h1 h2 h
    rw [Expr.levelFormEq_other h1 h2, decide_eq_true_eq] at h
    subst h; exact hrefl _
  intro a
  induction a with
  | app f x ihf ihx =>
    intro b h
    cases b with
    | app g y =>
      simp only [Expr.levelFormEq, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
      rcases h with h | ⟨hf, hx⟩
      · rw [h]; exact hrefl _
      · exact happ _ _ _ _ (ihf g hf) (ihx y hx)
    | _ => exact hother (by simp) (by simp) h
  | const c ls =>
    intro b h
    cases b with
    | const c' ls' =>
      simp only [Expr.levelFormEq, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨rfl, h⟩ := h
      exact hconst _ _ _ h
    | _ => exact hother (by simp) (by simp) h
  | _ => intro b h; exact hother (by simp) (by simp) h

/-- **A property of a firing, carried to the firing at a prefix**: a relation that every rule's
firing at a term establishes, and that applying both sides to an argument keeps, holds of the
firing at the prefix of the rule's arity. -/
theorem rewriteAt_ind {r : CoreFns CheckM} {env : Env} {d : Nat} {t : Name}
    (P : Expr → Expr → Prop)
    (hat : ∀ {x y : Expr}, rewriteAttempt r env d x t = .ok (some y) → P x y)
    (happ : ∀ {f a f₂ : Expr}, P f f₂ → P (.app f a) (.app f₂ a)) :
    ∀ (e : Expr) {e₂ : Expr}, rewriteAt r env d t e = .ok (some e₂) → P e e₂
  | .app f a, e₂, h => by
    rw [rewriteAt] at h
    simp only [bind, Except.bind] at h
    split at h
    · exact nomatch h
    rename_i o ho
    cases o with
    | some x =>
      simp only [pure, Except.pure, Except.ok.injEq, Option.some.injEq] at h
      exact h ▸ hat ho
    | none =>
      dsimp only at h
      split at h
      · exact nomatch h
      rename_i o' ho'
      cases o' with
      | some f₂ =>
        simp only [pure, Except.pure, Except.ok.injEq, Option.some.injEq] at h
        subst h
        exact happ (rewriteAt_ind P hat happ f ho')
      | none => simp [pure, Except.pure] at h
  | .bvar _, _, h | .sort _, _, h | .const .., _, h | .fvar .., _, h | .forallE .., _, h
  | .lam .., _, h | .letE .., _, h | .lit _, _, h | .proj .., _, h => by
    rw [rewriteAt_nonApp _ _ _ _ (by intro _ _ hh; cases hh)] at h
    exact hat h

/-- **ι at a prefix keeps a property** that ι at a term establishes and that applying both sides
to an argument keeps. -/
theorem iotaAt_ind {r : CoreFns CheckM} {env : Env} {d : Nat}
    (P : Expr → Expr → Prop)
    (hat : ∀ {x y : Expr}, iotaRec mode r env d x = .ok (some y) → P x y)
    (happ : ∀ {f a f₂ : Expr}, P f f₂ → P (.app f a) (.app f₂ a)) :
    ∀ (e : Expr) {e₂ : Expr}, iotaAt mode r env d e = .ok (some e₂) → P e e₂
  | .app f a, e₂, h => by
    rw [iotaAt] at h
    simp only [bind, Except.bind] at h
    split at h
    · exact nomatch h
    rename_i o ho
    cases o with
    | some x =>
      simp only [pure, Except.pure, Except.ok.injEq, Option.some.injEq] at h
      exact h ▸ hat ho
    | none =>
      dsimp only at h
      split at h
      · exact nomatch h
      rename_i o' ho'
      cases o' with
      | some f₂ =>
        simp only [pure, Except.pure, Except.ok.injEq, Option.some.injEq] at h
        subst h
        exact happ (iotaAt_ind P hat happ f ho')
      | none => simp [pure, Except.pure] at h
  | .bvar _, _, h | .sort _, _, h | .const .., _, h | .fvar .., _, h | .forallE .., _, h
  | .lam .., _, h | .letE .., _, h | .lit _, _, h | .proj .., _, h => by
    rw [iotaAt_nonApp _ _ _ (by intro _ _ hh; cases hh)] at h
    exact hat h

/-- **The rules fired again keep a property** that every firing keeps. -/
theorem fireMore_ind {r : CoreFns CheckM} {env : Env} {d : Nat} (Q : Expr → Expr → Prop)
    (hrefl : ∀ x, Q x x)
    (hstep : ∀ {x y z : Expr} {t : Name}, rewriteStep r env d false x = .ok (some (t, y)) →
      Q y z → Q x z) :
    ∀ {k : Nat} {e e' : Expr}, fireMore r env d k e = .ok e' → Q e e'
  | 0, e, e', h => by
    simp only [fireMore, pure, Except.pure, Except.ok.injEq] at h
    exact h ▸ hrefl e
  | k + 1, e, e', h => by
    simp only [fireMore, bind, Except.bind] at h
    split at h
    · exact nomatch h
    rename_i o ho
    cases o with
    | some te =>
      obtain ⟨t, y⟩ := te
      exact hstep ho (fireMore_ind Q hrefl hstep h)
    | none =>
      simp only [pure, Except.pure, Except.ok.injEq] at h
      exact h ▸ hrefl e

/-- **The rules fired again keep a unary property** that every firing keeps. -/
theorem fireMore_pres {r : CoreFns CheckM} {env : Env} {d : Nat} (Q : Expr → Prop)
    (hstep : ∀ {x y : Expr} {t : Name}, rewriteStep r env d false x = .ok (some (t, y)) →
      Q x → Q y) {k : Nat} {e e' : Expr} (h : fireMore r env d k e = .ok e') (hq : Q e) : Q e' :=
  fireMore_ind (fun x y => Q x → Q y) (fun _ h => h) (fun hr hyz hx => hyz (hstep hr hx)) h hq

/-- Inversion for the rules in order: a firing is one of the rules', the first. -/
theorem rewriteRules_inv {r : CoreFns CheckM} {env : Env} {d : Nat} {e e₂ : Expr} {t : Name} :
    ∀ {ts : List Name}, rewriteRules r env d e ts = .ok (some (t, e₂)) →
      t ∈ ts ∧ rewriteAt r env d t e = .ok (some e₂)
  | [], h => by simp [rewriteRules, pure, Except.pure] at h
  | t' :: ts, h => by
    unfold rewriteRules at h
    simp only [bind, Except.bind] at h
    split at h
    · exact nomatch h
    rename_i o ho
    cases o with
    | some e' =>
      simp only [pure, Except.pure, Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨List.mem_cons_self, ho⟩
    | none =>
      obtain ⟨hm, ha⟩ := rewriteRules_inv h
      exact ⟨List.mem_cons_of_mem _ hm, ha⟩

/-- Inversion for the rewrite step. -/
theorem rewriteStep_inv {r : CoreFns CheckM} {env : Env} {d : Nat} {stuck : Bool} {e e₂ : Expr}
    {t : Name} (h : rewriteStep r env d stuck e = .ok (some (t, e₂))) :
    rewriteAt r env d t e = .ok (some e₂) := by
  unfold rewriteStep at h
  split at h
  · split at h
    · simp [pure, Except.pure] at h
    · exact (rewriteRules_inv h).2
  · simp [pure, Except.pure] at h

/-- A firing rule is one in force at the term's head constant. -/
theorem rewriteStep_mem {r : CoreFns CheckM} {env : Env} {d : Nat} {stuck : Bool} {e e₂ : Expr}
    {t : Name} (h : rewriteStep r env d stuck e = .ok (some (t, e₂))) :
    ∃ c ls, e.getAppFn = .const c ls ∧ t ∈ env.rulesFor c := by
  unfold rewriteStep at h
  split at h
  · rename_i c ls hc
    split at h
    · simp [pure, Except.pure] at h
    · exact ⟨c, ls, hc, (rewriteRules_inv h).1⟩
  · simp [pure, Except.pure] at h

/-! ### The test before unfolding (`preFire`)

A firing of a marked rule at `e` matches the term `e'` that is `e`'s spine with its key arguments
replaced (`keyScan`).  Each replaced argument is reached from the original one by `whnf` and the
`Nat` literal reading of a key (`KeyArg`), and the firing at a prefix applies the reduct to the
remaining arguments of `e` (`preAt_ind`). -/

/-- **A key argument and what the key tests made of it**: a chain of `whnf` steps and `Nat`
literal readings (`keyLit`). -/
inductive KeyArg (r : CoreFns CheckM) (env : Env) (d : Nat) : Expr → Expr → Prop where
  | refl (a : Expr) : KeyArg r env d a a
  | lit {a b : Expr} (kc : Name) : KeyArg r env d a b → KeyArg r env d a (keyLit (natLitStored env) kc b)
  | whnf {a b w : Expr} : KeyArg r env d a b → r.whnf d b = .ok w → KeyArg r env d a w

theorem KeyArg.trans {r : CoreFns CheckM} {env : Env} {d : Nat} {a b c : Expr}
    (h₁ : KeyArg r env d a b) (h₂ : KeyArg r env d b c) : KeyArg r env d a c := by
  induction h₂ with
  | refl => exact h₁
  | lit kc _ ih => exact .lit kc ih
  | whnf _ hw ih => exact .whnf ih hw

/-- A property kept by `whnf` and by the literal reading is kept along a key argument's chain. -/
theorem KeyArg.pres {r : CoreFns CheckM} {env : Env} {d : Nat} (P : Expr → Prop)
    (hwh : ∀ {a w : Expr}, r.whnf d a = .ok w → P a → P w)
    (hlit : ∀ (kc : Name) {a : Expr}, P a → P (keyLit (natLitStored env) kc a))
    {a b : Expr} (h : KeyArg r env d a b) (ha : P a) : P b := by
  induction h with
  | refl => exact ha
  | lit kc _ ih => exact hlit kc ih
  | whnf _ hw ih => exact hwh hw ih

/-- **Arguments and what the key tests made of them**, position by position. -/
@[expose] def KeyArgs (r : CoreFns CheckM) (env : Env) (d : Nat) (args args' : List Expr) : Prop :=
  args'.length = args.length ∧
    ∀ (i : Nat) (h : i < args.length) (h' : i < args'.length), KeyArg r env d args[i] args'[i]

theorem KeyArgs.refl {r : CoreFns CheckM} {env : Env} {d : Nat} (args : List Expr) :
    KeyArgs r env d args args :=
  ⟨rfl, fun _ _ _ => .refl _⟩

theorem KeyArgs.trans {r : CoreFns CheckM} {env : Env} {d : Nat} {a b c : List Expr}
    (h₁ : KeyArgs r env d a b) (h₂ : KeyArgs r env d b c) : KeyArgs r env d a c :=
  ⟨h₂.1.trans h₁.1, fun i hi hi' =>
    (h₁.2 i hi (by rw [h₁.1]; exact hi)).trans (h₂.2 i (by rw [h₁.1]; exact hi) hi')⟩

/-- Replacing one argument by a key argument of it. -/
theorem KeyArgs.set {r : CoreFns CheckM} {env : Env} {d : Nat} {args : List Expr} {p : Nat}
    {a x : Expr} (hp : args[p]? = some a) (hx : KeyArg r env d a x) :
    KeyArgs r env d args (args.set p x) := by
  refine ⟨List.length_set, fun i hi hi' => ?_⟩
  rw [List.getElem_set]
  split
  · subst_vars
    rw [List.getElem?_eq_getElem hi, Option.some.injEq] at hp
    exact hp ▸ hx
  · exact .refl _

/-- One key test reaches its arguments by key steps. -/
theorem keyTest_keyArgs {r : CoreFns CheckM} {env : Env} {d : Nat} {key : Option (Nat × Name)}
    {args args' : List Expr} {b : Bool} (h : keyTest r env d key args = .ok (b, args')) :
    KeyArgs r env d args args' := by
  unfold keyTest at h
  split at h
  · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    exact h.2 ▸ KeyArgs.refl _
  · rename_i p kc
    split at h
    · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      exact h.2 ▸ KeyArgs.refl _
    · rename_i a ha
      dsimp only at h
      split at h
      · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        exact h.2 ▸ KeyArgs.set ha (.lit kc (.refl _))
      · split at h
        · obtain ⟨w, hw, h⟩ := bindM_ok h
          simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
          exact h.2 ▸ KeyArgs.set ha (.lit kc (.whnf (.lit kc (.refl _)) hw))
        · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
          exact h.2 ▸ KeyArgs.set ha (.lit kc (.refl _))

/-- The key tests in order reach their arguments by key steps. -/
theorem keyScan_keyArgs {r : CoreFns CheckM} {env : Env} {d : Nat} :
    ∀ {ks : List (Option (Nat × Name))} {args args' : List Expr} {cs : List (Option (Nat × Name))},
      keyScan r env d ks args = .ok (cs, args') → KeyArgs r env d args args'
  | [], args, args', cs, h => by
    simp only [keyScan, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    exact h.2 ▸ KeyArgs.refl _
  | k :: ks, args, args', cs, h => by
    unfold keyScan at h
    obtain ⟨⟨b, args₁⟩, h₁, h⟩ := bindM_ok h
    obtain ⟨⟨cs', args₂⟩, h₂, h⟩ := bindM_ok h
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    exact h.2 ▸ (keyTest_keyArgs h₁).trans (keyScan_keyArgs h₂)

/-- Inversion for the marked rules in order: a firing is one of the rules', the first. -/
theorem preRules_inv {r : CoreFns CheckM} {env : Env} {d : Nat} {e e' e₂ : Expr} {t : Name} :
    ∀ {ts : List Name}, preRules r env d e e' ts = .ok (some (t, e₂)) →
      t ∈ ts ∧ preAt r env d t e e' = .ok (some e₂)
  | [], h => by simp [preRules, pure, Except.pure] at h
  | t' :: ts, h => by
    unfold preRules at h
    simp only [bind, Except.bind] at h
    split at h
    · exact nomatch h
    rename_i o ho
    cases o with
    | some x =>
      simp only [pure, Except.pure, Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨List.mem_cons_self, ho⟩
    | none =>
      obtain ⟨hm, ha⟩ := preRules_inv h
      exact ⟨List.mem_cons_of_mem _ hm, ha⟩

/-- **Inversion for the test before unfolding**: the term's head is a constant with the firing
rule in force (`preRulesFor` keeps only rules of `Env.rulesFor`), and the rule fired at the prefix
of its arity of the spine with its key arguments replaced. -/
theorem preFire_inv {r : CoreFns CheckM} {env : Env} {d : Nat} {e e₂ : Expr} {t : Name}
    (h : preFire r env d e = .ok (some (t, e₂))) :
    ∃ c us args', e.getAppFn = .const c us ∧ t ∈ env.rulesFor c ∧
      KeyArgs r env d e.getAppArgs args' ∧
      preAt r env d t e (Expr.mkAppN (.const c us) args') = .ok (some e₂) := by
  unfold preFire at h
  split at h
  · rename_i c us hc
    split at h
    · split at h
      · simp [pure, Except.pure] at h
      · rename_i ts hts
        obtain ⟨⟨cs, args'⟩, hks, h⟩ := bindM_ok h
        obtain ⟨hmem, hat⟩ := preRules_inv h
        refine ⟨c, us, args', hc, ?_, keyScan_keyArgs hks, hat⟩
        obtain ⟨⟨t', k⟩, hz, hk⟩ := List.mem_filterMap.mp hmem
        have htt : t' = t := by
          dsimp only at hk
          split at hk
          · exact Option.some.inj hk
          · exact nomatch hk
        subst htt
        have ht : t' ∈ preRulesFor env.rulesFor c := (List.of_mem_zip hz).1
        unfold preRulesFor at ht
        exact List.contains_iff_mem.mp (List.mem_filter.mp ht).2
    · simp [pure, Except.pure] at h
  · simp [pure, Except.pure] at h

/-- **A property of a firing before unfolding, carried to the firing at a prefix**: a relation
among the term, the term with its key arguments replaced and the reduct, which every rule's firing
at the replaced term establishes, and which applying the terms to an argument keeps (the reduct
takes the original argument). -/
theorem preAt_ind {r : CoreFns CheckM} {env : Env} {d : Nat} {t : Name}
    (P : Expr → Expr → Expr → Prop)
    (hat : ∀ {x x' y : Expr}, preAttempt r env d x x' t = .ok (some y) → P x x' y)
    (happ : ∀ {f a f' a' f₂ : Expr}, P f f' f₂ → P (.app f a) (.app f' a') (.app f₂ a)) :
    ∀ (e e' : Expr) {e₂ : Expr}, preAt r env d t e e' = .ok (some e₂) → P e e' e₂ := by
  intro e
  induction e with
  | app f a ihf _ =>
    intro e' e₂ h
    cases e' with
    | app f' a' =>
      rw [preAt] at h
      simp only [bind, Except.bind] at h
      split at h
      · exact nomatch h
      rename_i o ho
      cases o with
      | some x =>
        simp only [pure, Except.pure, Except.ok.injEq, Option.some.injEq] at h
        exact h ▸ hat ho
      | none =>
        dsimp only at h
        split at h
        · exact nomatch h
        rename_i o' ho'
        cases o' with
        | some f₂ =>
          simp only [pure, Except.pure, Except.ok.injEq, Option.some.injEq] at h
          subst h
          exact happ (ihf f' ho')
        | none => simp [pure, Except.pure] at h
    | _ =>
      rw [preAt_nonApp _ _ _ _ (by intro _ _ _ _ hh; cases hh.2)] at h
      exact hat h
  | _ =>
    intro e' e₂ h
    rw [preAt_nonApp _ _ _ _ (by intro _ _ _ _ hh; cases hh.1)] at h
    exact hat h

/-- **Inversion for a rule's firing checks** (`rewriteFire`): read back at the view `e₁`. -/
theorem rewriteFire_inv {r : CoreFns CheckM} {env : Env} {d : Nat} {e : Expr} {cv : ConstantVal}
    {args : List Expr} {us : List Level} {e₁ e₂ : Expr}
    (h : rewriteFire r env d e cv args us e₁ = .ok (some e₂)) :
    ∃ (u : Level) (A : Expr) (c : Name) (ls : List Level) (l : Expr),
      piResidual (cv.type.instantiateLevelParams cv.levelParams us) args
        = some (.app (.app (.app (.const eqName [u]) A) l) e₂) ∧
      e₁.getAppFn = .const c ls ∧ us.length = cv.levelParams.length ∧
      (∀ x ∈ args, x ∈ appSubterms e₁) ∧
      ruleCerts r env d e.getAppArgs (headTypeOf env.find? e)
        (cv.type.instantiateLevelParams cv.levelParams us) args = .ok true ∧
      e₁.levelFormEq l = true := by
  unfold rewriteFire at h
  split at h
  · rename_i eqn u A l rhs hres
    rw [bind_eqSpine?_eq_some] at hres
    split at h
    · rename_i hchk
      obtain ⟨rfl, hlen, hle, hsub, hcst⟩ := hchk
      obtain ⟨c, ls, hhead⟩ : ∃ c ls, e₁.getAppFn = .const c ls := by
        revert hcst
        cases e₁.getAppFn <;> simp [Expr.isConstB]
      obtain ⟨b, hcert, h⟩ := bindM_ok h
      split at h
      · rename_i hb
        obtain rfl : rhs = e₂ := by simpa [pure, Except.pure] using h
        exact ⟨u, A, c, ls, l, hres, hhead, hlen, hsub, by rw [hcert, hb], hle⟩
      · simp [pure, Except.pure] at h
    · simp [pure, Except.pure] at h
  · simp [pure, Except.pure] at h

/-- **Inversion for a marked rule's firing at the replaced term**. -/
theorem preAttempt_inv {r : CoreFns CheckM} {env : Env} {d : Nat} {e e' e₂ : Expr} {t : Name}
    (h : preAttempt r env d e e' t = .ok (some e₂)) :
    ∃ (cv : ConstantVal) (args : List Expr) (us : List Level),
      env.find? t = some (.thmInfo cv) ∧ ruleArgsSyn cv e' = some (args, us) ∧
      rewriteFire r env d e cv args us e' = .ok (some e₂) := by
  unfold preAttempt at h
  split at h
  · rename_i cv hf
    split at h
    · rename_i args us hm
      exact ⟨cv, args, us, hf, hm, h⟩
    · simp [pure, Except.pure] at h
  · simp [pure, Except.pure] at h

/-- `keyLit` is the identity or the `Nat` literal's constructor form (`litToCtorIfNat`). -/
theorem keyLit_cases (env : Env) (kc : Name) (a : Expr) :
    keyLit (natLitStored env) kc a = a ∨ keyLit (natLitStored env) kc a = litToCtorIfNat env a := by
  unfold keyLit
  split
  · right
    cases a <;> try rfl
    rename_i l
    cases l <;> rfl
  · left; rfl

/-- Inversion for ι-then-rules: the ι step fired, or it did not and a rule did. -/
theorem iotaThenRule_inv {r : CoreFns CheckM} {env : Env} {d : Nat} {e e'' : Expr}
    (h : iotaThenRule mode r env d e = .ok (some e'')) :
    iotaAt mode r env d e = .ok (some e'') ∨
      (iotaAt mode r env d e = .ok none ∧
        ∃ t e₂, rewriteStep r env d false e = .ok (some (t, e₂)) ∧
          fireMore r env d ruleFireBudget e₂ = .ok e'') := by
  unfold iotaThenRule at h
  simp only [bind, Except.bind] at h
  split at h
  · exact nomatch h
  rename_i o ho
  cases o with
  | some e₁ =>
    simp only [pure, Except.pure, Except.ok.injEq, Option.some.injEq] at h
    exact .inl (h ▸ ho)
  | none =>
    dsimp only at h
    split at h
    · exact nomatch h
    rename_i ro hro
    cases ro with
    | some te =>
      dsimp only at h
      split at h
      · exact nomatch h
      rename_i e₃ he₃
      simp only [pure, Except.pure, Except.ok.injEq, Option.some.injEq] at h
      exact .inr ⟨ho, te.1, te.2, hro, h ▸ he₃⟩
    | none => simp [pure, Except.pure] at h

/-- Inversion for `whnfCore` on a constant: a rule whose left side is the bare constant fired,
or the constant is its own head normal form. -/
theorem whnfCore_const_inv {env : Env} {fuel d : Nat} {n : Name} {us : List Level} {e' : Expr}
    {c : Bool} (h : whnfCore mode eager env (fuel + 1) d (.const n us) c = .ok e') :
    (∃ t e₂ e₃, rewriteStep (pureFns mode eager env fuel) env d false (.const n us) =
          .ok (some (t, e₂)) ∧
        fireMore (pureFns mode eager env fuel) env d ruleFireBudget e₂ = .ok e₃ ∧
        whnfCore mode eager env fuel d e₃ c = .ok e') ∨
      (rewriteStep (pureFns mode eager env fuel) env d false (.const n us) = .ok none ∧
        e' = .const n us) := by
  rw [whnfCore_succ] at h
  simp only [whnfCoreBody, Bind.bind, Except.bind] at h
  split at h
  · exact nomatch h
  rename_i ro hro
  cases ro with
  | some te =>
    dsimp only at h
    split at h
    · exact nomatch h
    rename_i e₃ he₃
    exact .inl ⟨te.1, te.2, e₃, hro, he₃, h⟩
  | none =>
    simp only [pure, Except.pure, Except.ok.injEq] at h
    exact .inr ⟨hro, h.symm⟩

/-- Inversion for one iteration of the reduction loop
(`whnfStep`): head-normalize, then either the literal acceleration
(whose literal is final, any other reduct goes on) or one definition
unfolding hands the reduct to the loop's continuation `k`, or the head
normal form is final.  Task #106: the loop steps are
iteration on `whnfLoop`'s own budget, so this is stated about the
continuation-parameterized body; `whnfLoop … (n+1)` *is*
`whnfStep … (whnfLoop … n)`, so consumers apply it after `cases` on
the budget and use the budget induction hypothesis for `k`. -/
theorem whnfStep_inv {env : Env} {fuel d : Nat} {k : Option Expr → Expr → CheckM Expr}
    {o : Option Expr} {e e' : Expr}
    (h : whnfStep (pureFns mode eager env fuel) env d k o e = .ok e') :
    ∃ e₁, whnfCore mode eager env fuel d e = .ok e₁ ∧
      ((∃ e₂, reduceNatFueled mode eager env fuel d e₁ = .ok (some e₂) ∧
          ((e₂.isLit = true ∧ e' = e₂) ∨ k o e₂ = .ok e')) ∨
       (reduceNatFueled mode eager env fuel d e₁ = .ok none ∧
        ∃ e₂, unfoldDefinition env e₁ = some e₂ ∧
          k (noteOrigin env o e₁) e₂ = .ok e') ∨
       (reduceNatFueled mode eager env fuel d e₁ = .ok none ∧
        unfoldDefinition env e₁ = none ∧
        ((originFire (pureFns mode eager env fuel) env d o e₁ = .ok none ∧ e' = e₁) ∨
         ∃ t e₂, originFire (pureFns mode eager env fuel) env d o e₁ = .ok (some (t, e₂)) ∧
           k none e₂ = .ok e')) ∨
       (reduceNatFueled mode eager env fuel d e₁ = .ok none ∧
        ∃ t e₂, preFire (pureFns mode eager env fuel) env d e₁ = .ok (some (t, e₂)) ∧
          k o e₂ = .ok e')) := by
  simp only [whnfStep, whnfFix, Bind.bind, Except.bind] at h
  simp only [whnfCore_def] at h
  cases hwc : whnfCore mode eager env fuel d e with
  | error err => rw [hwc] at h; exact nomatch h
  | ok e₁ =>
  rw [hwc] at h
  dsimp only at h
  simp only [reduceNat_fold] at h
  cases hrn : reduceNatFueled mode eager env fuel d e₁ with
  | error err => rw [hrn] at h; exact nomatch h
  | ok o =>
  rw [hrn] at h
  dsimp only at h
  cases o with
  | some e₂ =>
    refine ⟨e₁, rfl, Or.inl ⟨e₂, hrn, ?_⟩⟩
    dsimp only at h
    by_cases hl : e₂.isLit = true
    · rw [ite_eq_left hl] at h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      exact Or.inl ⟨hl, h.symm⟩
    · rw [ite_eq_right hl] at h
      exact Or.inr h
  | none =>
  dsimp only at h
  cases hpf : preFire (pureFns mode eager env fuel) env d e₁ with
  | error err => rw [hpf] at h; exact nomatch h
  | ok po =>
  rw [hpf] at h
  dsimp only at h
  cases po with
  | some te =>
    obtain ⟨t, e₂⟩ := te
    exact ⟨e₁, rfl, Or.inr (Or.inr (Or.inr ⟨hrn, t, e₂, hpf, h⟩))⟩
  | none =>
  dsimp only at h
  cases hu : unfoldDefinition env e₁ with
  | some e₂ =>
    rw [hu] at h
    dsimp only at h
    exact ⟨e₁, rfl, Or.inr (Or.inl ⟨hrn, e₂, hu, h⟩)⟩
  | none =>
    rw [hu] at h
    dsimp only at h
    cases hof : originFire (pureFns mode eager env fuel) env d o e₁ with
    | error err => rw [hof] at h; exact nomatch h
    | ok ro =>
    rw [hof] at h
    cases ro with
    | none =>
      simp only [pure, Except.pure, Except.ok.injEq] at h
      exact ⟨e₁, rfl, Or.inr (Or.inr (Or.inl ⟨hrn, hu, Or.inl ⟨hof, h.symm⟩⟩))⟩
    | some te =>
      obtain ⟨t, e₂⟩ := te
      exact ⟨e₁, rfl, Or.inr (Or.inr (Or.inl ⟨hrn, hu, Or.inr ⟨t, e₂, hof, h⟩⟩))⟩

/-- Inversion for the rules at an origin: the origin is set, the term is stuck, and the rewrite
step fired at the origin (with `stuck`). -/
theorem originFire_inv {r : CoreFns CheckM} {env : Env} {d : Nat} {o : Option Expr}
    {e e₂ : Expr} {t : Name} (h : originFire r env d o e = .ok (some (t, e₂))) :
    ∃ o' e₁, o = some o' ∧ isStuckResult env e = true ∧
      rewriteStep r env d true o' = .ok (some (t, e₁)) ∧
      fireMore r env d ruleFireBudget e₁ = .ok e₂ := by
  unfold originFire at h
  split at h
  · rename_i o'
    split at h
    · rename_i hs
      simp only [bind, Except.bind] at h
      split at h
      · exact nomatch h
      rename_i ro hro
      cases ro with
      | some te =>
        dsimp only at h
        split at h
        · exact nomatch h
        rename_i e₃ he₃
        simp only [pure, Except.pure, Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨o', te.2, rfl, hs, hro, he₃⟩
      | none => simp [pure, Except.pure] at h
    · simp [pure, Except.pure] at h
  · simp [pure, Except.pure] at h

/-- Inversion for the λ-rule of `inferTypeCore` (infer-only: the
domain is reused whole).  The last conjunct is the **codomain
sort** (task #152), delivered at the verified modes only, in the
shape the checker computes it (infer, then whnf to a sort).  At
`.trusted`, which does not run the check, it is vacuous. -/
theorem inferTypeCore_lam_inv {env : Env} {fuel d : Nat}
    {ty body t : Expr}
    (h : inferTypeCore mode eager env (fuel + 1) d (.lam ty body) = .ok t) :
    ∃ tty u bt,
      inferTypeCore mode eager env fuel d ty = .ok tty ∧
      whnf mode eager env fuel d tty = .ok (.sort u) ∧
      inferTypeCore mode eager env fuel (d + 1)
        (body.instantiate1 (.fvar d ty)) = .ok bt ∧
      t = .forallE ty (bt.abstract1 d) := by
  rw [inferTypeCore_succ] at h
  simp only [inferBody, pure, Except.pure, Bind.bind, Except.bind] at h
  simp only [infer_def, whnf_def] at h
  cases htty : inferTypeCore mode eager env fuel d ty with
  | error err => rw [htty] at h; exact nomatch h
  | ok tty =>
  rw [htty] at h
  dsimp only at h
  cases hwtty : whnf mode eager env fuel d tty with
  | error err => rw [hwtty] at h; exact nomatch h
  | ok wtty =>
  rw [hwtty] at h
  dsimp only at h
  revert h
  match wtty with
  | .sort u => ?_
  | .bvar _ | .fvar _ _ | .const _ _ | .app _ _ | .lam _ _
  | .forallE _ _ | .letE _ _ _ | .lit _ | .proj _ _ _ =>
    intro h; simp [throw, throwThe, MonadExceptOf.throw] at h
  intro h
  dsimp only at h
  cases hbt : inferTypeCore mode eager env fuel (d + 1)
      (body.instantiate1 (.fvar d ty)) with
  | error err => rw [hbt] at h; exact nomatch h
  | ok bt =>
  rw [hbt] at h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  exact ⟨tty, u, bt, rfl, hwtty, rfl, h.symm⟩

/-- Inversion for the application rule of `inferTypeCore` (task #100
de-gating: the per-argument re-check runs unconditionally — the former
possibly-Prop gate of task #49 is unsound-to-model under the
domain-relative collapse). -/
theorem inferTypeCore_app_inv {env : Env} {fuel d : Nat} {f a t : Expr}
    (h : inferTypeCore mode eager env (fuel + 1) d (.app f a) = .ok t) :
    ∃ tf ty' body', inferTypeCore mode eager env fuel d f = .ok tf ∧
      whnf mode eager env fuel d tf = .ok (.forallE ty' body') ∧
      t = body'.instantiate1 a ∧
      ∃ ta, inferTypeCore mode eager env fuel d a = .ok ta ∧
        isDefEqCore mode (argEager eager a) env fuel d ta ty' = .ok true := by
  rw [inferTypeCore_succ] at h
  simp only [inferBody, pure, Except.pure, Bind.bind, Except.bind] at h
  simp only [infer_def, whnf_def, defeqArg_def] at h
  cases htf : inferTypeCore mode eager env fuel d f with
  | error err => rw [htf] at h; exact nomatch h
  | ok tf =>
  rw [htf] at h
  dsimp only at h
  cases hw : whnf mode eager env fuel d tf with
  | error err => rw [hw] at h; exact nomatch h
  | ok w =>
  rw [hw] at h
  dsimp only at h
  match w, h with
  | .forallE ty' body', h => ?_
  | .sort u, h => exact nomatch h
  | .fvar i t2, h => exact nomatch h
  | .const n2 us, h => exact nomatch h
  | .lam t2 b2, h => exact nomatch h
  | .bvar i, h => exact nomatch h
  | .app f2 a2, h => exact nomatch h
  | .letE t2 v2 b2, h => exact nomatch h
  | .lit l2, h => exact nomatch h
  | .proj s2 i2 e2, h => exact nomatch h
  dsimp only at h
  cases hta : inferTypeCore mode eager env fuel d a with
  | error err => rw [hta] at h; exact nomatch h
  | ok ta =>
  rw [hta] at h
  dsimp only at h
  cases hde : isDefEqCore mode (argEager eager a) env fuel d ta ty' with
  | error err => rw [hde] at h; exact nomatch h
  | ok r =>
  rw [hde] at h
  cases r with
  | false => simp [throw, throwThe, MonadExceptOf.throw] at h
  | true =>
    simp only [ite_true, pure, Except.pure, Except.ok.injEq] at h
    exact ⟨tf, ty', body', rfl, hw, h.symm, ta, rfl, hde⟩

/-- Inversion for the ∀-rule of `inferTypeCore` (task #100 stage 6:
the codomain sort is inferred from the opened body). -/
theorem inferTypeCore_forall_inv {env : Env} {fuel d : Nat}
    {ty body t : Expr}
    (h : inferTypeCore mode eager env (fuel + 1) d (.forallE ty body) = .ok t) :
    ∃ tty u bt v, inferTypeCore mode eager env fuel d ty = .ok tty ∧
      whnf mode eager env fuel d tty = .ok (.sort u) ∧
      inferTypeCore mode eager env fuel (d + 1)
        (body.instantiate1 (.fvar d ty)) = .ok bt ∧
      ensureSortCore mode eager env fuel (d + 1) bt = .ok v ∧
      t = .sort (.imax u v) := by
  rw [inferTypeCore_succ] at h
  simp only [inferBody, pure, Except.pure, Bind.bind, Except.bind] at h
  simp only [infer_def, whnf_def, ensureSort_def] at h
  try dsimp only at h
  cases hty : inferTypeCore mode eager env fuel d ty with
  | error err => rw [hty] at h; exact nomatch h
  | ok tty =>
  rw [hty] at h
  dsimp only at h
  cases hwt : whnf mode eager env fuel d tty with
  | error err => rw [hwt] at h; exact nomatch h
  | ok w =>
  rw [hwt] at h
  dsimp only at h
  revert h
  match w with
  | .sort u => ?_
  | .bvar _ | .fvar _ _ | .const _ _ | .app _ _ | .lam _ _
  | .forallE _ _ | .letE _ _ _ | .lit _ | .proj _ _ _ =>
    intro h; simp [throw, throwThe, MonadExceptOf.throw] at h
  intro h
  dsimp only at h
  cases hbt : inferTypeCore mode eager env fuel (d + 1)
      (body.instantiate1 (.fvar d ty)) with
  | error err => rw [hbt] at h; exact nomatch h
  | ok bt =>
  rw [hbt] at h
  dsimp only at h
  cases hes : ensureSortCore mode eager env fuel (d + 1) bt with
  | error err => rw [hes] at h; exact nomatch h
  | ok v =>
  rw [hes] at h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  exact ⟨tty, u, bt, v, rfl, hwt, rfl, hes, h.symm⟩

/-- Inversion for `ensureSortCore`: the subject whnfs to the sort. -/
theorem ensureSortCore_inv {env : Env} {fuel d : Nat} {t : Expr} {u : Level}
    (h : ensureSortCore mode eager env fuel d t = .ok u) :
    whnf mode eager env fuel d t = .ok (.sort u) := by
  unfold ensureSortCore ensureSort at h
  simp only [Bind.bind, Except.bind, whnf_def] at h
  cases hw : whnf mode eager env fuel d t with
  | error err => rw [hw] at h; exact nomatch h
  | ok w =>
  rw [hw] at h
  revert h
  match w with
  | .sort u' => ?_
  | .bvar _ | .fvar _ _ | .const _ _ | .app _ _ | .lam _ _
  | .forallE _ _ | .letE _ _ _ | .lit _ | .proj _ _ _ =>
    intro h; simp [throw, throwThe, MonadExceptOf.throw] at h
  intro h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  rw [h]

/-- The spine head of a well-scoped expression is well-scoped. -/
theorem Expr.WScoped.getAppFn {d : Nat} :
    ∀ {e : Expr}, WScoped d e → WScoped d e.getAppFn := by
  intro e
  induction e with
  | app f a ihf _ =>
    intro h
    have hfa : WScoped d f ∧ WScoped d a := by
      simpa only [WScoped] using h
    exact ihf hfa.1
  | _ => intro h; exact h

/-- Inversion for the `let` rule of `inferTypeCore` (official
`infer_let`): the type's type is a sort, the value's full-grade type is
definitionally the type, and the result is the body's type at the
value. -/
theorem inferTypeCore_letE_inv {env : Env} {fuel d : Nat}
    {ty v b t : Expr}
    (h : inferTypeCore mode eager env (fuel + 1) d (.letE ty v b) = .ok t) :
    ∃ tty u tv, inferTypeCore mode eager env fuel d ty = .ok tty ∧
      ensureSortCore mode eager env fuel d tty = .ok u ∧
      inferTypeCore mode eager env fuel d v = .ok tv ∧
      isDefEqCore mode eager env fuel d tv ty = .ok true ∧
      inferTypeCore mode eager env fuel d (b.instantiate1 v) = .ok t := by
  rw [inferTypeCore_succ] at h
  simp only [inferBody, Bind.bind, Except.bind] at h
  simp only [infer_def, ensureSort_def, defeq_def] at h
  cases hty : inferTypeCore mode eager env fuel d ty with
  | error err => simp [hty] at h
  | ok tty =>
  cases hes : ensureSortCore mode eager env fuel d tty with
  | error err => simp [hty, hes] at h
  | ok u =>
  cases hv : inferTypeCore mode eager env fuel d v with
  | error err => simp [hty, hes, hv] at h
  | ok tv =>
  cases hde : isDefEqCore mode eager env fuel d tv ty with
  | error err => simp [hty, hes, hv, hde] at h
  | ok r =>
  cases r with
  | false => simp [hty, hes, hv, hde, throw, throwThe, MonadExceptOf.throw] at h
  | true =>
    simp only [hty, hes, hv, hde] at h
    exact ⟨tty, u, tv, rfl, hes, rfl, hde, h⟩

/-- The ζ arm of `whnfCore`: the body at the value. -/
theorem whnfCore_letE_inv {env : Env} {fuel d : Nat}
    {ty v b e' : Expr} {c : Bool}
    (h : whnfCore mode eager env (fuel + 1) d (.letE ty v b) c = .ok e') :
    whnfCore mode eager env fuel d (b.instantiate1 v) c = .ok e' := by
  rw [whnfCore_succ] at h
  simpa [whnfCoreBody, whnfCore_def] using h

/-! ## Fuel-lifted inversions

The three inversions the native-pair projection's certificate walk
needs, in the form that walk consumes: stated at an arbitrary fuel
rather than at `fuel + 1`, by lifting the one-level forms through
`Verify/Mono.lean`.  They are `V`-free inversions of the checker, which
is what this module is for, and the model tier's projection case
consumes them from here. -/

theorem whnf_forallE_eq {env : Env} {fuel d : Nat}
    {t b e' : Expr}
    (h : whnf mode eager env fuel d (.forallE t b) = .ok e') :
    e' = .forallE t b := by
  have h1 := whnf_mono (Nat.le_add_right fuel 2) h
  have h2 : whnf mode eager env (fuel + 2) d (.forallE t b) =
      .ok (.forallE t b) := by
    -- one iteration of the reduction loop suffices (task #106: the
    -- budget is `irreducible`, so peel it with its positivity witness)
    obtain ⟨k, hk⟩ := whnfLoopFuel_succ
    rw [whnf_succ]
    show whnfLoop (pureFns mode eager env (fuel + 1)) env d whnfLoopFuel none _ = _
    rw [hk]
    rfl
  rw [h1] at h2
  exact Except.ok.inj h2

theorem inferTypeCore_app_inv' {env : Env} {fuel d : Nat}
    {f a t : Expr} (h : inferTypeCore mode eager env fuel d (.app f a) = .ok t) :
    ∃ tf ty' body', inferTypeCore mode eager env fuel d f = .ok tf ∧
      whnf mode eager env fuel d tf = .ok (.forallE ty' body') ∧
      t = body'.instantiate1 a ∧
      ∃ ta, inferTypeCore mode eager env fuel d a = .ok ta ∧
        isDefEqCore mode (argEager eager a) env fuel d ta ty' = .ok true := by
  match fuel, h with
  | 0, h => rw [inferTypeCore_zero] at h; exact nomatch h
  | fuel + 1, h =>
    obtain ⟨tf, ty', body', h1, h2, h3, ta, h4, h5⟩ :=
      inferTypeCore_app_inv h
    exact ⟨tf, ty', body', inferTypeCore_mono (Nat.le_succ _) h1,
      whnf_mono (Nat.le_succ _) h2, h3, ta,
      inferTypeCore_mono (Nat.le_succ _) h4,
      isDefEqCore_mono (Nat.le_succ _) h5⟩

/-! ## Application-spine helpers -/

theorem getD_mem {α : Type _} {l : List α} {i : Nat} {dflt : α} (h : i < l.length) :
    l.getD i dflt ∈ l := by
  induction l generalizing i with
  | nil => simp at h
  | cons x xs ih =>
    cases i with
    | zero => simp [List.getD]
    | succ j =>
      simp only [List.getD_cons_succ]
      exact List.mem_cons_of_mem _ (ih (by simpa using h))

theorem Expr.WScoped.getAppArgs {d : Nat} :
    ∀ {e : Expr}, WScoped d e → ∀ x ∈ e.getAppArgs, WScoped d x := by
  intro e
  induction e with
  | app f a ihf iha =>
    intro hw x hx
    simp only [Expr.getAppArgs, List.mem_append, List.mem_singleton] at hx
    simp only [WScoped] at hw
    rcases hx with hx | rfl
    · exact ihf hw.1 x hx
    · exact hw.2
  | _ => intro hw x hx; simp [Expr.getAppArgs] at hx

theorem Expr.WScoped.mkAppN {d : Nat} : ∀ {xs : List Expr} {f : Expr},
    WScoped d f → (∀ x ∈ xs, WScoped d x) → WScoped d (Expr.mkAppN f xs) := by
  intro xs
  induction xs with
  | nil => intro f hf _; exact hf
  | cons x xs ih =>
    intro f hf hxs
    simp only [Expr.mkAppN]
    refine ih ?_ (fun y hy => hxs y (List.mem_cons_of_mem _ hy))
    simp only [WScoped]
    exact ⟨hf, hxs x List.mem_cons_self⟩

theorem looseBVarsBounded_getAppArgs {k : Nat} :
    ∀ {e : Expr}, e.looseBVarsBounded k = true →
      ∀ x ∈ e.getAppArgs, x.looseBVarsBounded k = true := by
  intro e
  induction e with
  | app f a ihf iha =>
    intro hb x hx
    simp only [Expr.getAppArgs, List.mem_append, List.mem_singleton] at hx
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    rcases hx with hx | rfl
    · exact ihf hb.1 x hx
    · exact hb.2
  | _ => intro hb x hx; simp [Expr.getAppArgs] at hx

theorem Expr.mkAppN_append_one (f : Expr) (l : List Expr) (a : Expr) :
    Expr.mkAppN f (l ++ [a]) = .app (Expr.mkAppN f l) a := by
  induction l generalizing f with
  | nil => rfl
  | cons x xs ih => simp only [List.cons_append, Expr.mkAppN]; exact ih _

/-- An expression is its spine head applied to its spine arguments. -/
theorem Expr.mkAppN_getApp : ∀ (e : Expr), Expr.mkAppN e.getAppFn e.getAppArgs = e := by
  intro e
  induction e with
  | app f a ih _ =>
    simp only [Expr.getAppFn, Expr.getAppArgs]
    rw [Expr.mkAppN_append_one]
    exact congrArg (Expr.app · a) ih
  | _ => rfl

/-- The spine head of an application chain is the base's spine head. -/
theorem Expr.getAppFn_mkAppN : ∀ (args : List Expr) (f : Expr),
    (Expr.mkAppN f args).getAppFn = f.getAppFn
  | [], _ => rfl
  | a :: as, f => by
    rw [show Expr.mkAppN f (a :: as) = Expr.mkAppN (.app f a) as from rfl,
      Expr.getAppFn_mkAppN as]
    rfl

/-- The spine arguments of an application chain extend the base's. -/
theorem Expr.getAppArgs_mkAppN : ∀ (args : List Expr) (f : Expr),
    (Expr.mkAppN f args).getAppArgs = f.getAppArgs ++ args
  | [], _ => by simp [Expr.mkAppN]
  | a :: as, f => by
    rw [show Expr.mkAppN f (a :: as) = Expr.mkAppN (.app f a) as from rfl,
      Expr.getAppArgs_mkAppN as]
    simp [Expr.getAppArgs]

/-- **A property that holds of an application exactly where it holds of both parts**
(well-scopedness, the absence of an occurrence, …).  Head normalization takes an application as
a whole spine; such a property passes from the spine to its head and arguments and back. -/
@[expose] def AppClosed (P : Expr → Prop) : Prop := ∀ f a, P (.app f a) ↔ P f ∧ P a

theorem AppClosed.getAppFn {P : Expr → Prop} (hP : AppClosed P) :
    ∀ {e : Expr}, P e → P e.getAppFn := by
  intro e
  induction e with
  | app f a ihf _ => intro h; exact ihf ((hP f a).mp h).1
  | _ => intro h; exact h

theorem AppClosed.getAppArgs {P : Expr → Prop} (hP : AppClosed P) :
    ∀ {e : Expr}, P e → ∀ x ∈ e.getAppArgs, P x := by
  intro e
  induction e with
  | app f a ihf _ =>
    intro h x hx
    simp only [Expr.getAppArgs, List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | hx
    · exact ihf ((hP f a).mp h).1 x hx
    · rw [hx]; exact ((hP f a).mp h).2
  | _ => intro _ x hx; simp [Expr.getAppArgs] at hx

theorem AppClosed.mkAppN {P : Expr → Prop} (hP : AppClosed P) :
    ∀ {xs : List Expr} {f : Expr}, P f → (∀ x ∈ xs, P x) → P (Expr.mkAppN f xs) := by
  intro xs
  induction xs with
  | nil => intro f hf _; exact hf
  | cons x xs ih =>
    intro f hf hxs
    exact ih ((hP f x).mpr ⟨hf, hxs x List.mem_cons_self⟩)
      (fun y hy => hxs y (List.mem_cons_of_mem _ hy))

/-- **The test before unfolding keeps an application-closed property** that `whnf` and the
literal reading keep, and that every marked rule's firing at the replaced term keeps. -/
theorem preFire_pres {r : CoreFns CheckM} {env : Env} {d : Nat} {P : Expr → Prop}
    (hP : AppClosed P)
    (hwh : ∀ {a w : Expr}, r.whnf d a = .ok w → P a → P w)
    (hlit : ∀ (kc : Name) {a : Expr}, P a → P (keyLit (natLitStored env) kc a))
    (hat : ∀ {x x' y : Expr} {t : Name}, preAttempt r env d x x' t = .ok (some y) → P x' → P y)
    {e e₂ : Expr} {t : Name} (h : preFire r env d e = .ok (some (t, e₂))) (he : P e) : P e₂ := by
  obtain ⟨c, us, args', hc, -, hka, hat'⟩ := preFire_inv h
  have hargs' : ∀ x ∈ args', P x := by
    intro x hx
    obtain ⟨i, hi', rfl⟩ := List.getElem_of_mem hx
    have hi : i < e.getAppArgs.length := by rw [← hka.1]; exact hi'
    exact (hka.2 i hi hi').pres P hwh hlit (hP.getAppArgs he _ (List.getElem_mem hi))
  have he' : P (Expr.mkAppN (.const c us) args') := hP.mkAppN (hc ▸ hP.getAppFn he) hargs'
  exact preAt_ind (fun x x' y => P x → P x' → P y) (fun ha _ hx' => hat ha hx')
    (fun ih hfa hfa' => (hP _ _).mpr ⟨ih ((hP _ _).mp hfa).1 ((hP _ _).mp hfa').1,
      ((hP _ _).mp hfa).2⟩)
    e _ hat' he he'

/-- **The β arm's term keeps an application-closed property**: the λ body at the spine's first
argument, applied to the rest. -/
theorem AppClosed.beta {P : Expr → Prop} (hP : AppClosed P) {e ty body a₁ : Expr}
    {rest : List Expr} (hinst : P (.lam ty body) → P a₁ → P (body.instantiate1 a₁))
    (hargs : e.getAppArgs = a₁ :: rest) (he : P e) (hv : P (.lam ty body)) :
    P (Expr.mkAppN (body.instantiate1 a₁) rest) := by
  have ha := hP.getAppArgs he
  rw [hargs] at ha
  exact hP.mkAppN (hinst hv (ha a₁ List.mem_cons_self))
    (fun x hx => ha x (List.mem_cons_of_mem _ hx))

/-- Inversion for a firing projection rule (`reduceProjCore`): the
string-literal expansion step (`projLitToCtorFueled`), then a firing
table entry, certified, and the selected field. -/
theorem reduceProjCore_inv {env : Env} {fuel d : Nat} {sn : Name} {i : Nat}
    {c m : Expr}
    (h : reduceProjCoreFueled mode eager env fuel d sn i c = .ok (some m)) :
    ∃ e₃ us entry, projLitToCtorFueled mode eager env fuel d c = .ok e₃ ∧
      e₃.getAppFn = .const entry.ctor us ∧
      env.findProj? sn i = some entry ∧
      i < entry.numFields ∧
      e₃.getAppArgs.length = entry.numParams + entry.numFields ∧
      us.length = entry.levelParams.length ∧
      m = e₃.getAppArgs.getD (entry.numParams + i) (.bvar 0) ∧
      projCertAt env mode.verifiedChecks entry.ctor e₃.getAppArgs = true := by
  simp only [reduceProjCoreFueled, reduceProjCore, Bind.bind, Except.bind,
    projLitToCtor_fold] at h
  cases hlit : projLitToCtorFueled mode eager env fuel d c with
  | error err => rw [hlit] at h; exact nomatch h
  | ok e₃ =>
  rw [hlit] at h
  dsimp only at h
  cases hfp : env.findProj? sn i with
  | none => rw [hfp] at h; simp [pure, Except.pure] at h
  | some entry =>
  rw [hfp] at h
  dsimp only at h
  cases hfn : e₃.getAppFn with
  | const k us =>
    rw [hfn] at h
    dsimp only at h
    split at h
    next hcond =>
      obtain ⟨rfl, hi, hlen, hus⟩ := hcond
      cases hcert : projCertAt env mode.verifiedChecks entry.ctor e₃.getAppArgs with
      | true =>
        simp only [hcert, ite_true, pure, Except.pure, Except.ok.injEq,
          Option.some.injEq] at h
        exact ⟨e₃, us, entry, rfl, hfn, rfl, hi, hlen, hus, h.symm, hcert⟩
      | false => simp [hcert, pure, Except.pure] at h
    next => simp [pure, Except.pure] at h
  | _ => rw [hfn] at h; simp [pure, Except.pure] at h

/-- Inversion for `whnfCore` on projections: the scrutinee reduced
(`whnf`, or the cheap `whnfCore` at `cheap_proj`), then either the input
itself (a stuck projection keeps its scrutinee as it was, official
`whnf_core`: `reduce_proj` fails and the input is returned) or a firing
projection rule (`reduceProjCore`) and the field's head normalization. -/
theorem whnf_proj_inv {env : Env} {fuel d : Nat} {sn : Name} {i : Nat} {e e' : Expr}
    {c : Bool}
    (h : whnfCore mode eager env (fuel + 1) d (.proj sn i e) c = .ok e') :
    ∃ e₂, ((c = true ∧ whnfCore mode eager env fuel d e true = .ok e₂) ∨
        (c = false ∧ whnf mode eager env fuel d e = .ok e₂)) ∧
      (e' = .proj sn i e ∨
        ∃ m, reduceProjCoreFueled mode eager env fuel d sn i e₂ = .ok (some m) ∧
          whnfCore mode eager env fuel d m c = .ok e') := by
  rw [whnfCore_succ] at h
  simp only [whnfCoreBody, Bind.bind, Except.bind] at h
  simp only [whnfCore_def, whnf_def, reduceProjCore_fold] at h
  cases c with
  | true =>
    simp only [↓reduceIte] at h
    cases hx : whnfCore mode eager env fuel d e true with
    | error err => rw [hx] at h; exact nomatch h
    | ok e₂ =>
    rw [hx] at h
    dsimp only at h
    refine ⟨e₂, (Or.inl ⟨rfl, rfl⟩), ?_⟩
    cases hr : reduceProjCoreFueled mode eager env fuel d sn i e₂ with
    | error err => rw [hr] at h; exact nomatch h
    | ok o =>
    rw [hr] at h
    dsimp only at h
    cases o with
    | some m => exact Or.inr ⟨m, rfl, h⟩
    | none => exact Or.inl (Except.ok.inj h).symm

  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    cases hx : whnf mode eager env fuel d e with
    | error err => rw [hx] at h; exact nomatch h
    | ok e₂ =>
    rw [hx] at h
    dsimp only at h
    refine ⟨e₂, (Or.inr ⟨rfl, rfl⟩), ?_⟩
    cases hr : reduceProjCoreFueled mode eager env fuel d sn i e₂ with
    | error err => rw [hr] at h; exact nomatch h
    | ok o =>
    rw [hr] at h
    dsimp only at h
    cases o with
    | some m => exact Or.inr ⟨m, rfl, h⟩
    | none => exact Or.inl (Except.ok.inj h).symm

/-- At the verified mode the fire's gate is the arity check
(`projCertAt`; parity mirrors official, 2026-09-06): the head is a
stored constructor whose telescope has the spine's syntactic arity. -/
theorem projCertAt_verified_inv {env : Env} {c : Name} {args : List Expr}
    (h : projCertAt env CheckMode.verified.verifiedChecks c args = true) :
    ∃ cvC nP nF T, env.find? c = some (.ctorInfo cvC nP nF T) ∧
      teleArityOk cvC.type args = true := by
  simp only [projCertAt, CheckMode.verifiedChecks, ↓reduceIte, projCert] at h
  split at h
  · rename_i cvC nP nF T hf
    exact ⟨cvC, nP, nF, T, hf, h⟩
  · exact nomatch h

/-- **The major chain's induction principle.**  `prepareMajor` runs
`whnf`, the literal conversion and the rescue in one of two orders
(the K-flagged one runs the rescue alone, or the rescue and the literal
conversion; elsewhere the rescue on the raw major, then — failing a
constructor — `whnf`, the literal conversion and the rescue again, task
#342 R2); a property each step preserves is carried from the raw major
to the prepared one whichever order ran.  Task #334: at a K-flagged recursor `whnf` runs only when
the rescue did NOT already produce a constructor (`hca` below) — the
`hwhnf` hypothesis is simply unused on that branch, since `hlit`/`hmaj`
alone connect `a` to `m` there.  Every consumer of the chain (scoping,
bound variables, leaves, the P tier's readings and gradings) is an
instance, so none of them names the order. -/
theorem prepareMajorFueled_ind {env : Env} {fuel d : Nat} {recName : Name} {isK : Bool}
    {rules : List RecRule} {a m : Expr}
    (h : prepareMajorFueled mode eager env fuel d recName isK rules a = .ok m)
    (P : Expr → Prop)
    (hwhnf : ∀ {e e' : Expr}, whnf mode eager env fuel d e = .ok e' → P e → P e')
    (hlit : ∀ {e e' : Expr},
      litMajorToCtorFueled mode eager env fuel d e = .ok e' → P e → P e')
    (hmaj : ∀ {e e' : Expr},
      majorToCtorFueled mode eager env fuel d recName isK rules e = .ok e' → P e → P e')
    (ha : P a) : P m := by
  dsimp only [prepareMajorFueled] at h
  simp only [prepareMajor, Bind.bind, Except.bind, whnf_def, majorToCtor_fold,
    litMajorToCtor_fold] at h
  by_cases hk : isK = true
  · rw [ite_eq_left hk] at h
    cases h₁ : majorToCtorFueled mode eager env fuel d recName isK rules a with
    | error err => rw [h₁] at h; exact nomatch h
    | ok m₁ =>
      rw [h₁] at h
      dsimp only at h
      by_cases hca : isCtorApp env m₁ = true
      · rw [ite_eq_left hca] at h
        exact hlit h (hmaj h₁ ha)
      · rw [ite_eq_right hca] at h
        simp only [pure, Except.pure, Except.ok.injEq] at h
        exact h ▸ hmaj h₁ ha
  · -- the structure rescues on the major as found first (task #342 R2),
    -- then, failing a constructor, whnf, literal and rescue again
    rw [ite_eq_right hk] at h
    by_cases hs : a.isStrLit = true
    · rw [ite_eq_left hs] at h
      simp only [pure, Except.pure] at h
      have hE : P a := ha
      generalize a = mE at h hE
      by_cases hca : (isCtorApp env mE && !mE.isNatSuccApp) = true
      · rw [ite_eq_left hca] at h
        simp only [pure, Except.pure, Except.ok.injEq] at h
        exact h ▸ hE
      · rw [ite_eq_right hca] at h
        cases h₁ : whnf mode eager env fuel d mE with
        | error err => rw [h₁] at h; exact nomatch h
        | ok m₁ =>
          rw [h₁] at h
          dsimp only at h
          cases h₂ : litMajorToCtorFueled mode eager env fuel d m₁ with
          | error err => rw [h₂] at h; exact nomatch h
          | ok m₂ =>
            rw [h₂] at h
            dsimp only at h
            exact hmaj h (hlit h₂ (hwhnf h₁ hE))
    · rw [ite_eq_right hs] at h
      cases h₀ : majorToCtorFueled mode eager env fuel d recName isK rules a with
      | error err => rw [h₀] at h; exact nomatch h
      | ok mE =>
      rw [h₀] at h
      dsimp only at h
      have hE : P mE := hmaj h₀ ha
      by_cases hca : (isCtorApp env mE && !mE.isNatSuccApp) = true
      · rw [ite_eq_left hca] at h
        simp only [pure, Except.pure, Except.ok.injEq] at h
        exact h ▸ hE
      · rw [ite_eq_right hca] at h
        cases h₁ : whnf mode eager env fuel d mE with
        | error err => rw [h₁] at h; exact nomatch h
        | ok m₁ =>
          rw [h₁] at h
          dsimp only at h
          cases h₂ : litMajorToCtorFueled mode eager env fuel d m₁ with
          | error err => rw [h₂] at h; exact nomatch h
          | ok m₂ =>
            rw [h₂] at h
            dsimp only at h
            exact hmaj h (hlit h₂ (hwhnf h₁ hE))

/-- **The recursor's arity at a successful iota step** (task #342 L18):
the stored type has the spine's number of syntactic ∀-binders. -/
theorem iotaRec_arity {env : Env} {fuel d : Nat} {e eout : Expr} {c : Name}
    {us : List Level} {cv : ConstantVal} {mI rP : Nat} {isK : Bool} {rules : List RecRule}
    (h : iotaRecFueled mode eager env fuel d e = .ok (some eout))
    (hfn : e.getAppFn = .const c us)
    (hfc : env.find? c = some (.recInfo cv mI rP isK rules)) :
    (Expr.peelPis (mI + 1) cv.type).isSome = true := by
  dsimp only [iotaRecFueled] at h
  simp only [iotaRec, Bind.bind, Except.bind] at h
  rw [hfn] at h
  dsimp only at h
  rw [hfc] at h
  dsimp only at h
  by_cases hlen : e.getAppArgs.length = mI + 1 ∧
      us.length = cv.levelParams.length ∧ (Expr.peelPis (mI + 1) cv.type).isSome = true
  · exact hlen.2.2
  · rw [ite_eq_right hlen] at h; exact nomatch h

/-- Inversion of a successful iota step. -/
theorem iotaRec_inv {env : Env} {fuel d : Nat} {e eout : Expr}
    (h : iotaRecFueled mode eager env fuel d e = .ok (some eout)) :
    ∃ c us cv mI rP isK rules major cj usj cvj cnP cnF induct r,
      e.getAppFn = .const c us ∧
      env.find? c = some (.recInfo cv mI rP isK rules) ∧
      e.getAppArgs.length = mI + 1 ∧
      us.length = cv.levelParams.length ∧
      prepareMajorFueled mode eager env fuel d c isK rules (e.getAppArgs.getD mI (.bvar 0)) =
        .ok major ∧
      major.getAppFn = .const cj usj ∧
      env.find? cj = some (.ctorInfo cvj cnP cnF induct) ∧
      rules.find? (fun r' => r'.ctor == cj) = some r ∧
      major.getAppArgs.length = cnP + r.nfields ∧
      (mode.verifiedChecks = true → ∃ c3, iotaCaseAt (pureFns mode eager env fuel).whnf
          env.find? isK induct (recFireComparands r cnP cv.levelParams us cvj.levelParams
            e.getAppArgs rP).1 = .ok c3 ∧ (c3 = true →
        Level.isEquivList usj
          (recFireComparands r cnP cv.levelParams us cvj.levelParams
            e.getAppArgs rP).1 = some true ∧
        defEqListFueled mode eager env fuel d (major.getAppArgs.take cnP)
          (recFireComparands r cnP cv.levelParams us cvj.levelParams
            e.getAppArgs rP).2 = .ok true ∧
        iotaCertsFullFueled mode eager env fuel d
          (cvj.type.instantiateLevelParams cvj.levelParams usj)
          major.getAppArgs = .ok true ∧
        iotaIndexOkFueled mode eager env fuel d mI rP cnP
          (cvj.type.instantiateLevelParams cvj.levelParams usj)
          major.getAppArgs ((e.getAppArgs.take mI).drop rP) = .ok true)) ∧
      eout = r.iotaReduct cv.levelParams us rP
        (e.getAppArgs.take rP ++ major.getAppArgs.drop cnP) := by
  dsimp only [iotaRecFueled] at h
  simp only [iotaRec, Bind.bind, Except.bind] at h
  simp only [prepareMajor_fold, defEqList_fold,
    iotaCertsFull_fold, iotaIndexOk_fold] at h
  revert h
  cases hfn : e.getAppFn with
  | bvar i => intro h; exact nomatch h
  | fvar i ty => intro h; exact nomatch h
  | sort u => intro h; exact nomatch h
  | app f a => intro h; exact nomatch h
  | lam ty body => intro h; exact nomatch h
  | forallE ty body => intro h; exact nomatch h
  | letE ty v body => intro h; exact nomatch h
  | lit l => intro h; exact nomatch h
  | proj sn i pe => intro h; exact nomatch h
  | const c us =>
  intro h
  dsimp only at h
  revert h
  match hfc : env.find? c with
  | none => intro h; exact nomatch h
  | some (.axiomInfo _) => intro h; exact nomatch h
  | some (.defnInfo _ _ _) => intro h; exact nomatch h
  | some (.thmInfo _) => intro h; exact nomatch h
  | some (.indInfo _ _) => intro h; exact nomatch h
  | some (.ctorInfo _ _ _ _) => intro h; exact nomatch h
  | some (.recInfo cv mI rP isK rules) => ?_
  intro h
  dsimp only at h
  by_cases hlen : e.getAppArgs.length = mI + 1 ∧
      us.length = cv.levelParams.length ∧ (Expr.peelPis (mI + 1) cv.type).isSome = true
  case neg => rw [ite_eq_right hlen] at h; exact nomatch h
  rw [ite_eq_left hlen] at h
  try simp only [Bind.bind, Except.bind] at h
  cases hprep : prepareMajorFueled mode eager env fuel d c isK rules
      (e.getAppArgs.getD mI (.bvar 0)) with
  | error err => rw [hprep] at h; exact nomatch h
  | ok major =>
  rw [hprep] at h
  dsimp only at h
  revert h
  cases hmfn : major.getAppFn with
  | bvar i => intro h; exact nomatch h
  | fvar i ty => intro h; exact nomatch h
  | sort u => intro h; exact nomatch h
  | app f a => intro h; exact nomatch h
  | lam ty body => intro h; exact nomatch h
  | forallE ty body => intro h; exact nomatch h
  | letE ty v body => intro h; exact nomatch h
  | lit l => intro h; exact nomatch h
  | proj sn i pe => intro h; exact nomatch h
  | const cj usj =>
  intro h
  dsimp only at h
  revert h
  match hfj : env.find? cj with
  | none => intro h; exact nomatch h
  | some (.axiomInfo _) => intro h; exact nomatch h
  | some (.defnInfo _ _ _) => intro h; exact nomatch h
  | some (.thmInfo _) => intro h; exact nomatch h
  | some (.indInfo _ _) => intro h; exact nomatch h
  | some (.recInfo _ _ _ _ _) => intro h; exact nomatch h
  | some (.ctorInfo cvj cnP cnF induct) => ?_
  intro h
  dsimp only at h
  revert h
  cases hrule : rules.find? (fun r' => r'.ctor == cj) with
  | none => intro h; exact nomatch h
  | some r =>
  intro h
  dsimp only at h
  by_cases hml : major.getAppArgs.length = cnP + r.nfields
  case neg => rw [ite_eq_right hml] at h; exact nomatch h
  rw [ite_eq_left hml] at h
  try simp only [Bind.bind, Except.bind] at h
  -- Task #342 (r1): the case-3 decision is a certificate family, gated
  -- off at the trusted mode — one `mode.verifiedChecks` split outside
  -- the case split's.
  by_cases hμ : mode.verifiedChecks = true
  case neg =>
    rw [ite_eq_right hμ] at h
    simp only [pure, Except.pure, ↓reduceIte, Except.ok.injEq,
      Option.some.injEq] at h
    exact ⟨c, us, cv, mI, rP, isK, rules, major, cj, usj, cvj, cnP,
      cnF, induct, r, rfl, hfc, hlen.1, hlen.2.1, hprep, hmfn, hfj, hrule,
      hml, fun hμ' => absurd hμ' hμ, h.symm⟩
  rw [ite_eq_left hμ] at h
  generalize hcmp : recFireComparands r cnP cv.levelParams us cvj.levelParams
    e.getAppArgs rP = cmp at h
  cases hc3 : iotaCaseAt (pureFns mode eager env fuel).whnf env.find? isK induct cmp.1 with
  | error err => rw [hc3] at h; exact nomatch h
  | ok c3 =>
  rw [hc3] at h
  dsimp only at h
  by_cases h3 : c3 = true
  · rw [ite_eq_left h3] at h
    try simp only [Bind.bind, Except.bind] at h
    cases hlev : Level.isEquivList usj cmp.1 with
    | none => rw [hlev] at h; simp [liftFueled] at h
    | some bl =>
    rw [hlev] at h
    simp only [liftFueled, pure, Except.pure] at h
    try dsimp only at h
    cases bl with
    | false => simp [pure, Except.pure] at h
    | true =>
    simp only [↓reduceIte] at h
    try simp only [Bind.bind, Except.bind] at h
    cases hpeq : defEqListFueled mode eager env fuel d (major.getAppArgs.take cnP)
        cmp.2 with
    | error err => rw [hpeq] at h; exact nomatch h
    | ok rp =>
    rw [hpeq] at h
    dsimp only at h
    cases rp with
    | false => simp [pure, Except.pure] at h
    | true =>
    simp only [↓reduceIte] at h
    try simp only [Bind.bind, Except.bind] at h
    cases hmcerts : iotaCertsFullFueled mode eager env fuel d
        (cvj.type.instantiateLevelParams cvj.levelParams usj)
        major.getAppArgs with
    | error err => rw [hmcerts] at h; exact nomatch h
    | ok rmc =>
    rw [hmcerts] at h
    dsimp only at h
    cases rmc with
    | false => simp [pure, Except.pure] at h
    | true =>
    simp only [↓reduceIte] at h
    try simp only [Bind.bind, Except.bind] at h
    -- the index block (`iotaIndexOk`)
    cases hidx : iotaIndexOkFueled mode eager env fuel d mI rP cnP
        (cvj.type.instantiateLevelParams cvj.levelParams usj)
        major.getAppArgs ((e.getAppArgs.take mI).drop rP) with
    | error err => rw [hidx] at h; exact nomatch h
    | ok ri =>
    rw [hidx] at h
    dsimp only at h
    cases ri with
    | false => simp [pure, Except.pure] at h
    | true =>
    simp only [↓reduceIte, pure, Except.pure, Except.ok.injEq,
      Option.some.injEq] at h
    exact ⟨c, us, cv, mI, rP, isK, rules, major, cj, usj, cvj, cnP,
      cnF, induct, r, rfl, hfc, hlen.1, hlen.2.1, hprep, hmfn, hfj, hrule,
      hml, fun _ => ⟨c3, by rw [hcmp]; exact hc3,
        fun _ => by rw [hcmp]; exact ⟨hlev, hpeq, hmcerts, hidx⟩⟩, h.symm⟩
  · rw [ite_eq_right h3] at h
    simp only [pure, Except.pure, ↓reduceIte, Except.ok.injEq,
      Option.some.injEq] at h
    exact ⟨c, us, cv, mI, rP, isK, rules, major, cj, usj, cvj, cnP,
      cnF, induct, r, rfl, hfc, hlen.1, hlen.2.1, hprep, hmfn, hfj, hrule,
      hml, fun _ => ⟨c3, by rw [hcmp]; exact hc3, fun h3' => absurd h3' h3⟩, h.symm⟩

/-- Inversion of the canonical-index comparison where the recursor has
indices: the constructor telescope's residual exists and its index
arguments compare equal to the recursor's. -/
theorem iotaIndexOk_inv {env : Env} {fuel d mI rP cnP : Nat} {tyCtor : Expr}
    {margs idx : List Expr}
    (h : iotaIndexOkFueled mode eager env fuel d mI rP cnP tyCtor margs idx = .ok true)
    (hne : mI ≠ rP) :
    ∃ residual, piResidual tyCtor margs = some residual ∧
      defEqListFueled mode eager env fuel d (residual.getAppArgs.drop cnP) idx =
        .ok true := by
  dsimp only [iotaIndexOkFueled] at h
  simp only [iotaIndexOk, ite_eq_right hne, defEqList_fold] at h
  cases hres : piResidual tyCtor margs with
  | none => rw [hres] at h; simp [pure, Except.pure] at h
  | some residual => rw [hres] at h; exact ⟨residual, rfl, h⟩

/-- Inversion of the stuck-major rescue: either the major is returned
unchanged, or a constructor application was fabricated — in the
K branch certified by proof irrelevance, in the structure-eta branch
guarded by the η law's keys (no certificate), in the `And` branch by proof irrelevance again — and its
scoping was checked syntactically (the scope guard). -/
theorem majorToCtor_inv {env : Env} {fuel d : Nat} {recName : Name} {isK : Bool}
    {rules : List RecRule} {major major' : Expr}
    (h : majorToCtorFueled mode eager env fuel d recName isK rules major = .ok major') :
    major' = major ∨
    (major'.wscopedB d = true ∧ major'.looseBVarsBounded 0 = true ∧
     major'.fvarLeaves.all (fun l => major.fvarLeaves.contains l) = true ∧
     ∃ rl cvj cnP cnF tmaj₀ tmaj T ust cvT caps,
       rules = [rl] ∧
       env.find? rl.ctor = some (.ctorInfo cvj cnP cnF T) ∧
       env.find? T = some (.indInfo cvT caps) ∧
       inferTypeIO mode eager env fuel d major = .ok tmaj₀ ∧
       whnf mode eager env fuel d tmaj₀ = .ok tmaj ∧
       tmaj.getAppFn = .const T ust ∧
       ((isK = true ∧
         cvj.levelParams.length = ust.length ∧
         cnP ≤ tmaj.getAppArgs.length ∧
         major' = Expr.mkAppN (.const rl.ctor ust)
           (tmaj.getAppArgs.take cnP) ∧
         (∃ tfab, inferTypeIO mode eager env fuel d major' = .ok tfab ∧
           isDefEqCore mode eager env fuel d tmaj tfab = .ok true) ∧
         (mode.verifiedChecks = true →
           proofIrrelFueled mode eager env fuel d major' major = .ok true)) ∨
        (∃ tbl, etaRescueTable? (env.findTable? T) rl.ctor cvj cvT caps = some tbl ∧
         tmaj.getAppArgs.length = tbl.numParams ∧
         ust.length = cvT.levelParams.length ∧
         major' = Expr.mkAppN (.const tbl.ctor ust)
           (etaFabArgsE T tmaj.getAppArgs major tbl.numFields)) ∨
        (T = andName ∧
         tmaj.getAppArgs.length = cnP ∧
         cvj.levelParams.length = ust.length ∧
         andRescueSlots env rl.ctor cnP = true ∧
         major' = Expr.mkAppN (.const rl.ctor ust)
           (tmaj.getAppArgs ++ [.proj T 0 major, .proj T 1 major]) ∧
         (∃ tfab, inferTypeIO mode eager env fuel d major' = .ok tfab ∧
           isDefEqCore mode eager env fuel d tmaj tfab = .ok true) ∧
         (mode.verifiedChecks = true →
           proofIrrelFueled mode eager env fuel d major' major = .ok true)))) := by
  dsimp only [majorToCtorFueled] at h
  simp only [majorToCtor, Bind.bind, Except.bind] at h
  simp only [inferTypeIO_def, whnf_def, defeq_def, proofIrrel_fold] at h
  revert h
  cases hca : isCtorApp env major with
  | true =>
    intro h
    simp only [↓reduceIte, pure, Except.pure, Except.ok.injEq] at h
    exact Or.inl h.symm
  | false =>
  simp only [Bool.false_eq_true, ↓reduceIte]
  match hrs : rules with
  | [] =>
    intro h; dsimp only at h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    exact Or.inl h.symm
  | _ :: _ :: _ =>
    intro h; dsimp only at h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    exact Or.inl h.symm
  | [rl] =>
  intro h
  dsimp only at h
  revert h
  match hfj : env.find? rl.ctor with
  | none =>
    intro h; dsimp only at h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    exact Or.inl h.symm
  | some (.axiomInfo _) | some (.defnInfo _ _ _) | some (.thmInfo _)
  | some (.indInfo _ _) | some (.recInfo _ _ _ _ _) =>
    intro h; dsimp only at h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    exact Or.inl h.symm
  | some (.ctorInfo cvj cnP cnF T) =>
  intro h
  dsimp only at h
  revert h
  match hfT : env.find? T with
  | none =>
    intro h; dsimp only at h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    exact Or.inl h.symm
  | some (.axiomInfo _) | some (.defnInfo _ _ _) | some (.thmInfo _)
  | some (.ctorInfo _ _ _ _) | some (.recInfo _ _ _ _ _) =>
    intro h; dsimp only at h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    exact Or.inl h.symm
  | some (.indInfo cvT caps) =>
  intro h
  dsimp only at h
  by_cases hK : isK = true
  · rw [ite_eq_left hK] at h
    try simp only [Bind.bind, Except.bind] at h
    cases hti : inferTypeIO mode eager env fuel d major with
    | error err => rw [hti] at h; exact nomatch h
    | ok tmaj₀ =>
    rw [hti] at h
    dsimp only at h
    cases htw : whnf mode eager env fuel d tmaj₀ with
    | error err => rw [htw] at h; exact nomatch h
    | ok tmaj =>
    rw [htw] at h
    dsimp only at h
    revert h
    cases hth : tmaj.getAppFn with
    | bvar i =>
      intro h; dsimp only at h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      exact Or.inl h.symm
    | fvar i ty =>
      intro h; dsimp only at h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      exact Or.inl h.symm
    | sort u =>
      intro h; dsimp only at h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      exact Or.inl h.symm
    | app f a =>
      intro h; dsimp only at h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      exact Or.inl h.symm
    | lam ty body =>
      intro h; dsimp only at h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      exact Or.inl h.symm
    | forallE ty body =>
      intro h; dsimp only at h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      exact Or.inl h.symm
    | letE ty v body =>
      intro h; dsimp only at h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      exact Or.inl h.symm
    | lit l =>
      intro h; dsimp only at h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      exact Or.inl h.symm
    | proj sn i pe =>
      intro h; dsimp only at h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      exact Or.inl h.symm
    | const T' ust =>
    intro h
    dsimp only at h
    by_cases hTl : T' = T ∧ cvj.levelParams.length = ust.length
    case neg =>
      rw [ite_eq_right hTl] at h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      exact Or.inl h.symm
    obtain ⟨rfl, hlvl⟩ := hTl
    rw [ite_eq_left ⟨rfl, hlvl⟩] at h
    by_cases harK1 : cnP ≤ tmaj.getAppArgs.length
    case neg =>
      rw [ite_eq_right harK1] at h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      exact Or.inl h.symm
    rw [ite_eq_left harK1] at h
    cases hguard : (Expr.mkAppN (.const rl.ctor ust)
          (tmaj.getAppArgs.take cnP)).wscopedB d &&
        (Expr.mkAppN (.const rl.ctor ust)
          (tmaj.getAppArgs.take cnP)).looseBVarsBounded 0 &&
        (Expr.mkAppN (.const rl.ctor ust)
          (tmaj.getAppArgs.take cnP)).fvarLeaves.all
          (fun l => major.fvarLeaves.contains l) with
    | false =>
      rw [hguard] at h
      simp only [Bool.false_eq_true, ↓reduceIte, pure, Except.pure,
        Except.ok.injEq] at h
      exact Or.inl h.symm
    | true =>
    rw [hguard] at h
    simp only [↓reduceIte] at h
    try simp only [Bind.bind, Except.bind] at h
    cases htf : inferTypeIO mode eager env fuel d
        (Expr.mkAppN (.const rl.ctor ust)
          (tmaj.getAppArgs.take cnP)) with
    | error err => rw [htf] at h; exact nomatch h
    | ok tfab =>
    rw [htf] at h
    dsimp only at h
    cases hdeq : isDefEqCore mode eager env fuel d tmaj tfab with
    | error err => rw [hdeq] at h; exact nomatch h
    | ok bde =>
    rw [hdeq] at h
    dsimp only at h
    cases bde with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, pure, Except.pure,
        Except.ok.injEq] at h
      exact Or.inl h.symm
    | true =>
    simp only [↓reduceIte] at h
    try simp only [Bind.bind, Except.bind] at h
    -- Task #342 (r1): proof irrelevance here is a certificate family,
    -- gated off at the trusted mode (`certAtI mode (proofIrrelI ...)`
    -- in the cached twin).
    by_cases hμ : mode.verifiedChecks = true
    case neg =>
      rw [ite_eq_right hμ] at h
      simp only [pure, Except.pure, ↓reduceIte, Except.ok.injEq] at h
      subst h
      simp only [Bool.and_eq_true] at hguard
      exact Or.inr ⟨hguard.1.1, hguard.1.2, hguard.2,
        rl, cvj, cnP, cnF, tmaj₀, tmaj, T', ust, cvT, caps,
        rfl, hfj, hfT, rfl, htw, hth,
        Or.inl ⟨hK, hlvl, harK1, rfl,
          ⟨tfab, htf, hdeq⟩, fun hμ' => absurd hμ' hμ⟩⟩
    rw [ite_eq_left hμ] at h
    cases hpi : proofIrrelFueled mode eager env fuel d
        (Expr.mkAppN (.const rl.ctor ust)
          (tmaj.getAppArgs.take cnP)) major with
    | error err => rw [hpi] at h; exact nomatch h
    | ok bpi =>
    rw [hpi] at h
    dsimp only at h
    cases bpi with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, pure, Except.pure,
        Except.ok.injEq] at h
      exact Or.inl h.symm
    | true =>
    simp only [↓reduceIte, pure, Except.pure, Except.ok.injEq] at h
    subst h
    simp only [Bool.and_eq_true] at hguard
    exact Or.inr ⟨hguard.1.1, hguard.1.2, hguard.2,
      rl, cvj, cnP, cnF, tmaj₀, tmaj, T', ust, cvT, caps,
      rfl, hfj, hfT, rfl, htw, hth,
      Or.inl ⟨hK, hlvl, harK1, rfl,
        ⟨tfab, htf, hdeq⟩, fun _ => hpi⟩⟩
  · rw [ite_eq_right hK] at h
    cases hE : etaRescueTable? (env.findTable? T) rl.ctor cvj cvT caps with
    | none =>
      rw [hE] at h
      dsimp only at h
      by_cases hA : T = andName
      case neg =>
        rw [ite_eq_right hA] at h
        simp only [pure, Except.pure, Except.ok.injEq] at h
        exact Or.inl h.symm
      rw [ite_eq_left hA] at h
      try simp only [Bind.bind, Except.bind] at h
      cases hti : inferTypeIO mode eager env fuel d major with
      | error err => rw [hti] at h; exact nomatch h
      | ok tmaj₀ =>
      rw [hti] at h
      dsimp only at h
      cases htw : whnf mode eager env fuel d tmaj₀ with
      | error err => rw [htw] at h; exact nomatch h
      | ok tmaj =>
      rw [htw] at h
      dsimp only at h
      revert h
      cases hth : tmaj.getAppFn with
      | bvar i =>
        intro h; dsimp only at h
        simp only [pure, Except.pure, Except.ok.injEq] at h
        exact Or.inl h.symm
      | fvar i ty =>
        intro h; dsimp only at h
        simp only [pure, Except.pure, Except.ok.injEq] at h
        exact Or.inl h.symm
      | sort u =>
        intro h; dsimp only at h
        simp only [pure, Except.pure, Except.ok.injEq] at h
        exact Or.inl h.symm
      | app f a =>
        intro h; dsimp only at h
        simp only [pure, Except.pure, Except.ok.injEq] at h
        exact Or.inl h.symm
      | lam ty body =>
        intro h; dsimp only at h
        simp only [pure, Except.pure, Except.ok.injEq] at h
        exact Or.inl h.symm
      | forallE ty body =>
        intro h; dsimp only at h
        simp only [pure, Except.pure, Except.ok.injEq] at h
        exact Or.inl h.symm
      | letE ty v body =>
        intro h; dsimp only at h
        simp only [pure, Except.pure, Except.ok.injEq] at h
        exact Or.inl h.symm
      | lit l =>
        intro h; dsimp only at h
        simp only [pure, Except.pure, Except.ok.injEq] at h
        exact Or.inl h.symm
      | proj sn i pe =>
        intro h; dsimp only at h
        simp only [pure, Except.pure, Except.ok.injEq] at h
        exact Or.inl h.symm
      | const T' ust =>
      intro h
      dsimp only at h
      by_cases hTl : T' = T ∧ tmaj.getAppArgs.length = cnP ∧
          cvj.levelParams.length = ust.length ∧
          andRescueSlots env rl.ctor cnP = true
      case neg =>
        rw [ite_eq_right hTl] at h
        simp only [pure, Except.pure, Except.ok.injEq] at h
        exact Or.inl h.symm
      obtain ⟨rfl, hplen, hlvl, hslots⟩ := hTl
      rw [ite_eq_left ⟨rfl, hplen, hlvl, hslots⟩] at h
      cases hguard : (Expr.mkAppN (.const rl.ctor ust)
            (tmaj.getAppArgs ++ [.proj T' 0 major, .proj T' 1 major])).wscopedB d &&
          (Expr.mkAppN (.const rl.ctor ust)
            (tmaj.getAppArgs ++ [.proj T' 0 major, .proj T' 1 major])).looseBVarsBounded 0 &&
          (Expr.mkAppN (.const rl.ctor ust)
            (tmaj.getAppArgs ++ [.proj T' 0 major, .proj T' 1 major])).fvarLeaves.all
            (fun l => major.fvarLeaves.contains l) with
      | false =>
        rw [hguard] at h
        simp only [Bool.false_eq_true, ↓reduceIte, pure, Except.pure,
          Except.ok.injEq] at h
        exact Or.inl h.symm
      | true =>
      rw [hguard] at h
      simp only [↓reduceIte] at h
      try simp only [Bind.bind, Except.bind] at h
      cases htf : inferTypeIO mode eager env fuel d (Expr.mkAppN (.const rl.ctor ust)
            (tmaj.getAppArgs ++ [.proj T' 0 major, .proj T' 1 major])) with
      | error err => rw [htf] at h; exact nomatch h
      | ok tfab =>
      rw [htf] at h
      dsimp only at h
      cases hdeq : isDefEqCore mode eager env fuel d tmaj tfab with
      | error err => rw [hdeq] at h; exact nomatch h
      | ok bde =>
      rw [hdeq] at h
      dsimp only at h
      cases bde with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte, pure, Except.pure,
          Except.ok.injEq] at h
        exact Or.inl h.symm
      | true =>
      simp only [↓reduceIte] at h
      try simp only [Bind.bind, Except.bind] at h
      -- Task #342 (r1): proof irrelevance here, as in the K branch, is
      -- a certificate family — gated off at the trusted mode.
      by_cases hμ : mode.verifiedChecks = true
      case neg =>
        rw [ite_eq_right hμ] at h
        simp only [pure, Except.pure, ↓reduceIte, Except.ok.injEq] at h
        subst h
        simp only [Bool.and_eq_true] at hguard
        exact Or.inr ⟨hguard.1.1, hguard.1.2, hguard.2,
          rl, cvj, cnP, cnF, tmaj₀, tmaj, T', ust, cvT, caps,
          rfl, hfj, hfT, rfl, htw, hth,
          Or.inr (Or.inr ⟨hA, hplen, hlvl, hslots, rfl,
            ⟨tfab, htf, hdeq⟩, fun hμ' => absurd hμ' hμ⟩)⟩
      rw [ite_eq_left hμ] at h
      cases hpi : proofIrrelFueled mode eager env fuel d (Expr.mkAppN (.const rl.ctor ust)
            (tmaj.getAppArgs ++ [.proj T' 0 major, .proj T' 1 major])) major with
      | error err => rw [hpi] at h; exact nomatch h
      | ok bpi =>
      rw [hpi] at h
      dsimp only at h
      cases bpi with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte, pure, Except.pure,
          Except.ok.injEq] at h
        exact Or.inl h.symm
      | true =>
      simp only [↓reduceIte, pure, Except.pure, Except.ok.injEq] at h
      subst h
      simp only [Bool.and_eq_true] at hguard
      exact Or.inr ⟨hguard.1.1, hguard.1.2, hguard.2,
        rl, cvj, cnP, cnF, tmaj₀, tmaj, T', ust, cvT, caps,
        rfl, hfj, hfT, rfl, htw, hth,
        Or.inr (Or.inr ⟨hA, hplen, hlvl, hslots, rfl,
          ⟨tfab, htf, hdeq⟩, fun _ => hpi⟩)⟩
    | some tbl =>
    rw [hE] at h
    dsimp only at h
    try simp only [Bind.bind, Except.bind] at h
    cases hti : inferTypeIO mode eager env fuel d major with
    | error err => rw [hti] at h; exact nomatch h
    | ok tmaj₀ =>
    rw [hti] at h
    dsimp only at h
    cases htw : whnf mode eager env fuel d tmaj₀ with
    | error err => rw [htw] at h; exact nomatch h
    | ok tmaj =>
    rw [htw] at h
    dsimp only at h
    revert h
    cases hth : tmaj.getAppFn with
    | bvar i =>
      intro h; dsimp only at h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      exact Or.inl h.symm
    | fvar i ty =>
      intro h; dsimp only at h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      exact Or.inl h.symm
    | sort u =>
      intro h; dsimp only at h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      exact Or.inl h.symm
    | app f a =>
      intro h; dsimp only at h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      exact Or.inl h.symm
    | lam ty body =>
      intro h; dsimp only at h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      exact Or.inl h.symm
    | forallE ty body =>
      intro h; dsimp only at h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      exact Or.inl h.symm
    | letE ty v body =>
      intro h; dsimp only at h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      exact Or.inl h.symm
    | lit l =>
      intro h; dsimp only at h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      exact Or.inl h.symm
    | proj sn i pe =>
      intro h; dsimp only at h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      exact Or.inl h.symm
    | const T' ust =>
    intro h
    dsimp only at h
    by_cases hTl : T' = T ∧ tmaj.getAppArgs.length = tbl.numParams ∧
        ust.length = cvT.levelParams.length
    case neg =>
      rw [ite_eq_right hTl] at h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      exact Or.inl h.symm
    rw [ite_eq_left hTl] at h
    obtain ⟨rfl, hplen, hlvl⟩ := hTl
    cases hnzr : familyNeverZeroAt (pureFns mode eager env fuel).whnf cvT caps ust with
    | error err => rw [hnzr] at h; exact nomatch h
    | ok nz =>
    rw [hnzr] at h
    dsimp only at h
    cases nz with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at h
      exact Or.inl h.symm
    | true =>
    simp only [↓reduceIte] at h
    cases hguard : (Expr.mkAppN (.const tbl.ctor ust)
          (etaFabArgsE T' tmaj.getAppArgs major
            tbl.numFields)).wscopedB d &&
        (Expr.mkAppN (.const tbl.ctor ust)
          (etaFabArgsE T' tmaj.getAppArgs major
            tbl.numFields)).looseBVarsBounded 0 &&
        (Expr.mkAppN (.const tbl.ctor ust)
          (etaFabArgsE T' tmaj.getAppArgs major
            tbl.numFields)).fvarLeaves.all
          (fun l => major.fvarLeaves.contains l) with
    | false =>
      rw [hguard] at h
      simp only [Bool.false_eq_true, ↓reduceIte, pure, Except.pure,
        Except.ok.injEq] at h
      exact Or.inl h.symm
    | true =>
    rw [hguard] at h
    simp only [↓reduceIte, pure, Except.pure, Except.ok.injEq] at h
    subst h
    simp only [Bool.and_eq_true] at hguard
    exact Or.inr ⟨hguard.1.1, hguard.1.2, hguard.2,
      rl, cvj, cnP, cnF, tmaj₀, tmaj, T', ust, cvT, caps,
      rfl, hfj, hfT, rfl, htw, hth,
      Or.inr (Or.inl ⟨tbl, hE, hplen, hlvl, rfl⟩)⟩

/-- Inversion of one pairwise-defeq step. -/
theorem defEqList_step_inv {env : Env} {fuel d : Nat} {a b : Expr}
    {as bs : List Expr}
    (h : defEqListFueled mode eager env fuel d (a :: as) (b :: bs) = .ok true) :
    isDefEqCore mode eager env fuel d a b = .ok true ∧
    defEqListFueled mode eager env fuel d as bs = .ok true := by
  dsimp only [defEqListFueled] at h
  simp only [defEqList, Bind.bind, Except.bind] at h
  simp only [defeq_def, defEqList_fold] at h
  cases hde : isDefEqCore mode eager env fuel d a b with
  | error err => rw [hde] at h; exact nomatch h
  | ok r =>
  rw [hde] at h
  dsimp only at h
  cases r with
  | false => simp [pure, Except.pure] at h
  | true =>
  simp only [↓reduceIte] at h
  exact ⟨rfl, h⟩

/-- Inversion of the lazy delta same-head spine congruence: both sides
are applications of the same constant, at pointwise-equivalent levels,
with pairwise definitionally equal spines of equal length, compared
last to first (the reversed spines). -/
theorem defeqSpine_inv {env : Env} {fuel d : Nat} {a b : Expr}
    (h : defeqSpineFueled mode eager env fuel d a b = .ok true) :
    ∃ n us us', a.getAppFn = .const n us ∧ b.getAppFn = .const n us' ∧
      a.getAppArgs.length = b.getAppArgs.length ∧
      Level.isEquivList us us' = some true ∧
      defEqListFueled mode eager env fuel d a.getAppArgs.reverse
        b.getAppArgs.reverse = .ok true := by
  dsimp only [defeqSpineFueled] at h
  simp only [defeqSpine, defEqList_fold] at h
  revert h
  match hfa : a.getAppFn with
  | .bvar _ | .fvar _ _ | .sort _ | .app _ _ | .lam _ _
  | .forallE _ _ | .letE _ _ _ | .lit _ | .proj _ _ _ =>
    intro h; simp [pure, Except.pure] at h
  | .const n us => ?_
  intro h
  dsimp only at h
  revert h
  match hfb : b.getAppFn with
  | .bvar _ | .fvar _ _ | .sort _ | .app _ _ | .lam _ _
  | .forallE _ _ | .letE _ _ _ | .lit _ | .proj _ _ _ =>
    intro h; simp [pure, Except.pure] at h
  | .const n' us' => ?_
  intro h
  dsimp only at h
  revert h
  split
  case isTrue hcond =>
    obtain ⟨rfl, hlen⟩ := hcond
    intro h
    revert h
    match hlev : Level.isEquivList us us' with
    | some true => intro h; exact ⟨n, us, us', rfl, rfl, hlen, hlev, h⟩
    | some false => intro h; simp [pure, Except.pure] at h
    | none => intro h; simp [pure, Except.pure] at h
  case isFalse =>
    intro h; simp [pure, Except.pure] at h

/-- Inversion of one step of the full-grade certificate (task #342
L10): the argument's FULL-grade type is defeq to the domain, and the
rest certifies. -/
theorem iotaCertsFull_step_inv {env : Env} {fuel d : Nat}
    {ty body : Expr} {arg : Expr} {rest : List Expr}
    (h : iotaCertsFullFueled mode eager env fuel d (.forallE ty body) (arg :: rest) =
      .ok true) :
    ∃ ta, inferTypeCore mode eager env fuel d arg = .ok ta ∧
      isDefEqCore mode eager env fuel d ta ty = .ok true ∧
      iotaCertsFullFueled mode eager env fuel d (body.instantiate1 arg) rest = .ok true := by
  dsimp only [iotaCertsFullFueled] at h
  simp only [iotaCertsFull, Bind.bind, Except.bind] at h
  simp only [infer_def, defeq_def, iotaCertsFull_fold] at h
  cases hta : inferTypeCore mode eager env fuel d arg with
  | error err => rw [hta] at h; exact nomatch h
  | ok ta =>
  rw [hta] at h
  dsimp only at h
  cases hde : isDefEqCore mode eager env fuel d ta ty with
  | error err => rw [hde] at h; exact nomatch h
  | ok r =>
  rw [hde] at h
  dsimp only at h
  cases r with
  | false => simp [pure, Except.pure] at h
  | true =>
  simp only [↓reduceIte] at h
  exact ⟨ta, rfl, hde, h⟩

/-- Inversion for a rule firing's certificate step (`ruleCerts`): a head slot, or a certified
slot. -/
theorem ruleCerts_step_inv {env : Env} {fuel d : Nat} {eargs : List Expr} {hT : Option Expr}
    {ty body : Expr} {arg : Expr} {rest : List Expr}
    (h : ruleCertsFueled mode eager env fuel d eargs hT (.forallE ty body) (arg :: rest) =
      .ok true) :
    (headSlotOpt hT eargs arg ty = true ∧
      ruleCertsFueled mode eager env fuel d eargs hT (body.instantiate1 arg) rest = .ok true) ∨
    ∃ ta, inferTypeCore mode eager env fuel d arg = .ok ta ∧
      isDefEqCore mode eager env fuel d ta ty = .ok true ∧
      ruleCertsFueled mode eager env fuel d eargs hT (body.instantiate1 arg) rest = .ok true := by
  dsimp only [ruleCertsFueled] at h
  simp only [ruleCerts, Bind.bind, Except.bind] at h
  simp only [infer_def, defeq_def, ruleCerts_fold] at h
  by_cases hs : headSlotOpt hT eargs arg ty = true
  · simp only [hs, ↓reduceIte] at h
    exact .inl ⟨hs, h⟩
  simp only [hs, Bool.false_eq_true, ↓reduceIte] at h
  refine .inr ?_
  cases hta : inferTypeCore mode eager env fuel d arg with
  | error err => rw [hta] at h; exact nomatch h
  | ok ta =>
  rw [hta] at h
  dsimp only at h
  cases hde : isDefEqCore mode eager env fuel d ta ty with
  | error err => rw [hde] at h; exact nomatch h
  | ok r =>
  rw [hde] at h
  dsimp only at h
  cases r with
  | false => simp [pure, Except.pure] at h
  | true =>
  simp only [↓reduceIte] at h
  exact ⟨ta, rfl, hde, h⟩

/-- Inversion of a successful hoisted `Prop`-branch certification
(task #168): either the fast "yes" arm fired — both sides'
head-symbol readers say "proof" — or both types' sorts are `Prop` by
the slow branch.  The fast "not a proof" arm only ever answers
`false`, so it contributes nothing here.  Ungated since 2026-09-06:
the arms run in both modes, so no mode conjunct survives. -/
theorem propIrrel_inv {env : Env} {fuel d : Nat} {a b : Expr}
    (h : propIrrelFueled mode eager env fuel d a b = .ok true) :
    (isProofFast env.find? env.findTable? a = true ∧ isProofFast env.find? env.findTable? b = true) ∨
    ∃ ta sta uT tb stb vT,
      inferTypeIO mode eager env fuel d a = .ok ta ∧
      inferTypeIO mode eager env fuel d ta = .ok sta ∧
      whnf mode eager env fuel d sta = .ok (.sort uT) ∧
      Level.isEquiv uT .zero = some true ∧
      inferTypeIO mode eager env fuel d b = .ok tb ∧
      inferTypeIO mode eager env fuel d tb = .ok stb ∧
      whnf mode eager env fuel d stb = .ok (.sort vT) ∧
      Level.isEquiv vT .zero = some true := by
  dsimp only [propIrrelFueled] at h
  simp only [propIrrel, Bind.bind, Except.bind] at h
  simp only [inferTypeIO_def, whnf_def] at h
  split at h
  · simp [pure, Except.pure] at h
  split at h
  · next hc =>
    simp only [Bool.and_eq_true] at hc
    exact Or.inl ⟨hc.1, hc.2⟩
  refine Or.inr ?_
  cases hta : inferTypeIO mode eager env fuel d a with
  | error err => rw [hta] at h; exact nomatch h
  | ok ta =>
  rw [hta] at h
  dsimp only at h
  cases hsta : inferTypeIO mode eager env fuel d ta with
  | error err => rw [hsta] at h; exact nomatch h
  | ok sta =>
  rw [hsta] at h
  dsimp only at h
  cases hwta : whnf mode eager env fuel d sta with
  | error err => rw [hwta] at h; exact nomatch h
  | ok wta =>
  rw [hwta] at h
  match wta, h with
  | .sort uT, h => ?_
  | .bvar i2, h => exact nomatch h
  | .fvar i2 t2, h => exact nomatch h
  | .const n2 us2, h => exact nomatch h
  | .app f2 a2, h => exact nomatch h
  | .lam t2 b2, h => exact nomatch h
  | .forallE t2 b2, h => exact nomatch h
  | .letE t2 v2 b2, h => exact nomatch h
  | .lit l2, h => exact nomatch h
  | .proj s2 i2 e3, h => exact nomatch h
  dsimp only at h
  cases heq1 : Level.isEquiv uT .zero with
  | none => rw [heq1] at h; simp [liftFueled] at h
  | some okA =>
  rw [heq1] at h
  try dsimp only [liftFueled] at h
  try simp only [Bind.bind, Except.bind, pure, Except.pure] at h
  try dsimp only at h
  cases htb : inferTypeIO mode eager env fuel d b with
  | error err => rw [htb] at h; exact nomatch h
  | ok tb =>
  rw [htb] at h
  dsimp only at h
  cases hstb : inferTypeIO mode eager env fuel d tb with
  | error err => rw [hstb] at h; exact nomatch h
  | ok stb =>
  rw [hstb] at h
  dsimp only at h
  cases hwtb : whnf mode eager env fuel d stb with
  | error err => rw [hwtb] at h; exact nomatch h
  | ok wtb =>
  rw [hwtb] at h
  match wtb, h with
  | .sort vT, h => ?_
  | .bvar i2, h => exact nomatch h
  | .fvar i2 t2, h => exact nomatch h
  | .const n2 us2, h => exact nomatch h
  | .app f2 a2, h => exact nomatch h
  | .lam t2 b2, h => exact nomatch h
  | .forallE t2 b2, h => exact nomatch h
  | .letE t2 v2 b2, h => exact nomatch h
  | .lit l2, h => exact nomatch h
  | .proj s2 i2 e3, h => exact nomatch h
  dsimp only at h
  cases heq2 : Level.isEquiv vT .zero with
  | none => rw [heq2] at h; simp [liftFueled] at h
  | some okB =>
  rw [heq2] at h
  try dsimp only [liftFueled] at h
  try simp only [pure, Except.pure, Except.ok.injEq] at h
  obtain ⟨rfl, rfl⟩ : okA = true ∧ okB = true := by
    have := h
    cases okA <;> cases okB <;> simp_all
  exact ⟨ta, sta, uT, tb, stb, vT, rfl, hsta, hwta, heq1, rfl, hstb, hwtb, heq2⟩

/-- Inversion of a successful proof-irrelevance certification: both
types' sorts are `Prop`. -/
theorem proofIrrel_inv {env : Env} {fuel d : Nat} {a b : Expr}
    (h : proofIrrelFueled mode eager env fuel d a b = .ok true) :
    ∃ ta sta uT tb stb vT,
      inferTypeIO mode eager env fuel d a = .ok ta ∧
      inferTypeIO mode eager env fuel d ta = .ok sta ∧
      whnf mode eager env fuel d sta = .ok (.sort uT) ∧
      Level.isEquiv uT .zero = some true ∧
      inferTypeIO mode eager env fuel d b = .ok tb ∧
      inferTypeIO mode eager env fuel d tb = .ok stb ∧
      whnf mode eager env fuel d stb = .ok (.sort vT) ∧
      Level.isEquiv vT .zero = some true := by
  dsimp only [proofIrrelFueled] at h
  simp only [proofIrrel, Bind.bind, Except.bind] at h
  simp only [inferTypeIO_def, whnf_def] at h
  cases hta : inferTypeIO mode eager env fuel d a with
  | error err => rw [hta] at h; exact nomatch h
  | ok ta =>
  rw [hta] at h
  dsimp only at h
  cases hsta : inferTypeIO mode eager env fuel d ta with
  | error err => rw [hsta] at h; exact nomatch h
  | ok sta =>
  rw [hsta] at h
  dsimp only at h
  cases hwta : whnf mode eager env fuel d sta with
  | error err => rw [hwta] at h; exact nomatch h
  | ok wta =>
  rw [hwta] at h
  match wta, h with
  | .sort uT, h => ?_
  | .bvar i2, h => exact nomatch h
  | .fvar i2 t2, h => exact nomatch h
  | .const n2 us2, h => exact nomatch h
  | .app f2 a2, h => exact nomatch h
  | .lam t2 b2, h => exact nomatch h
  | .forallE t2 b2, h => exact nomatch h
  | .letE t2 v2 b2, h => exact nomatch h
  | .lit l2, h => exact nomatch h
  | .proj s2 i2 e3, h => exact nomatch h
  dsimp only at h
  cases heq1 : Level.isEquiv uT .zero with
  | none => rw [heq1] at h; simp [liftFueled] at h
  | some okA =>
  rw [heq1] at h
  try dsimp only [liftFueled] at h
  try simp only [Bind.bind, Except.bind, pure, Except.pure] at h
  try dsimp only at h
  cases htb : inferTypeIO mode eager env fuel d b with
  | error err => rw [htb] at h; exact nomatch h
  | ok tb =>
  rw [htb] at h
  dsimp only at h
  cases hstb : inferTypeIO mode eager env fuel d tb with
  | error err => rw [hstb] at h; exact nomatch h
  | ok stb =>
  rw [hstb] at h
  dsimp only at h
  cases hwtb : whnf mode eager env fuel d stb with
  | error err => rw [hwtb] at h; exact nomatch h
  | ok wtb =>
  rw [hwtb] at h
  match wtb, h with
  | .sort vT, h => ?_
  | .bvar i2, h => exact nomatch h
  | .fvar i2 t2, h => exact nomatch h
  | .const n2 us2, h => exact nomatch h
  | .app f2 a2, h => exact nomatch h
  | .lam t2 b2, h => exact nomatch h
  | .forallE t2 b2, h => exact nomatch h
  | .letE t2 v2 b2, h => exact nomatch h
  | .lit l2, h => exact nomatch h
  | .proj s2 i2 e3, h => exact nomatch h
  dsimp only at h
  cases heq2 : Level.isEquiv vT .zero with
  | none => rw [heq2] at h; simp [liftFueled] at h
  | some okB =>
  rw [heq2] at h
  try dsimp only [liftFueled] at h
  try simp only [pure, Except.pure, Except.ok.injEq] at h
  obtain ⟨rfl, rfl⟩ : okA = true ∧ okB = true := by
    have := h
    cases okA <;> cases okB <;> simp_all
  exact ⟨ta, sta, uT, tb, stb, vT, rfl, hsta, hwta, heq1, rfl, hstb, hwtb, heq2⟩

/-- `andRescueSlots`, unpacked: both of `And`'s slots are stored tower
entries naming the rule's constructor at the major's parameter count,
two fields. -/
theorem andRescueSlots_inv {env : Env} {ctor : Name} {nP : Nat}
    (h : andRescueSlots env ctor nP = true) :
    ∀ j, j < 2 → ∃ e : ProjEntry, env.findProj? andName j = some e ∧
      e.ctor = ctor ∧ e.numParams = nP ∧ e.numFields = 2 := by
  intro j hj
  have := List.all_eq_true.mp h j (List.mem_range.mpr hj)
  revert this
  cases env.findProj? andName j with
  | none => intro h; exact nomatch h
  | some e =>
    intro hb
    simp only [Bool.and_eq_true, beq_iff_eq] at hb
    exact ⟨e, rfl, hb.1.1, hb.1.2, hb.2⟩

set_option maxHeartbeats 3200000 in
/-- Inversion of a successful structural eta certification. -/
theorem structEtaCertWith_inv {env : Env} {fuel d : Nat} {a b wtb : Expr}
    (h : structEtaCertWithFueled mode eager env fuel d a b wtb = .ok true) :
    ∃ (c : Name) (us : List Level) (cvc : ConstantVal) (cnP cnF : Nat) (cT : Name)
      (T : Name) (us' : List Level)
      (cvT : ConstantVal) (caps : IndCaps) (tbl : ProjTable),
      a.getAppFn = .const c us ∧
      env.find? c = some (.ctorInfo cvc cnP cnF cT) ∧
      a.getAppArgs.length = cnP + cnF ∧
      wtb.getAppFn = .const T us' ∧
      env.find? T = some (.indInfo cvT caps) ∧
      env.findTable? T = some tbl ∧
      caps.eta = true ∧ tbl.ctor = c ∧
      wtb.getAppArgs.length = tbl.numParams ∧
      us'.length = cvT.levelParams.length ∧
      cvc.levelParams = cvT.levelParams ∧
      Level.isEquivList us us' = some true ∧
      defEqListFueled mode eager env fuel d (a.getAppArgs.take tbl.numParams)
        wtb.getAppArgs = .ok true ∧
      defEqListFueled mode eager env fuel d (a.getAppArgs.drop tbl.numParams)
        (etaProjs T b tbl.numFields) = .ok true := by
  dsimp only [structEtaCertWithFueled] at h
  rw [structEtaCertWith] at h
  simp only [defEqList_fold] at h
  revert h
  match hfn : a.getAppFn with
  | .bvar _ => intro h; exact nomatch h
  | .fvar _ _ => intro h; exact nomatch h
  | .sort _ => intro h; exact nomatch h
  | .app _ _ => intro h; exact nomatch h
  | .lam _ _ => intro h; exact nomatch h
  | .forallE _ _ => intro h; exact nomatch h
  | .letE _ _ _ => intro h; exact nomatch h
  | .lit _ => intro h; exact nomatch h
  | .proj _ _ _ => intro h; exact nomatch h
  | .const c us => ?_
  intro h
  dsimp only at h
  revert h
  match hfc : env.find? c with
  | none => intro h; exact nomatch h
  | some (.axiomInfo _) => intro h; exact nomatch h
  | some (.defnInfo _ _ _) => intro h; exact nomatch h
  | some (.thmInfo _) => intro h; exact nomatch h
  | some (.indInfo _ _) => intro h; exact nomatch h
  | some (.recInfo _ _ _ _ _) => intro h; exact nomatch h
  | some (.ctorInfo cvc cnP cnF cT) => ?_
  intro h
  dsimp only at h
  by_cases hal : a.getAppArgs.length = cnP + cnF
  case neg => rw [ite_eq_right hal] at h; exact nomatch h
  rw [ite_eq_left hal] at h
  revert h
  match hwfn : wtb.getAppFn with
  | .bvar _ => intro h; exact nomatch h
  | .fvar _ _ => intro h; exact nomatch h
  | .sort _ => intro h; exact nomatch h
  | .app _ _ => intro h; exact nomatch h
  | .lam _ _ => intro h; exact nomatch h
  | .forallE _ _ => intro h; exact nomatch h
  | .letE _ _ _ => intro h; exact nomatch h
  | .lit _ => intro h; exact nomatch h
  | .proj _ _ _ => intro h; exact nomatch h
  | .const T us' => ?_
  intro h
  dsimp only at h
  revert h
  match hfT : env.find? T with
  | none => intro h; exact nomatch h
  | some (.axiomInfo _) => intro h; exact nomatch h
  | some (.defnInfo _ _ _) => intro h; exact nomatch h
  | some (.thmInfo _) => intro h; exact nomatch h
  | some (.ctorInfo _ _ _ _) => intro h; exact nomatch h
  | some (.recInfo _ _ _ _ _) => intro h; exact nomatch h
  | some (.indInfo cvT caps) => ?_
  intro h
  dsimp only at h
  revert h
  cases htbl : env.findTable? T with
  | none => intro h; exact nomatch h
  | some tbl => ?_
  intro h
  dsimp only at h
  by_cases hcond : caps.eta = true ∧ tbl.ctor = c ∧
      wtb.getAppArgs.length = tbl.numParams ∧
      us'.length = cvT.levelParams.length ∧
      cvc.levelParams = cvT.levelParams
  case neg => rw [ite_eq_right hcond] at h; exact nomatch h
  rw [ite_eq_left hcond] at h
  obtain ⟨he1, he2, he6, he7, he8⟩ := hcond
  try simp only [Bind.bind, Except.bind] at h
  cases hlev : Level.isEquivList us us' with
  | none => rw [hlev] at h; simp [liftFueled] at h
  | some okL => ?_
  rw [hlev] at h
  try dsimp only [liftFueled] at h
  try simp only [Bind.bind, Except.bind, pure, Except.pure] at h
  cases okL with
  | false => simp at h
  | true => ?_
  simp only [↓reduceIte] at h
  cases hd1 : defEqListFueled mode eager env fuel d (a.getAppArgs.take tbl.numParams)
      wtb.getAppArgs with
  | error e => rw [hd1] at h; exact nomatch h
  | ok r₃ => ?_
  rw [hd1] at h
  try dsimp only at h
  cases r₃ with
  | false => simp [pure, Except.pure] at h
  | true => ?_
  simp only [↓reduceIte] at h
  exact ⟨c, us, cvc, cnP, cnF, cT, T, us', cvT, caps, tbl,
    rfl, hfc, hal, rfl, hfT, htbl, he1, he2, he6, he7, he8, hlev, hd1, h⟩

/-- Inversion of the fully-applied structure-eta certificate through its
type reduction: the stuck side's type is inferred and reduced, and the
`With` form of the certificate ran on the result. -/
theorem structEtaFull_inv {env : Env} {fuel d : Nat} {a b : Expr}
    (h : structEtaFullFueled mode eager env fuel d a b = .ok true) :
    ∃ tb wtb, inferTypeIO mode eager env fuel d b = .ok tb ∧
      whnf mode eager env fuel d tb = .ok wtb ∧
      structEtaCertWithFueled mode eager env fuel d a b wtb = .ok true := by
  dsimp only [structEtaFullFueled] at h
  rw [structEtaFull] at h
  split at h
  case isFalse => exact nomatch h
  simp only [Bind.bind, Except.bind] at h
  simp only [inferTypeIO_def, whnf_def, structEtaCertWith_fold] at h
  cases htb : inferTypeIO mode eager env fuel d b with
  | error e => rw [htb] at h; exact nomatch h
  | ok tb =>
  rw [htb] at h
  dsimp only at h
  cases hwtb : whnf mode eager env fuel d tb with
  | error e => rw [hwtb] at h; exact nomatch h
  | ok wtb =>
  rw [hwtb] at h
  dsimp only at h
  exact ⟨tb, wtb, rfl, hwtb, h⟩

/-- Inversion of the η-expansion at `k + 1`: a `∀` whose opened body
carries the expansion one level down. -/
theorem structEtaExpand_succ_inv {env : Env} {fuel k d : Nat} {a b t : Expr}
    (h : structEtaExpandFueled mode eager env fuel (k + 1) d a b t = .ok true) :
    ∃ dom body, t = .forallE dom body ∧
      structEtaExpandFueled mode eager env fuel k (d + 1) (.app a (.fvar d dom))
        (.app b (.fvar d dom)) (body.instantiate1 (.fvar d dom)) = .ok true := by
  dsimp only [structEtaExpandFueled] at h
  cases t with
  | forallE dom body => exact ⟨dom, body, rfl, by rw [structEtaExpand] at h; exact h⟩
  | _ => simp [structEtaExpand, pure, Except.pure] at h

/-- A partially applied constructor is neutral: its head is a constant. -/
theorem ioNeutral_of_etaCtorPartial {env : Env} {a : Expr} {k : Nat}
    (h : etaCtorPartial env a = some k) : a.ioNeutral = true := by
  unfold etaCtorPartial at h
  unfold Expr.ioNeutral
  revert h
  cases a.getAppFn <;> intro h <;> first | rfl | exact nomatch h

/-- Inversion of the structure-eta certificate: the fully applied
certificate, or the partial arm — a neutral other side, the two
io-inferred types compared, and the η-expansion along the constructor
side's type. -/
theorem structEtaCert_inv {env : Env} {fuel d : Nat} {a b : Expr}
    (h : structEtaCertFueled mode eager env fuel d a b = .ok true) :
    structEtaFullFueled mode eager env fuel d a b = .ok true ∨
      ∃ k ta tb, a.ioNeutral = true ∧ b.ioNeutral = true ∧
        inferTypeIO mode eager env fuel d a = .ok ta ∧
        inferTypeIO mode eager env fuel d b = .ok tb ∧
        isDefEqCore mode eager env fuel d tb ta = .ok true ∧
        structEtaExpandFueled mode eager env fuel k d a b ta = .ok true := by
  dsimp only [structEtaCertFueled] at h
  rw [structEtaCert] at h
  split at h
  case isTrue => exact Or.inl h
  revert h
  cases hp : etaCtorPartial env a with
  | none => intro h; exact nomatch h
  | some k =>
  intro h
  dsimp only at h
  have hna := ioNeutral_of_etaCtorPartial hp
  cases hn : b.ioNeutral with
  | false => simp [hn, pure, Except.pure] at h
  | true =>
  simp only [hn, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
  simp only [Bind.bind, Except.bind] at h
  simp only [inferTypeIO_def, defeq_def, structEtaExpand_fold] at h
  cases hta : inferTypeIO mode eager env fuel d a with
  | error e => rw [hta] at h; exact nomatch h
  | ok ta =>
  rw [hta] at h
  dsimp only at h
  cases htb : inferTypeIO mode eager env fuel d b with
  | error e => rw [htb] at h; exact nomatch h
  | ok tb =>
  rw [htb] at h
  dsimp only at h
  cases hde : isDefEqCore mode eager env fuel d tb ta with
  | error e => rw [hde] at h; exact nomatch h
  | ok v =>
  rw [hde] at h
  cases v with
  | false => simp [pure, Except.pure] at h
  | true => exact Or.inr ⟨k, ta, tb, hna, rfl, rfl, rfl, hde, h⟩

/-- Inversion of the proposition test (official's `is_prop`). -/
theorem isPropType_inv {env : Env} {fuel d : Nat} {T : Expr}
    (h : isPropTypeFueled mode eager env fuel d T = .ok true) :
    ∃ tt u, inferTypeIO mode eager env fuel d T = .ok tt ∧
      whnf mode eager env fuel d tt = .ok (.sort u) ∧
      Level.isEquiv u .zero = some true := by
  dsimp only [isPropTypeFueled] at h
  simp only [isPropType, Bind.bind, Except.bind, inferTypeIO_def, whnf_def] at h
  cases htt : inferTypeIO mode eager env fuel d T with
  | error e => rw [htt] at h; exact nomatch h
  | ok tt =>
  rw [htt] at h
  dsimp only at h
  cases hw : whnf mode eager env fuel d tt with
  | error e => rw [hw] at h; exact nomatch h
  | ok w =>
  rw [hw] at h
  cases w with
  | sort u =>
    refine ⟨tt, u, rfl, hw, ?_⟩
    dsimp only at h
    cases hu : Level.isEquiv u .zero with
    | none => rw [hu] at h; exact nomatch h
    | some v =>
      rw [hu] at h
      simp only [liftFueled, pure, Except.pure, Except.ok.injEq] at h
      rw [h]
  | _ => exact nomatch h

/-- Inversion of the field loop of the unit-like test, one field. -/
theorem unitLikeFields_succ_inv {env : Env} {fuel n d : Nat} {t : Expr}
    {ul : Nat → Expr → CheckM Bool}
    (h : unitLikeFields (pureFns mode eager env fuel) ul (n + 1) d t = .ok true) :
    ∃ dom body, t = .forallE dom body ∧
      (isPropTypeFueled mode eager env fuel d dom = .ok true ∨ ul d dom = .ok true) ∧
      unitLikeFields (pureFns mode eager env fuel) ul n (d + 1)
        (body.instantiate1 (.fvar d dom)) = .ok true := by
  cases t with
  | forallE dom body =>
    refine ⟨dom, body, rfl, ?_⟩
    rw [unitLikeFields] at h
    simp only [Bind.bind, Except.bind, isPropType_fold] at h
    cases hp : isPropTypeFueled mode eager env fuel d dom with
    | error e => rw [hp] at h; exact nomatch h
    | ok p =>
    rw [hp] at h
    cases p with
    | true =>
      simp only [↓reduceIte] at h
      exact ⟨Or.inl rfl, h⟩
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h
      cases hu : ul d dom with
      | error e => rw [hu] at h; exact nomatch h
      | ok v =>
      rw [hu] at h
      cases v with
      | false => simp [pure, Except.pure] at h
      | true => exact ⟨Or.inr rfl, h⟩
  | _ => simp [unitLikeFields, pure, Except.pure] at h

/-- Inversion of the structure arm of the unit-like test: an η family
whose field telescope passes the field loop. -/
theorem unitLikeStruct_inv {env : Env} {fuel d : Nat} {w : Expr}
    {ul : Nat → Expr → CheckM Bool}
    (h : unitLikeStruct (pureFns mode eager env fuel) ul env d w = .ok true) :
    ∃ tele n, unitLikeShape env w = some (tele, n) ∧
      unitLikeFields (pureFns mode eager env fuel) ul n d tele = .ok true := by
  unfold unitLikeStruct at h
  revert h
  split
  · rename_i tele n hsh; intro h; exact ⟨tele, n, hsh, h⟩
  · intro h; exact nomatch h

/-- Inversion of a successful unit-like test at `f + 1`: the reduct is
a `∀` whose opened codomain is unit-like one level down, or no `∀` and
passes the structure arm. -/
theorem unitLikeLoop_succ_inv {env : Env} {fuel f d : Nat} {T : Expr}
    (h : unitLikeLoopFueled mode eager env fuel (f + 1) d T = .ok true) :
    ∃ w, whnf mode eager env fuel d T = .ok w ∧
      ((∃ dom body, w = .forallE dom body ∧
          unitLikeLoopFueled mode eager env fuel f (d + 1)
            (body.instantiate1 (.fvar d dom)) = .ok true) ∨
        unitLikeStruct (pureFns mode eager env fuel)
          (unitLikeLoopFueled mode eager env fuel f) env d w = .ok true) := by
  dsimp only [unitLikeLoopFueled] at h
  rw [unitLikeLoop] at h
  simp only [Bind.bind, Except.bind, whnf_def] at h
  cases hw : whnf mode eager env fuel d T with
  | error e => rw [hw] at h; exact nomatch h
  | ok w =>
  rw [hw] at h
  dsimp only at h
  refine ⟨w, rfl, ?_⟩
  cases w with
  | forallE dom body => exact Or.inl ⟨dom, body, rfl, h⟩
  | _ => exact Or.inr h

/-- Inversion of a successful unit-likeness certification. -/
theorem structUnitCert_inv {env : Env} {fuel d : Nat} {a b : Expr}
    (h : structUnitCertFueled mode eager env fuel d a b = .ok true) :
    ∃ (ta wta tb wtb : Expr),
      inferTypeIO mode eager env fuel d a = .ok ta ∧
      whnf mode eager env fuel d ta = .ok wta ∧
      (wta.isForallE = true → a.ioNeutral = true) ∧
      unitLikeLoopFueled mode eager env fuel unitLikeFuel d wta = .ok true ∧
      inferTypeIO mode eager env fuel d b = .ok tb ∧
      whnf mode eager env fuel d tb = .ok wtb ∧
      (wtb.isForallE = true → b.ioNeutral = true) ∧
      isDefEqCore mode eager env fuel d wta wtb = .ok true := by
  dsimp only [structUnitCertFueled] at h
  rw [structUnitCert] at h
  simp only [Bind.bind, Except.bind] at h
  simp only [inferTypeIO_def, whnf_def, defeq_def, unitLikeLoop_fold] at h
  cases hta : inferTypeIO mode eager env fuel d a with
  | error e => rw [hta] at h; exact nomatch h
  | ok ta => ?_
  rw [hta] at h
  try dsimp only at h
  cases hwta : whnf mode eager env fuel d ta with
  | error e => rw [hwta] at h; exact nomatch h
  | ok wta => ?_
  rw [hwta] at h
  try dsimp only at h
  have hA : wta.isForallE = true → a.ioNeutral = true := by
    intro hF
    cases hn : a.ioNeutral with
    | true => rfl
    | false => simp [hF, hn, pure, Except.pure] at h
  have hA' : (wta.isForallE && !a.ioNeutral) = false := by
    cases hF : wta.isForallE with
    | false => rfl
    | true => simp [hA hF]
  simp only [hA', Bool.false_eq_true, ↓reduceIte] at h
  cases hu : unitLikeLoopFueled mode eager env fuel unitLikeFuel d wta with
  | error e => rw [hu] at h; exact nomatch h
  | ok u => ?_
  rw [hu] at h
  cases u with
  | false => simp [pure, Except.pure] at h
  | true => ?_
  simp only [↓reduceIte] at h
  cases htb : inferTypeIO mode eager env fuel d b with
  | error e => rw [htb] at h; exact nomatch h
  | ok tb => ?_
  rw [htb] at h
  try dsimp only at h
  cases hwtb : whnf mode eager env fuel d tb with
  | error e => rw [hwtb] at h; exact nomatch h
  | ok wtb => ?_
  rw [hwtb] at h
  try dsimp only at h
  have hB : wtb.isForallE = true → b.ioNeutral = true := by
    intro hF
    cases hn : b.ioNeutral with
    | true => rfl
    | false => simp [hF, hn, pure, Except.pure] at h
  have hB' : (wtb.isForallE && !b.ioNeutral) = false := by
    cases hF : wtb.isForallE with
    | false => rfl
    | true => simp [hB hF]
  simp only [hB', Bool.false_eq_true, ↓reduceIte] at h
  exact ⟨ta, wta, tb, wtb, rfl, hwta, hA, hu, rfl, hwtb, hB, h⟩

/-- Inversion of a successful eta certification. -/
theorem etaCert_inv {env : Env} {fuel d : Nat} {ty₁ body₁ b : Expr}
    (h : etaCertFueled mode eager env fuel d ty₁ body₁ b = .ok true) :
    b.ioNeutral = true ∧ ∃ tb ty₂ fb,
      inferTypeIO mode eager env fuel d b = .ok tb ∧
      whnf mode eager env fuel d tb = .ok (.forallE ty₂ fb) ∧
      isDefEqCore mode eager env fuel d ty₂ ty₁ = .ok true ∧
      isDefEqCore mode eager env fuel (d + 1) (body₁.instantiate1 (.fvar d ty₁))
        (.app b (.fvar d ty₁)) = .ok true ∧
      (mode.verifiedChecks = true → ∃ t₁,
        inferTypeCore mode eager env fuel (d + 1) (body₁.instantiate1 (.fvar d ty₁)) = .ok t₁ ∧
        isDefEqCore mode eager env fuel (d + 1) t₁ (fb.instantiate1 (.fvar d ty₁)) = .ok true) := by
  dsimp only [etaCertFueled] at h
  simp only [etaCert, Bind.bind, Except.bind] at h
  simp only [inferTypeIO_def, whnf_def, defeq_def, infer_def] at h
  cases hneu : b.ioNeutral with
  | false => simp [hneu, pure, Except.pure] at h
  | true =>
  simp only [hneu, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
  refine ⟨rfl, ?_⟩
  cases htb : inferTypeIO mode eager env fuel d b with
  | error err => rw [htb] at h; exact nomatch h
  | ok tb =>
  rw [htb] at h
  dsimp only at h
  cases hwtb : whnf mode eager env fuel d tb with
  | error err => rw [hwtb] at h; exact nomatch h
  | ok wtb =>
  rw [hwtb] at h
  match wtb, h with
  | .forallE ty₂ fb, h => ?_
  | .bvar i2, h => exact nomatch h
  | .fvar i2 t2, h => exact nomatch h
  | .sort u2, h => exact nomatch h
  | .const n2 us2, h => exact nomatch h
  | .app f2 a2, h => exact nomatch h
  | .lam t2 b2, h => exact nomatch h
  | .letE t2 v2 b2, h => exact nomatch h
  | .lit l2, h => exact nomatch h
  | .proj s2 i2 e3, h => exact nomatch h
  dsimp only at h
  cases hd1 : isDefEqCore mode eager env fuel d ty₂ ty₁ with
  | error err => rw [hd1] at h; exact nomatch h
  | ok r₁ =>
  rw [hd1] at h
  dsimp only at h
  cases r₁ with
  | false => simp [pure, Except.pure] at h
  | true =>
  simp only [↓reduceIte] at h
  cases hd2 : isDefEqCore mode eager env fuel (d + 1)
      (body₁.instantiate1 (.fvar d ty₁)) (.app b (.fvar d ty₁)) with
  | error err => rw [hd2] at h; exact nomatch h
  | ok r₂ =>
  rw [hd2] at h
  dsimp only at h
  cases r₂ with
  | false => simp [pure, Except.pure] at h
  | true =>
  simp only [↓reduceIte] at h
  refine ⟨tb, ty₂, fb, rfl, hwtb, hd1, rfl, ?_⟩
  intro hv
  rw [hv] at h
  simp only [↓reduceIte] at h
  cases ht : inferTypeCore mode eager env fuel (d + 1) (body₁.instantiate1 (.fvar d ty₁)) with
  | error err => simp [ht] at h
  | ok t₁ =>
  cases hd3 : isDefEqCore mode eager env fuel (d + 1) t₁ (fb.instantiate1 (.fvar d ty₁)) with
  | error err => simp [ht, hd3] at h
  | ok r₃ =>
  cases r₃ with
  | false => simp [ht, hd3, pure, Except.pure] at h
  | true => exact ⟨t₁, rfl, hd3⟩

/-- Inversion for the projection rule of `inferTypeCore`: the subject's
type whnfs to a type application whose head has a native
projection-table entry, and the result is the entry type's residual
along the arguments and the subject. -/
theorem inferTypeCore_proj_inv {env : Env} {fuel d : Nat} {sn : Name} {i : Nat}
    {e t : Expr}
    (h : inferTypeCore mode eager env (fuel + 1) d (.proj sn i e) = .ok t) :
    ∃ tpe te T us entry,
      inferTypeCore mode eager env fuel d e = .ok tpe ∧
      whnf mode eager env fuel d tpe = .ok te ∧
      te.getAppFn = .const T us ∧
      env.findProj? T i = some entry ∧
      te.getAppArgs.length = entry.numParams ∧
      us.length = entry.levelParams.length ∧
      -- the official `infer_proj` restriction, at this use
      checkProjGuard (pureFns mode eager env fuel).inferIO (pureFns mode eager env fuel).whnf
        env entry us = .ok () ∧
      -- task #175 S1: the returned type is the entry's body at the
      -- spine and the subject (`ProjEntry.typeAt`)
      (t = entry.typeAt us te.getAppArgs e ∧
       -- task #175 wiring W5: the node's struct name is the head's
       T = sn) := by
  rw [inferTypeCore_succ] at h
  simp only [inferBody, pure, Except.pure, Bind.bind, Except.bind] at h
  simp only [infer_def, whnf_def] at h
  cases hte : inferTypeCore mode eager env fuel d e with
  | error err => rw [hte] at h; exact nomatch h
  | ok tpe =>
  rw [hte] at h
  dsimp only at h
  cases hw : whnf mode eager env fuel d tpe with
  | error err => rw [hw] at h; exact nomatch h
  | ok te =>
  rw [hw] at h
  dsimp only at h
  revert h
  cases hfn : te.getAppFn with
  | const T us => ?_
  | bvar i2 => intro h; exact nomatch h
  | sort u => intro h; exact nomatch h
  | fvar i2 t2 => intro h; exact nomatch h
  | app f2 a2 => intro h; exact nomatch h
  | lam t2 b2 => intro h; exact nomatch h
  | forallE t2 b2 => intro h; exact nomatch h
  | letE t2 v2 b2 => intro h; exact nomatch h
  | lit l2 => intro h; exact nomatch h
  | proj s2 i2 e2 => intro h; exact nomatch h
  intro h
  dsimp only at h
  revert h
  cases hfp : env.findProj? T i with
  | none => intro h; exact nomatch h
  | some entry => ?_
  intro h
  dsimp only at h
  split at h
  case isFalse => exact nomatch h
  case isTrue hcond =>
    obtain ⟨hsn, hlen, hus⟩ := hcond
    -- the guard at this use, then the residual walk's result
    cases hg : checkProjGuard (pureFns mode eager env fuel).inferIO
        (pureFns mode eager env fuel).whnf env entry us with
    | error err => rw [hg] at h; exact nomatch h
    | ok _ =>
      rw [hg] at h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      exact ⟨tpe, te, T, us, entry, rfl, hw, hfn, hfp, hlen, hus,
        hg, h.symm, hsn⟩

/-! ## The tower-entry helpers (task #175 wiring W2c)

Shared by the inversion's consumers: the stored entry type is a stored
constant's closed type, and `instPisAt` preserves scoping.
(`instPisAt_WScoped` moved here from `BridgeWfImp` so the leaf modules
can reach it.) -/

/-- A stored projection entry's body is well-formed (`EnvWF`'s table
clause at the view, task #175 S1): fvar-free, level-defined,
resolving, scoped at the parameters and the subject. -/
theorem projEntry_body_wf {env : Env} (henv : EnvWF env) {T : Name}
    {i : Nat} {entry : ProjEntry} (hf : env.findProj? T i = some entry) :
    entry.body.hasFvar = false ∧
    entry.body.allLevelParamsDefined entry.levelParams = true ∧
    entry.body.constsResolve env = true ∧
    entry.body.looseBVarsBounded (entry.numParams + 1) = true := by
  obtain ⟨tbl, hf', hi, rfl⟩ := Env.findProj?_some hf
  obtain ⟨-, hsize, hb⟩ := henv.table hf'
  have hlt : i < tbl.bodies.size := by rw [hsize]; exact hi
  have := hb i (tbl.bodies[i]'hlt) (Array.getElem?_eq_getElem hlt)
  simp only [ProjTable.entry_body, ProjTable.entry_levelParams, ProjTable.entry_numParams]
  rw [Array.getD, dite_eq_left hlt]
  exact this

/-- The level-instantiated body has no fvars. -/
theorem projEntry_body_hasFvar {env : Env} (henv : EnvWF env) {T : Name}
    {i : Nat} {entry : ProjEntry} (hf : env.findProj? T i = some entry)
    (us : List Level) :
    (entry.body.instantiateLevelParams entry.levelParams us).hasFvar = false := by
  rw [Expr.hasFvar_instantiateLevelParams]
  exact (projEntry_body_wf henv hf).1

/-- The level-instantiated body is scoped at the parameters and the
subject. -/
theorem projEntry_body_looseBVars {env : Env} (henv : EnvWF env) {T : Name}
    {i : Nat} {entry : ProjEntry} (hf : env.findProj? T i = some entry)
    (us : List Level) :
    (entry.body.instantiateLevelParams entry.levelParams us).looseBVarsBounded
      (entry.numParams + 1) = true := by
  rw [Expr.looseBVarsBounded_instantiateLevelParams]
  exact (projEntry_body_wf henv hf).2.2.2

/-- **The projection's type is the instantiation spine of the body**
(task #175 S1): `ProjEntry.typeAt`'s single `instantiateList` is the
telescope instantiation `instSpine` along the arguments and the
subject, outermost first. -/
theorem ProjEntry.typeAt_eq_instSpine (entry : ProjEntry) (us : List Level)
    {targs : List Expr} (hlen : targs.length = entry.numParams) (pe : Expr) :
    entry.typeAt us targs pe
      = Expr.instSpine (targs ++ [pe]) entry.numParams
          (entry.body.instantiateLevelParams entry.levelParams us) := by
  unfold ProjEntry.typeAt
  rw [Expr.instSpine_eq_instantiateList _ _ _ (by simp [hlen]), List.reverse_append,
    List.reverse_singleton, List.singleton_append]

/-- The projection's type commutes with the shift: the body is
fvar-free, so the shift passes to the spine and the subject. -/
theorem ProjEntry.typeAt_shiftFrom {env : Env} (henv : EnvWF env) {T : Name}
    {i : Nat} {entry : ProjEntry} (hf : env.findProj? T i = some entry)
    (us : List Level) {p : Nat} {targs : List Expr}
    (hlen : targs.length = entry.numParams) (pe : Expr) :
    Expr.shiftFrom p (entry.typeAt us targs pe)
      = entry.typeAt us (targs.map (Expr.shiftFrom p)) (Expr.shiftFrom p pe) := by
  rw [ProjEntry.typeAt_eq_instSpine entry us hlen pe,
    ProjEntry.typeAt_eq_instSpine entry us (by simp [hlen]) _,
    shiftFrom_instSpine, List.map_append,
    shiftFrom_eq_self_of_not_hasFvar (projEntry_body_hasFvar henv hf us)]
  rfl

/-- The projection's type is scoped wherever its arguments are. -/
theorem projEntry_typeAt_WScoped {env : Env} (henv : EnvWF env) {T : Name}
    {i : Nat} {entry : ProjEntry} (hf : env.findProj? T i = some entry)
    (us : List Level) {d : Nat} {targs : List Expr}
    (hlen : targs.length = entry.numParams) {pe : Expr}
    (hargs : ∀ a ∈ targs, WScoped d a) (hpe : WScoped d pe) :
    WScoped d (entry.typeAt us targs pe) := by
  rw [ProjEntry.typeAt_eq_instSpine entry us hlen pe]
  refine instSpine_WScoped _ (WScoped.of_not_hasFvar (projEntry_body_hasFvar henv hf us)) ?_
  intro a ha
  rcases List.mem_append.mp ha with ha | ha
  · exact hargs a ha
  · rw [List.mem_singleton] at ha; subst ha; exact hpe

/-- The projection's type is bvar-closed at bvar-closed arguments. -/
theorem projEntry_typeAt_looseBVars {env : Env} (henv : EnvWF env) {T : Name}
    {i : Nat} {entry : ProjEntry} (hf : env.findProj? T i = some entry)
    (us : List Level) {targs : List Expr}
    (hlen : targs.length = entry.numParams) {pe : Expr}
    (hargs : ∀ a ∈ targs, a.looseBVarsBounded 0 = true)
    (hpe : pe.looseBVarsBounded 0 = true) :
    (entry.typeAt us targs pe).looseBVarsBounded 0 = true := by
  rw [ProjEntry.typeAt_eq_instSpine entry us hlen pe]
  have hl : (targs ++ [pe]).length = entry.numParams + 1 := by simp [hlen]
  have := instSpine_closed (args := targs ++ [pe])
    (e := entry.body.instantiateLevelParams entry.levelParams us)
    (fun a ha => by
      rcases List.mem_append.mp ha with ha | ha
      · exact hargs a ha
      · rw [List.mem_singleton] at ha; subst ha; exact hpe)
    (by rw [hl]; exact projEntry_body_looseBVars henv hf us)
  rw [hl, Nat.add_sub_cancel] at this
  exact this

/-- Instantiating a `∀`-telescope at scoped arguments produces scoped
domains and a scoped residual. -/
theorem instPisAt_WScoped {d : Nat} :
    ∀ (args : List Expr) (ty : Expr) {doms : List Expr} {res : Expr},
      Expr.instPisAt args ty = some (doms, res) → WScoped d ty →
      (∀ a ∈ args, WScoped d a) →
      (∀ x ∈ doms, WScoped d x) ∧ WScoped d res
  | [], ty, doms, res, h, hty, _ => by
    simp only [Expr.instPisAt, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨(fun x hx => nomatch hx), hty⟩
  | a :: as, ty, doms, res, h, hty, hargs => by
    cases ty with
    | forallE dom body =>
      simp only [Expr.instPisAt] at h
      revert h
      cases hrec : Expr.instPisAt as (body.instantiate1 a) with
      | none => intro h; exact nomatch h
      | some p =>
        obtain ⟨ds, rest⟩ := p
        intro h
        simp only [Option.map_some, Option.some.injEq,
          Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp only [WScoped] at hty
        obtain ⟨hdom, hbody⟩ := hty
        have hinst : WScoped d (body.instantiate1 a) :=
          WScoped.instantiate1_gen (hargs a List.mem_cons_self) 0 hbody
        obtain ⟨hds, hres⟩ := instPisAt_WScoped as _ hrec hinst
          (fun x hx => hargs x (List.mem_cons_of_mem _ hx))
        exact ⟨fun x hx => by
          rcases List.mem_cons.mp hx with rfl | hx
          · exact hdom
          · exact hds x hx, hres⟩
    | bvar _ | fvar _ _ | sort _ | const _ _ | app _ _ | lam _ _
    | letE _ _ _ | lit _ | proj _ _ _ => exact nomatch h

/-! ## Well-scopedness preservation through reduction -/

/-- The constructor form of a literal is closed. -/
theorem natLitToConstructor_WScoped (n : Nat) {d : Nat} :
    WScoped d (natLitToConstructor n) := by
  cases n <;> simp [natLitToConstructor, WScoped]

/-- Inversion of the literal-major conversion: either the one-layer
`Nat` conversion applied, or the major was a supported string literal
and the result is the reduced constructor form. -/
theorem litMajorToCtorFueled_inv {env : Env} {fuel d : Nat} {e e₁ : Expr}
    (h : litMajorToCtorFueled mode eager env fuel d e = .ok e₁) :
    e₁ = litToCtorIfNat env e ∨
    ∃ s, e = .lit (.strVal s) ∧ strLitStored env = true ∧
      whnf mode eager env fuel d (strLitToConstructor s) = .ok e₁ := by
  match e with
  | .lit (.strVal s) =>
    dsimp only [litMajorToCtorFueled, litMajorToCtor] at h
    revert h
    split
    · intro h
      exact Or.inr ⟨s, rfl, by assumption, h⟩
    · intro h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      exact Or.inl rfl
  | .lit (.natVal n) =>
    simp only [litMajorToCtorFueled, litMajorToCtor, pure, Except.pure,
      Except.ok.injEq] at h
    exact Or.inl h.symm
  | .bvar _ | .fvar _ _ | .sort _ | .const _ _ | .app _ _
  | .lam _ _ | .forallE _ _ | .letE _ _ _ | .proj _ _ _ =>
    simp only [litMajorToCtorFueled, litMajorToCtor, pure, Except.pure,
      Except.ok.injEq] at h
    exact Or.inl h.symm

/-- Inversion of the projection-scrutinee literal conversion: either the
identity, or the scrutinee was a supported string literal and the
result is the reduced constructor form. -/
theorem projLitToCtorFueled_inv {env : Env} {fuel d : Nat} {e e₁ : Expr}
    (h : projLitToCtorFueled mode eager env fuel d e = .ok e₁) :
    e₁ = e ∨
    ∃ s, e = .lit (.strVal s) ∧ strLitStored env = true ∧
      whnf mode eager env fuel d (strLitToConstructor s) = .ok e₁ := by
  match e with
  | .lit (.strVal s) =>
    dsimp only [projLitToCtorFueled, projLitToCtor] at h
    revert h
    split
    · intro h
      exact Or.inr ⟨s, rfl, by assumption, h⟩
    · intro h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      exact Or.inl rfl
  | .lit (.natVal n) =>
    simp only [projLitToCtorFueled, projLitToCtor, pure, Except.pure,
      Except.ok.injEq] at h
    exact Or.inl h.symm
  | .bvar _ | .fvar _ _ | .sort _ | .const _ _ | .app _ _
  | .lam _ _ | .forallE _ _ | .letE _ _ _ | .proj _ _ _ =>
    simp only [projLitToCtorFueled, projLitToCtor, pure, Except.pure,
      Except.ok.injEq] at h
    exact Or.inl h.symm

/-- A predicate passes through a firing projection rule
(`reduceProjCore`) when it passes to an application's arguments,
through `whnf` and to a string literal's constructor form. -/
theorem reduceProjCore_pres {env : Env} {fuel d : Nat} {sn : Name} {i : Nat}
    {c m : Expr} (P : Expr → Prop)
    (hargs : ∀ {x : Expr}, P x → ∀ y ∈ x.getAppArgs, P y)
    (hW : ∀ {x y : Expr}, whnf mode eager env fuel d x = .ok y → P x → P y)
    (hstr : ∀ s, strLitStored env = true → P (strLitToConstructor s))
    (h : reduceProjCoreFueled mode eager env fuel d sn i c = .ok (some m)) (hc : P c) :
    P m := by
  obtain ⟨e₃, us, entry, hlit, -, -, hi, hlen, -, rfl, -⟩ := reduceProjCore_inv h
  have h3 : P e₃ := by
    rcases projLitToCtorFueled_inv hlit with rfl | ⟨s, -, hs, hred⟩
    · exact hc
    · exact hW hred (hstr s hs)
  exact hargs h3 _ (getD_mem (by omega))

/-- The retry's literal reading: the `Nat` one, or a stored `String` literal's constructor form. -/
theorem litToCtor_cases (env : Env) (e : Expr) :
    litToCtor env e = litToCtorIfNat env e ∨
      ∃ s, e = .lit (.strVal s) ∧ strLitStored env = true ∧
        litToCtor env e = strLitToConstructor s := by
  match e with
  | .lit (.strVal s) =>
    by_cases hs : strLitStored env = true
    · exact .inr ⟨s, rfl, hs, by simp only [litToCtor, hs, ↓reduceIte]⟩
    · exact .inl (by simp only [litToCtor, hs, Bool.false_eq_true, ↓reduceIte, litToCtorIfNat])
  | .lit (.natVal n) => exact .inl rfl
  | .bvar _ | .fvar _ _ | .sort _ | .const _ _ | .app _ _ | .lam _ _ | .forallE _ _ | .letE _ _ _
  | .proj _ _ _ => exact .inl rfl

/-- Off `String` literals the retry's reading is the `Nat` one. -/
theorem litToCtor_of_not_str {env : Env} {e : Expr} (h : ∀ s, e ≠ .lit (.strVal s)) :
    litToCtor env e = litToCtorIfNat env e := by
  rcases litToCtor_cases env e with h' | ⟨s, rfl, -, -⟩
  · exact h'
  · exact absurd rfl (h s)

/-- The literal-major conversion preserves well-scopedness. -/
theorem litToCtorIfNat_WScoped {env : Env} {d : Nat} {e : Expr}
    (hw : WScoped d e) : WScoped d (litToCtorIfNat env e) := by
  match e with
  | .lit (.natVal n) =>
    rw [litToCtorIfNat]
    split
    · exact natLitToConstructor_WScoped n
    · exact hw
  | .lit (.strVal _) => exact hw
  | .bvar _ | .fvar _ _ | .sort _ | .const _ _ | .app _ _
  | .lam _ _ | .forallE _ _ | .letE _ _ _ | .proj _ _ _ =>
    exact hw

theorem litToCtor_WScoped {env : Env} {d : Nat} {e : Expr}
    (hw : WScoped d e) : WScoped d (litToCtor env e) := by
  rcases litToCtor_cases env e with h | ⟨s, -, -, h⟩
  · rw [h]; exact litToCtorIfNat_WScoped hw
  · rw [h]; exact strLitToConstructor_WScoped s d

/-- The fast-path reducts are closed atoms. -/
theorem natOpResult_shape {c : Name} {a b : Nat} {e₂ : Expr}
    (h : natOpResult c a b = some e₂) :
    (∃ n, e₂ = .lit (.natVal n)) ∨ (∃ bn, e₂ = .const bn []) := by
  unfold natOpResult at h
  by_cases h1 : c = natPredName
  · rw [ite_eq_left h1] at h
    exact Or.inl ⟨_, (Option.some.inj h).symm⟩
  rw [ite_eq_right h1] at h
  by_cases h2 : c = natAddName
  · rw [ite_eq_left h2] at h
    exact Or.inl ⟨_, (Option.some.inj h).symm⟩
  rw [ite_eq_right h2] at h
  by_cases h3 : c = natSubName
  · rw [ite_eq_left h3] at h
    exact Or.inl ⟨_, (Option.some.inj h).symm⟩
  rw [ite_eq_right h3] at h
  by_cases h4 : c = natMulName
  · rw [ite_eq_left h4] at h
    exact Or.inl ⟨_, (Option.some.inj h).symm⟩
  rw [ite_eq_right h4] at h
  by_cases h5 : c = natPowName
  · rw [ite_eq_left h5] at h
    exact Or.inl ⟨_, (Option.some.inj h).symm⟩
  rw [ite_eq_right h5] at h
  by_cases h6 : c = natDivName
  · rw [ite_eq_left h6] at h
    exact Or.inl ⟨_, (Option.some.inj h).symm⟩
  rw [ite_eq_right h6] at h
  by_cases h7 : c = natModName
  · rw [ite_eq_left h7] at h
    exact Or.inl ⟨_, (Option.some.inj h).symm⟩
  rw [ite_eq_right h7] at h
  by_cases h8 : c = natGcdName
  · rw [ite_eq_left h8] at h
    exact Or.inl ⟨_, (Option.some.inj h).symm⟩
  rw [ite_eq_right h8] at h
  by_cases h9 : c = natLandName
  · rw [ite_eq_left h9] at h
    exact Or.inl ⟨_, (Option.some.inj h).symm⟩
  rw [ite_eq_right h9] at h
  by_cases h10 : c = natLorName
  · rw [ite_eq_left h10] at h
    exact Or.inl ⟨_, (Option.some.inj h).symm⟩
  rw [ite_eq_right h10] at h
  by_cases h11 : c = natXorName
  · rw [ite_eq_left h11] at h
    exact Or.inl ⟨_, (Option.some.inj h).symm⟩
  rw [ite_eq_right h11] at h
  by_cases h12 : c = natShiftLeftName
  · rw [ite_eq_left h12] at h
    exact Or.inl ⟨_, (Option.some.inj h).symm⟩
  rw [ite_eq_right h12] at h
  by_cases h13 : c = natShiftRightName
  · rw [ite_eq_left h13] at h
    exact Or.inl ⟨_, (Option.some.inj h).symm⟩
  rw [ite_eq_right h13] at h
  by_cases h15 : c = natBeqName
  · rw [ite_eq_left h15] at h
    exact Or.inr ⟨_, (Option.some.inj h).symm⟩
  rw [ite_eq_right h15] at h
  by_cases h16 : c = natBleName
  · rw [ite_eq_left h16] at h
    exact Or.inr ⟨_, (Option.some.inj h).symm⟩
  rw [ite_eq_right h16] at h
  exact nomatch h

/-- Literal acceleration produces closed atoms: a literal or a
`Bool`-constant head. -/
theorem reduceNat_inv {env : Env} {fuel d : Nat} {e e₂ : Expr}
    (h : reduceNatFueled mode eager env fuel d e = .ok (some e₂)) :
    (∃ n, e₂ = .lit (.natVal n)) ∨ (∃ bn, e₂ = .const bn []) := by
  dsimp only [reduceNatFueled] at h
  revert h
  match e with
  | .app (.const c []) a => ?_
  | .app (.app (.const c []) a) b => ?_
  | .bvar _ | .fvar _ _ | .sort _ | .lam _ _ | .forallE _ _
  | .letE _ _ _ | .lit _ | .proj _ _ _ | .const _ _ =>
    intro h; simp [reduceNat, pure, Except.pure] at h
  | .app (.bvar _) _ | .app (.fvar _ _) _ | .app (.sort _) _
  | .app (.lam _ _) _ | .app (.forallE _ _) _
  | .app (.letE _ _ _) _ | .app (.lit _) _ | .app (.proj _ _ _) _ =>
    intro h; simp [reduceNat, pure, Except.pure] at h
  | .app (.const c (_ :: _)) _ =>
    intro h; simp [reduceNat, pure, Except.pure] at h
  | .app (.app (.bvar _) _) _ | .app (.app (.fvar _ _) _) _
  | .app (.app (.sort _) _) _ | .app (.app (.app _ _) _) _
  | .app (.app (.lam _ _) _) _ | .app (.app (.forallE _ _) _) _
  | .app (.app (.letE _ _ _) _) _ | .app (.app (.lit _) _) _
  | .app (.app (.proj _ _ _) _) _ =>
    intro h; simp [reduceNat, pure, Except.pure] at h
  | .app (.app (.const c (_ :: _)) _) _ =>
    intro h; simp [reduceNat, pure, Except.pure] at h
  · -- unary heads: `succ` folding or the `pred` fast path
    intro h
    simp only [reduceNat, Bind.bind, Except.bind, whnf_def] at h
    revert h
    split
    · intro h
      revert h
      cases hw0 : whnf mode eager env fuel d a with
      | error err => intro h; exact nomatch h
      | ok a0 =>
      intro h
      dsimp only at h
      revert h
      match rawNatLit? a0 with
      | some n =>
        intro h
        simp only [pure, Except.pure, Except.ok.injEq, Option.some.injEq] at h
        exact Or.inl ⟨n + 1, h.symm⟩
      | none => intro h; simp [pure, Except.pure] at h
    · intro h; simp [pure, Except.pure] at h
  · -- binary fast paths
    intro h
    simp only [reduceNat, Bind.bind, Except.bind, whnf_def] at h
    revert h
    split
    · -- first argument first; the second only behind a literal (D15)
      intro h
      revert h
      cases hw1 : whnf mode eager env fuel d a with
      | error err => intro h; exact nomatch h
      | ok a' =>
      intro h
      dsimp only at h
      revert h
      match rawNatLit? a' with
      | none => intro h; simp [pure, Except.pure] at h
      | some n₁ =>
        intro h
        revert h
        cases hw2 : whnf mode eager env fuel d b with
        | error err => intro h; exact nomatch h
        | ok b' =>
        intro h
        dsimp only at h
        revert h
        match rawNatLit? b' with
        | some n₂ =>
          intro h
          dsimp only at h
          cases hres : natOpResult c n₁ n₂ with
          | none => rw [hres] at h; simp [pure, Except.pure] at h
          | some r =>
            rw [hres] at h
            simp only [pure, Except.pure, Except.ok.injEq,
              Option.some.injEq] at h
            exact h ▸ natOpResult_shape hres
        | none => intro h; simp [pure, Except.pure] at h
    · intro h; simp [pure, Except.pure] at h

/-- The gated unfolding is the raw one where it unfolds. -/
theorem unfoldDefinition_raw {env : Env} {e e₂ : Expr} (h : unfoldDefinition env e = some e₂) :
    unfoldDefinitionRaw env e = some e₂ := by
  unfold unfoldDefinition at h
  unfold unfoldDefinitionRaw
  split at h
  · split at h
    · split at h
      · rename_i hc; rw [ite_eq_left hc.1]; exact h
      · exact nomatch h
    · exact nomatch h
  · exact nomatch h

/-- Unfolding a definition at the head preserves well-scopedness (the
stored value is closed by environment well-formedness). -/
theorem unfoldDefinition_WScoped_raw {env : Env} (henv : EnvWF env)
    {d : Nat} {e e₂ : Expr}
    (h : unfoldDefinitionRaw env e = some e₂) (hw : WScoped d e) :
    WScoped d e₂ := by
  unfold unfoldDefinitionRaw at h
  revert h
  match hfn : e.getAppFn with
  | .const n us => ?_
  | .bvar _ | .fvar _ _ | .sort _ | .app _ _ | .lam _ _
  | .forallE _ _ | .letE _ _ _ | .lit _ | .proj _ _ _ =>
    intro h; exact nomatch h
  intro h
  dsimp only at h
  revert h
  match hf : env.find? n with
  | none => intro h; exact nomatch h
  | some (.axiomInfo _) => intro h; exact nomatch h
  | some (.thmInfo _) => intro h; exact nomatch h
  | some (.indInfo _ _) => intro h; exact nomatch h
  | some (.ctorInfo _ _ _ _) => intro h; exact nomatch h
  | some (.recInfo _ _ _ _ _) => intro h; exact nomatch h
  | some (.defnInfo cv value hint) => ?_
  intro h
  dsimp only at h
  revert h
  split
  · intro h
    simp only [Option.some.injEq] at h
    subst h
    obtain ⟨-, -, -, -, hval, -⟩ := henv.consts _ (Env.find?_mem hf)
    obtain ⟨hvc, -, -, -⟩ := hval cv value hint rfl
    refine Expr.WScoped.mkAppN
      (WScoped.of_not_hasFvar (by
        rw [hasFvar_instantiateLevelParams]; exact hvc)) ?_
    intro x hx
    exact hw.getAppArgs x hx
  · intro h; exact nomatch h


theorem unfoldDefinition_WScoped {env : Env} (henv : EnvWF env)
    {d : Nat} {e e₂ : Expr}
    (h : unfoldDefinition env e = some e₂) (hw : WScoped d e) :
    WScoped d e₂ :=
  unfoldDefinition_WScoped_raw henv (unfoldDefinition_raw h) hw

/-- Peeling a `∀`-telescope along scoped arguments preserves
well-scopedness. -/
theorem piResidual_WScoped {d : Nat} :
    ∀ {as : List Expr} {t res : Expr}, piResidual t as = some res →
      WScoped d t → (∀ x ∈ as, WScoped d x) → WScoped d res
  | [], t, res, h, hw, _ => by
    simp only [piResidual, Option.some.injEq] at h
    exact h ▸ hw
  | a :: as, t, res, h, hw, has => by
    match t, h with
    | .forallE ty body, h =>
      have hw' : WScoped d ty ∧ WScoped d body := by
        simpa only [WScoped] using hw
      have h' : piResidual (body.instantiate1 a) as = some res := h
      exact piResidual_WScoped h'
        (WScoped.instantiate1_gen (has a (List.mem_cons_self ..)) 0 hw'.2)
        (fun x hx => has x (List.mem_cons_of_mem _ hx))

/-- A subterm of the application tree is scoped where the term is. -/
theorem appSubterms_WScoped {d : Nat} (e : Expr) :
    ∀ {x : Expr}, x ∈ appSubterms e → WScoped d e → WScoped d x := by
  induction e with
  | app f a ihf iha =>
    intro x hx hw
    simp only [appSubterms, List.mem_cons, List.mem_append] at hx
    rcases hx with rfl | hx | hx
    · exact hw
    · exact ihf hx (by simp only [WScoped] at hw; exact hw.1)
    · exact iha hx (by simp only [WScoped] at hw; exact hw.2)
  | _ => intro x hx hw; simp only [appSubterms, List.mem_singleton] at hx; subst hx; exact hw

/-- A rule's match keeps well-scopedness where the retry's `whnf` does. -/
theorem MatchPres.wscoped {env : Env} {r : CoreFns CheckM} {d : Nat}
    (hwh : ∀ {a w : Expr}, r.whnf d a = .ok w → WScoped d a → WScoped d w) :
    MatchPres r env d (WScoped d) :=
  ⟨by intro f a; simp only [WScoped], fun hw h => litToCtor_WScoped (hwh hw h)⟩

/-- **A rule's right side is scoped where the term it rewrites is**: the theorem's type is
closed, the arguments are subterms of the term. -/
theorem rewriteAttempt_WScoped {env : Env} (henv : EnvWF env) {r : CoreFns CheckM} {d : Nat}
    (hwh : ∀ {a w : Expr}, r.whnf d a = .ok w → WScoped d a → WScoped d w)
    {e e₂ : Expr} {t : Name} (h : rewriteAttempt r env d e t = .ok (some e₂))
    (hw : WScoped d e) : WScoped d e₂ := by
  obtain ⟨cv, args, us, u, A, c, ls, e₁, _, hf, hm, hres, -, -, hsub, -⟩ :=
    rewriteAttempt_inv h
  have hw₁ := ruleArgsM_pres (MatchPres.wscoped hwh) hm hw
  have hT : WScoped d (cv.type.instantiateLevelParams cv.levelParams us) :=
    WScoped.of_not_hasFvar (by
      rw [hasFvar_instantiateLevelParams]; exact (henv.consts _ (Env.find?_mem hf)).1)
  have hR := piResidual_WScoped hres hT (fun x hx => appSubterms_WScoped e₁ (hsub x hx) hw₁)
  simp only [WScoped] at hR
  exact hR.2

/-- The rewrite step keeps well-scopedness, at the prefix of the rule's arity. -/
theorem rewriteStep_WScoped {env : Env} (henv : EnvWF env) {r : CoreFns CheckM} {d : Nat}
    (hwh : ∀ {a w : Expr}, r.whnf d a = .ok w → WScoped d a → WScoped d w)
    {stuck : Bool} {e e₂ : Expr} {t : Name} (h : rewriteStep r env d stuck e = .ok (some (t, e₂)))
    (hw : WScoped d e) : WScoped d e₂ :=
  rewriteAt_ind (fun x y => WScoped d x → WScoped d y)
    (fun ha => rewriteAttempt_WScoped henv hwh ha)
    (fun hf hw' => by simp only [WScoped] at hw' ⊢; exact ⟨hf hw'.1, hw'.2⟩) e
    (rewriteStep_inv h) hw

/-- The rules fired again keep well-scopedness. -/
theorem fireMore_WScoped {env : Env} (henv : EnvWF env) {r : CoreFns CheckM} {d : Nat}
    (hwh : ∀ {a w : Expr}, r.whnf d a = .ok w → WScoped d a → WScoped d w)
    {k : Nat} {e e' : Expr} (h : fireMore r env d k e = .ok e') (hw : WScoped d e) :
    WScoped d e' :=
  fireMore_pres (WScoped d) (fun hrw hx => rewriteStep_WScoped henv hwh hrw hx) h hw

theorem appClosed_WScoped (d : Nat) : AppClosed (WScoped d) := fun _ _ => by simp only [WScoped]

/-- A marked rule's firing at the replaced term keeps well-scopedness. -/
theorem preAttempt_WScoped {env : Env} (henv : EnvWF env) {r : CoreFns CheckM} {d : Nat}
    {e e' e₂ : Expr} {t : Name} (h : preAttempt r env d e e' t = .ok (some e₂))
    (hw : WScoped d e') : WScoped d e₂ := by
  obtain ⟨cv, args, us, hf, -, hfire⟩ := preAttempt_inv h
  obtain ⟨u, A, c, ls, l, hres, -, -, hsub, -, -⟩ := rewriteFire_inv hfire
  have hT : WScoped d (cv.type.instantiateLevelParams cv.levelParams us) :=
    WScoped.of_not_hasFvar (by
      rw [hasFvar_instantiateLevelParams]; exact (henv.consts _ (Env.find?_mem hf)).1)
  have hR := piResidual_WScoped hres hT (fun x hx => appSubterms_WScoped e' (hsub x hx) hw)
  simp only [WScoped] at hR
  exact hR.2

/-- The test before unfolding keeps well-scopedness. -/
theorem preFire_WScoped {env : Env} (henv : EnvWF env) {r : CoreFns CheckM} {d : Nat}
    (hwh : ∀ {a w : Expr}, r.whnf d a = .ok w → WScoped d a → WScoped d w)
    {e e₂ : Expr} {t : Name} (h : preFire r env d e = .ok (some (t, e₂)))
    (hw : WScoped d e) : WScoped d e₂ :=
  preFire_pres (appClosed_WScoped d) hwh
    (fun kc a ha => by
      rcases keyLit_cases env kc a with h' | h' <;> rw [h']
      · exact ha
      · exact litToCtorIfNat_WScoped ha)
    (fun ha hx => preAttempt_WScoped henv ha hx) h hw

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1600000 in
/-- Head normalization and the reduction loop preserve
well-scopedness. -/
theorem whnfPres_WScoped {env : Env} (henv : EnvWF env) :
    ∀ (fuel : Nat),
      (∀ {c : Bool} {d : Nat} {e e' : Expr}, whnfCore mode eager env fuel d e c = .ok e' →
        WScoped d e → WScoped d e') ∧
      (∀ {d : Nat} {e e' : Expr}, whnf mode eager env fuel d e = .ok e' →
        WScoped d e → WScoped d e')
  | 0 => ⟨(fun {_ _ _ _} h _ => nomatch h), (fun {_ _ _} h _ => nomatch h)⟩
  | fuel + 1 => by
    obtain ⟨ihCore, ihLoop⟩ := whnfPres_WScoped henv fuel
    constructor
    · -- whnfCore
      intro c d e e' h hw
      cases e with
      | sort u =>
        rw [whnfCore_succ] at h
        simp only [whnfCoreBody, pure, Except.pure, Except.ok.injEq] at h
        exact h ▸ hw
      | fvar idx ty =>
        rw [whnfCore_succ] at h
        simp only [whnfCoreBody, pure, Except.pure, Except.ok.injEq] at h
        exact h ▸ hw
      | forallE ty body =>
        rw [whnfCore_succ] at h
        simp only [whnfCoreBody, pure, Except.pure, Except.ok.injEq] at h
        exact h ▸ hw
      | lam ty body =>
        rw [whnfCore_succ] at h
        simp only [whnfCoreBody, pure, Except.pure, Except.ok.injEq] at h
        exact h ▸ hw
      | const n ws =>
        rcases whnfCore_const_inv h with ⟨t, e₂, e₃, hrw, hfm, hk⟩ | ⟨-, rfl⟩
        · exact ihCore hk
            (fireMore_WScoped henv ihLoop hfm (rewriteStep_WScoped henv ihLoop hrw hw))
        · exact hw
      | lit l =>
        rw [whnfCore_succ] at h
        simp only [whnfCoreBody, pure, Except.pure, Except.ok.injEq] at h
        exact h ▸ hw
      | bvar i =>
        rw [whnfCore_succ] at h
        simp [whnfCoreBody, throw, throwThe, MonadExceptOf.throw] at h
      | letE tt vv bb =>
        -- ζ: the body at the value
        simp only [WScoped] at hw
        exact ihCore (whnfCore_letE_inv h) (WScoped.instantiate1_gen hw.2.1 0 hw.2.2)
      | app f a =>
        have hP := appClosed_WScoped d
        obtain ⟨v, hwf, hcase⟩ := whnf_app_inv h
        have hwv : WScoped d v := ihCore hwf (hP.getAppFn hw)
        rcases hcase with ⟨ty, body, a₁, rest, rfl, hargs, hbeta⟩ |
          ⟨-, ⟨e'', hio', hwe''⟩ | ⟨-, rfl⟩⟩ | ⟨-, -, hk⟩
        · exact ihCore hbeta (hP.beta (fun hl ha => by
            simp only [WScoped] at hl; exact WScoped.instantiate1_gen ha 0 hl.2) hargs hw hwv)
        · rcases iotaThenRule_inv hio' with hio | ⟨-, t, e₂, hrw, hfm⟩
          rotate_left
          · exact ihCore hwe''
              (fireMore_WScoped henv ihLoop hfm (rewriteStep_WScoped henv ihLoop hrw hw))
          -- iota step, at the prefix of the recursor's arity
          refine ihCore hwe'' (iotaAt_ind (fun x y => WScoped d x → WScoped d y) ?_
            (fun hf hw' => by simp only [WScoped] at hw' ⊢; exact ⟨hf hw'.1, hw'.2⟩) _ hio hw)
          intro x y hio hwapp
          obtain ⟨c, us, cv, mI, rP, isK, rules, major, cj, usj,
            cvj, cnP, cnF, induct, r, hfn, hfc, hlen, -, hprep,
            hmfn, hfj,
            hrule,
            hml, hlev, hpeq, hmcerts, -, rfl⟩ :=
            iotaRec_inv hio
          have hargs : ∀ z, z ∈ x.getAppArgs → WScoped d z :=
            fun z hz => hwapp.getAppArgs z hz
          have hrf : r.rhs.hasFvar = false := by
            obtain ⟨-, -, -, -, -, hrules⟩ := henv.consts _ (Env.find?_mem hfc)
            exact (hrules cv mI rP isK rules rfl r (List.mem_of_find?_eq_some hrule)).1
          -- the major's scoping, through the chain in either order
          have hmajw : WScoped d major :=
            prepareMajorFueled_ind hprep (WScoped d)
              (fun hw' hwe => ihLoop hw' hwe)
              (fun hl hwe => by
                rcases litMajorToCtorFueled_inv hl with rfl | ⟨s, -, -, hred⟩
                · exact litToCtorIfNat_WScoped hwe
                · exact ihLoop hred (strLitToConstructor_WScoped s d))
              (fun hs hwe => by
                rcases majorToCtor_inv hs with rfl | ⟨hwsc, -, -, -⟩
                · exact hwe
                · exact WScoped.of_wscopedB hwsc)
              (hargs _ (getD_mem (by omega)))
          refine RecRule.iotaReduct_WScoped hrf ?_
          intro z hz
          rcases List.mem_append.mp hz with hz | hz
          · exact hargs _ (List.mem_of_mem_take hz)
          · exact hmajw.getAppArgs _ (List.mem_of_mem_drop hz)
        · exact hw
        · exact ihCore hk (hP.mkAppN hwv (hP.getAppArgs hw))
      | proj sn i pe =>
        simp only [WScoped] at hw
        obtain ⟨e₂, hst, hcase⟩ := whnf_proj_inv h
        have hwe₂ : WScoped d e₂ := by
          rcases hst with ⟨-, h2⟩ | ⟨-, h2⟩
          · exact ihCore h2 hw
          · exact ihLoop h2 hw
        rcases hcase with rfl | ⟨m, hr, hm⟩
        · simpa [WScoped] using hw
        · exact ihCore hm (reduceProjCore_pres (WScoped d)
            (fun hx => hx.getAppArgs) ihLoop
            (fun s _ => strLitToConstructor_WScoped s d) hr hwe₂)
    · -- whnf loop: the reduction chain is iteration on the loop's own
      -- step budget (task #106), so this is an induction on that
      -- budget at the *same* knot fuel; `ihCore` covers the per-step
      -- head normalization.
      have hloop : ∀ (n : Nat) {d : Nat} {o : Option Expr} {e e' : Expr},
          whnfLoop (pureFns mode eager env fuel) env d n o e = .ok e' →
          OriginP (WScoped d) o → WScoped d e → WScoped d e' := by
        intro n
        induction n with
        | zero => intro _ _ _ _ h _ _; exact nomatch h
        | succ n ihN =>
          intro d o e e' h ho hw
          obtain ⟨e₁, hwc, hcase⟩ := whnfStep_inv h
          have hwe₁ : WScoped d e₁ := ihCore hwc hw
          rcases hcase with ⟨e₂, hrn, ⟨-, rfl⟩ | hcont⟩ | ⟨-, e₂, hu, hcont⟩ |
            ⟨-, -, ⟨-, rfl⟩ | ⟨t, e₂, hof, hcont⟩⟩ | ⟨-, t, e₂, hpf, hcont⟩
          · rcases reduceNat_inv hrn with ⟨k, rfl⟩ | ⟨bn, rfl⟩ <;> simp [WScoped]
          · rcases reduceNat_inv hrn with ⟨k, rfl⟩ | ⟨bn, rfl⟩ <;>
              exact ihN hcont ho (by simp [WScoped])
          · exact ihN hcont (ho.note hwe₁) (unfoldDefinition_WScoped henv hu hwe₁)
          · exact hwe₁
          · obtain ⟨o', e₃, rfl, -, hrw, hfm⟩ := originFire_inv hof
            exact ihN hcont (OriginP.none _) (fireMore_WScoped henv ihLoop hfm
              (rewriteStep_WScoped henv ihLoop hrw (ho _ rfl)))
          · exact ihN hcont ho (preFire_WScoped henv ihLoop hpf hwe₁)
      intro d e e' h hw
      exact hloop whnfLoopFuel h (OriginP.none _) hw

/-- Head normalization preserves well-scopedness. -/
theorem whnfCore_WScoped {env : Env} (henv : EnvWF env)
    (fuel : Nat) {d : Nat} {e e' : Expr} {c : Bool}
    (h : whnfCore mode eager env fuel d e c = .ok e') (hw : WScoped d e) : WScoped d e' :=
  (whnfPres_WScoped henv fuel).1 h hw

/-- The reduction loop preserves well-scopedness. -/
theorem whnf_WScoped {env : Env} (henv : EnvWF env)
    (fuel : Nat) {d : Nat} {e e' : Expr}
    (h : whnf mode eager env fuel d e = .ok e' ) (hw : WScoped d e) : WScoped d e' :=
  (whnfPres_WScoped henv fuel).2 h hw

/-- The major chain preserves well-scopedness (an instance of
`prepareMajorFueled_ind`). -/
theorem prepareMajorFueled_WScoped {env : Env} (henv : EnvWF env)
    {fuel d : Nat} {recName : Name} {isK : Bool} {rules : List RecRule} {a m : Expr}
    (h : prepareMajorFueled mode eager env fuel d recName isK rules a = .ok m)
    (hw : WScoped d a) : WScoped d m :=
  prepareMajorFueled_ind h (WScoped d)
    (fun hw' hwe => whnf_WScoped henv fuel hw' hwe)
    (fun hl hwe => by
      rcases litMajorToCtorFueled_inv hl with rfl | ⟨s, -, -, hred⟩
      · exact litToCtorIfNat_WScoped hwe
      · exact whnf_WScoped henv fuel hred (strLitToConstructor_WScoped s d))
    (fun hs hwe => by
      rcases majorToCtor_inv hs with rfl | ⟨hwsc, -, -, -⟩
      · exact hwe
      · exact WScoped.of_wscopedB hwsc)
    hw

/-- The predecessor of a successor form is in scope. -/
theorem natPred?_WScoped {d : Nat} {e x : Expr} (h : e.natPred? = some x)
    (hw : WScoped d e) : WScoped d x := by
  match e, h with
  | .lit (.natVal (n + 1)), h =>
    simp only [Expr.natPred?, Option.some.injEq] at h
    subst h
    simp [WScoped]
  | .app (.const c []) y, h =>
    simp only [Expr.natPred?] at h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      simp only [WScoped] at hw
      exact hw.2
    · exact nomatch h

/-! ## The lazy-delta loops' pairs (lane CHEAPPROJ)

A predicate preserved by unfolding and by `whnfCore` (either mode) is
preserved along the lazy-delta step and loop: every pair they hand on
is reached from the input pair by those operations. -/

section LazyPres

variable {env : Env} {fuel d : Nat}

/-- `deltaQuick` hands on its own pair. -/
theorem deltaQuick_cont {x y a' b' : Expr} {fa fb fa' fb' : Bool}
    (h : deltaQuickFueled mode eager env fuel d x y fa fb = .ok (.cont a' b' fa' fb')) :
    a' = x ∧ b' = y := by
  simp only [deltaQuickFueled, deltaQuick, Bind.bind, Except.bind, quickDefEq_fold] at h
  cases hq : quickDefEqFueled mode eager env fuel d x y with
  | error err => rw [hq] at h; exact nomatch h
  | ok o =>
  rw [hq] at h
  dsimp only at h
  match o, h with
  | none, h =>
    simp only [pure, Except.pure, Except.ok.injEq, DeltaStep.cont.injEq] at h
    exact ⟨h.1.symm, h.2.1.symm⟩
  | some true, h => simp [pure, Except.pure] at h
  | some false, h => simp [pure, Except.pure] at h

/-- One side's lazy step keeps a property that unfolding, `whnfCore` and the test before unfolding
keep. -/
theorem lazyUnfold_pres (P : Expr → Prop)
    (hu : ∀ {x y : Expr}, unfoldDefinition env x = some y → P x → P y)
    (hC : ∀ {c : Bool} {x y : Expr}, whnfCore mode eager env fuel d x c = .ok y → P x → P y)
    (hpf : ∀ {x y : Expr} {t : Name}, preFire (pureFns mode eager env fuel) env d x = .ok (some (t, y)) →
      P x → P y)
    {x y : Expr} {f : Bool}
    (h : lazyUnfold (pureFns mode eager env fuel) env d x = .ok (some (y, f))) (hx : P x) : P y := by
  unfold lazyUnfold at h
  obtain ⟨o, ho, h⟩ := bindM_ok h
  cases o with
  | some te =>
    obtain ⟨t, x₂⟩ := te
    obtain ⟨x₃, hx₃, h⟩ := bindM_ok h
    simp only [pure, Except.pure, Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact hC (c := true) (by rw [whnfCore_def] at hx₃; exact hx₃) (hpf ho hx)
  | none =>
    dsimp only at h
    split at h
    · rename_i x₂ hx₂
      obtain ⟨x₃, hx₃, h⟩ := bindM_ok h
      simp only [pure, Except.pure, Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact hC (c := true) (by rw [whnfCore_def] at hx₃; exact hx₃) (hu hx₂ hx)
    · simp [pure, Except.pure] at h

/-- Both sides' unfolding keeps a property that unfolding and `whnfCore` keep. -/
theorem lazyBothUnfold_pres (P : Expr → Prop)
    (hu : ∀ {x y : Expr}, unfoldDefinition env x = some y → P x → P y)
    (hC : ∀ {c : Bool} {x y : Expr}, whnfCore mode eager env fuel d x c = .ok y → P x → P y)
    {a b a' b' : Expr} {f : Bool}
    (h : lazyBothUnfold (pureFns mode eager env fuel) env d a b = .ok (some (a', b', f)))
    (ha : P a) (hb : P b) : P a' ∧ P b' := by
  unfold lazyBothUnfold at h
  split at h
  · rename_i a₂ b₂ ha₂ hb₂
    obtain ⟨a₃, ha₃, h⟩ := bindM_ok h
    obtain ⟨b₃, hb₃, h⟩ := bindM_ok h
    simp only [pure, Except.pure, Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, -⟩ := h
    exact ⟨hC (c := true) (by rw [whnfCore_def] at ha₃; exact ha₃) (hu ha₂ ha),
      hC (c := true) (by rw [whnfCore_def] at hb₃; exact hb₃) (hu hb₂ hb)⟩
  · simp [pure, Except.pure] at h

/-- The same head on both sides keeps a property that unfolding, `whnfCore` and the test before
unfolding keep. -/
theorem lazyBoth_pres (P : Expr → Prop)
    (hu : ∀ {x y : Expr}, unfoldDefinition env x = some y → P x → P y)
    (hC : ∀ {c : Bool} {x y : Expr}, whnfCore mode eager env fuel d x c = .ok y → P x → P y)
    (hpf : ∀ {x y : Expr} {t : Name}, preFire (pureFns mode eager env fuel) env d x = .ok (some (t, y)) →
      P x → P y)
    {a b a' b' : Expr} {f : Bool}
    (h : lazyBoth (pureFns mode eager env fuel) env d a b = .ok (some (a', b', f)))
    (ha : P a) (hb : P b) : P a' ∧ P b' := by
  unfold lazyBoth at h
  obtain ⟨o, ho, h⟩ := bindM_ok h
  cases o with
  | some te =>
    obtain ⟨t, a₂⟩ := te
    dsimp only at h
    obtain ⟨o', ho', h⟩ := bindM_ok h
    cases o' with
    | some te' =>
      obtain ⟨t', b₂⟩ := te'
      dsimp only at h
      obtain ⟨a₃, ha₃, h⟩ := bindM_ok h
      obtain ⟨b₃, hb₃, h⟩ := bindM_ok h
      simp only [pure, Except.pure, Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, -⟩ := h
      exact ⟨hC (c := true) (by rw [whnfCore_def] at ha₃; exact ha₃) (hpf ho ha),
        hC (c := true) (by rw [whnfCore_def] at hb₃; exact hb₃) (hpf ho' hb)⟩
    | none => exact lazyBothUnfold_pres P hu hC h ha hb
  | none => exact lazyBothUnfold_pres P hu hC h ha hb

/-- **The lazy-delta step's pair** is reached by unfolding, `whnfCore` and the test before
unfolding. -/
theorem lazyDeltaStep_pres (P : Expr → Prop)
    (hu : ∀ {x y : Expr}, unfoldDefinition env x = some y → P x → P y)
    (hC : ∀ {c : Bool} {x y : Expr}, whnfCore mode eager env fuel d x c = .ok y → P x → P y)
    (hpf : ∀ {x y : Expr} {t : Name}, preFire (pureFns mode eager env fuel) env d x = .ok (some (t, y)) →
      P x → P y)
    {a b a' b' : Expr} {fa fb : Bool}
    (h : lazyDeltaStepFueled mode eager env fuel d a b = .ok (.cont a' b' fa fb))
    (ha : P a) (hb : P b) : P a' ∧ P b' := by
  unfold lazyDeltaStepFueled lazyDeltaStep at h
  have hT : ∀ {x x' : Expr}, tryUnfoldProjApp (pureFns mode eager env fuel) d x = .ok (some x') →
      P x → P x' := by
    intro x x' ht hx
    simp only [tryUnfoldProjApp, Bind.bind, Except.bind, whnfCore_def] at ht
    split at ht
    · cases hw : whnfCore mode eager env fuel d x with
      | error err => rw [hw] at ht; exact nomatch ht
      | ok x₁ =>
      rw [hw] at ht
      dsimp only at ht
      split at ht
      · simp [pure, Except.pure] at ht
      · simp only [pure, Except.pure, Except.ok.injEq, Option.some.injEq] at ht
        subst ht
        exact hC hw hx
    · simp [pure, Except.pure] at ht
  have hQ : ∀ {x y : Expr} {fx fy : Bool},
      deltaQuick mode (pureFns mode eager env fuel) d x y fx fy = .ok (.cont a' b' fa fb) →
      P x → P y → P a' ∧ P b' := by
    intro x y fx fy hq hx hy
    obtain ⟨rfl, rfl⟩ := deltaQuick_cont hq
    exact ⟨hx, hy⟩
  have hU := fun {x y : Expr} {f : Bool} (hh : lazyUnfold (pureFns mode eager env fuel) env d x =
    .ok (some (y, f))) (hx : P x) => lazyUnfold_pres P hu hC hpf hh hx
  cases hda : unfoldableHead env a <;> cases hdb : unfoldableHead env b <;>
    simp only [hda, hdb] at h
  · simp [pure, Except.pure] at h
  · obtain ⟨o, ht, h⟩ := bindM_ok h
    rcases o with _ | a₂
    · obtain ⟨o', ho', h⟩ := bindM_ok h
      rcases o' with _ | ⟨b₃, f⟩
      · simp [pure, Except.pure] at h
      · exact hQ h ha (hU ho' hb)
    · exact hQ h (hT ht ha) hb
  · obtain ⟨o, ht, h⟩ := bindM_ok h
    rcases o with _ | b₂
    · obtain ⟨o', ho', h⟩ := bindM_ok h
      rcases o' with _ | ⟨a₃, f⟩
      · simp [pure, Except.pure] at h
      · exact hQ h (hU ho' ha) hb
    · exact hQ h ha (hT ht hb)
  · split at h
    · obtain ⟨o', ho', h⟩ := bindM_ok h
      rcases o' with _ | ⟨a₃, f⟩
      · simp [pure, Except.pure] at h
      · exact hQ h (hU ho' ha) hb
    split at h
    · obtain ⟨o', ho', h⟩ := bindM_ok h
      rcases o' with _ | ⟨b₃, f⟩
      · simp [pure, Except.pure] at h
      · exact hQ h ha (hU ho' hb)
    split at h
    · obtain ⟨o', ho', h⟩ := bindM_ok h
      rcases o' with _ | ⟨a₃, f⟩
      · simp [pure, Except.pure] at h
      · obtain ⟨o'', ho'', h⟩ := bindM_ok h
        rcases o'' with _ | ⟨b₃, f'⟩
        · simp [pure, Except.pure] at h
        · exact hQ h (hU ho' ha) (hU ho'' hb)
    obtain ⟨sp, -, h⟩ := bindM_ok h
    cases sp with
    | true => simp [pure, Except.pure] at h
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    obtain ⟨o, ho, h⟩ := bindM_ok h
    rcases o with _ | ⟨a₃, b₃, f⟩
    · simp [pure, Except.pure] at h
    · obtain ⟨ha₃, hb₃⟩ := lazyBoth_pres P hu hC hpf ho ha hb
      exact hQ h ha₃ hb₃

/-- **The lazy-delta loop's stuck pair** is reached by unfolding and
`whnfCore`. -/
theorem lazyDeltaReduction_pres (P : Expr → Prop)
    (hu : ∀ {x y : Expr}, unfoldDefinition env x = some y → P x → P y)
    (hC : ∀ {c : Bool} {x y : Expr}, whnfCore mode eager env fuel d x c = .ok y → P x → P y)
    (hpf : ∀ {x y : Expr} {t : Name}, preFire (pureFns mode eager env fuel) env d x = .ok (some (t, y)) →
      P x → P y) :
    ∀ (n : Nat) {oa ob oa₁ ob₁ : Option Expr} {a b a₁ b₁ : Expr},
      lazyDeltaReductionFueled mode eager env fuel d n oa ob a b =
        .ok (.unknown oa₁ ob₁ a₁ b₁) →
      OriginP P oa → OriginP P ob → P a → P b →
      P a₁ ∧ P b₁ ∧ OriginP P oa₁ ∧ OriginP P ob₁
  | 0, _, _, _, _, _, _, _, _, h, _, _, _, _ => by
    simp [lazyDeltaReductionFueled, lazyDeltaReduction, throw, throwThe,
      MonadExceptOf.throw] at h
  | n + 1, oa, ob, oa₁, ob₁, a, b, a₁, b₁, h, hoa, hob, ha, hb => by
    simp only [lazyDeltaReductionFueled, lazyDeltaReduction, Bind.bind, Except.bind,
      defeqOffset_fold, reduceNat_fold, lazyDeltaStep_fold, defeq_def] at h
    cases ho : defeqOffsetFueled mode eager env fuel d a b with
    | error err => rw [ho] at h; exact nomatch h
    | ok o =>
    rw [ho] at h
    dsimp only at h
    cases o with
    | some v => simp [pure, Except.pure] at h
    | none =>
    dsimp only at h
    cases hna : (if eager || (!a.hasFvar && !b.hasFvar) then
        reduceNatFueled mode eager env fuel d a else pure none) with
    | error err => rw [hna] at h; exact nomatch h
    | ok o₁ =>
    rw [hna] at h
    dsimp only at h
    cases o₁ with
    | some a₂ =>
      dsimp only at h
      cases hde : isDefEqCore mode eager env fuel d a₂ b with
      | error err => rw [hde] at h; exact nomatch h
      | ok v => rw [hde] at h; simp [pure, Except.pure] at h
    | none =>
    dsimp only at h
    cases hnb : (if eager || (!a.hasFvar && !b.hasFvar) then
        reduceNatFueled mode eager env fuel d b else pure none) with
    | error err => rw [hnb] at h; exact nomatch h
    | ok o₂ =>
    rw [hnb] at h
    dsimp only at h
    cases o₂ with
    | some b₂ =>
      dsimp only at h
      cases hde : isDefEqCore mode eager env fuel d a b₂ with
      | error err => rw [hde] at h; exact nomatch h
      | ok v => rw [hde] at h; simp [pure, Except.pure] at h
    | none =>
    dsimp only at h
    cases hs : lazyDeltaStepFueled mode eager env fuel d a b with
    | error err => rw [hs] at h; exact nomatch h
    | ok st =>
    rw [hs] at h
    dsimp only at h
    cases st with
    | cont a' b' fa fb =>
      obtain ⟨ha', hb'⟩ := lazyDeltaStep_pres P hu hC hpf hs ha hb
      exact lazyDeltaReduction_pres P hu hC hpf n h ((hoa.drop fa a).note ha')
        ((hob.drop fb b).note hb') ha' hb'
    | eq => simp [pure, Except.pure] at h
    | diff => simp [pure, Except.pure] at h
    | unknown =>
      simp only [pure, Except.pure, Except.ok.injEq, LazyRes.unknown.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      exact ⟨ha, hb, hoa, hob⟩

end LazyPres

end ConLeche
