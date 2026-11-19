module

public import ConLeche.Verify.Fueled

public section

/-!
# Bulk beta: the head-normalization step and its identification with `whnfCoreBody`
(task #50)

The cached checker's app case (`whnfHeadI`/`betaPeelI`/`whnfStuckI`,
`ConLeche/Cached/CoreC.lean`) takes a whole application spine at once, as `whnfCoreBody` does,
and batches consecutive lambda binders into a single bulk substitution; every reduction hands
the head-normalization loop the term to continue with (`WhnfStep.cont`, task #342 R2), so every
step is the loop's own tail call.  This file provides the step-returning pure mirrors
(`betaPeelW`, `whnfStuckW`, `whnfHeadW`, `whnfCoreStepW`) the cached walk simulates, and proves
the **soundness of a step against the specification**: a step at the pure fueled knot, continued
by `whnfCore`, is reproduced by `whnfCoreBody` at some fuel (`whnfCoreStepW_sound`).  Off the λ
arm the step is the body's arm followed by `whnfCore` at the same fuel
(`whnfCoreBody_eq_step`, `whnfStuckW_run`); the bulk substitution is the body's one-binder β
iterated (`peelTerm_sound`).  The cached walk (`ConLeche/Verify/Cached/DiscC4`) composes its
simulation of each step with these theorems.
-/

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace ConLeche

variable {mode : CheckMode} {eager : Bool}
variable {mi : CheckMode}

open Expr

variable {m : Type → Type} [Monad m] [MonadExceptOf CheckError m]

/-! ## The step-returning mirrors (task #342 R2)

The cached loop (`whnfCoreStepI` and its arms, `ConLeche/Cached/CoreC.lean`) does not call its
continuation: it *returns* it (`WhnfStep.cont`, `WhnfStep.fire`), so that every reduction step
is the loop's own tail call.  These are its pure mirrors; `whnfCoreStepW_sound` below carries a
step followed by `whnfCore` to `whnfCoreBody` at some knot fuel. -/

/-- Continue a step's outcome with the continuation `k`. -/
@[expose] def WhnfStep.run (k : Expr → m Expr) : WhnfStep → m Expr
  | .done v => pure v
  | .cont e => k e
  | .fire _ e => k e

/-- Pure mirror of the cached `betaPeelI`: `t` is the raw lambda body after the binders consumed
so far, `acc` their arguments (innermost first; the cached loop reads them in place, as a range
of its spine array). -/
@[expose] def betaPeelW (mode : CheckMode) (r : CoreFns m) (env : Env) (depth : Nat) :
    Expr → List Expr → List Expr → m WhnfStep
  | t, acc, [] => pure (.cont (t.instantiateList acc))
  | t, acc, a :: rest =>
    match t with
    | .lam _ body => betaPeelW mode r env depth body (a :: acc) rest
    | t => pure (.cont (Expr.mkAppN (t.instantiateList acc) (a :: rest)))

omit [MonadExceptOf CheckError m] in
theorem betaPeelW_nil (r : CoreFns m) (env : Env) (depth : Nat)
    (t : Expr) (acc : List Expr) :
    betaPeelW mode r env depth t acc [] = pure (.cont (t.instantiateList acc)) := by
  rw [betaPeelW]

omit [MonadExceptOf CheckError m] in
theorem betaPeelW_lam (r : CoreFns m) (env : Env) (depth : Nat)
    (ty body : Expr) (acc : List Expr) (a : Expr) (rest : List Expr) :
    betaPeelW mode r env depth (.lam ty body) acc (a :: rest)
      = betaPeelW mode r env depth body (a :: acc) rest := by
  rw [betaPeelW]

omit [MonadExceptOf CheckError m] in
theorem betaPeelW_ne_lam (r : CoreFns m) (env : Env) (depth : Nat)
    {t : Expr} (ht : ∀ ty body, t ≠ .lam ty body)
    (acc : List Expr) (a : Expr) (rest : List Expr) :
    betaPeelW mode r env depth t acc (a :: rest)
      = pure (.cont (Expr.mkAppN (t.instantiateList acc) (a :: rest))) := by
  cases t with
  | lam ty body => exact absurd rfl (ht ty body)
  | _ => rw [betaPeelW] <;> exact fun _ _ h => nomatch h

/-- The ι target of a spine head: the spine length `mI + 1` at which the ι step can
fire, where the head is a stored recursor at its own number of levels. -/
@[expose] def iotaTarget (env : Env) (h : Expr) : Option Nat :=
  match h with
  | .const c us =>
    match env.find? c with
    | some (.recInfo cv mI _ _ _) =>
      if us.length = cv.levelParams.length then some (mI + 1) else none
    | _ => none
  | _ => none

/-- Pure mirror of the cached `whnfStuckRuleI`: the rules of the head at the whole spine, and the
rules fired again on the reduct, marked as a firing; otherwise the spine itself. -/
@[expose] def whnfStuckRuleW (r : CoreFns m) (env : Env) (depth : Nat) (e : Expr) :
    m WhnfStep := do
  match ← rewriteStep r env depth false e with
  | some (t, e₂) => do
    let e₃ ← fireMore r env depth ruleFireBudget e₂
    pure (.fire t e₃)
  | none => pure (.done e)

/-- What the stuck arm answers after the ι step at its target prefix `k`. -/
@[expose] def whnfStuckTail (r : CoreFns m) (env : Env) (depth : Nat) (e : Expr) (k : Nat) :
    Option Expr → m WhnfStep
  | some e'' => pure (.cont (Expr.mkAppN e'' (e.getAppArgs.drop k)))
  | none => whnfStuckRuleW r env depth e

/-- Pure mirror of the cached `whnfStuckI`: the ι step at its target prefix, then the rules. -/
@[expose] def whnfStuckW (mode : CheckMode) (r : CoreFns m) (env : Env) (depth : Nat)
    (h e : Expr) : m WhnfStep :=
  match iotaTarget env h with
  | some k =>
    if k ≤ e.getAppArgs.length then
      iotaRec mode r env depth (Expr.mkAppN h (e.getAppArgs.take k)) >>=
        whnfStuckTail r env depth e k
    else whnfStuckRuleW r env depth e
  | none => whnfStuckRuleW r env depth e

/-- Pure mirror of the cached `whnfHeadI`. -/
@[expose] def whnfHeadW (mode : CheckMode) (r : CoreFns m) (env : Env) (depth : Nat)
    (v h e : Expr) : m WhnfStep :=
  match v with
  | .lam _ body =>
    match e.getAppArgs with
    | a :: rest => betaPeelW mode r env depth body [a] rest
    | [] => pure (.done e)
  | v =>
    if v = h then whnfStuckW mode r env depth h e
    else pure (.cont (Expr.mkAppN v e.getAppArgs))

theorem whnfHeadW_lam (r : CoreFns m) (env : Env) (depth : Nat) (ty body h e : Expr) :
    whnfHeadW mode r env depth (.lam ty body) h e =
      match e.getAppArgs with
      | a :: rest => betaPeelW mode r env depth body [a] rest
      | [] => pure (.done e) := by
  rw [whnfHeadW]

theorem whnfHeadW_ne_lam (r : CoreFns m) (env : Env) (depth : Nat) {v : Expr}
    (hv : ∀ ty body, v ≠ .lam ty body) (h e : Expr) :
    whnfHeadW mode r env depth v h e =
      if v = h then whnfStuckW mode r env depth h e
      else pure (.cont (Expr.mkAppN v e.getAppArgs)) := by
  cases v with
  | lam ty body => exact absurd rfl (hv ty body)
  | _ => rw [whnfHeadW] <;> exact fun _ _ hh => nomatch hh

/-! ## The head-normalization step mirror (task #106) -/

/-- Pure mirror of `whnfCoreStepI`: one head-normalization step,
returning the head normal form or the term to continue with. -/
@[expose] def whnfCoreStepW (mode : CheckMode) (r : CoreFns m) (env : Env) (cheap : Bool)
    (depth : Nat) : Expr → m WhnfStep
  | .sort u => pure (.done (.sort u))
  | .fvar idx ty => pure (.done (.fvar idx ty))
  | .forallE ty body => pure (.done (.forallE ty body))
  | .lam ty body => pure (.done (.lam ty body))
  | .const n us => do
    match ← rewriteStep r env depth false (.const n us) with
    | some (t, e₂) => do
      let e₃ ← fireMore r env depth ruleFireBudget e₂
      pure (.fire t e₃)
    | none => pure (.done (.const n us))
  | .lit l => pure (.done (.lit l))
  | .app f a =>
    r.whnfCore cheap depth (Expr.app f a).getAppFn >>= fun v =>
      whnfHeadW mode r env depth v (Expr.app f a).getAppFn (.app f a)
  | .proj sn i pe => do
    let c ← if cheap then r.whnfCore true depth pe else r.whnf depth pe
    match ← reduceProjCore mode r env depth sn i c with
    | some m' => pure (.cont m')
    | none => pure (.done (.proj sn i pe))
  | .letE _ v b => pure (.cont (b.instantiate1 v))
  | .bvar _ => throw (.notImplemented "whnf beyond the supported fragment")

/-! ## `atF` equations and fuel monotonicity for the mirrors -/

section AtF

variable {env : Env}

theorem betaPeelW_atF (d : Nat) (F : Nat) :
    ∀ (xs : List Expr) (t : Expr) (acc : List Expr),
      (betaPeelW mode (fueledFns mode eager env) env d t acc xs).val F
        = betaPeelW mode (pureFns mode eager env F) env d t acc xs
  | [], t, acc => by rw [betaPeelW_nil, betaPeelW_nil]; rfl
  | a :: rest, t, acc => by
    by_cases hlam : ∃ ty body, t = Expr.lam ty body
    · obtain ⟨ty, body, rfl⟩ := hlam
      rw [betaPeelW_lam, betaPeelW_lam]
      exact betaPeelW_atF d F rest body (a :: acc)
    · have ht : ∀ ty body, t ≠ Expr.lam ty body :=
        fun ty b hh => hlam ⟨ty, b, hh⟩
      rw [betaPeelW_ne_lam _ _ _ ht, betaPeelW_ne_lam _ _ _ ht]
      rfl

theorem whnfStuckRuleW_atF (d : Nat) (F : Nat) (e : Expr) :
    (whnfStuckRuleW (fueledFns mode eager env) env d e).val F
      = whnfStuckRuleW (pureFns mode eager env F) env d e := by
  unfold whnfStuckRuleW
  rw [FueledM.atF_bind, rewriteStep_atF]
  congr 1
  funext o
  cases o with
  | some te =>
    dsimp only
    rw [FueledM.atF_bind, fireMore_atF]
    rfl
  | none => rfl

theorem whnfStuckW_atF (d : Nat) (F : Nat) (h e : Expr) :
    (whnfStuckW mode (fueledFns mode eager env) env d h e).val F
      = whnfStuckW mode (pureFns mode eager env F) env d h e := by
  unfold whnfStuckW
  split
  · split
    · rw [FueledM.atF_bind, iotaRec_atF]
      congr 1
      funext o
      cases o with
      | some e'' => rfl
      | none => exact whnfStuckRuleW_atF d F e
    · exact whnfStuckRuleW_atF d F e
  · exact whnfStuckRuleW_atF d F e

theorem whnfHeadW_atF (d : Nat) (F : Nat) (v h e : Expr) :
    (whnfHeadW mode (fueledFns mode eager env) env d v h e).val F
      = whnfHeadW mode (pureFns mode eager env F) env d v h e := by
  by_cases hlam : ∃ ty body, v = Expr.lam ty body
  · obtain ⟨ty, body, rfl⟩ := hlam
    rw [whnfHeadW_lam, whnfHeadW_lam]
    split
    · exact betaPeelW_atF d F _ _ _
    · rfl
  · have hv : ∀ ty body, v ≠ Expr.lam ty body := fun ty b hh => hlam ⟨ty, b, hh⟩
    rw [whnfHeadW_ne_lam _ _ _ hv, whnfHeadW_ne_lam _ _ _ hv]
    split
    · exact whnfStuckW_atF d F h e
    · rfl

theorem whnfCoreStepW_atF (c : Bool) (d : Nat) (F : Nat) (e : Expr) :
    (whnfCoreStepW mode (fueledFns mode eager env) env c d e).val F
      = whnfCoreStepW mode (pureFns mode eager env F) env c d e := by
  cases e <;> (unfold whnfCoreStepW; try rfl)
  case const n us =>
    rw [FueledM.atF_bind, rewriteStep_atF]
    congr 1
    funext o
    cases o with
    | some te =>
      dsimp only
      rw [FueledM.atF_bind, fireMore_atF]
      rfl
    | none => rfl
  case app f a =>
    rw [FueledM.atF_bind]
    congr 1
    funext vh
    exact whnfHeadW_atF d F _ _ _
  case proj sn i pe =>
    atF_tac4

theorem whnfCoreStepW_mono {c : Bool} {d : Nat} {e : Expr} {F F' : Nat}
    (hle : F ≤ F') {st : WhnfStep}
    (h : whnfCoreStepW mode (pureFns mode eager env F) env c d e = .ok st) :
    whnfCoreStepW mode (pureFns mode eager env F') env c d e = .ok st := by
  rw [← whnfCoreStepW_atF] at h ⊢
  exact (whnfCoreStepW mode (fueledFns mode eager env) env c d e).property hle h

/-- `whnfCore` is the identity on a lambda (at nonzero fuel). -/
theorem whnfCore_lam (F d : Nat) (ty body : Expr)
    {c : Bool} :
    whnfCore mode eager env (F + 1) d (.lam ty body) c
      = .ok (.lam ty body) := rfl

end AtF

/-! ## Soundness of the loop step against the specification body -/

section Sound

variable {env : Env} {c : Bool}

private theorem bind_ok {α β : Type} {x : Except CheckError α}
    {f : α → Except CheckError β} {b : β}
    (h : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases hx : x with
  | error e =>
    rw [hx] at h
    exact nomatch h
  | ok a =>
    rw [hx] at h
    exact ⟨a, rfl, h⟩

private theorem ok_bind {α β : Type} (a : α)
    (f : α → Except CheckError β) :
    ((Except.ok a : Except CheckError α) >>= f) = f a := rfl

/-- The bulk substitution of a lambda, exposed. -/
theorem instList_lam (ty body : Expr)
    (acc : List Expr) :
    (Expr.lam ty body).instantiateList acc
      = .lam (ty.instantiateList acc) (body.instantiateList acc 1) := by
  simp [Expr.instantiateList]

/-- The bulk substitution splits off its head as the innermost
`instantiate1` (the `d = 0`, one-binder-under form used by the peel). -/
theorem instList_cons0 (body : Expr) (a : Expr)
    (acc : List Expr) :
    body.instantiateList (a :: acc)
      = (body.instantiateList acc 1).instantiate1 a := by
  exact Expr.instantiateList_cons acc body a 0

theorem instList_single (body : Expr) (a : Expr) :
    body.instantiateList [a] = body.instantiate1 a := by
  rw [instList_cons0, Expr.instantiateList_nil]

/-- An application with more arguments is still an application. -/
theorem mkAppN_app_isApp : ∀ (rest : List Expr) (x y : Expr),
    ∃ f a, Expr.mkAppN (.app x y) rest = .app f a
  | [], x, y => ⟨x, y, rfl⟩
  | b :: bs, x, y => mkAppN_app_isApp bs (.app x y) b

/-- **β at a spine's first argument, as the specification takes it**: the chained `whnfCore` of
a λ applied to arguments answers what it answers on the body at the first argument, applied to
the rest, with one more unit of fuel (and one for the λ head). -/
theorem whnfCore_beta_spine {d N : Nat} {ty body a : Expr} {rest : List Expr} {v : Expr}
    (h : whnfCore mode eager env N d (Expr.mkAppN (body.instantiate1 a) rest) c = .ok v) :
    whnfCore mode eager env (N + 2) d (Expr.mkAppN (.lam ty body) (a :: rest)) c = .ok v := by
  obtain ⟨f₀, a₀, hfa⟩ := mkAppN_app_isApp rest (.lam ty body) a
  show whnfCore mode eager env (N + 2) d (Expr.mkAppN (.app (.lam ty body) a) rest) c = .ok v
  rw [hfa, whnfCore_succ]
  simp only [whnfCoreBody]
  rw [← hfa, Expr.getAppFn_mkAppN, Expr.getAppArgs_mkAppN]
  show (whnfCore mode eager env (N + 1) d (.lam ty body) c >>= _) = _
  rw [whnfCore_lam, ok_bind]
  exact whnfCore_mono (Nat.le_succ N) h

/-- What the peel loop continues with. -/
@[expose] def peelTerm : Expr → List Expr → List Expr → Expr
  | t, acc, [] => t.instantiateList acc
  | t, acc, a :: rest =>
    match t with
    | .lam _ body => peelTerm body (a :: acc) rest
    | t => Expr.mkAppN (t.instantiateList acc) (a :: rest)

omit [MonadExceptOf CheckError m] in
/-- The peel loop continues with `peelTerm`. -/
theorem betaPeelW_eq (r : CoreFns m) (d : Nat) :
    ∀ (rest : List Expr) (t : Expr) (acc : List Expr),
      betaPeelW mode r env d t acc rest = pure (.cont (peelTerm t acc rest))
  | [], t, acc => by rw [betaPeelW_nil]; simp only [peelTerm]
  | a :: rest, t, acc => by
    cases t with
    | lam ty body =>
      rw [betaPeelW_lam, betaPeelW_eq r d rest body (a :: acc)]; simp only [peelTerm]
    | _ => rw [betaPeelW_ne_lam _ _ _ (by intro _ _ hh; cases hh)]; simp only [peelTerm]

/-- **A peel is reproduced by the specification**: the multi-binder substitution of the peel
loop (one bulk `instantiateList`) is the chained one-binder β of `whnfCoreBody`, at some fuel. -/
theorem peelTerm_sound {d N : Nat} {v : Expr} :
    ∀ (rest : List Expr) (t : Expr) (acc : List Expr),
      whnfCore mode eager env N d (peelTerm t acc rest) c = .ok v →
      ∃ M, whnfCore mode eager env M d (Expr.mkAppN (t.instantiateList acc) rest) c = .ok v
  | [], t, acc, hk => ⟨N, by simp only [peelTerm] at hk; exact hk⟩
  | a :: rest, t, acc, hk => by
    cases t with
    | lam ty body =>
      simp only [peelTerm] at hk
      obtain ⟨M, hM⟩ := peelTerm_sound rest body (a :: acc) hk
      rw [instList_cons0] at hM
      refine ⟨M + 2, ?_⟩
      rw [instList_lam]
      exact whnfCore_beta_spine hM
    | _ => exact ⟨N, by simp only [peelTerm] at hk; exact hk⟩

/-- Away from its target the ι step answers `none`. -/
theorem iotaRec_none_of_target {d : Nat} (r : CoreFns m) {x : Expr}
    (ht : iotaTarget env x.getAppFn ≠ some x.getAppArgs.length) :
    iotaRec mode r env d x = pure none := by
  unfold iotaRec
  split
  · next c us hfn =>
    split
    · next cv mI rP isK rules hfc =>
      rw [ite_eq_right]
      rintro ⟨hlen, hlvl, -⟩
      apply ht
      rw [hfn]
      simp [iotaTarget, hfc, hlvl, hlen]
    · rfl
  · rfl

theorem iotaTarget_pos {h : Expr} {k : Nat}
    (hk : iotaTarget env h = some k) : 0 < k := by
  unfold iotaTarget at hk
  split at hk
  · split at hk
    · split at hk
      · cases hk; omega
      · cases hk
    · cases hk
  · cases hk

/-- **ι at a prefix is ι at the target prefix**: the recursion of `iotaAt` over the spine reaches
the one prefix where the ι step can fire, the recursor's arity. -/
theorem iotaAt_target {d : Nat} (r : CoreFns CheckM) :
    ∀ (e : Expr), iotaAt mode r env d e =
      match iotaTarget env e.getAppFn with
      | some k =>
        if k ≤ e.getAppArgs.length then
          iotaRec mode r env d (Expr.mkAppN e.getAppFn (e.getAppArgs.take k)) >>= fun o =>
            pure (o.map fun e'' => Expr.mkAppN e'' (e.getAppArgs.drop k))
        else pure none
      | none => pure none
  | .app f a => by
    have ih := iotaAt_target (d := d) r f
    have hfn : (Expr.app f a).getAppFn = f.getAppFn := rfl
    have hargs : (Expr.app f a).getAppArgs = f.getAppArgs ++ [a] := rfl
    rw [iotaAt, hfn, hargs]
    cases htk : iotaTarget env f.getAppFn with
    | none =>
      rw [htk] at ih
      dsimp only at ih
      rw [iotaRec_none_of_target r (by rw [hfn, htk]; simp), ih]
      rfl
    | some k =>
      rw [htk] at ih
      dsimp only at ih ⊢
      by_cases hk : k = f.getAppArgs.length + 1
      · subst hk
        rw [ite_eq_right (by omega)] at ih
        rw [ite_eq_left (by simp), List.take_of_length_le (by simp),
          List.drop_of_length_le (by simp),
          show Expr.mkAppN f.getAppFn (f.getAppArgs ++ [a]) = .app f a by
            rw [Expr.mkAppN_append_one, Expr.mkAppN_getApp]]
        cases hio : iotaRec mode r env d (.app f a) with
        | error err => rfl
        | ok o =>
          cases o with
          | some e'' => rfl
          | none => rw [ih]; rfl
      · rw [iotaRec_none_of_target r (by rw [hfn, htk, hargs]; simp; omega)]
        show (iotaAt mode r env d f >>= fun o => match o with
          | some f₂ => pure (some (Expr.app f₂ a)) | none => pure none) = _
        rw [ih]
        by_cases hkn : k ≤ f.getAppArgs.length
        · rw [ite_eq_left hkn, ite_eq_left (by simp; omega), List.take_append_of_le_length hkn,
            List.drop_append_of_le_length hkn]
          cases hio : iotaRec mode r env d (Expr.mkAppN f.getAppFn (f.getAppArgs.take k)) with
          | error err => rfl
          | ok o =>
            cases o with
            | some e'' =>
              show (pure (some (Expr.app (Expr.mkAppN e'' (f.getAppArgs.drop k)) a)) :
                CheckM (Option Expr)) = _
              rw [← Expr.mkAppN_append_one]; rfl
            | none => rfl
        · rw [ite_eq_right hkn, ite_eq_right (by simp; omega)]
          rfl
  | .bvar _ | .sort _ | .const .. | .fvar .. | .forallE .. | .lam .. | .letE .. | .lit _
  | .proj .. => by
    rw [iotaAt_nonApp _ _ _ (by intro _ _ hh; cases hh)]
    rw [iotaRec_none_of_target r (by
      intro hh
      have := iotaTarget_pos hh
      simp [Expr.getAppArgs] at this)]
    split
    · next k hk =>
      have := iotaTarget_pos hk
      rw [ite_eq_right (by simp [Expr.getAppArgs]; omega)]
    · rfl

/-- **The stuck arm and its continuation are ι-then-rules**: at a spine whose head is its own
head normal form, the stuck mirror followed by `k` is `whnfCoreBody`'s arm for it. -/
theorem whnfStuckW_run {d : Nat} (r : CoreFns CheckM) (k : Expr → CheckM Expr) (e : Expr) :
    (whnfStuckW mode r env d e.getAppFn e >>= WhnfStep.run k) =
      (iotaThenRule mode r env d e >>= fun o => match o with
        | some e'' => k e''
        | none => pure e) := by
  have hrule : (whnfStuckRuleW r env d e >>= WhnfStep.run k) =
      (((rewriteStep r env d false e >>= fun o => match o with
          | some (_, e₂) => (do
            let e₃ ← fireMore r env d ruleFireBudget e₂
            pure (some e₃) : CheckM (Option Expr))
          | none => (pure none : CheckM (Option Expr))) : CheckM (Option Expr)) >>= fun o =>
        match o with
        | some e'' => k e''
        | none => pure e) := by
    unfold whnfStuckRuleW
    cases rewriteStep r env d false e with
    | error er => rfl
    | ok ro =>
      cases ro with
      | none => rfl
      | some te =>
        show (fireMore r env d ruleFireBudget te.2 >>= _) >>= _ =
          (fireMore r env d ruleFireBudget te.2 >>= _) >>= _
        cases fireMore r env d ruleFireBudget te.2 <;> rfl
  unfold whnfStuckW iotaThenRule
  rw [iotaAt_target r e]
  split
  · split
    · cases iotaRec mode r env d (Expr.mkAppN e.getAppFn (e.getAppArgs.take _)) with
      | error er => rfl
      | ok o =>
        cases o with
        | some e'' => rfl
        | none => exact hrule
    · exact hrule
  · exact hrule

/-- `whnfCore` of an application whose spine head normalized to a λ. -/
theorem whnfCore_app_lam {d N : Nat} {f a ty body : Expr}
    (hv : whnfCore mode eager env N d (Expr.app f a).getAppFn c = .ok (.lam ty body)) :
    whnfCore mode eager env (N + 1) d (.app f a) c =
      match (Expr.app f a).getAppArgs with
      | a₁ :: rest => whnfCore mode eager env N d (Expr.mkAppN (body.instantiate1 a₁) rest) c
      | [] => pure (.app f a) := by
  rw [whnfCore_succ]
  simp only [whnfCoreBody]
  rw [whnfCore_def, hv, ok_bind]
  rfl

/-- `whnfCore` of an application whose spine head normalized to something else. -/
theorem whnfCore_app_ne_lam {d N : Nat} {f a v : Expr} (hlam : ∀ ty body, v ≠ .lam ty body)
    (hv : whnfCore mode eager env N d (Expr.app f a).getAppFn c = .ok v) :
    whnfCore mode eager env (N + 1) d (.app f a) c =
      if v = (Expr.app f a).getAppFn then
        (iotaThenRule mode (pureFns mode eager env N) env d (.app f a) >>= fun o => match o with
          | some e'' => whnfCore mode eager env N d e'' c
          | none => pure (.app f a))
      else whnfCore mode eager env N d (Expr.mkAppN v (Expr.app f a).getAppArgs) c := by
  rw [whnfCore_succ]
  simp only [whnfCoreBody]
  rw [whnfCore_def, hv, ok_bind]
  cases v with
  | lam ty body => exact absurd rfl (hlam ty body)
  | _ => rfl

/-- **The specification body is the step followed by `whnfCore`**, away from applications
(where the multi-binder peel takes more knot levels than one). -/
theorem whnfCoreBody_eq_step {d N : Nat} {e : Expr} (he : ∀ f a, e ≠ .app f a) :
    whnfCore mode eager env (N + 1) d e c =
      (whnfCoreStepW mode (pureFns mode eager env N) env c d e >>=
        WhnfStep.run (fun x => whnfCore mode eager env N d x c)) := by
  rw [whnfCore_succ]
  cases e with
  | app f a => exact absurd rfl (he f a)
  | const n us =>
    simp only [whnfCoreBody, whnfCoreStepW]
    cases rewriteStep (pureFns mode eager env N) env d false (.const n us) with
    | error er => rfl
    | ok ro =>
      cases ro with
      | none => rfl
      | some te =>
        obtain ⟨t, e₂⟩ := te
        show (fireMore (pureFns mode eager env N) env d ruleFireBudget e₂ >>= _ : CheckM Expr) =
          ((fireMore (pureFns mode eager env N) env d ruleFireBudget e₂ >>= _ : CheckM WhnfStep) >>= _)
        cases fireMore (pureFns mode eager env N) env d ruleFireBudget e₂ <;> rfl
  | proj sn i pe =>
    cases c with
    | false =>
      simp only [whnfCoreBody, whnfCoreStepW, Bool.false_eq_true, ↓reduceIte]
      cases (pureFns mode eager env N).whnf d pe with
      | error er => rfl
      | ok w =>
        simp only [Bind.bind, Except.bind]
        cases reduceProjCore mode (pureFns mode eager env N) env d sn i w with
        | error er => rfl
        | ok o => cases o <;> rfl
    | true =>
      simp only [whnfCoreBody, whnfCoreStepW, ↓reduceIte]
      cases (pureFns mode eager env N).whnfCore true d pe with
      | error er => rfl
      | ok w =>
        simp only [Bind.bind, Except.bind]
        cases reduceProjCore mode (pureFns mode eager env N) env d sn i w with
        | error er => rfl
        | ok o => cases o <;> rfl
  | _ => rfl

/-- **A step followed by `whnfCore` is reproduced by the specification** at some knot fuel. -/
theorem whnfCoreStepW_sound {d F G : Nat} {e v : Expr} {st : WhnfStep}
    (hs : whnfCoreStepW mode (pureFns mode eager env F) env c d e = .ok st)
    (hk : st.run (fun x => whnfCore mode eager env G d x c) = .ok v) :
    ∃ M, whnfCore mode eager env M d e c = .ok v := by
  have hs' := whnfCoreStepW_mono (Nat.le_max_left F G) hs
  have hk' : st.run (fun x => whnfCore mode eager env (max F G) d x c) = .ok v := by
    cases st with
    | done w => exact hk
    | cont x => exact whnfCore_mono (Nat.le_max_right F G) hk
    | fire t x => exact whnfCore_mono (Nat.le_max_right F G) hk
  generalize max F G = N at hs' hk'
  by_cases happ : ∃ f a, e = .app f a
  · obtain ⟨f, a, rfl⟩ := happ
    simp only [whnfCoreStepW] at hs'
    obtain ⟨w, hw, hh⟩ := bind_ok hs'
    rw [whnfCore_def] at hw
    by_cases hlam : ∃ ty body, w = Expr.lam ty body
    · obtain ⟨ty, body, rfl⟩ := hlam
      rw [whnfHeadW_lam] at hh
      cases hargs : (Expr.app f a).getAppArgs with
      | nil => exact absurd hargs (getAppArgs_app_ne_nil f a)
      | cons a₁ rest =>
        rw [hargs] at hh
        dsimp only at hh
        rw [betaPeelW_eq] at hh
        cases hh
        obtain ⟨M, hM⟩ := peelTerm_sound rest body [a₁] hk'
        rw [instList_single] at hM
        refine ⟨max M N + 1, ?_⟩
        rw [whnfCore_app_lam (whnfCore_mono (Nat.le_max_right M N) hw), hargs]
        exact whnfCore_mono (Nat.le_max_left M N) hM
    · have hv : ∀ ty body, w ≠ Expr.lam ty body := fun ty b hh => hlam ⟨ty, b, hh⟩
      rw [whnfHeadW_ne_lam _ _ _ hv] at hh
      refine ⟨N + 1, ?_⟩
      rw [whnfCore_app_ne_lam hv hw]
      by_cases hwh : w = (Expr.app f a).getAppFn
      · rw [ite_eq_left hwh] at hh ⊢
        rw [← whnfStuckW_run (pureFns mode eager env N) _ (.app f a), hh, ok_bind]
        exact hk'
      · rw [ite_eq_right hwh] at hh ⊢
        cases hh
        exact hk'
  · have he : ∀ f a, e ≠ .app f a := fun f a hh => happ ⟨f, a, hh⟩
    exact ⟨N + 1, by rw [whnfCoreBody_eq_step he, hs', ok_bind]; exact hk'⟩

/-- **A step that continues** (the cached loop's `.cont`): the chained `whnfCore` of the term
answers what it answers on the continuation, at some knot fuel.  The cached walk composes the
steps it takes with this, a memo hit included, so the specification never sees the loop. -/
theorem whnfCore_of_stepW_cont {d F G : Nat} {e e' v : Expr}
    (hs : (whnfCoreStepW mode (fueledFns mode eager env) env c d e).val F = .ok (.cont e'))
    (hk : ((fueledFns mode eager env).whnfCore c d e').val G = .ok v) :
    ∃ M, whnfCore mode eager env M d e c = .ok v := by
  rw [whnfCoreStepW_atF] at hs
  exact whnfCoreStepW_sound (st := .cont e') hs hk

/-- **A step that fires a rule** (the cached loop's `.fire`): as a continuing step. -/
theorem whnfCore_of_stepW_fire {d F G : Nat} {e e' v : Expr} {t : Name}
    (hs : (whnfCoreStepW mode (fueledFns mode eager env) env c d e).val F = .ok (.fire t e'))
    (hk : ((fueledFns mode eager env).whnfCore c d e').val G = .ok v) :
    ∃ M, whnfCore mode eager env M d e c = .ok v := by
  rw [whnfCoreStepW_atF] at hs
  exact whnfCoreStepW_sound (st := .fire t e') hs hk

/-- **A step that answers** (the cached loop's `.done`): its answer is the chained `whnfCore`'s. -/
theorem whnfCore_of_stepW_done {d F : Nat} {e v : Expr}
    (hs : (whnfCoreStepW mode (fueledFns mode eager env) env c d e).val F = .ok (.done v)) :
    ∃ M, whnfCore mode eager env M d e c = .ok v := by
  rw [whnfCoreStepW_atF] at hs
  exact whnfCoreStepW_sound (G := 0) (st := .done v) hs rfl

end Sound

/-! ## The application-inference spine loop (task #50)

Same construction for `inferBody`'s app case: the type of an
application spine is inferred by walking the Π-telescope with deferred
substitution — syntactic `∀`-binders are peeled against the arguments
(each argument checked against its *substituted domain* only), the
codomain substituted once per peeled group; a non-syntactic telescope
step substitutes and normalizes, exactly like the chained body. -/

/-- The continuation of `inferBody`'s app case after the function
part's inference. -/
def inferStep (r : CoreFns m) (depth : Nat) (tf a : Expr) : m Expr := do
  match ← r.whnf depth tf with
  | .forallE ty body => do
    let ta ← r.infer depth a
    unless ← defeqArg r depth a ta ty do
      throw (.invalid "application type mismatch")
    pure (body.instantiate1 a)
  | _ => throw (.invalid "function expected")

/-- `inferBody`'s app case at the pure knot is one inference followed
by `inferStep` (stated at `CheckM`, where the do-notation reduces). -/
theorem inferBody_app_pure (env : Env) (F depth : Nat) (f a : Expr) :
    inferBody (pureFns mode eager env F) env depth (.app f a)
      = (pureFns mode eager env F).infer depth f >>= fun tf =>
          inferStep (pureFns mode eager env F) depth tf a := by rfl

/-- Pure mirror of the cached inference spine loop `inferSpineI`:
`ty` is the raw Π-telescope after the binders consumed so far, `acc`
their arguments (innermost first). -/
@[expose] def inferSpine (r : CoreFns m) (depth : Nat) :
    Expr → List Expr → List Expr → m Expr
  | ty, acc, [] => pure (ty.instantiateList acc)
  | ty, acc, a :: rest =>
    match ty with
    | .forallE dom body => do
      let ta ← r.infer depth a
      unless ← defeqArg r depth a ta (dom.instantiateList acc) do
        throw (.invalid "application type mismatch")
      inferSpine r depth body (a :: acc) rest
    | ty => do
      match ← r.whnf depth (ty.instantiateList acc) with
      | .forallE dom body => do
        let ta ← r.infer depth a
        unless ← defeqArg r depth a ta dom do
          throw (.invalid "application type mismatch")
        inferSpine r depth body [a] rest
      | _ => throw (.invalid "function expected")

/-- The syntactic-`∀` arm of `inferSpine`. -/
@[expose] def inferSpinePi (r : CoreFns m) (depth : Nat) (dom body : Expr)
    (acc : List Expr) (a : Expr) (rest : List Expr) :
    m Expr := do
  let ta ← r.infer depth a
  unless ← defeqArg r depth a ta (dom.instantiateList acc) do
    throw (.invalid "application type mismatch")
  inferSpine r depth body (a :: acc) rest

/-- The normalize-and-retry arm of `inferSpine`. -/
@[expose] def inferSpineWhnf (r : CoreFns m) (depth : Nat) (ty : Expr)
    (acc : List Expr) (a : Expr) (rest : List Expr) : m Expr := do
  match ← r.whnf depth (ty.instantiateList acc) with
  | .forallE dom body => do
    let ta ← r.infer depth a
    unless ← defeqArg r depth a ta dom do
      throw (.invalid "application type mismatch")
    inferSpine r depth body [a] rest
  | _ => throw (.invalid "function expected")

theorem inferSpine_nil (r : CoreFns m) (depth : Nat) (ty : Expr)
    (acc : List Expr) :
    inferSpine r depth ty acc [] = pure (ty.instantiateList acc) := by
  rw [inferSpine]

theorem inferSpine_pi (r : CoreFns m) (depth : Nat)
    (dom body : Expr) (acc : List Expr) (a : Expr)
    (rest : List Expr) :
    inferSpine r depth (.forallE dom body) acc (a :: rest)
      = inferSpinePi r depth dom body acc a rest := by
  rw [inferSpine, inferSpinePi]

theorem inferSpine_ne_pi (r : CoreFns m) (depth : Nat) {ty : Expr}
    (hty : ∀ dom body, ty ≠ .forallE dom body)
    (acc : List Expr) (a : Expr) (rest : List Expr) :
    inferSpine r depth ty acc (a :: rest)
      = inferSpineWhnf r depth ty acc a rest := by
  cases ty with
  | forallE dom body => exact absurd rfl (hty dom body)
  | _ => rw [inferSpine, inferSpineWhnf] <;> exact fun _ _ h => nomatch h

/-- The bulk substitution of a `∀`, exposed. -/
theorem instList_forallE (dom body : Expr)
    (acc : List Expr) :
    (Expr.forallE dom body).instantiateList acc
      = .forallE (dom.instantiateList acc)
          (body.instantiateList acc 1) := by
  simp [Expr.instantiateList]

section InferAtF

variable {env : Env}

theorem inferStep_atF (d : Nat) (tf a : Expr) (F : Nat) :
    (inferStep (fueledFns mode eager env) d tf a).val F
      = inferStep (pureFns mode eager env F) d tf a := by
  unfold inferStep
  atF_tac4

theorem inferSpine_atF (d : Nat) :
    ∀ (xs : List Expr) (ty : Expr) (acc : List Expr) (F : Nat),
      (inferSpine (fueledFns mode eager env) d ty acc xs).val F
        = inferSpine (pureFns mode eager env F) d ty acc xs
  | [], ty, acc, F => by rw [inferSpine_nil, inferSpine_nil]; rfl
  | a :: rest, ty, acc, F => by
    by_cases hpi : ∃ dom body, ty = Expr.forallE dom body
    · obtain ⟨dom, body, rfl⟩ := hpi
      rw [inferSpine_pi, inferSpine_pi]
      unfold inferSpinePi
      rw [FueledM.atF_bind]
      congr 1
      funext ta
      rw [FueledM.atF_bind]
      congr 1
      · exact defeqArg_atF d a ta _ F
      funext b
      cases b with
      | true =>
        show (inferSpine (fueledFns mode eager env) d body (a :: acc) rest).val F = _
        rw [inferSpine_atF d rest body (a :: acc) F]
        rfl
      | false => rfl
    · have hty : ∀ dom body, ty ≠ Expr.forallE dom body :=
        fun dom b hh => hpi ⟨dom, b, hh⟩
      rw [inferSpine_ne_pi _ _ hty, inferSpine_ne_pi _ _ hty]
      unfold inferSpineWhnf
      rw [FueledM.atF_bind]
      congr 1
      funext w
      cases w with
      | forallE dom body =>
        dsimp only
        rw [FueledM.atF_bind]
        congr 1
        funext ta
        rw [FueledM.atF_bind]
        congr 1
        · exact defeqArg_atF d a ta _ F
        funext b
        cases b with
        | true =>
          show (inferSpine (fueledFns mode eager env) d body [a] rest).val F = _
          rw [inferSpine_atF d rest body [a] F]
          rfl
        | false => rfl
      | _ => rfl

theorem inferSpine_mono {d : Nat} {xs acc : List Expr} {ty : Expr}
    {F F' : Nat} (hle : F ≤ F') {res : Expr}
    (h : inferSpine (pureFns mode eager env F) d ty acc xs = .ok res) :
    inferSpine (pureFns mode eager env F') d ty acc xs = .ok res := by
  rw [← inferSpine_atF] at h ⊢
  exact (inferSpine (fueledFns mode eager env) d ty acc xs).property hle h

theorem inferStep_mono {d : Nat} {tf a : Expr} {F F' : Nat}
    (hle : F ≤ F') {res : Expr}
    (h : inferStep (pureFns mode eager env F) d tf a = .ok res) :
    inferStep (pureFns mode eager env F') d tf a = .ok res := by
  rw [← inferStep_atF] at h ⊢
  exact (inferStep (fueledFns mode eager env) d tf a).property hle h

/-- `whnf` is the identity on a `∀` (at fuel `≥ 2`: one level for the
`whnfCore` inside the loop). -/
theorem whnf_forallE (F d : Nat) (t b : Expr)
    :
    whnf mode eager env (F + 2) d (.forallE t b) = .ok (.forallE t b) := by
  -- one iteration of the reduction loop suffices (task #106: the step
  -- budget is `irreducible`, so peel it with its positivity witness)
  obtain ⟨k, hk⟩ := whnfLoopFuel_succ
  rw [whnf_succ]
  show whnfLoop (pureFns mode eager env (F + 1)) env d whnfLoopFuel none _ = _
  rw [hk]
  rfl

end InferAtF

section InferSnoc

variable {env : Env}

theorem inferSpine_snoc {d : Nat} :
    ∀ (xs : List Expr) (ty : Expr) (acc : List Expr) (a : Expr) (F : Nat)
      (vres : Expr),
      inferSpine (pureFns mode eager env F) d ty acc (xs ++ [a]) = .ok vres →
      ∃ F' w, inferSpine (pureFns mode eager env F') d ty acc xs = .ok w ∧
        inferStep (pureFns mode eager env F') d w a = .ok vres
  | [], ty, acc, a, F, vres => by
    intro H
    rw [List.nil_append] at H
    by_cases hpi : ∃ dom body, ty = Expr.forallE dom body
    · obtain ⟨dom, body, rfl⟩ := hpi
      rw [inferSpine_pi] at H
      unfold inferSpinePi at H
      obtain ⟨ta, hta, H⟩ := bind_ok H
      obtain ⟨b, hb, H⟩ := bind_ok H
      cases b with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at H
        exact nomatch H
      | true =>
        simp only [↓reduceIte] at H
        rw [inferSpine_nil] at H
        injection H with h
        subst h
        refine ⟨F + 2, _, by rw [inferSpine_nil]; rfl, ?_⟩
        unfold inferStep
        rw [instList_forallE, whnf_def, whnf_forallE, ok_bind]
        dsimp only
        rw [infer_def, inferTypeCore_mono (Nat.le_add_right F 2) hta,
          ok_bind, defeqArg_mono (Nat.le_add_right F 2) hb,
          ok_bind]
        simp only [↓reduceIte]
        rw [← instList_cons0]
        rfl
    · have hty : ∀ dom body, ty ≠ Expr.forallE dom body :=
        fun dom b hh => hpi ⟨dom, b, hh⟩
      rw [inferSpine_ne_pi _ _ hty] at H
      unfold inferSpineWhnf at H
      obtain ⟨w₀, hw₀, H⟩ := bind_ok H
      refine ⟨F, ty.instantiateList acc, by rw [inferSpine_nil]; rfl, ?_⟩
      unfold inferStep
      rw [whnf_def]
      show (whnf mode eager env F d (ty.instantiateList acc) >>= _) = _
      rw [show whnf mode eager env F d (ty.instantiateList acc) = .ok w₀ from hw₀,
        ok_bind]
      cases w₀ with
      | forallE dom body =>
        dsimp only at H ⊢
        obtain ⟨ta, hta, H⟩ := bind_ok H
        obtain ⟨b, hb, H⟩ := bind_ok H
        rw [hta, ok_bind, hb, ok_bind]
        cases b with
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte] at H
          exact nomatch H
        | true =>
          simp only [↓reduceIte] at H ⊢
          rw [inferSpine_nil, instList_single] at H
          exact H
      | bvar i => exact nomatch H
      | fvar idx t => exact nomatch H
      | sort u => exact nomatch H
      | const nm us => exact nomatch H
      | app f' a' => exact nomatch H
      | lam t b => exact nomatch H
      | letE t v b => exact nomatch H
      | lit l => exact nomatch H
      | proj s i e => exact nomatch H
  | x :: xs', ty, acc, a, F, vres => by
    intro H
    rw [List.cons_append] at H
    by_cases hpi : ∃ dom body, ty = Expr.forallE dom body
    · obtain ⟨dom, body, rfl⟩ := hpi
      rw [inferSpine_pi] at H
      unfold inferSpinePi at H
      obtain ⟨ta, hta, H⟩ := bind_ok H
      obtain ⟨b, hb, H⟩ := bind_ok H
      cases b with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at H
        exact nomatch H
      | true =>
        simp only [↓reduceIte] at H
        obtain ⟨F₁, w, hw, hstep⟩ :=
          inferSpine_snoc xs' body (x :: acc) a F vres H
        refine ⟨max F F₁, w, ?_,
          inferStep_mono (Nat.le_max_right F F₁) hstep⟩
        rw [inferSpine_pi]
        unfold inferSpinePi
        rw [infer_def, inferTypeCore_mono (Nat.le_max_left F F₁) hta,
          ok_bind, defeqArg_mono (Nat.le_max_left F F₁) hb,
          ok_bind]
        simp only [↓reduceIte]
        exact inferSpine_mono (Nat.le_max_right F F₁) hw
    · have hty : ∀ dom body, ty ≠ Expr.forallE dom body :=
        fun dom b hh => hpi ⟨dom, b, hh⟩
      rw [inferSpine_ne_pi _ _ hty] at H
      unfold inferSpineWhnf at H
      obtain ⟨w₀, hw₀, H⟩ := bind_ok H
      cases w₀ with
      | forallE dom body =>
        dsimp only at H
        obtain ⟨ta, hta, H⟩ := bind_ok H
        obtain ⟨b, hb, H⟩ := bind_ok H
        cases b with
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte] at H
          exact nomatch H
        | true =>
          simp only [↓reduceIte] at H
          obtain ⟨F₁, w, hw, hstep⟩ :=
            inferSpine_snoc xs' body [x] a F vres H
          refine ⟨max F F₁, w, ?_,
            inferStep_mono (Nat.le_max_right F F₁) hstep⟩
          rw [inferSpine_ne_pi _ _ hty]
          unfold inferSpineWhnf
          rw [whnf_def]
          show (whnf mode eager env (max F F₁) d (ty.instantiateList acc) >>= _) = _
          rw [whnf_mono (Nat.le_max_left F F₁) hw₀, ok_bind]
          dsimp only
          rw [infer_def, inferTypeCore_mono (Nat.le_max_left F F₁) hta,
            ok_bind, defeqArg_mono (Nat.le_max_left F F₁) hb, ok_bind]
          simp only [↓reduceIte]
          exact inferSpine_mono (Nat.le_max_right F F₁) hw
      | bvar i => exact nomatch H
      | fvar idx t => exact nomatch H
      | sort u => exact nomatch H
      | const nm us => exact nomatch H
      | app f' a' => exact nomatch H
      | lam t b => exact nomatch H
      | letE t v b => exact nomatch H
      | lit l => exact nomatch H
      | proj s i e => exact nomatch H

private theorem inferSpine_sound_rev {d : Nat} :
    ∀ (rxs : List Expr) (h th vres : Expr) (F₀ F : Nat),
      inferTypeCore mode eager env F₀ d h = .ok th →
      inferSpine (pureFns mode eager env F) d th [] rxs.reverse = .ok vres →
      ∃ F', inferTypeCore mode eager env F' d (Expr.mkAppN h rxs.reverse) = .ok vres
  | [], h, th, vres, F₀, F => by
    intro hh H
    rw [List.reverse_nil, inferSpine_nil, Expr.instantiateList_nil] at H
    injection H with h1
    subst h1
    exact ⟨F₀, hh⟩
  | r :: rrs, h, th, vres, F₀, F => by
    intro hh H
    rw [List.reverse_cons] at H
    obtain ⟨F₁, w, hw, hstep⟩ := inferSpine_snoc rrs.reverse th [] r F vres H
    obtain ⟨F₂, hP⟩ := inferSpine_sound_rev rrs h th w F₀ F₁ hh hw
    refine ⟨max F₂ F₁ + 1, ?_⟩
    rw [List.reverse_cons, Expr.mkAppN_append_one, inferTypeCore_succ,
      inferBody_app_pure, infer_def,
      inferTypeCore_mono (Nat.le_max_left F₂ F₁) hP, ok_bind]
    exact inferStep_mono (Nat.le_max_right F₂ F₁) hstep

/-- A successful inference-spine run over the head's inferred type is
reproduced by the chained inference on the whole application, at some
fuel. -/
theorem inferSpine_sound {d : Nat} (xs : List Expr) (h th vres : Expr)
    (F₀ F : Nat) (hh : inferTypeCore mode eager env F₀ d h = .ok th)
    (H : inferSpine (pureFns mode eager env F) d th [] xs = .ok vres) :
    ∃ F', inferTypeCore mode eager env F' d (Expr.mkAppN h xs) = .ok vres := by
  have hx : xs.reverse.reverse = xs := List.reverse_reverse xs
  have := inferSpine_sound_rev (d := d) xs.reverse h th vres F₀ F hh
    (by rw [hx]; exact H)
  rwa [hx] at this

/-- The bridge the cached walk uses. -/
theorem inferSpine_sound_body (d : Nat) (fx ax : Expr) (vres : Expr)
    (F : Nat)
    (H : ((fueledFns mode eager env).infer d (Expr.app fx ax).getAppFn >>=
        fun tf => inferSpine (fueledFns mode eager env) d tf []
          (Expr.app fx ax).getAppArgs).val F = .ok vres) :
    ∃ F', (inferBody (fueledFns mode eager env) env d (.app fx ax)).val F'
      = .ok vres := by
  rw [FueledM.atF_bind] at H
  obtain ⟨th, hth, H⟩ := bind_ok H
  rw [inferSpine_atF] at H
  obtain ⟨F', hP⟩ := inferSpine_sound (Expr.app fx ax).getAppArgs
    (Expr.app fx ax).getAppFn th vres F F hth H
  rw [Expr.mkAppN_getApp] at hP
  cases F' with
  | zero =>
    rw [inferTypeCore_zero] at hP
    exact nomatch hP
  | succ G =>
    refine ⟨G, ?_⟩
    rw [inferBody_atF, ← inferTypeCore_succ]
    exact hP

end InferSnoc

section InferIOSpine

/-! ## The io-grade spine (task #172 B4, task #346)

The io twins of `inferStep`/`inferSpine` and their identification
with the io inference body over the io-grade view: what the cached
walks consume at the application clause.  The io grade is official's
`infer_only`: no argument is inferred or compared.  Everything is
stated over the knot's io *slot* family (`inferTypeIO` /
`CoreFns.inferIO`), which is the io lane (`inferTypeIO_on`). -/

variable {m : Type → Type} [Monad m] [MonadExceptOf CheckError m]

/-- The io continuation of the application clause: the head's type
reduces to a `∀`, whose body at the argument is the result. -/
def inferStepIO (r : CoreFns m) (depth : Nat)
    (tf a : Expr) : m Expr := do
  match ← r.whnf depth tf with
  | .forallE _ body => pure (body.instantiate1 a)
  | _ => throw (.invalid "function expected")

/-- The io-grade spine mirror (the cached `inferSpineIOI`'s pure
twin): no argument is checked. -/
@[expose] def inferSpineIO (r : CoreFns m) (depth : Nat) :
    Expr → List Expr → List Expr → m Expr
  | ty, acc, [] => pure (ty.instantiateList acc)
  | ty, acc, a :: rest =>
    match ty with
    | .forallE _ body => inferSpineIO r depth body (a :: acc) rest
    | ty => do
      match ← r.whnf depth (ty.instantiateList acc) with
      | .forallE _ body => inferSpineIO r depth body [a] rest
      | _ => throw (.invalid "function expected")

/-- The syntactic-`∀` arm of `inferSpineIO`. -/
@[expose] def inferSpineIOPi (r : CoreFns m) (depth : Nat)
    (body : Expr) (acc : List Expr) (a : Expr)
    (rest : List Expr) : m Expr :=
  inferSpineIO r depth body (a :: acc) rest

/-- The normalize-and-retry arm of `inferSpineIO`. -/
@[expose] def inferSpineIOWhnf (r : CoreFns m) (depth : Nat)
    (ty : Expr) (acc : List Expr) (a : Expr) (rest : List Expr) :
    m Expr := do
  match ← r.whnf depth (ty.instantiateList acc) with
  | .forallE _ body => inferSpineIO r depth body [a] rest
  | _ => throw (.invalid "function expected")

theorem inferSpineIO_nil (r : CoreFns m) (depth : Nat)
    (ty : Expr) (acc : List Expr) :
    inferSpineIO r depth ty acc [] = pure (ty.instantiateList acc) := by
  rw [inferSpineIO]

theorem inferSpineIO_pi (r : CoreFns m) (depth : Nat)
    (dom body : Expr) (acc : List Expr)
    (a : Expr) (rest : List Expr) :
    inferSpineIO r depth (.forallE dom body) acc (a :: rest)
      = inferSpineIOPi r depth body acc a rest := by
  rw [inferSpineIO, inferSpineIOPi]

theorem inferSpineIO_ne_pi (r : CoreFns m) (depth : Nat)
    {ty : Expr} (hty : ∀ dom body, ty ≠ .forallE dom body)
    (acc : List Expr) (a : Expr) (rest : List Expr) :
    inferSpineIO r depth ty acc (a :: rest)
      = inferSpineIOWhnf r depth ty acc a rest := by
  cases ty with
  | forallE dom body => exact absurd rfl (hty dom body)
  | _ => rw [inferSpineIO, inferSpineIOWhnf] <;>
      exact fun _ _ h => nomatch h

end InferIOSpine

section InferIOAtF

variable {mode : CheckMode} {eager : Bool} {env : Env}

theorem inferStepIO_atF (d : Nat) (tf a : Expr) (F : Nat) :
    (inferStepIO (fueledFns mode eager env) d tf a).val F
      = inferStepIO (pureFns mode eager env F) d tf a := by
  unfold inferStepIO
  atF_tac4

theorem inferSpineIO_atF (d : Nat) :
    ∀ (xs : List Expr) (ty : Expr) (acc : List Expr) (F : Nat),
      (inferSpineIO (fueledFns mode eager env) d ty acc xs).val F
        = inferSpineIO (pureFns mode eager env F) d ty acc xs
  | [], ty, acc, F => by rw [inferSpineIO_nil, inferSpineIO_nil]; rfl
  | a :: rest, ty, acc, F => by
    by_cases hpi : ∃ dom body, ty = Expr.forallE dom body
    · obtain ⟨dom, body, rfl⟩ := hpi
      rw [inferSpineIO_pi, inferSpineIO_pi]
      unfold inferSpineIOPi
      exact inferSpineIO_atF d rest body (a :: acc) F
    · have hty : ∀ dom body, ty ≠ Expr.forallE dom body :=
        fun dom b hh => hpi ⟨dom, b, hh⟩
      rw [inferSpineIO_ne_pi _ _ hty, inferSpineIO_ne_pi _ _ hty]
      unfold inferSpineIOWhnf
      rw [FueledM.atF_bind]
      congr 1
      funext w
      cases w with
      | forallE dom body => exact inferSpineIO_atF d rest body [a] F
      | _ => rfl

theorem inferSpineIO_mono {d : Nat} {xs acc : List Expr} {ty : Expr}
    {F F' : Nat} (hle : F ≤ F') {res : Expr}
    (h : inferSpineIO (pureFns mode eager env F) d ty acc xs = .ok res) :
    inferSpineIO (pureFns mode eager env F') d ty acc xs = .ok res := by
  rw [← inferSpineIO_atF] at h ⊢
  exact (inferSpineIO (fueledFns mode eager env) d ty acc xs).property hle h

theorem inferStepIO_mono {d : Nat} {tf a : Expr} {F F' : Nat}
    (hle : F ≤ F') {res : Expr}
    (h : inferStepIO (pureFns mode eager env F) d tf a = .ok res) :
    inferStepIO (pureFns mode eager env F') d tf a = .ok res := by
  rw [← inferStepIO_atF] at h ⊢
  exact (inferStepIO (fueledFns mode eager env) d tf a).property hle h

/-- The io inference body's app case over the io-grade view is one
io-slot inference followed by `inferStepIO` (stated at `CheckM`). -/
theorem inferBodyIO_app_pure (env : Env) (F depth : Nat) (f a : Expr) :
    inferBodyIO (CoreFns.ioView (pureFns mode eager env F)) env depth
        (.app f a)
      = (pureFns mode eager env F).inferIO depth f >>= fun tf =>
          inferStepIO (CoreFns.ioView (pureFns mode eager env F)) depth
            tf a := by rfl

/-- The io mirrors read only `whnf`, `inferIO` and `defeq`, none of
which the io-grade view touches, so the view is transparent to them. -/
theorem inferStepIO_ioView (F d : Nat) (tf a : Expr) :
    inferStepIO (CoreFns.ioView (pureFns mode eager env F)) d tf a
      = inferStepIO (pureFns mode eager env F) d tf a := by rfl

end InferIOAtF

section InferIOSnoc

variable {mode : CheckMode} {eager : Bool} {env : Env}

theorem inferSpineIO_snoc {d : Nat} :
    ∀ (xs : List Expr) (ty : Expr) (acc : List Expr) (a : Expr) (F : Nat)
      (vres : Expr),
      inferSpineIO (pureFns mode eager env F) d ty acc (xs ++ [a]) = .ok vres →
      ∃ F' w, inferSpineIO (pureFns mode eager env F') d ty acc xs = .ok w ∧
        inferStepIO (pureFns mode eager env F') d w a = .ok vres
  | [], ty, acc, a, F, vres => by
    intro H
    rw [List.nil_append] at H
    by_cases hpi : ∃ dom body, ty = Expr.forallE dom body
    · obtain ⟨dom, body, rfl⟩ := hpi
      rw [inferSpineIO_pi] at H
      unfold inferSpineIOPi at H
      refine ⟨F + 2, _, by rw [inferSpineIO_nil]; rfl, ?_⟩
      unfold inferStepIO
      rw [instList_forallE, whnf_def, whnf_forallE, ok_bind]
      dsimp only
      rw [inferSpineIO_nil] at H
      injection H with h1
      subst h1
      rw [← instList_cons0]
      rfl
    · have hty : ∀ dom body, ty ≠ Expr.forallE dom body :=
        fun dom b hh => hpi ⟨dom, b, hh⟩
      rw [inferSpineIO_ne_pi _ _ hty] at H
      unfold inferSpineIOWhnf at H
      obtain ⟨w₀, hw₀, H⟩ := bind_ok H
      refine ⟨F, ty.instantiateList acc, by rw [inferSpineIO_nil]; rfl, ?_⟩
      unfold inferStepIO
      rw [whnf_def]
      show (whnf mode eager env F d (ty.instantiateList acc) >>= _) = _
      rw [show whnf mode eager env F d (ty.instantiateList acc) = .ok w₀ from hw₀,
        ok_bind]
      cases w₀ with
      | forallE dom body =>
        dsimp only at H ⊢
        rw [inferSpineIO_nil, instList_single] at H
        exact H
      | bvar i => exact nomatch H
      | fvar idx t => exact nomatch H
      | sort u => exact nomatch H
      | const nm us => exact nomatch H
      | app f' a' => exact nomatch H
      | lam t b => exact nomatch H
      | letE t v b => exact nomatch H
      | lit l => exact nomatch H
      | proj s i e => exact nomatch H
  | x :: xs', ty, acc, a, F, vres => by
    intro H
    rw [List.cons_append] at H
    by_cases hpi : ∃ dom body, ty = Expr.forallE dom body
    · obtain ⟨dom, body, rfl⟩ := hpi
      rw [inferSpineIO_pi] at H
      unfold inferSpineIOPi at H
      obtain ⟨F₁, w, hw, hstep⟩ :=
        inferSpineIO_snoc xs' body (x :: acc) a F vres H
      refine ⟨F₁, w, ?_, hstep⟩
      rw [inferSpineIO_pi]
      unfold inferSpineIOPi
      exact hw
    · have hty : ∀ dom body, ty ≠ Expr.forallE dom body :=
        fun dom b hh => hpi ⟨dom, b, hh⟩
      rw [inferSpineIO_ne_pi _ _ hty] at H
      unfold inferSpineIOWhnf at H
      obtain ⟨w₀, hw₀, H⟩ := bind_ok H
      cases w₀ with
      | forallE dom body =>
        dsimp only at H
        obtain ⟨F₁, w, hw, hstep⟩ :=
          inferSpineIO_snoc xs' body [x] a F vres H
        refine ⟨max F F₁, w, ?_,
          inferStepIO_mono (Nat.le_max_right F F₁) hstep⟩
        rw [inferSpineIO_ne_pi _ _ hty]
        unfold inferSpineIOWhnf
        rw [whnf_def]
        show (whnf mode eager env (max F F₁) d (ty.instantiateList acc) >>= _) = _
        rw [whnf_mono (Nat.le_max_left F F₁) hw₀, ok_bind]
        exact inferSpineIO_mono (Nat.le_max_right F F₁) hw
      | bvar i => exact nomatch H
      | fvar idx t => exact nomatch H
      | sort u => exact nomatch H
      | const nm us => exact nomatch H
      | app f' a' => exact nomatch H
      | lam t b => exact nomatch H
      | letE t v b => exact nomatch H
      | lit l => exact nomatch H
      | proj s i e => exact nomatch H

private theorem inferSpineIO_sound_rev {d : Nat} :
    ∀ (rxs : List Expr) (h th vres : Expr) (F₀ F : Nat),
      inferTypeIO mode eager env F₀ d h = .ok th →
      inferSpineIO (pureFns mode eager env F) d th [] rxs.reverse
        = .ok vres →
      ∃ F', inferTypeIO mode eager env F' d (Expr.mkAppN h rxs.reverse)
        = .ok vres
  | [], h, th, vres, F₀, F => by
    intro hh H
    rw [List.reverse_nil, inferSpineIO_nil, Expr.instantiateList_nil] at H
    injection H with h1
    subst h1
    exact ⟨F₀, hh⟩
  | r :: rrs, h, th, vres, F₀, F => by
    intro hh H
    rw [List.reverse_cons] at H
    obtain ⟨F₁, w, hw, hstep⟩ :=
      inferSpineIO_snoc rrs.reverse th [] r F vres H
    obtain ⟨F₂, hP⟩ := inferSpineIO_sound_rev rrs h th w F₀ F₁ hh hw
    refine ⟨max F₂ F₁ + 1, ?_⟩
    rw [List.reverse_cons, Expr.mkAppN_append_one, inferTypeIO_succ,
      inferBodyIO_app_pure]
    rw [show (pureFns mode eager env (max F₂ F₁)).inferIO d
        (Expr.mkAppN h rrs.reverse)
      = inferTypeIO mode eager env (max F₂ F₁) d (Expr.mkAppN h rrs.reverse)
      from rfl]
    rw [inferTypeIO_mono (Nat.le_max_left F₂ F₁) hP, ok_bind]
    rw [inferStepIO_ioView]
    exact inferStepIO_mono (Nat.le_max_right F₂ F₁) hstep

/-- A successful io-spine run over the head's io-inferred type is
reproduced by the chained io slot on the whole application, at some
fuel. -/
theorem inferSpineIO_sound {d : Nat}
    (xs : List Expr) (h th vres : Expr) (F₀ F : Nat)
    (hh : inferTypeIO mode eager env F₀ d h = .ok th)
    (H : inferSpineIO (pureFns mode eager env F) d th [] xs = .ok vres) :
    ∃ F', inferTypeIO mode eager env F' d (Expr.mkAppN h xs) = .ok vres := by
  have hx : xs.reverse.reverse = xs := List.reverse_reverse xs
  have := inferSpineIO_sound_rev (d := d) xs.reverse h th vres F₀ F hh
    (by rw [hx]; exact H)
  rwa [hx] at this

/-- The bridge the cached io walk uses. -/
theorem inferSpineIO_sound_body (d : Nat)
    (fx ax : Expr) (vres : Expr) (F : Nat)
    (H : ((fueledFns mode eager env).inferIO d (Expr.app fx ax).getAppFn >>=
        fun tf => inferSpineIO (fueledFns mode eager env) d tf []
          (Expr.app fx ax).getAppArgs).val F = .ok vres) :
    ∃ F', (inferBodyIO (CoreFns.ioView (fueledFns mode eager env)) env d
      (.app fx ax)).val F' = .ok vres := by
  rw [FueledM.atF_bind] at H
  obtain ⟨th, hth, H⟩ := bind_ok H
  rw [inferSpineIO_atF] at H
  obtain ⟨F', hP⟩ := inferSpineIO_sound (Expr.app fx ax).getAppArgs
    (Expr.app fx ax).getAppFn th vres F F hth H
  rw [Expr.mkAppN_getApp] at hP
  cases F' with
  | zero =>
    rw [inferTypeIO_zero] at hP
    simp [throw, throwThe, MonadExceptOf.throw] at hP
  | succ G =>
    refine ⟨G, ?_⟩
    rw [inferBodyIO_atF]
    rw [inferTypeIO_succ] at hP
    exact hP

end InferIOSnoc

end ConLeche
