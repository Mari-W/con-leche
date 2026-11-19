module

public import ConLeche.Verify.Cached.BinderLoopC
import ConLeche.Verify.BetaSpine
import ConLeche.Verify.Cached.IndWalksC
import ConLeche.Verify.LooseBVar
public import ConLeche.Verify.ProjGuard

public section

/-!
# Cached body walks, part 4: head normalization and the whnf loop

Simulation walks (task #163) for the cached `reduceProjCoreI`,
`whnfHeadI`/`betaPeelI`/`whnfStuckI`, `whnfCoreStepI`/`whnfCoreLoopI`/`whnfCoreBodyI`,
`whnfLoopI`/`whnfBodyI`, `inferSpineI`/`inferSpineIOI` and
`inferBodyI`/`inferBodyIOI` (`ConLeche/Cached/CoreC.lean`) against the
pure fueled comparands.  Every walk is a `Std.WP` triple proved by
`vcgen` and `grind` (`ConLeche/Verify/Cached/Grind.lean`); the bodies
are stated as `BodySpec`s, which the knot (`KnotC.lean`) consumes.

The loops are unfolded by their own `eq_def` in the `vcgen` list (the
generated per-arm equations of their inner `match` are conditional, which
`vcgen` skips); the pure mirrors' own equation lemmas go into the `sym`
list.  The bodies' `Expr` dispatch is one level deep, so the pure
bodies are unfolded as they are (one equation per constructor); where the
cached body walks a loop the chained specification does not
(`whnfCoreBody`'s head-normalization loop, `inferBody`'s spine), a
guarded `Runs` bridge (`Runs.whnfCore_of_cont`, `Runs.inferBody_app`,
`Runs.inferBodyIO_app`) carries the loop's answer to the body's.

In `inferBodyI` the binder-telescope peel fuel is the constant
`peelFuelM`, opaque to the binder-loop tails, which quantify over the
fuel.
-/

set_option experimental.vcgen true

namespace ConLeche.Cached

open ConLeche.Expr Std.WP
open scoped Lean.Order

variable {mode : CheckMode} {eager : Bool}

section Walks

variable {env : Env} {f : Nat}

/-! ### The stuck spine

`whnfStuckI` answers a spine whose head is its own head normal form with the ι step at the one
prefix where it can fire (`iotaTarget`), and otherwise with the rules at the whole spine; its
mirror is `whnfStuckW`. -/

private theorem isStuckHeadC_getAppFn {h : Expr} (hh : isStuckHeadC h = true) :
    h.getAppFn = h := by
  cases h <;> first | rfl | exact nomatch hh

/-- At a spine whose head no rule rewrites (`noRulesC`) the rewrite step answers `none`. -/
theorem rewriteStep_noRules {m : Type → Type} [Monad m] [MonadExceptOf CheckError m]
    {r : CoreFns m} {d : Nat} {stuck : Bool} {x h : Expr} (hx : x.getAppFn = h)
    (hn : noRulesC (mkFEnv env) h = true) : rewriteStep r env d stuck x = pure none := by
  unfold rewriteStep
  rw [hx]
  cases h with
  | const c us =>
    simp only [noRulesC, mkFEnv_rulesFor, List.isEmpty_iff] at hn
    show (if (!stuck && unfoldableHead env x) = true then pure none
      else rewriteRules r env d x (env.rulesFor c)) = _
    rw [hn]
    split <;> rfl
  | _ => rfl

/-! The ι target's arms, one equation each. -/

theorem iotaTarget_rec {h : Expr} {c : Name} {us : List Level} {cv : ConstantVal} {mI rP : Nat}
    {isK : Bool} {rules : List RecRule} (h0 : h = .const c us)
    (h1 : env.find? c = some (.recInfo cv mI rP isK rules)) (h2 : us.length = cv.levelParams.length) :
    iotaTarget env h = some (mI + 1) := by
  subst h0; simp only [iotaTarget, h1, h2, ↓reduceIte]
grind_pattern [conleche_grind] iotaTarget_rec =>
    iotaTarget env h, Expr.const c us, ConstantInfo.recInfo cv mI rP isK rules where
  guard h = .const c us
  guard env.find? c = some (.recInfo cv mI rP isK rules)

theorem iotaTarget_lvl {h : Expr} {c : Name} {us : List Level} {cv : ConstantVal} {mI rP : Nat}
    {isK : Bool} {rules : List RecRule} (h0 : h = .const c us)
    (h1 : env.find? c = some (.recInfo cv mI rP isK rules)) (h2 : ¬ us.length = cv.levelParams.length) :
    iotaTarget env h = none := by
  subst h0; simp only [iotaTarget, h1, h2, ↓reduceIte]
grind_pattern [conleche_grind] iotaTarget_lvl =>
    iotaTarget env h, Expr.const c us, ConstantInfo.recInfo cv mI rP isK rules where
  guard h = .const c us
  guard env.find? c = some (.recInfo cv mI rP isK rules)

theorem iotaTarget_notrec {h : Expr} {c : Name} {us : List Level} (h0 : h = .const c us)
    (h1 : ∀ cv mI rP isK rules, env.find? c = some (.recInfo cv mI rP isK rules) → False) :
    iotaTarget env h = none := by
  subst h0
  cases hf : env.find? c with
  | none => simp only [iotaTarget, hf]
  | some ci =>
    cases ci <;> first | exact (h1 _ _ _ _ _ hf).elim | simp only [iotaTarget, hf]
grind_pattern [conleche_grind] iotaTarget_notrec => iotaTarget env h, Expr.const c us where
  guard h = .const c us

theorem iotaTarget_notconst {h : Expr} (h0 : ∀ c us, h = .const c us → False) :
    iotaTarget env h = none := by
  cases h with
  | const c us => exact (h0 c us rfl).elim
  | _ => rfl

/-- A range from `k` to the end is the suffix past `k`. -/
@[conleche_grind =] theorem mkAppRange_rest (f : Expr) (A : Array Expr) (k : Nat) :
    mkAppRange f A k A.size = Expr.mkAppN f (A.toList.drop k) := by
  rw [mkAppRange_eq, show A.toList.take A.size = A.toList from List.take_of_length_le (by simp)]

theorem getAppFn_getAppFn' (e : Expr) : e.getAppFn.getAppFn = e.getAppFn := by
  induction e with
  | app f a ih _ => simpa [Expr.getAppFn] using ih
  | _ => rfl

theorem toList_drop_of_lt {A : Array Expr} {i : Nat} (h : i < A.size) :
    A.toList.drop i = A[i] :: A.toList.drop (i + 1) := by
  rw [List.drop_eq_getElem_cons (by simpa using h)]
  simp

theorem toList_drop_of_ge {A : Array Expr} {i : Nat} (h : ¬ i < A.size) :
    A.toList.drop i = [] := by
  apply List.drop_eq_nil_of_le; simp; omega

/-- The peeled range `A[s:i+1]`, innermost first: one more argument in
front of `A[s:i]`. -/
theorem extract_rev_succ {A : Array Expr} {s i : Nat} (hs : s ≤ i) (h : i < A.size) :
    (A.extract s (i + 1)).toList.reverse = A[i] :: (A.extract s i).toList.reverse := by
  rw [← List.reverse_concat, Array.toList_extract, Array.toList_extract]
  congr 1
  simp only [List.extract_eq_take_drop]
  rw [show i + 1 - s = (i - s) + 1 by omega, List.take_add_one]
  simp [List.getElem?_drop, show s + (i - s) = i by omega, h]

/-- The one-argument range `A[i:i+1]`. -/
theorem extract_rev_single {A : Array Expr} {i : Nat} (h : i < A.size) :
    (A.extract i (i + 1)).toList.reverse = [A[i]] := by
  rw [extract_rev_succ (Nat.le_refl i) h]
  simp

theorem allWS_getAppArgs_app {d : Nat} {v a : Expr} (hv : Expr.WScoped d v)
    (ha : Expr.WScoped d a) : AllWS d (Expr.app v a).getAppArgs :=
  allWS_getAppArgs (by rw [wscoped_app_eq]; exact ⟨hv, ha⟩)
grind_pattern [conleche_grind] allWS_getAppArgs_app =>
  Expr.WScoped d v, Expr.WScoped d a, (Expr.app v a).getAppArgs

theorem AllWS.getElem {d : Nat} {A : Array Expr} (h : AllWS d A.toList) {i : Nat}
    (hi : i < A.size) : Expr.WScoped d A[i] :=
  h _ (by simp)
grind_pattern [conleche_grind] AllWS.getElem => AllWS d A.toList, A[i]

/-- The projection rule simulates its specification. -/
theorem reduceProjCoreC_spec (ih : SSimC mode eager env f) {d : Nat} {sn : Name} {ip : Nat}
    {i : Expr} {s₀ : CState} (hs : CSOK mode eager env s₀) (hw : Expr.WScoped d i) :
    ⦃fun s => s = s₀⦄
      reduceProjCoreI mode (mkFEnv env) eager f d sn ip i
    ⦃fun o s' => CSOK mode eager env s' ∧
      Runs (reduceProjCore mode (fueledFns mode eager env) env d sn ip i) o ∧ OptWS d o; ⊤⦄ := by
  sym only [conleche_grind, reduceProjCore, mkFEnv_findProj?, projCertAtF_mkFEnv] =>
    vcgen [reduceProjCoreI.eq_def, projLitToCtorC_spec ih] <;> finish

/-- The spine head is the constant `c`, at any levels. -/
@[expose] def HeadIs (c : Name) : Expr → Prop
  | .const c' _ => c' = c
  | _ => False

@[conleche_grind =] theorem HeadIs.const_eq (c c' : Name) (us : List Level) :
    HeadIs c (.const c' us) = (c' = c) := rfl

/-- The rewrite step at a spine headed by the constant `c`, past the δ gate, reads `c`'s rules. -/
theorem rewriteStep_head {m : Type → Type} [Monad m] [MonadExceptOf CheckError m]
    {r : CoreFns m} {d : Nat} {stuck : Bool} {e : Expr} {c : Name} {us : List Level}
    (h : e.getAppFn = .const c us) (hg : (!stuck && unfoldableHead env e) = false) :
    rewriteStep r env d stuck e = rewriteRules r env d e (env.rulesFor c) := by
  unfold rewriteStep; rw [h]; simp only [hg, Bool.false_eq_true, ↓reduceIte]
grind_pattern [conleche_grind] rewriteStep_head => rewriteStep r env d stuck e, Expr.const c us where
  guard e.getAppFn = .const c us
  guard (!stuck && unfoldableHead env e) = false

/-- The δ gate: a rule on a head that unfolds does not fire unless the unfolding got stuck. -/
theorem rewriteStep_gate {m : Type → Type} [Monad m] [MonadExceptOf CheckError m]
    {r : CoreFns m} {d : Nat} {e : Expr} (hg : unfoldableHead env e = true) :
    rewriteStep r env d false e = pure none := by
  unfold rewriteStep; split
  · simp only [hg, Bool.not_false, Bool.and_self, ↓reduceIte]
  · rfl

theorem rewriteStep_headIs {m : Type → Type} [Monad m] [MonadExceptOf CheckError m]
    {r : CoreFns m} {d : Nat} {stuck : Bool} {e : Expr} {c : Name} (h : HeadIs c e.getAppFn)
    (hg : (!stuck && unfoldableHead env e) = false) :
    rewriteStep r env d stuck e = rewriteRules r env d e (env.rulesFor c) := by
  unfold rewriteStep
  revert h
  cases e.getAppFn with
  | const c' us => rintro rfl; simp only [hg, Bool.false_eq_true, ↓reduceIte]
  | _ => intro h; exact h.elim

theorem rewriteStep_notconst {m : Type → Type} [Monad m] [MonadExceptOf CheckError m]
    {r : CoreFns m} {d : Nat} {stuck : Bool} {e : Expr}
    (h : ∀ c us, e.getAppFn = .const c us → False) :
    rewriteStep r env d stuck e = pure none := by
  unfold rewriteStep; split
  · next h' => exact (h _ _ h').elim
  · rfl

/-- A rule firing's scope side condition: the reduct is well-scoped. -/
@[expose] def RuleWS (d : Nat) : Option (Name × Expr) → Prop
  | none => True
  | some (_, e) => Expr.WScoped d e

@[conleche_grind =] theorem RuleWS.none_eq (d : Nat) : RuleWS d none = True := rfl

@[conleche_grind =] theorem RuleWS.some_eq (d : Nat) (t : Name) (e : Expr) :
    RuleWS d (some (t, e)) = Expr.WScoped d e := rfl

/-- A rule match's scope side condition: the matched view and the slots' bindings are
well-scoped. -/
@[expose] def MatchWS (d : Nat) :
    Option ((List (Option Expr) × List (Option Level)) × Expr) → Prop
  | none => True
  | some (st, x) => Expr.WScoped d x ∧ SlotsP (Expr.WScoped d) st

@[conleche_grind =] theorem MatchWS.none_eq (d : Nat) : MatchWS d none = True := rfl

@[conleche_grind =] theorem MatchWS.some_eq (d : Nat) (st : List (Option Expr) × List (Option Level))
    (x : Expr) : MatchWS d (some (st, x)) = (Expr.WScoped d x ∧ SlotsP (Expr.WScoped d) st) := rfl

grind_pattern [conleche_grind] SlotsP.set => SlotsP Q (st.1.set i (some a), st.2)
grind_pattern [conleche_grind] SlotsP.replicate => SlotsP Q (List.replicate n none, lv)
grind_pattern [conleche_grind] SlotsP.lv => SlotsP Q (sl, lv'), SlotsP Q (sl, lv)

/-! A variable position's four arms, one guarded equation each, on both sides. -/

theorem ruleBindVar_none {m : Type → Type} [Monad m] {r : CoreFns m} {d n k : Nat}
    {st : List (Option Expr) × List (Option Level)} {e : Expr} (h : ruleSlot? n k st.1 = none) :
    ruleBindVar r d n k st e = pure none := by
  unfold ruleBindVar; rw [h]
grind_pattern [conleche_grind] ruleBindVar_none => ruleBindVar r d n k st e where
  guard ruleSlot? n k st.1 = none

theorem ruleBindVar_fresh {m : Type → Type} [Monad m] {r : CoreFns m} {d n k : Nat}
    {st : List (Option Expr) × List (Option Level)} {e : Expr}
    (h : ruleSlot? n k st.1 = some none) :
    ruleBindVar r d n k st e = pure (some ((st.1.set (n - 1 - k) (some e), st.2), e)) := by
  unfold ruleBindVar; rw [h]
grind_pattern [conleche_grind] ruleBindVar_fresh => ruleBindVar r d n k st e where
  guard ruleSlot? n k st.1 = some none

theorem ruleBindVar_same {m : Type → Type} [Monad m] {r : CoreFns m} {d n k : Nat}
    {st : List (Option Expr) × List (Option Level)} {e e' : Expr}
    (h : ruleSlot? n k st.1 = some (some e')) (he : e' = e) :
    ruleBindVar r d n k st e = pure (some (st, e')) := by
  unfold ruleBindVar; rw [h]; exact ite_eq_left he
grind_pattern [conleche_grind] ruleBindVar_same => ruleBindVar r d n k st e, some (some e') where
  guard ruleSlot? n k st.1 = some (some e')
  guard e' = e

theorem ruleBindVar_diff {m : Type → Type} [Monad m] {r : CoreFns m} {d n k : Nat}
    {st : List (Option Expr) × List (Option Level)} {e e' : Expr}
    (h : ruleSlot? n k st.1 = some (some e')) (he : ¬e' = e) :
    ruleBindVar r d n k st e =
      (r.defeq d e' e >>= fun b => if b = true then pure (some (st, e')) else pure none) := by
  unfold ruleBindVar; rw [h]; exact ite_eq_right he
grind_pattern [conleche_grind] ruleBindVar_diff => ruleBindVar r d n k st e, some (some e') where
  guard ruleSlot? n k st.1 = some (some e')
  guard ¬e' = e

/-- A variable position simulates its specification: a repeated variable's comparison through
`ih.defeq_spec`, its binding scoped by the slot invariant. -/
theorem ruleBindVarC_spec (ih : SSimC mode eager env f) {d n k : Nat}
    (st : List (Option Expr) × List (Option Level)) {e : Expr} {s₀ : CState}
    (hs : CSOK mode eager env s₀) (hst : SlotsP (Expr.WScoped d) st) (hw : Expr.WScoped d e) :
    ⦃fun s => s = s₀⦄ ruleBindVarI mode (mkFEnv env) eager f d n k st e
    ⦃fun o s' => CSOK mode eager env s' ∧
      Runs (ruleBindVar (fueledFns mode eager env) d n k st e) o ∧ MatchWS d o; ⊤⦄ := by
  rcases hq : ruleSlot? n k st.1 with _ | (_ | e')
  · sym only [conleche_grind] => vcgen [ruleBindVarI.eq_def] <;> finish
  · sym only [conleche_grind] => vcgen [ruleBindVarI.eq_def] <;> finish
  · have hw' : Expr.WScoped d e' := hst e' (ruleSlot?_mem hq)
    by_cases he : e' = e
    · sym only [conleche_grind] => vcgen [ruleBindVarI.eq_def] <;> finish
    · sym only [conleche_grind] => vcgen [ruleBindVarI.eq_def, ih.defeq_spec] <;> finish

/-- The match's arguments' scope side condition: the matched view is well-scoped. -/
@[expose] def ArgsWS (d : Nat) : Option (List Expr × List Level × Expr) → Prop
  | none => True
  | some (_, _, x) => Expr.WScoped d x

@[conleche_grind =] theorem ArgsWS.none_eq (d : Nat) : ArgsWS d none = True := rfl

@[conleche_grind =] theorem ArgsWS.some_eq (d : Nat) (args : List Expr) (us : List Level)
    (x : Expr) : ArgsWS d (some (args, us, x)) = Expr.WScoped d x := rfl

/-! The argument step's two arms, one guarded equation each. -/

theorem ruleArgStep_var {m : Type → Type} [Monad m] [MonadExceptOf CheckError m]
    {r : CoreFns m} {d n j : Nat}
    {k : Expr → m (Option ((List (Option Expr) × List (Option Level)) × Expr))} {p a : Expr}
    {st : List (Option Expr) × List (Option Level)} (h : p.bvarIdx? = some j) :
    ruleArgStep r env d n k p st a = ruleBindVar r d n j st a := by
  unfold ruleArgStep; rw [h]
grind_pattern [conleche_grind] ruleArgStep_var => ruleArgStep r env d n k p st a, some j where
  guard p.bvarIdx? = some j

theorem ruleArgStep_pat {m : Type → Type} [Monad m] [MonadExceptOf CheckError m]
    {r : CoreFns m} {d n : Nat}
    {k : Expr → m (Option ((List (Option Expr) × List (Option Level)) × Expr))} {p a : Expr}
    {st : List (Option Expr) × List (Option Level)} (h : p.bvarIdx? = none) :
    ruleArgStep r env d n k p st a = ruleOrRetry r env d k a := by
  unfold ruleArgStep; rw [h]
grind_pattern [conleche_grind] ruleArgStep_pat => ruleArgStep r env d n k p st a where
  guard p.bvarIdx? = none

grind_pattern [conleche_grind] ruleOrRetry.eq_1 => ruleOrRetry r env depth k a

/-- The retry simulates its specification. -/
theorem ruleRetryC_spec (ih : SSimC mode eager env f) {d : Nat} {a : Expr} {s₀ : CState}
    (hs : CSOK mode eager env s₀) (hw : Expr.WScoped d a) :
    ⦃fun s => s = s₀⦄ ruleRetryI mode (mkFEnv env) eager f d a
    ⦃fun r s' => CSOK mode eager env s' ∧ Runs (ruleRetry (fueledFns mode eager env) env d a) r ∧
      Expr.WScoped d r; ⊤⦄ := by
  sym only [conleche_grind, ruleRetry, litToCtorIfNat_WScoped] =>
    vcgen [ruleRetryI.eq_def, ih.whnf_spec,
      litToCtorIfNatC_spec (mode := mode) (eager := eager) (env := env)] <;> finish

/-- The argument step simulates its specification, given the match's at the same pattern. -/
theorem ruleArgC_spec (ih : SSimC mode eager env f) {d n : Nat} {lps : List Name} {p : Expr}
    (hm : ∀ (st : List (Option Expr) × List (Option Level)) {e : Expr} {s₀ : CState},
      CSOK mode eager env s₀ → SlotsP (Expr.WScoped d) st → Expr.WScoped d e →
      ⦃fun s => s = s₀⦄ ruleMatchI mode (mkFEnv env) eager f d n lps p st e
      ⦃fun o s' => CSOK mode eager env s' ∧
        Runs (ruleMatchM (fueledFns mode eager env) env d n lps p st e) o ∧ MatchWS d o; ⊤⦄)
    (st : List (Option Expr) × List (Option Level)) {a : Expr} {s₀ : CState}
    (hs : CSOK mode eager env s₀) (hst : SlotsP (Expr.WScoped d) st) (hw : Expr.WScoped d a) :
    ⦃fun s => s = s₀⦄ ruleArgI mode (mkFEnv env) eager f d n lps p st a
    ⦃fun o s' => CSOK mode eager env s' ∧
      Runs (ruleArgStep (fueledFns mode eager env) env d n
        (ruleMatchM (fueledFns mode eager env) env d n lps p st) p st a) o ∧ MatchWS d o; ⊤⦄ := by
  cases hq : p.bvarIdx? with
  | some j => sym only [conleche_grind] => vcgen [ruleArgI.eq_def, ruleBindVarC_spec ih] <;> finish
  | none =>
    sym only [conleche_grind] =>
      vcgen [ruleArgI.eq_def, hm, ruleRetryC_spec ih] <;> finish

/-- The cached match's view of an application where nothing changed is the application. -/
@[conleche_grind =] theorem appView_eq (f' a f₁ a₁ : Expr) :
    appView (.app f' a) f' a f₁ a₁ = Expr.app f₁ a₁ := by
  unfold appView
  split
  · rename_i h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    rw [h.1, h.2]
  · rfl

/-- A rule's match simulates its specification. -/
theorem ruleMatchC_spec (ih : SSimC mode eager env f) {d n : Nat} {lps : List Name} :
    ∀ (pat : Expr) (st : List (Option Expr) × List (Option Level)) {e : Expr} {s₀ : CState},
      CSOK mode eager env s₀ → SlotsP (Expr.WScoped d) st → Expr.WScoped d e →
      ⦃fun s => s = s₀⦄ ruleMatchI mode (mkFEnv env) eager f d n lps pat st e
      ⦃fun o s' => CSOK mode eager env s' ∧
        Runs (ruleMatchM (fueledFns mode eager env) env d n lps pat st e) o ∧ MatchWS d o; ⊤⦄ := by
  intro pat
  induction pat with
  | app g q ihg ihq =>
    intro st e s₀ hs hst hw
    cases e with
    | app g' a =>
      sym only [conleche_grind, ruleMatchM] =>
        vcgen [ruleMatchI.eq_def, ihg, ruleArgC_spec ih ihq] <;> finish
    | _ => sym only [conleche_grind, ruleMatchM] => vcgen [ruleMatchI.eq_def] <;> finish
  | const c ls =>
    intro st e s₀ hs hst hw
    cases e with
    | const c' ls' =>
      obtain ⟨sl, lv⟩ := st
      cases hm : matchLevels lps lv ls ls' <;>
        sym only [conleche_grind, ruleMatchM, Option.map_none, Option.map_some] =>
          vcgen [ruleMatchI.eq_def] <;> finish
    | _ => sym only [conleche_grind, ruleMatchM] => vcgen [ruleMatchI.eq_def] <;> finish
  | _ => intro st e s₀ hs hst hw; sym only [conleche_grind, ruleMatchM] => vcgen [ruleMatchI.eq_def] <;> finish

/-- The match's arguments simulate their specification. -/
theorem ruleArgsC_spec (ih : SSimC mode eager env f) {d : Nat} (cv : ConstantVal) {e : Expr}
    {s₀ : CState} (hs : CSOK mode eager env s₀) (hw : Expr.WScoped d e) :
    ⦃fun s => s = s₀⦄ ruleArgsI mode (mkFEnv env) eager f d cv e
    ⦃fun o s' => CSOK mode eager env s' ∧
      Runs (ruleArgsM (fueledFns mode eager env) env d cv e) o ∧ ArgsWS d o; ⊤⦄ := by
  unfold ruleArgsI ruleArgsM
  split
  · sym only [conleche_grind] => vcgen [ruleMatchC_spec ih] <;> finish
  · sym only [conleche_grind] => vcgen <;> finish

/-- One rule's firing after its match simulates its specification: the theorem's type through
the memo, then every check the specification's. -/
theorem rewriteFireC_spec (ih : SSimC mode eager env f) (henv : EnvWF env) {d : Nat}
    {t : Name} {cv : ConstantVal} (hft : env.find? t = some (.thmInfo cv)) (args : List Expr)
    (us : List Level) {e₁ : Expr} {s₀ : CState} (hs : CSOK mode eager env s₀)
    (hw : Expr.WScoped d e₁) :
    ⦃fun s => s = s₀⦄ rewriteFireI mode (mkFEnv env) eager f d t cv args us e₁
    ⦃fun o s' => CSOK mode eager env s' ∧
      Runs (rewriteFire (fueledFns mode eager env) env d cv args us e₁) o ∧ OptWS d o; ⊤⦄ := by
  unfold rewriteFireI rewriteFire
  have hfind : (env.find? t).isSome = true := by rw [hft]; rfl
  have hcl : cv.type.hasFvar = false := (henv.consts _ (Env.find?_mem hft)).1
  have hT : constTyOf env t us = cv.type.instantiateLevelParams cv.levelParams us := by
    simp [constTyOf, hft, ConstantInfo.toConstantVal]
  have hwT : Expr.WScoped d (cv.type.instantiateLevelParams cv.levelParams us) :=
    Expr.WScoped.of_not_hasFvar (by rw [Expr.hasFvar_instantiateLevelParams]; exact hcl)
  cases hsp : (piResidual (cv.type.instantiateLevelParams cv.levelParams us) args).bind
      eqSpine? with
  | none =>
    sym only [conleche_grind] =>
      vcgen [constTyAtM_spec (mode := mode) (eager := eager) (env := env) hs t t us hfind,
        piResidualM_spec (mode := mode) (eager := eager) (env := env)] <;> finish
  | some q =>
    obtain ⟨eqn, u, A, l, rhs⟩ := q
    dsimp only
    by_cases hg : RuleGate cv us args e₁ eqn l rhs
    · rw [ite_eq_left hg]
      have hargs : AllWS d args := fun x hx => appSubterms_WScoped e₁ (hg.2.2.2.1 x hx) hw
      obtain ⟨R, hres, hR⟩ : ∃ R, piResidual
          (cv.type.instantiateLevelParams cv.levelParams us) args = some R ∧
          eqSpine? R = some (eqn, u, A, l, rhs) := by
        cases h : piResidual (cv.type.instantiateLevelParams cv.levelParams us) args with
        | none => rw [h] at hsp; exact nomatch hsp
        | some R => rw [h] at hsp; exact ⟨R, rfl, hsp⟩
      rw [eqSpine?_eq_some] at hR
      subst hR
      have hwR := piResidual_WScoped hres hwT hargs
      simp only [Expr.WScoped] at hwR
      have hwA := hwR.1.1.2
      have hwr := hwR.2
      sym only [conleche_grind] =>
        vcgen [constTyAtM_spec (mode := mode) (eager := eager) (env := env) hs t t us hfind,
          piResidualM_spec (mode := mode) (eager := eager) (env := env),
          iotaCertsFullC_spec ih, ih.infer_spec] <;> finish
    · rw [ite_eq_right hg]
      sym only [conleche_grind] =>
        vcgen [constTyAtM_spec (mode := mode) (eager := eager) (env := env) hs t t us hfind,
          piResidualM_spec (mode := mode) (eager := eager) (env := env)] <;> finish

/-- One rule's firing simulates its specification: the match, then the firing. -/
theorem rewriteAttemptC_spec (ih : SSimC mode eager env f) (henv : EnvWF env) {d : Nat}
    {e : Expr} (t : Name) {s₀ : CState} (hs : CSOK mode eager env s₀) (hw : Expr.WScoped d e) :
    ⦃fun s => s = s₀⦄ rewriteAttemptI mode (mkFEnv env) eager f d e t
    ⦃fun o s' => CSOK mode eager env s' ∧
      Runs (rewriteAttempt (fueledFns mode eager env) env d e t) o ∧ OptWS d o; ⊤⦄ := by
  unfold rewriteAttemptI rewriteAttempt
  rw [mkFEnv_find_fun]
  cases hft : env.find? t with
  | none => sym only [conleche_grind] => vcgen <;> finish
  | some ci =>
    cases ci
    case thmInfo cv =>
      dsimp only
      sym only [conleche_grind] =>
        vcgen [ruleArgsC_spec ih cv, rewriteFireC_spec ih henv hft] <;> finish
    all_goals sym only [conleche_grind] => vcgen <;> finish

/-- A rule at the prefix of its arity simulates its specification. -/
theorem rewriteAtC_spec (ih : SSimC mode eager env f) (henv : EnvWF env) {d : Nat} (t : Name) :
    ∀ (e : Expr) {s₀ : CState}, CSOK mode eager env s₀ → Expr.WScoped d e →
    ⦃fun s => s = s₀⦄ rewriteAtI mode (mkFEnv env) eager f d t e
    ⦃fun o s' => CSOK mode eager env s' ∧
      Runs (rewriteAt (fueledFns mode eager env) env d t e) o ∧ OptWS d o; ⊤⦄ := by
  intro e
  induction e with
  | app fn a ihf _ =>
    intro s₀ hs hw
    sym only [conleche_grind, rewriteAt] =>
      vcgen [rewriteAtI.eq_def, rewriteAttemptC_spec ih henv t, ihf] <;> finish
  | _ =>
    intro s₀ hs hw
    rw [rewriteAtI.eq_def, rewriteAt_nonApp _ _ _ _ (by intro _ _ hh; cases hh)]
    exact rewriteAttemptC_spec ih henv t hs hw

/-- The rules in order simulate their specification. -/
theorem rewriteRulesC_spec (ih : SSimC mode eager env f) (henv : EnvWF env) {d : Nat}
    {e : Expr} (hw : Expr.WScoped d e) (ts : List Name) :
    ∀ {s₀ : CState}, CSOK mode eager env s₀ →
    ⦃fun s => s = s₀⦄ rewriteRulesI mode (mkFEnv env) eager f d e ts
    ⦃fun o s' => CSOK mode eager env s' ∧
      Runs (rewriteRules (fueledFns mode eager env) env d e ts) o ∧ RuleWS d o; ⊤⦄ := by
  induction ts with
  | nil =>
    intro s₀ hs
    sym only [conleche_grind, rewriteRules] => vcgen [rewriteRulesI.eq_def] <;> finish
  | cons t ts iht =>
    intro s₀ hs
    sym only [conleche_grind, rewriteRules] =>
      vcgen [rewriteRulesI.eq_def, rewriteAtC_spec ih henv t, iht] <;> finish

/-- The rewrite step simulates its specification: the index's rules are `Env.rulesFor`'s. -/
theorem rewriteStepC_spec (ih : SSimC mode eager env f) (henv : EnvWF env) {d : Nat}
    {stuck : Bool} {e : Expr} {s₀ : CState} (hs : CSOK mode eager env s₀)
    (hw : Expr.WScoped d e) :
    ⦃fun s => s = s₀⦄ rewriteStepI mode (mkFEnv env) eager f d stuck e
    ⦃fun o s' => CSOK mode eager env s' ∧
      Runs (rewriteStep (fueledFns mode eager env) env d stuck e) o ∧ RuleWS d o; ⊤⦄ := by
  unfold rewriteStepI rewriteStep
  rw [mkFEnv_rulesFor_fun, unfoldableHeadC_spec]
  cases e.getAppFn with
  | const c ls =>
    by_cases hg : (!stuck && unfoldableHead env e) = true
    · simp only [hg, ↓reduceIte]
      sym only [conleche_grind] => vcgen <;> finish
    · simp only [hg, Bool.false_eq_true, ↓reduceIte]
      exact rewriteRulesC_spec ih henv hw _ hs
  | _ => sym only [conleche_grind] => vcgen <;> finish

/-- A rule firing's count (`tickRuleI`) keeps the invariant: no clause reads the count. -/
theorem CSOK.tickRule {s : CState} (hs : CSOK mode eager env s) :
    CSOK mode eager env s.tickRule :=
  { hs with }
grind_pattern [conleche_grind] CSOK.tickRule => CSOK mode eager env s, s.tickRule

/-- The rules fired again simulate their specification: the cached loop counts every firing
against the declaration's total, and rejects where the specification stops. -/
theorem fireMoreC_spec (ih : SSimC mode eager env f) (henv : EnvWF env) {d : Nat} :
    ∀ (k : Nat) {e : Expr} {s₀ : CState}, CSOK mode eager env s₀ → Expr.WScoped d e →
    ⦃fun s => s = s₀⦄ fireMoreI mode (mkFEnv env) eager f d k e
    ⦃fun v s' => CSOK mode eager env s' ∧
      Runs (fireMore (fueledFns mode eager env) env d k e) v ∧ Expr.WScoped d v; ⊤⦄ := by
  intro k
  induction k with
  | zero =>
    intro e s₀ hs hw
    sym only [conleche_grind, fireMore] =>
      vcgen [fireMoreI.eq_def, rewriteStepC_spec ih henv] <;> finish
  | succ k ihk =>
    intro e s₀ hs hw
    sym only [conleche_grind, fireMore, CSOK.tickRule] =>
      vcgen [fireMoreI.eq_def, rewriteStepC_spec ih henv, tickRuleI, ihk] <;> finish

/-- Noting an origin at a well-scoped term keeps the origin well scoped. -/
theorem OptWS.note {d : Nat} {o : Option Expr} {e : Expr} (ho : OptWS d o)
    (he : Expr.WScoped d e) : OptWS d (noteOrigin env o e) := by
  cases hn : noteOrigin env o e with
  | none => trivial
  | some o' =>
    rcases noteOrigin_cases hn with rfl | rfl
    · exact ho
    · exact he
grind_pattern [conleche_grind] OptWS.note => OptWS d (noteOrigin env o e)

@[conleche_grind =] theorem noteOriginC_eq (env : Env) (o : Option Expr) (e : Expr) :
    noteOriginC (mkFEnv env) o e = noteOrigin env o e := noteOriginC_spec

@[conleche_grind =] theorem isStuckResultC_eq (env : Env) (e : Expr) :
    isStuckResultC (mkFEnv env) e = isStuckResult env e := isStuckResultC_spec

@[conleche_grind =] theorem unfoldableHeadC_eq (env : Env) (e : Expr) :
    unfoldableHeadC (mkFEnv env) e = unfoldableHead env e := unfoldableHeadC_spec

/-- The rules at an origin simulate their specification. -/
theorem originFireC_spec (ih : SSimC mode eager env f) (henv : EnvWF env) {d : Nat}
    {o : Option Expr} {e : Expr} {s₀ : CState} (hs : CSOK mode eager env s₀)
    (ho : OptWS d o) :
    ⦃fun s => s = s₀⦄ originFireI mode (mkFEnv env) eager f d o e
    ⦃fun r s' => CSOK mode eager env s' ∧
      Runs (originFire (fueledFns mode eager env) env d o e) r ∧ RuleWS d r; ⊤⦄ := by
  unfold originFireI originFire
  cases o with
  | none => sym only [conleche_grind] => vcgen <;> finish
  | some o' =>
    dsimp only
    rw [isStuckResultC_spec]
    by_cases hst : isStuckResult env e = true
    · simp only [hst, ↓reduceIte]
      sym only [conleche_grind] =>
        vcgen [rewriteStepC_spec ih henv, fireMoreC_spec ih henv] <;> finish
    · simp only [hst, Bool.false_eq_true, ↓reduceIte]
      sym only [conleche_grind] => vcgen <;> finish


/-! ### The application step, by `vcgen` and `grind`

Each walk below is `sym only [conleche_grind, …] => vcgen […] <;> finish`
(`ConLeche/Verify/Cached/Grind.lean`).  The peel loop matches its body on `.lam`, and the
equation compiler states its `a :: rest` step as one equation per arm, the fall-through one
conditional, which `vcgen` skips; the unconditional `eq_def` unfolds it instead.  `vcgen` splits
the `match` and hands each arm its fall-through hypothesis; the pure mirror's own equation
lemmas (`betaPeelW.eq_*`, the fall-through one included) go into the `sym` list, and `grind`
discharges the fall-through premise from the arm's hypothesis. -/

/-- The peel step's scope: a binder peeled off a well-scoped
instantiated lambda, instantiated with one more well-scoped argument. -/
theorem wscoped_peel {d : Nat} {ty body a : Expr} {acc : List Expr}
    (hw : Expr.WScoped d ((Expr.lam ty body).instantiateList acc)) (ha : Expr.WScoped d a) :
    Expr.WScoped d (body.instantiateList (a :: acc)) := by
  rw [instList_lam, Expr.WScoped] at hw
  rw [Expr.instantiateList_cons]
  exact Expr.WScoped.instantiate1_gen ha 0 hw.2
grind_pattern [conleche_grind] wscoped_peel =>
  Expr.WScoped d ((Expr.lam ty body).instantiateList acc), body.instantiateList (a :: acc)

/-- The peel loop simulates its pure mirror: the peeled range
`args[j:i]` is the mirror's accumulator, innermost first. -/
theorem betaPeelC_spec (lv : Nat) {d : Nat} :
    ∀ (n : Nat) {args : Array Expr} {j i : Nat} {t : Expr} {s₀ : CState},
      args.size - i = n → j ≤ i → CSOK mode eager env s₀ →
      Expr.WScoped d (t.instantiateList (args.extract j i).toList.reverse) →
      AllWS d args.toList →
      ⦃fun s => s = s₀⦄ betaPeelI mode (mkFEnv env) eager lv d t j args i
      ⦃fun v s' => CSOK mode eager env s' ∧
          Runs (betaPeelW mode (fueledFns mode eager env) env d t
            (args.extract j i).toList.reverse (args.toList.drop i)) v ∧
          StepWS d v; ⊤⦄ := by
  intro n
  induction n with
  | zero =>
    intro args j i t s₀ hn _ hs _ _
    sym only [conleche_grind, betaPeelW.eq_1, Expr.instantiateRevRange_spec,
        toList_drop_of_ge (A := args) (i := i) (by omega)] =>
      vcgen [betaPeelI.eq_def] <;> finish
  | succ n ihr =>
    intro args j i t s₀ hn hj hs _ _
    sym only [conleche_grind, betaPeelW.eq_2, betaPeelW.eq_3, Expr.instantiateRevRange_spec,
        toList_drop_of_lt (A := args) (i := i) (by omega),
        extract_rev_succ (A := args) (s := j) (i := i) hj (by omega)] =>
      vcgen [betaPeelI.eq_def, ihr (args := args) (j := j) (i := i + 1) (by omega) (by omega)] <;>
        finish

/-! The stuck mirror's tail, one equation per arm. -/

@[conleche_grind =] theorem whnfStuckTail_some (d : Nat) (e : Expr) (k : Nat) (e'' : Expr) :
    whnfStuckTail (fueledFns .verified eager env) env d e k (some e'') =
      pure (.cont (Expr.mkAppN e'' (e.getAppArgs.drop k))) := rfl

@[conleche_grind =] theorem whnfStuckTail_none (d : Nat) (e : Expr) (k : Nat) :
    whnfStuckTail (fueledFns .verified eager env) env d e k none =
      whnfStuckRuleW (fueledFns .verified eager env) env d e := rfl

/-- An application's argument list is not empty. -/
theorem getAppArgs_app_ne_nil' (fn a : Expr) : (Expr.app fn a).getAppArgs ≠ [] :=
  getAppArgs_app_ne_nil fn a
grind_pattern [conleche_grind] getAppArgs_app_ne_nil' => (Expr.app fn a).getAppArgs

/-- The rule arm of the stuck spine simulates its pure mirror: where the head has no rule, the
rewrite step answers `none`. -/
theorem whnfStuckRuleC_spec (ih : SSimC .verified eager env f) (henv : EnvWF env) {d : Nat}
    {e : Expr} {s₀ : CState} (hs : CSOK .verified eager env s₀) (hw : Expr.WScoped d e) :
    ⦃fun s => s = s₀⦄ whnfStuckRuleI .verified (mkFEnv env) eager f d e.getAppFn e
    ⦃fun v s' => CSOK .verified eager env s' ∧
      Runs (whnfStuckRuleW (fueledFns .verified eager env) env d e) v ∧ StepWS d v; ⊤⦄ := by
  cases hnr : noRulesC (mkFEnv env) e.getAppFn with
  | true =>
    sym only [conleche_grind, whnfStuckRuleW,
        rewriteStep_noRules (r := fueledFns .verified eager env) (d := d) (stuck := false) rfl hnr] =>
      vcgen [whnfStuckRuleI.eq_def] <;> finish
  | false =>
    sym only [conleche_grind, whnfStuckRuleW] =>
      vcgen [whnfStuckRuleI.eq_def, rewriteStepC_spec ih henv, fireMoreC_spec ih henv] <;> finish

/-- The stuck arm simulates its pure mirror: the ι step at its target prefix, then the rules. -/
theorem whnfStuckC_spec (ih : SSimC .verified eager env f)
    (henv : EnvWF env) {d : Nat} {i : Expr} {s₀ : CState}
    (hs : CSOK .verified eager env s₀) (hw : Expr.WScoped d i) :
    ⦃fun s => s = s₀⦄
      whnfStuckI .verified (mkFEnv env) eager f d i.getAppFn i
    ⦃fun v s' => CSOK .verified eager env s' ∧
      Runs (whnfStuckW .verified (fueledFns .verified eager env) env d i.getAppFn i) v ∧
      StepWS d v; ⊤⦄ := by
  have hwa : AllWS d i.getAppArgs := allWS_getAppArgs hw
  sym only [conleche_grind, whnfStuckW, iotaNumArgs_eq_length, iotaTarget_notconst] =>
    vcgen [whnfStuckI.eq_def, iotaRecC_spec ih henv, whnfStuckRuleC_spec ih henv] <;> finish

/-- A stuck head is its own head normal form. -/
theorem Runs.whnfCore_stuckHead {c : Bool} {d : Nat} {h : Expr} (hh : isStuckHeadC h = true)
    (hnr : noRulesC (mkFEnv env) h = true) :
    Runs ((fueledFns .verified eager env).whnfCore c d h) h := by
  refine ⟨1, ?_⟩
  cases h with
  | const n us =>
    show whnfCoreBody .verified (pureFns .verified eager env 0) env c d (.const n us) = _
    simp only [whnfCoreBody]
    rw [rewriteStep_noRules (r := pureFns .verified eager env 0) (d := d) rfl hnr]
    rfl
  | _ => first | rfl | exact nomatch hh

/-- At a stuck head with no rule the mirror's application step is the stuck arm: the head is
its own head normal form. -/
theorem whnfStuckFastC_spec (ih : SSimC .verified eager env f)
    (henv : EnvWF env) {c : Bool} {d : Nat} {i : Expr} {s₀ : CState}
    (hs : CSOK .verified eager env s₀) (hw : Expr.WScoped d i)
    (hh' : (isStuckHeadC i.getAppFn && noRulesC (mkFEnv env) i.getAppFn) = true) :
    ⦃fun s => s = s₀⦄
      whnfStuckI .verified (mkFEnv env) eager f d i.getAppFn i
    ⦃fun v s' => CSOK .verified eager env s' ∧
      Runs ((fueledFns .verified eager env).whnfCore c d i.getAppFn >>= fun w =>
        whnfHeadW .verified (fueledFns .verified eager env) env d w i.getAppFn i) v ∧
      StepWS d v; ⊤⦄ := by
  have hh : isStuckHeadC i.getAppFn = true := (Bool.and_eq_true _ _ ▸ hh').1
  have hnr : noRulesC (mkFEnv env) i.getAppFn = true := (Bool.and_eq_true _ _ ▸ hh').2
  have hne : ∀ ty b, i.getAppFn ≠ .lam ty b := by
    intro ty b hb; rw [hb] at hh; exact nomatch hh
  have heq : whnfHeadW .verified (fueledFns .verified eager env) env d i.getAppFn i.getAppFn i =
      whnfStuckW .verified (fueledFns .verified eager env) env d i.getAppFn i := by
    rw [whnfHeadW_ne_lam _ _ _ hne, ite_eq_left rfl]
  simp only [Runs.bind_eq _ (Runs.whnfCore_stuckHead (eager := eager) (c := c) (d := d) hh hnr),
    heq]
  exact whnfStuckC_spec ih henv hs hw

/-- The cached application step at a head that is not a λ. -/
theorem whnfHeadI_ne_lam {d : Nat} {v : Expr} (hv : ∀ ty b, v ≠ .lam ty b) (h e : Expr) :
    whnfHeadI .verified (mkFEnv env) eager f d v h e =
      if v = h then whnfStuckI .verified (mkFEnv env) eager f d h e
      else (do
        let args ← pure (getAppArgsArr e)
        pure (.cont (mkAppRange v args 0 args.size))) := by
  cases v with
  | lam ty b => exact absurd rfl (hv ty b)
  | _ => rw [whnfHeadI.eq_def]

/-- The application step past the head's normalization simulates its pure mirror. -/
theorem whnfHeadC_spec (ih : SSimC .verified eager env f)
    (henv : EnvWF env) {d : Nat} {v i : Expr} {s₀ : CState}
    (hs : CSOK .verified eager env s₀) (hw : Expr.WScoped d i)
    (hv : Expr.WScoped d v) (hne : i.getAppArgs ≠ []) :
    ⦃fun s => s = s₀⦄
      whnfHeadI .verified (mkFEnv env) eager f d v i.getAppFn i
    ⦃fun st s' => CSOK .verified eager env s' ∧
      Runs (whnfHeadW .verified (fueledFns .verified eager env) env d v i.getAppFn i) st ∧
      StepWS d st; ⊤⦄ := by
  have hwa : AllWS d i.getAppArgs := allWS_getAppArgs hw
  by_cases hlam : ∃ ty body, v = Expr.lam ty body
  · obtain ⟨ty, body, rfl⟩ := hlam
    rw [whnfHeadW_lam]
    cases hargs : i.getAppArgs with
    | nil => exact absurd hargs hne
    | cons a₁ rest =>
      have hA : (getAppArgsArr i).toList = a₁ :: rest := by
        rw [getAppArgsArr_toList, hargs]
      have hpos : 0 < (getAppArgsArr i).size := by
        rw [← Array.length_toList, hA]; simp
      have hex : ((getAppArgsArr i).extract 0 1).toList.reverse = [a₁] := by
        rw [extract_rev_single hpos]
        simp only [List.cons.injEq, and_true]
        rw [← Array.getElem_toList (h := by simpa using hpos)]
        simp [hA]
      have hdr : (getAppArgsArr i).toList.drop 1 = rest := by rw [hA]; rfl
      rw [hargs] at hwa
      have hw1 : Expr.WScoped d (body.instantiateList [a₁]) := by
        rw [instList_single]
        simp only [Expr.WScoped] at hv
        exact Expr.WScoped.instantiate1_gen (hwa a₁ List.mem_cons_self) 0 hv.2
      have hall : AllWS d (getAppArgsArr i).toList := by rw [hA]; exact hwa
      have := betaPeelC_spec (mode := .verified) (eager := eager) (env := env) f
        (d := d) _ (args := getAppArgsArr i) (j := 0) (i := 1) (t := body) rfl
        (by omega) hs (by rw [hex]; exact hw1) hall
      rw [hex, hdr] at this
      rw [whnfHeadI.eq_def]
      exact this
  · have hne' : ∀ ty body, v ≠ Expr.lam ty body := fun ty b hh => hlam ⟨ty, b, hh⟩
    rw [whnfHeadW_ne_lam _ _ _ hne']
    rw [whnfHeadI_ne_lam hne']
    by_cases hvh : v = i.getAppFn
    · rw [ite_eq_left hvh, ite_eq_left hvh]
      exact whnfStuckC_spec ih henv hs hw
    · rw [ite_eq_right hvh, ite_eq_right hvh]
      sym only [conleche_grind, List.drop_zero] =>
        vcgen <;> finish

/-- One head-normalization step simulates its pure mirror. -/
theorem whnfCoreStepC_spec (ih : SSimC .verified eager env f)
    (henv : EnvWF env) {c : Bool} {d : Nat} {i : Expr} {s₀ : CState} (hs : CSOK .verified eager env s₀)
    (hw : Expr.WScoped d i) :
    ⦃fun s => s = s₀⦄
      whnfCoreStepI .verified (mkFEnv env) eager f c d i.getAppFn i
    ⦃fun v s' => CSOK .verified eager env s' ∧
      Runs (whnfCoreStepW .verified (fueledFns .verified eager env) env c d i) v ∧ StepWS d v; ⊤⦄ := by
  sym only [conleche_grind, whnfCoreStepW] =>
    vcgen [whnfCoreStepI.eq_def, inst1M_spec hs, ih.whnfCore_spec, ih.whnf_spec,
      reduceProjCoreC_spec ih, whnfHeadC_spec ih henv, whnfStuckFastC_spec (c := c) ih henv,
      rewriteStepC_spec ih henv, fireMoreC_spec ih henv] <;> finish

/-! ### The head-normalization loop and its memo policy

The cached loop (`whnfCoreLoopI`) looks every key up and stores the
keys of a chain at its end.  Its answer is stated against the chained
`whnfCore` directly: a hit is the backed `CSOK` clause, an answering
step is `whnfCore_of_stepW_done` and a continuing one
`whnfCore_of_stepW_cont`.  The keys waiting for the answer satisfy
`PendOK`: each answers what the current term answers. -/

/-- An easy case is its own whnfCore answer (`whnfCoreBody`'s value arms). -/
theorem Runs.whnfCore_easy {c : Bool} {d : Nat} {i : Expr}
    (h : (whnfCoreEasy i && noRulesC (mkFEnv env) i) = true) :
    Runs ((fueledFns mode eager env).whnfCore c d i) i := by
  refine ⟨1, ?_⟩
  cases i with
  | const n us =>
    show whnfCoreBody mode (pureFns mode eager env 0) env c d (.const n us) = _
    simp only [whnfCoreBody]
    rw [rewriteStep_noRules (r := pureFns mode eager env 0) (d := d) rfl
      (Bool.and_eq_true _ _ ▸ h).2]
    rfl
  | _ => first | rfl | exact nomatch h
grind_pattern [conleche_grind] Runs.whnfCore_easy =>
  Runs ((fueledFns mode eager env).whnfCore c d i) i

/-- A full whnfCore memo hit answers the fueled whnfCore, well scoped. -/
theorem CSOK.whnfCore_hit (henv : EnvWF env) {s : CState} {d : Nat} {i r : Expr}
    (hs : CSOK mode eager env s) (hl : s.whnfCoreC[i]? = some r) (hw : Expr.WScoped d i) :
    Runs ((fueledFns mode eager env).whnfCore false d i) r ∧ Expr.WScoped d r := by
  obtain ⟨F, hall⟩ := hs.whnfCoreC i r hl
  have hrun := hall d hw.to_wscopedB
  exact ⟨⟨F, hrun⟩, whnfCore_WScoped henv F hrun hw⟩
grind_pattern [conleche_grind] CSOK.whnfCore_hit =>
  CSOK mode eager env s, s.whnfCoreC[i]?, Runs ((fueledFns mode eager env).whnfCore false d i) r

/-- A cheap whnfCore memo hit answers the fueled cheap whnfCore. -/
theorem CSOK.whnfCoreCheap_hit (henv : EnvWF env) {s : CState} {d : Nat} {i r : Expr}
    (hs : CSOK mode eager env s) (hl : s.whnfCoreCheapC[i]? = some r) (hw : Expr.WScoped d i) :
    Runs ((fueledFns mode eager env).whnfCore true d i) r ∧ Expr.WScoped d r := by
  obtain ⟨F, hall⟩ := hs.whnfCoreCheapC i r hl
  have hrun := hall d hw.to_wscopedB
  exact ⟨⟨F, hrun⟩, whnfCore_WScoped henv F hrun hw⟩
grind_pattern [conleche_grind] CSOK.whnfCoreCheap_hit =>
  CSOK mode eager env s, s.whnfCoreCheapC[i]?, Runs ((fueledFns mode eager env).whnfCore true d i) r

/-- A continuing step: the term answers what its continuation answers. -/
theorem Runs.whnfCore_of_cont {c : Bool} {d : Nat} {e e' v : Expr}
    (hs : Runs (whnfCoreStepW mode (fueledFns mode eager env) env c d e) (.cont e'))
    (hk : Runs ((fueledFns mode eager env).whnfCore c d e') v) :
    Runs ((fueledFns mode eager env).whnfCore c d e) v := by
  obtain ⟨F, hF⟩ := hs
  obtain ⟨G, hG⟩ := hk
  exact whnfCore_of_stepW_cont hF hG
grind_pattern [conleche_grind] Runs.whnfCore_of_cont =>
  Runs (whnfCoreStepW mode (fueledFns mode eager env) env c d e) (.cont e'),
  Runs ((fueledFns mode eager env).whnfCore c d e') v

/-- A firing step: the term answers what its continuation answers. -/
theorem Runs.whnfCore_of_fire {c : Bool} {d : Nat} {e e' v : Expr} {t : Name}
    (hs : Runs (whnfCoreStepW mode (fueledFns mode eager env) env c d e) (.fire t e'))
    (hk : Runs ((fueledFns mode eager env).whnfCore c d e') v) :
    Runs ((fueledFns mode eager env).whnfCore c d e) v := by
  obtain ⟨F, hF⟩ := hs
  obtain ⟨G, hG⟩ := hk
  exact whnfCore_of_stepW_fire hF hG
grind_pattern [conleche_grind] Runs.whnfCore_of_fire =>
  Runs (whnfCoreStepW mode (fueledFns mode eager env) env c d e) (.fire t e'),
  Runs ((fueledFns mode eager env).whnfCore c d e') v

/-- An answering step: its answer is the term's. -/
theorem Runs.whnfCore_of_done {c : Bool} {d : Nat} {e v : Expr}
    (hs : Runs (whnfCoreStepW mode (fueledFns mode eager env) env c d e) (.done v)) :
    Runs ((fueledFns mode eager env).whnfCore c d e) v := by
  obtain ⟨F, hF⟩ := hs
  exact whnfCore_of_stepW_done hF
grind_pattern [conleche_grind] Runs.whnfCore_of_done =>
  Runs (whnfCoreStepW mode (fueledFns mode eager env) env c d e) (.done v),
  (fueledFns mode eager env).whnfCore c d e

/-- A lambda or a stuck head no rule rewrites is its own head normal form in both modes. -/
private theorem whnfCore_cheapHead {c : Bool} {d : Nat} {h : Expr}
    (hh : (match h with | .lam .. => true | h => isStuckHeadC h) = true)
    (hnr : noRulesC (mkFEnv env) h = true) :
    (fueledFns mode eager env).whnfCore true d h = (fueledFns mode eager env).whnfCore c d h := by
  apply Subtype.ext; funext F
  cases F with
  | zero => rfl
  | succ F =>
    cases h with
    | const n us =>
      show whnfCoreBody mode (pureFns mode eager env F) env true d (.const n us) =
        whnfCoreBody mode (pureFns mode eager env F) env c d (.const n us)
      simp only [whnfCoreBody]
      rw [rewriteStep_noRules (r := pureFns mode eager env F) (d := d) rfl hnr]
      rfl
    | _ => first | rfl | exact nomatch hh

/-- A step the two modes take alike (`whnfCoreCheapSafeC`) is the same step
in the cheap mode. -/
theorem whnfCoreStepW_cheap {c : Bool} {d : Nat} {e : Expr}
    (h' : (whnfCoreCheapSafeC e.getAppFn e && noRulesC (mkFEnv env) e.getAppFn) = true) :
    whnfCoreStepW mode (fueledFns mode eager env) env true d e
      = whnfCoreStepW mode (fueledFns mode eager env) env c d e := by
  have h := (Bool.and_eq_true _ _ ▸ h').1
  have hnr := (Bool.and_eq_true _ _ ▸ h').2
  cases e with
  | app f a =>
    simp only [whnfCoreStepW]
    rw [whnfCore_cheapHead (c := c) h hnr]
  | letE _ _ _ => rfl
  | _ => exact nomatch h

/-- The keys pending in the loop: each, well scoped, answers what `e`
answers (in the mode `c`). -/
@[expose] def PendOK (mode : CheckMode) (eager : Bool) (env : Env) (c : Bool) (d : Nat)
    (pend : List Expr) (e : Expr) : Prop :=
  ∀ k ∈ pend, Expr.WScoped d k ∧ ∀ v, Runs ((fueledFns mode eager env).whnfCore c d e) v →
    Runs ((fueledFns mode eager env).whnfCore c d k) v

@[conleche_grind] theorem PendOK.nil {c : Bool} {d : Nat} {e : Expr} :
    PendOK mode eager env c d [] e := by
  intro k hk; exact nomatch hk

/-- The term itself joins its pending keys. -/
theorem PendOK.self {c : Bool} {d : Nat} {pend : List Expr} {e : Expr}
    (hp : PendOK mode eager env c d pend e) (hw : Expr.WScoped d e) :
    PendOK mode eager env c d (e :: pend) e := by
  intro k hk
  rcases List.mem_cons.mp hk with rfl | hk
  · exact ⟨hw, fun _ h => h⟩
  · exact hp k hk
grind_pattern [conleche_grind] PendOK.self =>
  PendOK mode eager env c d pend e, PendOK mode eager env c d (e :: pend) e

/-- Past a continuing step, the pending keys answer what the
continuation answers. -/
theorem PendOK.cont {c : Bool} {d : Nat} {pend : List Expr} {e e' : Expr}
    (hp : PendOK mode eager env c d pend e)
    (hs : Runs (whnfCoreStepW mode (fueledFns mode eager env) env c d e) (.cont e')) :
    PendOK mode eager env c d pend e' :=
  fun k hk => ⟨(hp k hk).1, fun _ h => (hp k hk).2 _ (Runs.whnfCore_of_cont hs h)⟩
grind_pattern [conleche_grind] PendOK.cont =>
  PendOK mode eager env c d pend e,
  Runs (whnfCoreStepW mode (fueledFns mode eager env) env c d e) (.cont e'),
  PendOK mode eager env c d pend e'

/-- Past a firing step, the pending keys answer what the continuation answers. -/
theorem PendOK.fire {c : Bool} {d : Nat} {pend : List Expr} {e e' : Expr} {t : Name}
    (hp : PendOK mode eager env c d pend e)
    (hs : Runs (whnfCoreStepW mode (fueledFns mode eager env) env c d e) (.fire t e')) :
    PendOK mode eager env c d pend e' :=
  fun k hk => ⟨(hp k hk).1, fun _ h => (hp k hk).2 _ (Runs.whnfCore_of_fire hs h)⟩

/-- The cheap-mode keys past a step the two modes take alike. -/
theorem PendOK.contCheap {c : Bool} {d : Nat} {pend : List Expr} {e e' : Expr}
    (hp : PendOK mode eager env true d pend e) (hsafe : (whnfCoreCheapSafeC e.getAppFn e && noRulesC (mkFEnv env) e.getAppFn) = true)
    (hs : Runs (whnfCoreStepW mode (fueledFns mode eager env) env c d e) (.cont e')) :
    PendOK mode eager env true d pend e' := by
  rw [← whnfCoreStepW_cheap hsafe] at hs
  exact PendOK.cont hp hs
grind_pattern [conleche_grind] PendOK.contCheap =>
  PendOK mode eager env true d pend e,
  Runs (whnfCoreStepW mode (fueledFns mode eager env) env c d e) (.cont e'),
  PendOK mode eager env true d pend e'

/-- The cheap-mode keys past a firing step the two modes take alike. -/
theorem PendOK.fireCheap {c : Bool} {d : Nat} {pend : List Expr} {e e' : Expr} {t : Name}
    (hp : PendOK mode eager env true d pend e)
    (hsafe : (whnfCoreCheapSafeC e.getAppFn e && noRulesC (mkFEnv env) e.getAppFn) = true)
    (hs : Runs (whnfCoreStepW mode (fueledFns mode eager env) env c d e) (.fire t e')) :
    PendOK mode eager env true d pend e' := by
  rw [← whnfCoreStepW_cheap hsafe] at hs
  exact PendOK.fire hp hs

/-- An answering step the two modes take alike answers the cheap mode too. -/
theorem Runs.whnfCore_of_doneCheap {c : Bool} {d : Nat} {e v : Expr}
    (hsafe : (whnfCoreCheapSafeC e.getAppFn e && noRulesC (mkFEnv env) e.getAppFn) = true)
    (hs : Runs (whnfCoreStepW mode (fueledFns mode eager env) env c d e) (.done v)) :
    Runs ((fueledFns mode eager env).whnfCore true d e) v := by
  rw [← whnfCoreStepW_cheap hsafe] at hs
  exact Runs.whnfCore_of_done hs
grind_pattern [conleche_grind] Runs.whnfCore_of_doneCheap =>
  Runs (whnfCoreStepW mode (fueledFns mode eager env) env c d e) (.done v),
  (fueledFns mode eager env).whnfCore true d e

/-- A memo whose entries are backed keeps them so under inserting
backed keys, one answer for all. -/
private theorem foldl_insert_backed {P : Expr → Expr → Prop} {v : Expr} :
    ∀ {pend : List Expr} {m : Std.HashMap Expr Expr}, (∀ k w, m[k]? = some w → P k w) →
      (∀ k ∈ pend, P k v) →
      ∀ k w, (pend.foldl (fun m k => m.insert k v) m)[k]? = some w → P k w
  | [], _, hm, _ => hm
  | k :: rest, _, hm, hp =>
    foldl_insert_backed (pend := rest) (HashMap.insert_backed hm (hp k (.head _)))
      (fun k' hk' => hp k' (.tail _ hk'))

/-- A pending key, answered by `v` at `e`, is a backed memo entry. -/
private theorem PendOK.backed (henv : EnvWF env) {c : Bool} {d : Nat} {pend : List Expr}
    {e v : Expr} (hp : PendOK mode eager env c d pend e)
    (hv : Runs ((fueledFns mode eager env).whnfCore c d e) v) :
    ∀ k ∈ pend, ∃ F, ∀ d', (Expr.wscopedB d' k) = true →
      whnfCore mode eager env F d' k c = .ok v := by
  intro k hk
  obtain ⟨hw, hrun⟩ := hp k hk
  obtain ⟨F, hF⟩ := hrun v hv
  exact ⟨F, fun d' hd' => by rw [whnfCore_depth_inv henv F hd' hw.to_wscopedB]; exact hF⟩

/-- A finished chain's store keeps the invariant: its full keys answer
`v` in the full mode, its cheap keys in the cheap mode. -/
theorem CSOK.chainStored (henv : EnvWF env) {s : CState} {d : Nat} {pend pendC : List Expr}
    {e v : Expr} (hs : CSOK mode eager env s)
    (hp : PendOK mode eager env false d pend e)
    (hv : Runs ((fueledFns mode eager env).whnfCore false d e) v)
    (hpc : PendOK mode eager env true d pendC e)
    (hvc : Runs ((fueledFns mode eager env).whnfCore true d e) v) :
    CSOK mode eager env (storeChain s pend pendC v) :=
  { hs with
    whnfCoreC := foldl_insert_backed hs.whnfCoreC (hp.backed henv hv)
    whnfCoreCheapC := foldl_insert_backed hs.whnfCoreCheapC (hpc.backed henv hvc) }
grind_pattern [conleche_grind] CSOK.chainStored =>
  CSOK mode eager env s, PendOK mode eager env false d pend e,
  PendOK mode eager env true d pendC e, storeChain s pend pendC v

/-- A store with no cheap keys (the chain took a step the modes take
differently, or ended at a hit). -/
theorem CSOK.chainStored_nil (henv : EnvWF env) {s : CState} {d : Nat} {pend : List Expr}
    {e v : Expr} (hs : CSOK mode eager env s)
    (hp : PendOK mode eager env false d pend e)
    (hv : Runs ((fueledFns mode eager env).whnfCore false d e) v) :
    CSOK mode eager env (storeChain s pend [] v) :=
  { hs with
    whnfCoreC := foldl_insert_backed hs.whnfCoreC (hp.backed henv hv)
    whnfCoreCheapC := hs.whnfCoreCheapC }
grind_pattern [conleche_grind] CSOK.chainStored_nil =>
  CSOK mode eager env s, PendOK mode eager env false d pend e, storeChain s pend [] v

/-- The loop's continuing arm: the keys it passes on, the term joining
them where it is stored, answer what the continuation answers. -/
theorem PendOK.push {b : Bool} {c : Bool} {d : Nat} {pend : List Expr}
    {e e' : Expr} (hp : PendOK mode eager env c d pend e) (hw : Expr.WScoped d e)
    (hs : Runs (whnfCoreStepW mode (fueledFns mode eager env) env c d e) (.cont e')) :
    PendOK mode eager env c d (pushKey b e pend) e' := by
  unfold pushKey
  split
  · exact PendOK.cont (hp.self hw) hs
  · exact PendOK.cont hp hs
grind_pattern [conleche_grind] PendOK.push =>
  PendOK mode eager env c d (pushKey b e pend) e',
  Runs (whnfCoreStepW mode (fueledFns mode eager env) env c d e) (.cont e')

/-- The loop's firing arm: as its continuing arm. -/
theorem PendOK.pushFire {b : Bool} {c : Bool} {d : Nat} {pend : List Expr}
    {e e' : Expr} {t : Name} (hp : PendOK mode eager env c d pend e) (hw : Expr.WScoped d e)
    (hs : Runs (whnfCoreStepW mode (fueledFns mode eager env) env c d e) (.fire t e')) :
    PendOK mode eager env c d (pushKey b e pend) e' := by
  unfold pushKey
  split
  · exact PendOK.fire (hp.self hw) hs
  · exact PendOK.fire hp hs
grind_pattern [conleche_grind] PendOK.pushFire =>
  PendOK mode eager env c d (pushKey b e pend) e',
  Runs (whnfCoreStepW mode (fueledFns mode eager env) env c d e) (.fire t e')

/-- The loop's firing arm, cheap keys. -/
theorem PendOK.pushCheapFire {b : Bool} {c : Bool} {d : Nat} {pend : List Expr}
    {e e' : Expr} {t : Name} (hp : PendOK mode eager env true d pend e) (hw : Expr.WScoped d e)
    (hs : Runs (whnfCoreStepW mode (fueledFns mode eager env) env c d e) (.fire t e')) :
    PendOK mode eager env true d
      (pushCheapKey (whnfCoreCheapSafeC e.getAppFn e && noRulesC (mkFEnv env) e.getAppFn) b e
        pend) e' := by
  unfold pushCheapKey pushKey
  split
  · rename_i hsafe
    split
    · exact PendOK.fireCheap (hp.self hw) hsafe hs
    · exact PendOK.fireCheap hp hsafe hs
  · exact PendOK.nil
grind_pattern [conleche_grind] PendOK.pushCheapFire =>
  PendOK mode eager env true d
    (pushCheapKey (whnfCoreCheapSafeC e.getAppFn e && noRulesC (mkFEnv env) e.getAppFn) b e pend)
    e',
  Runs (whnfCoreStepW mode (fueledFns mode eager env) env c d e) (.fire t e')

/-- The loop's continuing arm, cheap keys: kept past a step the two
modes take alike, dropped past any other. -/
theorem PendOK.pushCheap {b : Bool} {c : Bool} {d : Nat} {pend : List Expr}
    {e e' : Expr} (hp : PendOK mode eager env true d pend e) (hw : Expr.WScoped d e)
    (hs : Runs (whnfCoreStepW mode (fueledFns mode eager env) env c d e) (.cont e')) :
    PendOK mode eager env true d (pushCheapKey (whnfCoreCheapSafeC e.getAppFn e && noRulesC (mkFEnv env) e.getAppFn) b e pend) e' := by
  unfold pushCheapKey pushKey
  split
  · rename_i hsafe
    split
    · exact PendOK.contCheap (hp.self hw) hsafe hs
    · exact PendOK.contCheap hp hsafe hs
  · exact PendOK.nil
grind_pattern [conleche_grind] PendOK.pushCheap =>
  PendOK mode eager env true d (pushCheapKey (whnfCoreCheapSafeC e.getAppFn e && noRulesC (mkFEnv env) e.getAppFn) b e pend) e',
  Runs (whnfCoreStepW mode (fueledFns mode eager env) env c d e) (.cont e')

/-- The loop's answering arm in the full mode: the chain's keys, the term
joining them where it is stored, stored with the answer. -/
theorem CSOK.chainStoredDone (henv : EnvWF env) {b c : Bool} {s : CState}
    {d : Nat} {pend pendC : List Expr} {e v : Expr} (hs : CSOK mode eager env s)
    (hc : c = false)
    (hp : PendOK mode eager env c d pend e) (hpc : PendOK mode eager env true d pendC e)
    (hw : Expr.WScoped d e)
    (hst : Runs (whnfCoreStepW mode (fueledFns mode eager env) env c d e) (.done v)) :
    CSOK mode eager env (storeChain s (pushKey b e pend) (pushCheapKey (whnfCoreCheapSafeC e.getAppFn e && noRulesC (mkFEnv env) e.getAppFn) b e pendC) v) := by
  subst hc
  have hv := Runs.whnfCore_of_done hst
  have hp' : PendOK mode eager env false d (pushKey b e pend) e := by
    unfold pushKey
    split
    · exact hp.self hw
    · exact hp
  unfold pushCheapKey
  split
  · rename_i hsafe
    have hvc := Runs.whnfCore_of_doneCheap hsafe hst
    refine CSOK.chainStored henv hs hp' hv ?_ hvc
    unfold pushKey
    split
    · exact hpc.self hw
    · exact hpc
  · exact CSOK.chainStored_nil henv hs hp' hv
grind_pattern [conleche_grind] CSOK.chainStoredDone =>
  storeChain s (pushKey b e pend) (pushCheapKey (whnfCoreCheapSafeC e.getAppFn e && noRulesC (mkFEnv env) e.getAppFn) b e pendC) v,
  Runs (whnfCoreStepW mode (fueledFns mode eager env) env c d e) (.done v)

/-- Entering and leaving a rules-last restart keeps the invariant: no clause reads the count. -/
theorem CSOK.nestEnter {s : CState} (hs : CSOK mode eager env s) :
    CSOK mode eager env s.nestEnter :=
  { hs with }
grind_pattern [conleche_grind] CSOK.nestEnter => CSOK mode eager env s, s.nestEnter

theorem CSOK.nestLeave {s : CState} (hs : CSOK mode eager env s) :
    CSOK mode eager env s.nestLeave :=
  { hs with }
grind_pattern [conleche_grind] CSOK.nestLeave => CSOK mode eager env s, s.nestLeave

/-- The head-normalization *loop* answers the chained `whnfCore` of its
term, by induction on the shared step budget (task #106); a step's
outcome is the same on both sides, a continuation re-enters the loop
(task #342 R2), and the memo is looked up at every key and written with
the chain's keys at its end. -/
theorem whnfCoreLoopC_spec (ih : SSimC .verified eager env f)
    (henv : EnvWF env) {c : Bool} {d : Nat} (n : Nat) :
    ∀ {fires : Nat} {pend pendC : List Expr} {i : Expr} {s₀ : CState},
      CSOK .verified eager env s₀ →
      Expr.WScoped d i → PendOK .verified eager env c d pend i →
      PendOK .verified eager env true d pendC i →
      ⦃fun s => s = s₀⦄
        whnfCoreLoopI .verified (mkFEnv env) eager f c d n fires pend pendC i
      ⦃fun v s' => CSOK .verified eager env s' ∧
        Runs ((fueledFns .verified eager env).whnfCore c d i) v ∧
        Expr.WScoped d v; ⊤⦄ := by
  induction n with
  | zero =>
    intro fires pend pendC i s₀ hs hw hp hpc
    sym only [conleche_grind] => vcgen [whnfCoreLoopI.eq_def] <;> finish
  | succ n ihn =>
    intro fires pend pendC i s₀ hs hw hp hpc
    sym only [conleche_grind, CSOK.chainStored henv, CSOK.chainStored_nil henv,
        CSOK.chainStoredDone henv, CSOK.whnfCore_hit henv, CSOK.whnfCoreCheap_hit henv,
        CSOK.tickRule] =>
      vcgen [whnfCoreLoopI.eq_def, storeChainI, whnfCoreLookupI, tickRuleI,
        whnfCoreStepC_spec ih henv, ihn] <;> finish

/-- The cached head-normalization body answers the chained `whnfCore`:
the loop with no key pending. -/
theorem whnfCoreBodyC_spec (ih : SSimC .verified eager env f)
    (henv : EnvWF env) (c : Bool) :
    BodySpec .verified eager env (whnfCoreBodyI .verified (mkFEnv env) eager f c)
      (fun d i => (fueledFns .verified eager env).whnfCore c d i) := by
  intro s₀ d i hs hw
  sym only [conleche_grind] =>
    vcgen [whnfCoreBodyI.eq_def, whnfCoreLoopC_spec ih henv] <;> finish

end Walks

section Walks2

variable {env : Env} {f : Nat}

/-- The loop's fixpoint where no rule fired at the origin: the stuck term. -/
theorem Runs.whnfFix_none_eq {k : Option Expr → Expr → FueledM Expr} {d : Nat}
    {o : Option Expr} {e₁ : Expr} (v : Expr)
    (h : Runs (originFire (fueledFns mode eager env) env d o e₁) none) :
    Runs (whnfFix (fueledFns mode eager env) env d k o e₁) v = (e₁ = v) := by
  unfold whnfFix
  rw [Runs.bind_eq v h]
  exact Runs.pure_eq e₁ v
grind_pattern [conleche_grind] Runs.whnfFix_none_eq =>
  Runs (originFire (fueledFns mode eager env) env d o e₁) none,
  Runs (whnfFix (fueledFns mode eager env) env d k o e₁) v

/-- The loop's fixpoint where a rule fired at the origin: the loop goes on from the reduct. -/
theorem Runs.whnfFix_some_eq {k : Option Expr → Expr → FueledM Expr} {d : Nat}
    {o : Option Expr} {e₁ e₂ : Expr} {t : Name} (v : Expr)
    (h : Runs (originFire (fueledFns mode eager env) env d o e₁) (some (t, e₂))) :
    Runs (whnfFix (fueledFns mode eager env) env d k o e₁) v = Runs (k none e₂) v := by
  unfold whnfFix
  rw [Runs.bind_eq v h]
grind_pattern [conleche_grind] Runs.whnfFix_some_eq =>
  Runs (originFire (fueledFns mode eager env) env d o e₁) (some (t, e₂)),
  Runs (whnfFix (fueledFns mode eager env) env d k o e₁) v

/-- The reduction loop simulates its specification, by induction on the
shared step budget (task #106). -/
theorem whnfLoopC_spec (ih : SSimC mode eager env f) (henv : EnvWF env) {d : Nat} (n : Nat) :
    ∀ {fires : Nat} {o : Option Expr} {i : Expr} {s₀ : CState}, CSOK mode eager env s₀ →
      OptWS d o → Expr.WScoped d i →
      ⦃fun s => s = s₀⦄ whnfLoopI mode (mkFEnv env) eager f d n fires o i
      ⦃fun v s' => CSOK mode eager env s' ∧
        Runs (whnfLoop (fueledFns mode eager env) env d n o i) v ∧ Expr.WScoped d v; ⊤⦄ := by
  induction n with
  | zero =>
    intro fires o i s₀ hs ho hw
    sym only [conleche_grind] => vcgen [whnfLoopI.eq_def] <;> finish
  | succ n ihn =>
    intro fires o i s₀ hs ho hw
    sym only [conleche_grind, whnfLoop, whnfStep, unfoldDefinition_WScoped henv] =>
      vcgen [whnfLoopI.eq_def, ih.whnfCore_spec, reduceNatC_spec ih,
        unfoldDefinitionC_spec (mode := mode) (eager := eager) (env := env),
        originFireC_spec ih henv, tickRuleI, ihn] <;> finish

theorem whnfBodyC_spec (ih : SSimC mode eager env f) (henv : EnvWF env) :
    BodySpec mode eager env (whnfBodyI mode (mkFEnv env) eager f)
      (whnfBody (fueledFns mode eager env) env) := by
  intro s₀ d i hs hw
  sym only [conleche_grind, whnfBody] =>
    vcgen [whnfBodyI.eq_def, whnfLoopC_spec ih henv] <;> finish

end Walks2

section Walks3

variable {env : Env} {f : Nat}

/-! ### The io view's entry points

The io-grade walks call the knot's io entry point (`inferI … true`); their
pure side runs on `CoreFns.ioView` of the fueled family, read through
`CoreFns.ioView_*`, so the specs whose pure side is at the view are
restated here. -/

theorem ensureSortIOC_spec (ih : SSimC mode eager env f) {d : Nat} {i : Expr} {s₀ : CState}
    (hs : CSOK mode eager env s₀) (hw : Expr.WScoped d i) :
    ⦃fun s => s = s₀⦄ ensureSortI mode (mkFEnv env) eager f d i
    ⦃fun v s' => CSOK mode eager env s' ∧
      Runs (ensureSort (CoreFns.ioView (fueledFns mode eager env)) env d i) v; ⊤⦄ :=
  ensureSortC_spec ih hs hw

theorem CoreFns.ioView_whnf {m : Type → Type} (r : CoreFns m) (d : Nat) (e : Expr) :
    (CoreFns.ioView r).whnf d e = r.whnf d e := rfl

theorem CoreFns.ioView_infer {m : Type → Type} (r : CoreFns m) (d : Nat) (e : Expr) :
    (CoreFns.ioView r).infer d e = r.inferIO d e := rfl

/-! ### The inference spine loops

As for the argument loop: the cached loops by their `eq_def`, the pure
mirrors' own equation lemmas in the `sym` list. -/

/-- The application-inference spine loop simulates its pure mirror. -/
theorem inferSpineC_spec (ih : SSimC mode eager env f) {d : Nat} :
    ∀ {args : List Expr} {ty : Expr} {acc : Array Expr} {s₀ : CState}, CSOK mode eager env s₀ →
      Expr.WScoped d (ty.instantiateList acc.toList.reverse) → AllWS d args →
      ⦃fun s => s = s₀⦄ inferSpineI mode (mkFEnv env) eager f false d ty acc args
      ⦃fun v s' => CSOK mode eager env s' ∧
        Runs (inferSpine (fueledFns mode eager env) d ty acc.toList.reverse args) v ∧
        Expr.WScoped d v; ⊤⦄ := by
  intro args
  induction args with
  | nil =>
    intro _ _ _ hs _ _
    sym only [conleche_grind, inferSpine.eq_1] =>
      vcgen [inferSpineI.eq_def, instListRevM_spec hs] <;> finish
  | cons _ rest ihr =>
    intro _ _ _ _ _ _
    sym only [conleche_grind, inferSpine.eq_2, inferSpine.eq_3, toListRev_singleton] =>
      vcgen [inferSpineI.eq_def, instListRevM_spec (mode := mode) (eager := eager) (env := env),
          ih.infer_spec,
        ih.whnf_spec, defeqArgC_spec ih, ihr] <;> finish

/-- The io-grade spine loop simulates its pure mirror. -/
theorem inferSpineIOC_spec (ih : SSimC mode eager env f) {d : Nat} :
    ∀ {args : List Expr} {ty : Expr} {acc : Array Expr} {s₀ : CState}, CSOK mode eager env s₀ →
      Expr.WScoped d (ty.instantiateList acc.toList.reverse) → AllWS d args →
      ⦃fun s => s = s₀⦄
        inferSpineIOI mode (mkFEnv env) eager f d ty acc
            args
      ⦃fun v s' => CSOK mode eager env s' ∧
        Runs (inferSpineIO (fueledFns mode eager env) d ty acc.toList.reverse args) v ∧
        Expr.WScoped d v; ⊤⦄ := by
  intro args
  induction args with
  | nil =>
    intro _ _ _ hs _ _
    sym only [conleche_grind, inferSpineIO.eq_1] =>
      vcgen [inferSpineIOI.eq_def, instListRevM_spec hs] <;> finish
  | cons _ rest ihr =>
    intro _ _ _ _ _ _
    sym only [conleche_grind, inferSpineIO.eq_2, inferSpineIO.eq_3, toListRev_singleton] =>
      vcgen [inferSpineIOI.eq_def, instListRevM_spec (mode := mode) (eager := eager) (env := env),
        ih.whnf_spec, ihr] <;> finish

/-! ### The inference bodies -/

/-- A free variable's type is scoped at the variable's depth, so at any
depth above it. -/
theorem wscoped_fvar_ty {d idx : Nat} {ty : Expr} (h : Expr.WScoped d (.fvar idx ty)) :
    Expr.WScoped d ty := by
  rw [Expr.WScoped] at h
  exact Expr.WScoped.mono (Nat.le_of_lt h.1) h.2
grind_pattern [conleche_grind] wscoped_fvar_ty => Expr.WScoped d (.fvar idx ty)

/-- A stored constant's type is closed. -/
theorem EnvWF.constTy_closed (henv : EnvWF env) {n : Name} {ci : ConstantInfo}
    (h : env.find? n = some ci) : ci.toConstantVal.type.hasFvar = false :=
  (henv.consts _ (Env.find?_mem h)).1

/-- A projection's type is well scoped at its subject's scope. -/
theorem wscoped_typeAt (henv : EnvWF env) {T : Name} {i : Nat} {entry : ProjEntry}
    (hf : env.findProj? T i = some entry) (us : List Level) {d : Nat} {targs : List Expr}
    (hlen : targs.length = entry.numParams) {pe : Expr} (hargs : AllWS d targs)
    (hpe : Expr.WScoped d pe) : Expr.WScoped d (entry.typeAt us targs pe) :=
  projEntry_typeAt_WScoped henv hf us hlen hargs hpe

/-- The cached spine walk's answer is the chained application clause's
(`inferSpine_sound_body`). -/
theorem Runs.inferBody_app {d : Nat} {g a tf v : Expr}
    (h₁ : Runs ((fueledFns mode eager env).infer d (Expr.app g a).getAppFn) tf)
    (h₂ : Runs (inferSpine (fueledFns mode eager env) d tf [] (Expr.app g a).getAppArgs) v) :
    Runs (inferBody (fueledFns mode eager env) env d (.app g a)) v := by
  obtain ⟨F, hF⟩ := Runs.bind (f := fun tf =>
    inferSpine (fueledFns mode eager env) d tf [] (Expr.app g a).getAppArgs) h₁ h₂
  exact inferSpine_sound_body d g a v F hF
grind_pattern [conleche_grind] Runs.inferBody_app =>
  Runs (inferSpine (fueledFns mode eager env) d tf [] (Expr.app g a).getAppArgs) v,
  inferBody (fueledFns mode eager env) env d (.app g a)

/-- The ∀-telescope loop against `inferBody`'s ∀ tail, as a triple. -/
theorem inferPisC_tail_spec (ih : SSimC mode eager env f) {d fuel : Nat} {b ty : Expr} {u : Level}
    {s₀ : CState} (hs : CSOK mode eager env s₀) (hwty : Expr.WScoped d ty)
    (hwb : Expr.WScoped d b) :
    ⦃fun s => s = s₀⦄ inferPisI mode (mkFEnv env) eager f false d fuel b 1 #[.fvar d ty] [u]
    ⦃fun r s' => CSOK mode eager env s' ∧
      Runs (do
        let v ← ensureSort (fueledFns mode eager env) env (d + 1)
          (← (fueledFns mode eager env).infer (d + 1) (b.instantiate1 (.fvar d ty)))
        pure (Expr.sort (.imax u v))) r ∧ Expr.WScoped d r; ⊤⦄ :=
  (inferPisC_tail_sim ih hs rfl rfl rfl hwty hwb).triple relEC_inv

/-- The λ-telescope loop against `inferBody`'s λ tail, as a triple. -/
theorem inferLamsC_tail_spec (ih : SSimC mode eager env f) (henv : EnvWF env) {d fuel : Nat}
    {b ty : Expr} {s₀ : CState} (hs : CSOK mode eager env s₀) (hwty : Expr.WScoped d ty)
    (hwb : Expr.WScoped d b) :
    ⦃fun s => s = s₀⦄ inferLamsI mode (mkFEnv env) eager f false d fuel b 1 #[.fvar d ty] [ty]
    ⦃fun r s' => CSOK mode eager env s' ∧
      Runs (do
        let bt ← (fueledFns mode eager env).infer (d + 1) (b.instantiate1 (.fvar d ty))
        pure (Expr.forallE ty (bt.abstract1 d))) r ∧ Expr.WScoped d r; ⊤⦄ :=
  (inferLamsC_tail_sim ih henv hs rfl rfl rfl hwty hwb).triple relEC_inv

/-- The rows of a projection's guard simulate their fueled original. -/
theorem checkGuardRowsC_spec (ih : SSimC mode eager env f) (guardSort : Level) :
    ∀ {rows : List (Nat × Expr)} {s₀ : CState}, CSOK mode eager env s₀ → GuardRowsWS rows →
      ⦃fun s => s = s₀⦄ checkGuardRowsI mode (mkFEnv env) eager f
        guardSort rows
      ⦃fun v s' => CSOK mode eager env s' ∧
        Runs (checkGuardRows (fueledFns mode eager env).inferIO
          (fueledFns mode eager env).whnf guardSort rows) v; ⊤⦄ := by
  intro rows
  induction rows with
  | nil =>
    intro _ _ _
    sym only [conleche_grind, checkGuardRows] =>
      vcgen [checkGuardRowsI.eq_def] <;> finish
  | cons p rest ihr =>
    obtain ⟨d, dom⟩ := p
    intro s₀ hs hw
    have hd := hw.head
    have hr := hw.tail
    sym only [conleche_grind, checkGuardRows] =>
      vcgen [checkGuardRowsI.eq_def, ih.inferIO_spec, ih.whnf_spec, ihr] <;> finish

/-- What a projection's rows lie under simulates its fueled original. -/
theorem projGuardSortC_spec (ih : SSimC mode eager env f) {cvT : ConstantVal} {caps : IndCaps}
    {us : List Level} {s₀ : CState} (hcl : cvT.type.hasFvar = false)
    (hs : CSOK mode eager env s₀) :
    ⦃fun s => s = s₀⦄ projGuardSortI mode (mkFEnv env) eager f cvT caps us
    ⦃fun v s' => CSOK mode eager env s' ∧
      Runs (projGuardSort (fueledFns mode eager env).whnf cvT caps us) v; ⊤⦄ := by
  have hw : Expr.WScoped 0 (cvT.type.instantiateLevelParams cvT.levelParams us) :=
    Expr.WScoped.of_not_hasFvar (by rw [hasFvar_instantiateLevelParams]; exact hcl)
  sym only [conleche_grind, projGuardSort] =>
    vcgen [projGuardSortI.eq_def, instLevelParamsM, formerSortLoopC_spec ih] <;> finish

/-- The cached guard rows are the kernel's (task #497). -/
theorem projGuardRowsGoC_eq :
    ∀ (k d : Nat) (e : Expr), projGuardRowsGoC k d e = projGuardRowsGo k d e
  | 0, _, .forallE .. => rfl
  | k + 1, d, .forallE dom body => by
    simp only [projGuardRowsGoC, projGuardRowsGo, hasLooseBVarBC_spec,
      Expr.instantiate1C_spec, projGuardRowsGoC_eq k (d + 1)]
    split <;> rfl
  | 0, _, .bvar _ | 0, _, .fvar .. | 0, _, .sort _ | 0, _, .const .. | 0, _, .app ..
  | 0, _, .lam .. | 0, _, .letE .. | 0, _, .lit _ | 0, _, .proj .. => rfl
  | _ + 1, _, .bvar _ | _ + 1, _, .fvar .. | _ + 1, _, .sort _ | _ + 1, _, .const ..
  | _ + 1, _, .app .. | _ + 1, _, .lam .. | _ + 1, _, .letE .. | _ + 1, _, .lit _
  | _ + 1, _, .proj .. => rfl

/-! ### The guard's fast case (task #498, L7)

`projGuardRowsC` reads the raw field telescope through `projGuardFastC`
before it rebuilds it.  Where the fast case answers, no field before the
projected one is mentioned after it, so the specification's loop steps
over every one of them and its one row is the projected field's domain
(`projGuardFastC_rows`). -/

/-- A window the reference answers `false` for holds no loose variable. -/
theorem Expr.hasLooseBVarInP_false :
    ∀ (e : Expr) {w d i : Nat}, Expr.hasLooseBVarInP w e d = false → d ≤ i → i < d + w →
      e.hasLooseBVar i = false := by
  have cut : ∀ (e : Expr) {d i : Nat}, e.bvarB ≤ d → d ≤ i → e.hasLooseBVar i = false :=
    fun e d i h hi => Expr.hasLooseBVar_eq_false_of_bound e i (by rw [← Expr.bvarB_eq]; omega)
  intro e
  induction e with
  | bvar k =>
    intro w d i h hd hw
    by_cases hc : (Expr.bvar k).bvarB ≤ d
    · exact cut _ hc hd
    · rw [Expr.hasLooseBVarInP.eq_def] at h
      simp only [hc, ite_false, Bool.and_eq_false_iff, decide_eq_false_iff_not] at h
      simp only [Expr.hasLooseBVar, beq_eq_false_iff_ne]
      omega
  | fvar _ _ _ => intro _ _ _ _ _ _; rfl
  | sort _ => intro _ _ _ _ _ _; rfl
  | const _ _ => intro _ _ _ _ _ _; rfl
  | lit _ => intro _ _ _ _ _ _; rfl
  | app f a ihf iha =>
    intro w d i h hd hw
    by_cases hc : (Expr.app f a).bvarB ≤ d
    · exact cut _ hc hd
    · rw [Expr.hasLooseBVarInP.eq_def] at h
      simp only [hc, ite_false, Bool.or_eq_false_iff] at h
      simp only [Expr.hasLooseBVar, ihf h.1 hd hw, iha h.2 hd hw, Bool.or_false]
  | lam ty b iht ihb =>
    intro w d i h hd hw
    by_cases hc : (Expr.lam ty b).bvarB ≤ d
    · exact cut _ hc hd
    · rw [Expr.hasLooseBVarInP.eq_def] at h
      simp only [hc, ite_false, Bool.or_eq_false_iff] at h
      simp only [Expr.hasLooseBVar, iht h.1 hd hw, ihb (i := i + 1) h.2 (by omega) (by omega), Bool.or_false]
  | forallE ty b iht ihb =>
    intro w d i h hd hw
    by_cases hc : (Expr.forallE ty b).bvarB ≤ d
    · exact cut _ hc hd
    · rw [Expr.hasLooseBVarInP.eq_def] at h
      simp only [hc, ite_false, Bool.or_eq_false_iff] at h
      simp only [Expr.hasLooseBVar, iht h.1 hd hw, ihb (i := i + 1) h.2 (by omega) (by omega), Bool.or_false]
  | letE t v b iht ihv ihb =>
    intro w d i h hd hw
    by_cases hc : (Expr.letE t v b).bvarB ≤ d
    · exact cut _ hc hd
    · rw [Expr.hasLooseBVarInP.eq_def] at h
      simp only [hc, ite_false, Bool.or_eq_false_iff] at h
      simp only [Expr.hasLooseBVar, iht h.1.1 hd hw, ihv h.1.2 hd hw,
        ihb (i := i + 1) h.2 (by omega) (by omega), Bool.or_false]
  | proj sn ix s ih =>
    intro w d i h hd hw
    by_cases hc : (Expr.proj sn ix s).bvarB ≤ d
    · exact cut _ hc hd
    · rw [Expr.hasLooseBVarInP.eq_def] at h
      simp only [hc, ite_false] at h
      simp only [Expr.hasLooseBVar, ih h hd hw]

/-- The empty window holds nothing. -/
theorem Expr.hasLooseBVarInP_zero : ∀ (e : Expr) (d : Nat), Expr.hasLooseBVarInP 0 e d = false := by
  intro e
  induction e with
  | bvar k =>
    intro d; rw [Expr.hasLooseBVarInP.eq_def]
    split
    · rfl
    · simp only [Nat.add_zero, Bool.and_eq_false_iff, decide_eq_false_iff_not]; omega
  | fvar _ _ _ | sort _ | const _ _ | lit _ =>
    intro d; rw [Expr.hasLooseBVarInP.eq_def]; split <;> rfl
  | app f a ihf iha =>
    intro d; rw [Expr.hasLooseBVarInP.eq_def]; split
    · rfl
    · simp only [ihf, iha, Bool.or_false]
  | lam ty b iht ihb =>
    intro d; rw [Expr.hasLooseBVarInP.eq_def]; split
    · rfl
    · simp only [iht, ihb, Bool.or_false]
  | forallE ty b iht ihb =>
    intro d; rw [Expr.hasLooseBVarInP.eq_def]; split
    · rfl
    · simp only [iht, ihb, Bool.or_false]
  | letE t v b iht ihv ihb =>
    intro d; rw [Expr.hasLooseBVarInP.eq_def]; split
    · rfl
    · simp only [iht, ihv, ihb, Bool.or_false]
  | proj _ _ s ih =>
    intro d; rw [Expr.hasLooseBVarInP.eq_def]; split
    · rfl
    · simp only [ih]

/-- The cached window query is its reference. -/
theorem Expr.hasLooseBVarInC_spec {d w : Nat} {e : Expr} :
    Expr.hasLooseBVarInC d w e = Expr.hasLooseBVarInP w e d := by
  unfold Expr.hasLooseBVarInC
  split
  · next hw => subst hw; exact (Expr.hasLooseBVarInP_zero e d).symm
  · split
    · next h => exact (Expr.hasLooseBVarInP_cut h).symm
    · rw [Expr.resBool_eq]

/-- Substituting free variables at and above `off` leaves an index below
it occurring as it did. -/
theorem Expr.hasLooseBVar_instantiateList_fvars_lt :
    ∀ (acc : List Expr), (∀ a ∈ acc, ∃ k t, a = .fvar k t) →
      ∀ (e : Expr) {off i : Nat}, i < off →
        (e.instantiateList acc off).hasLooseBVar i = e.hasLooseBVar i
  | [], _, e, off, _, _ => by rw [Expr.instantiateList_nil]
  | v :: vs, hacc, e, off, i, hi => by
    obtain ⟨k, t, rfl⟩ := hacc v (List.mem_cons_self ..)
    rw [Expr.instantiateList_cons,
      Expr.hasLooseBVar_instantiate1_lt (v := .fvar k t) rfl _ hi,
      Expr.hasLooseBVar_instantiateList_fvars_lt vs
        (fun a ha => hacc a (List.mem_cons_of_mem _ ha)) e (by omega)]

/-- Where the fast case answers, the telescope mentions no field before
the window's top. -/
theorem projGuardFastC_below :
    ∀ (k j : Nat) (e : Expr) {dom : Expr}, projGuardFastC k j e = some dom →
      ∀ i, i < j → e.hasLooseBVar i = false
  | 0, j, .forallE dom' b, dom, h, i, hi => by
    simp only [projGuardFastC] at h
    split at h
    · exact nomatch h
    · next hc =>
      rw [Bool.not_eq_true, Expr.hasLooseBVarInC_spec] at hc
      exact Expr.hasLooseBVarInP_false _ hc (Nat.zero_le i) (by omega)
  | k + 1, j, .forallE dom0 body, dom, h, i, hi => by
    simp only [projGuardFastC] at h
    split at h
    · exact nomatch h
    · next hc =>
      rw [Bool.not_eq_true, Expr.hasLooseBVarInC_spec] at hc
      simp only [Expr.hasLooseBVar,
        Expr.hasLooseBVarInP_false _ hc (Nat.zero_le i) (by omega),
        projGuardFastC_below k (j + 1) body h (i + 1) (by omega), Bool.or_false]
  | 0, _, .bvar _, _, h, _, _ | 0, _, .fvar .., _, h, _, _ | 0, _, .sort _, _, h, _, _
  | 0, _, .const .., _, h, _, _ | 0, _, .app .., _, h, _, _ | 0, _, .lam .., _, h, _, _
  | 0, _, .letE .., _, h, _, _ | 0, _, .lit _, _, h, _, _ | 0, _, .proj .., _, h, _, _
  | _ + 1, _, .bvar _, _, h, _, _ | _ + 1, _, .fvar .., _, h, _, _
  | _ + 1, _, .sort _, _, h, _, _ | _ + 1, _, .const .., _, h, _, _
  | _ + 1, _, .app .., _, h, _, _ | _ + 1, _, .lam .., _, h, _, _
  | _ + 1, _, .letE .., _, h, _, _ | _ + 1, _, .lit _, _, h, _, _
  | _ + 1, _, .proj .., _, h, _, _ => by simp [projGuardFastC] at h

/-- **The fast case is the loop's answer**: over the telescope with the
parameters substituted, the specification steps over every field before
the projected one and returns its domain as the one row. -/
theorem projGuardFastC_rows {acc : List Expr} (hacc : ∀ a ∈ acc, ∃ k t, a = .fvar k t) :
    ∀ (k j d : Nat) (e : Expr) {dom : Expr}, projGuardFastC k j e = some dom →
      projGuardRowsGo k d (e.instantiateList acc j)
        = some [(d + k, dom.instantiateList acc (j + k))]
  | 0, j, d, .forallE dom' b, dom, h => by
    have hd : dom' = dom := by
      simp only [projGuardFastC] at h
      split at h
      · exact nomatch h
      · exact Option.some.inj h
    subst hd
    rw [Expr.instantiateList]
    rfl
  | k + 1, j, d, .forallE dom0 body, dom, h => by
    have hb : projGuardFastC k (j + 1) body = some dom := by
      simp only [projGuardFastC] at h
      split at h
      · exact nomatch h
      · exact h
    have hu : (body.instantiateList acc (j + 1)).hasLooseBVarB 0 = false := by
      rw [Expr.hasLooseBVarB_eq,
        Expr.hasLooseBVar_instantiateList_fvars_lt acc hacc body (by omega)]
      exact projGuardFastC_below k (j + 1) body hb 0 (by omega)
    rw [Expr.instantiateList]
    have e1 : d + 1 + k = d + (k + 1) := by omega
    have e2 : j + 1 + k = j + (k + 1) := by omega
    simp only [projGuardRowsGo, hu, Bool.false_eq_true, ite_false,
      projGuardFastC_rows hacc k (j + 1) (d + 1) body hb, e1, e2]
  | 0, _, _, .bvar _, _, h | 0, _, _, .fvar .., _, h | 0, _, _, .sort _, _, h
  | 0, _, _, .const .., _, h | 0, _, _, .app .., _, h | 0, _, _, .lam .., _, h
  | 0, _, _, .letE .., _, h | 0, _, _, .lit _, _, h | 0, _, _, .proj .., _, h
  | _ + 1, _, _, .bvar _, _, h | _ + 1, _, _, .fvar .., _, h
  | _ + 1, _, _, .sort _, _, h | _ + 1, _, _, .const .., _, h
  | _ + 1, _, _, .app .., _, h | _ + 1, _, _, .lam .., _, h
  | _ + 1, _, _, .letE .., _, h | _ + 1, _, _, .lit _, _, h
  | _ + 1, _, _, .proj .., _, h => by simp [projGuardFastC] at h

/-- The cached rows where the parameters do not open: none. -/
theorem projGuardRowsC_none {nP idx : Nat} {cty : Expr}
    (h : openPisAtFvars nP cty 0 = none) : projGuardRowsC nP idx cty = none := by
  unfold projGuardRowsC
  cases hraw : openPisRawGoC [] nP cty 0 with
  | none => rfl
  | some p =>
    obtain ⟨fvs, acc, r⟩ := p
    have ho := openPisAtFvarsC_eq nP cty 0
    simp only [openPisAtFvarsC, openPisAtFvarsGoC, hraw, h] at ho
    exact nomatch ho

/-- The cached rows where the parameters open: the loop over the opened
residual. -/
theorem projGuardRowsC_some {nP idx : Nat} {cty r : Expr} {fvs : List Expr}
    (h : openPisAtFvars nP cty 0 = some (fvs, r)) :
    projGuardRowsC nP idx cty = projGuardRowsGo idx nP r := by
  unfold projGuardRowsC
  cases hraw : openPisRawGoC [] nP cty 0 with
  | none =>
    have ho := openPisAtFvarsC_eq nP cty 0
    simp only [openPisAtFvarsC, openPisAtFvarsGoC, hraw, h] at ho
    exact nomatch ho
  | some p =>
    obtain ⟨fvs', acc, R⟩ := p
    have ho := openPisAtFvarsC_eq nP cty 0
    simp only [openPisAtFvarsC, openPisAtFvarsGoC, hraw, h, Expr.instantiateListC_spec,
      Option.some.injEq, Prod.mk.injEq] at ho
    obtain ⟨-, rfl⟩ := ho
    have hacc := openPisRawGoC_fvars [] nP cty 0 (by simp) hraw
    simp only
    split
    · next dom hf =>
      rw [Expr.instantiateListC_spec, projGuardFastC_rows hacc idx 0 nP R hf, Nat.zero_add]
    · rw [Expr.instantiateListC_spec, projGuardRowsGoC_eq]

/-- The rows at a guardSort simulate their fueled original. -/
theorem projRowsC_spec (ih : SSimC mode eager env f) (henv : EnvWF env)
    {entry : ProjEntry} {us : List Level} {guardSort : Level} {s₀ : CState}
    (hs : CSOK mode eager env s₀) :
    ⦃fun s => s = s₀⦄ checkProjRowsI mode (mkFEnv env) eager f
      entry us guardSort
    ⦃fun v s' => CSOK mode eager env s' ∧
      Runs (match projGuardRows env.find? entry us with
        | some rows => checkGuardRows (fueledFns mode eager env).inferIO
            (fueledFns mode eager env).whnf guardSort rows
        | none => throw (.invalid "projection from a propositional structure must be a proposition"))
        v; ⊤⦄ := by
  cases hc : env.find? entry.ctor with
  | none =>
    have hp : projGuardRows env.find? entry us = none := by
      simp only [projGuardRows, hc]
    sym only [conleche_grind, constTyOf, Option.isSome_some] =>
      vcgen [checkProjRowsI.eq_def, constTyAtM_spec (mode := mode) (eager := eager) (env := env),
        checkGuardRowsC_spec ih] <;> finish
  | some ci =>
    cases ho : openPisAtFvars entry.numParams
        (ci.toConstantVal.type.instantiateLevelParams ci.toConstantVal.levelParams us) 0 with
    | none =>
      have hp : projGuardRows env.find? entry us = none := by
        simp only [projGuardRows, hc, ho]
      have hr := projGuardRowsC_none (idx := entry.idx) ho
      sym only [conleche_grind, constTyOf, Option.isSome_some] =>
        vcgen [checkProjRowsI.eq_def, constTyAtM_spec (mode := mode) (eager := eager) (env := env),
          checkGuardRowsC_spec ih] <;> finish
    | some p =>
      obtain ⟨fvsP, r⟩ := p
      have hr := projGuardRowsC_some (idx := entry.idx) ho
      cases hg : projGuardRowsGo entry.idx entry.numParams r with
      | none =>
        have hp : projGuardRows env.find? entry us = none := by
          simp only [projGuardRows, hc, ho, hg]
        sym only [conleche_grind, constTyOf, Option.isSome_some] =>
          vcgen [checkProjRowsI.eq_def, constTyAtM_spec (mode := mode) (eager := eager) (env := env),
            checkGuardRowsC_spec ih] <;> finish
      | some rows =>
        have hp : projGuardRows env.find? entry us = some rows := by
          simp only [projGuardRows, hc, ho, hg]
        have hws : GuardRowsWS rows :=
          projGuardRows_ws (fun ci' hc' => (henv.consts _ (Env.find?_mem hc')).1) hp
        sym only [conleche_grind, constTyOf, Option.isSome_some] =>
          vcgen [checkProjRowsI.eq_def, constTyAtM_spec (mode := mode) (eager := eager) (env := env),
            checkGuardRowsC_spec ih] <;> finish

/-- A projection's guard simulates its fueled original. -/
theorem checkProjGuardC_spec (ih : SSimC mode eager env f) (henv : EnvWF env)
    {entry : ProjEntry} {us : List Level} {s₀ : CState} (hs : CSOK mode eager env s₀) :
    ⦃fun s => s = s₀⦄ checkProjGuardI mode (mkFEnv env) eager f
      entry us
    ⦃fun v s' => CSOK mode eager env s' ∧
      Runs (checkProjGuard (fueledFns mode eager env).inferIO
        (fueledFns mode eager env).whnf env entry us) v; ⊤⦄ := by
  unfold checkProjGuardI checkProjGuard
  simp only [mkFEnv_find_fun]
  split
  · next cvT caps hT =>
    have hcl : cvT.type.hasFvar = false := (henv.consts _ (Env.find?_mem hT)).1
    sym only [conleche_grind] =>
      vcgen [projGuardSortC_spec ih hcl, projRowsC_spec ih henv] <;> finish
  · sym only [conleche_grind] => vcgen <;> finish

/-- `checkProjGuardC_spec` at the io views the io body runs it at. -/
theorem checkProjGuardC_specIO (ih : SSimC mode eager env f) (henv : EnvWF env)
    {entry : ProjEntry} {us : List Level} {s₀ : CState} (hs : CSOK mode eager env s₀) :
    ⦃fun s => s = s₀⦄ checkProjGuardI mode (mkFEnv env) eager f
      entry us
    ⦃fun v s' => CSOK mode eager env s' ∧
      Runs (checkProjGuard (CoreFns.ioView (fueledFns mode eager env)).infer
        (CoreFns.ioView (fueledFns mode eager env)).whnf env entry us) v; ⊤⦄ :=
  checkProjGuardC_spec ih henv hs

/-- The cached inference body simulates the specification body; the
application clause through the spine walk and `inferSpine_sound_body`. -/
theorem inferBodyC_spec (ih : SSimC mode eager env f) (henv : EnvWF env) :
    BodySpec mode eager env (inferBodyI mode (mkFEnv env) eager f false)
      (inferBody (fueledFns mode eager env) env) := by
  intro s₀ d i hs hw
  sym only [conleche_grind, inferBody, mkFEnv_natLit, mkFEnv_strLit,
      mkFEnv_findProj?, constTyOf, ProjEntry.typeAtI_eq,
      toListRev_empty, Option.isSome_some, EnvWF.constTy_closed henv, wscoped_typeAt henv] =>
    vcgen [inferBodyI.eq_def, peelFuelM, maxNatSizeM, inst1M_spec (mode := mode) (eager := eager) (env := env),
        ih.infer_spec, ih.whnf_spec, ih.defeq_spec,
      ensureSortC_spec ih, constTyAtM_spec (mode := mode) (eager := eager) (env := env),
      inferSpineC_spec ih, inferPisC_tail_spec ih, inferLamsC_tail_spec ih henv,
      checkProjGuardC_spec ih henv] <;> finish

/-- Abstracting away the top variable lowers the scope bound. -/
theorem wscoped_abstract1 {d : Nat} {e : Expr} (k : Nat) (h : Expr.WScoped (d + 1) e) :
    Expr.WScoped d (e.abstract1 d k) :=
  ConLeche.WScoped.abstract1 k h
grind_pattern [conleche_grind] wscoped_abstract1 => Expr.WScoped (d + 1) e, e.abstract1 d k

/-- The cached io spine walk's answer is the io application clause's
(`inferSpineIO_sound_body`). -/
theorem Runs.inferBodyIO_app {d : Nat} {g a tf v : Expr}
    (h₁ : Runs ((fueledFns mode eager env).inferIO d (Expr.app g a).getAppFn) tf)
    (h₂ : Runs (inferSpineIO (fueledFns mode eager env) d tf [] (Expr.app g a).getAppArgs) v) :
    Runs (inferBodyIO (CoreFns.ioView (fueledFns mode eager env)) env d (.app g a)) v := by
  obtain ⟨F, hF⟩ := Runs.bind (f := fun tf =>
    inferSpineIO (fueledFns mode eager env) d tf [] (Expr.app g a).getAppArgs) h₁ h₂
  exact inferSpineIO_sound_body d g a v F hF
grind_pattern [conleche_grind] Runs.inferBodyIO_app =>
  Runs (inferSpineIO (fueledFns mode eager env) d tf [] (Expr.app g a).getAppArgs) v,
  inferBodyIO (CoreFns.ioView (fueledFns mode eager env)) env d (.app g a)

/-- The io inference body's walk (task #172 B4).  The leaf and `proj`
arms are `inferBodyI`'s at the io view; the binder and `letE` arms are
the io lane's own chained clauses; the application arm is the io spine
walk (`inferSpineIOI`, no argument check) with
`inferSpineIO_sound_body`. -/
theorem inferBodyIOC_spec (ih : SSimC mode eager env f) (henv : EnvWF env) :
    BodySpec mode eager env
      (inferBodyIOI mode (mkFEnv env) eager f)
      (inferBodyIO (CoreFns.ioView (fueledFns mode eager env)) env) := by
  intro s₀ d i hs hw
  sym only [conleche_grind, inferBodyIO, CoreFns.ioView_infer, CoreFns.ioView_whnf,
      mkFEnv_natLit, mkFEnv_strLit, mkFEnv_findProj?, constTyOf,
      ProjEntry.typeAtI_eq, toListRev_empty, Option.isSome_some,
      abstract1C_spec, EnvWF.constTy_closed henv, wscoped_typeAt henv] =>
    vcgen [inferBodyIOI.eq_def, inferBodyI.eq_def, maxNatSizeM, abstract1M, ensureSortIOC_spec ih,
      inst1M_spec (mode := mode) (eager := eager) (env := env), ih.inferIO_spec, ih.whnf_spec,
      constTyAtM_spec (mode := mode) (eager := eager) (env := env), inferSpineIOC_spec ih,
      checkProjGuardC_specIO ih henv] <;>
          finish

end Walks3

end ConLeche.Cached
