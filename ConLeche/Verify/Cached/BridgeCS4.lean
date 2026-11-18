module

public import ConLeche.Verify.Cached.BridgeCS3
public import ConLeche.Verify.CheckerF
import ConLeche.Verify.Extend.Inversions
import ConLeche.Verify.Extend.Recs
import ConLeche.Kernel.Checker
import ConLeche.Verify.Abstract
import ConLeche.Verify.EnvWF
import ConLeche.Verify.Inductives.NestedRead
import ConLeche.Verify.Shift
import ConLeche.Verify.Subst

public section

/-!
# Cached shared-state checker: run-level toolkit

Dissection lemmas for successful `CheckCM` runs and the fueled-run
upgrade `FueledM.up`, used by the per-declaration composition over the
phase drivers of `ConLeche/Cached/CheckerC.lean`.  Each phase starts
with `flushC`, which re-establishes `CSOK` for the phase's environment
(`flushC_csok`); the state fact threaded across a transition is the
environment-free residue `CSOKF`.
-/

namespace ConLeche.Cached

open ConLeche
open Expr

variable {mode : CheckMode}

/-! ## Run-level toolkit -/

/-- Upgrade a fueled run (subject inferred from the hypothesis). -/
theorem FueledM.up {α : Type} {x : FueledM α} {F F' : Nat} {v : α}
    (hle : F ≤ F') (h : x.val F = .ok v) : x.val F' = .ok v :=
  x.property hle h

/-! ## The recursor group -/

/-- A `CheckCM` throw composed with anything never succeeds. -/
theorem throwC_bind_ok {α β : Type} {e : CheckError} {k : α → CheckCM β}
    {s₀ : CState} {v : β} {s' : CState}
    (h : ((throw e : CheckCM α) >>= k) s₀ = .ok (v, s')) : False := by
  exact nomatch h

end ConLeche.Cached
