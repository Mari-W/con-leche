module

public import ConLeche.Verify.Cached.SimCS
import ConLeche.Verify.Cached.KnotCongr
import ConLeche.Verify.CheckerF
import ConLeche.Verify.EnvWF

public section

/-!
# Head normalization below a family's block, at the cached operations

A family declared at a definition has its telescope reduced below its block (`CheckerOps.whnfB`,
`Env.famBelow`).  The cached operations run the cached core there between two flushes
(`whnfBC`): the view below the block (`FEnv.famBelow`) answers the lookups of the environment cut
there (`mkFEnv_below_find`, `mkFEnv_below_findTable`), so the cached core at the view is the
cached core at that environment (`knotI_congr`), and the cut is well formed (`EnvWF.famBelow`).
The flushes hand the state on as an invariant state of the environment in hand.
-/

namespace ConLeche.Cached

open ConLeche
open ConLeche.Expr Std.WP
open scoped Lean.Order

variable {env : Env}

/-- **Head normalization below a family's block simulates its fueled original.** -/
theorem whnfBS_spec (henv : EnvWF env) {n : Name} {d : Nat} {e : Expr} {s₀ : CState}
    (hs : CSOK .verified false env s₀) (hw : Expr.WScoped d e) :
    ⦃fun s => s = s₀⦄ (sharedOpsC .verified (mkFEnv env)).whnfB env n d e
    ⦃fun v s' => CSOK .verified false env s' ∧ Runs ((fueledOpsM .verified).whnfB env n d e) v ∧
      Expr.WScoped d v; ⊤⦄ :=
  triple_iff_run.mpr fun v s' hr => by
    change whnfBC .verified (mkFEnv env) n d e s₀ = _ at hr
    unfold whnfBC at hr
    obtain ⟨u₀, s₀', hfl₀, hr⟩ := bindC_ok hr
    rw [flushC_run] at hfl₀
    injection hfl₀ with hfl₀
    obtain rfl : s₀.flushed = s₀' := congrArg Prod.snd hfl₀
    obtain ⟨t, s₁, hrun, hr⟩ := bindC_ok hr
    obtain ⟨u, s₂, hfl, hr⟩ := bindC_ok hr
    rw [flushC_run] at hfl
    injection hfl with hfl
    obtain rfl : s₁.flushed = s₂ := congrArg Prod.snd hfl
    obtain ⟨rfl, rfl⟩ := pureC_ok hr
    unfold whnfBelowC FEnv.famBelow at hrun
    rw [mkFEnv_find?] at hrun
    cases hfind : env.find? n with
    | none => rw [hfind] at hrun; exact nomatch hrun
    | some ci =>
    rw [hfind] at hrun
    cases ci
    case indInfo cv caps =>
      simp only at hrun
      have hfb : env.famBelow n
          = some (env.cutAt ((Env.suffixAfter env.consts n).drop caps.blockPos)) := by
        unfold Env.famBelow
        rw [hfind]
      have henv' := henv.famBelow hfb
      have hf : ((mkFEnv env).below n caps.blockPos).find?
          = (mkFEnv (env.cutAt ((Env.suffixAfter env.consts n).drop caps.blockPos))).find? := by
        rw [mkFEnv_below_find, mkFEnv_find?_fun]
        rfl
      have ht : ((mkFEnv env).below n caps.blockPos).findTable?
          = (mkFEnv (env.cutAt ((Env.suffixAfter env.consts n).drop caps.blockPos))).findTable? := by
        rw [mkFEnv_below_findTable]
        funext T
        rw [mkFEnv_findTable?]
      have hru : ((mkFEnv env).below n caps.blockPos).rulesFor
          = (mkFEnv (env.cutAt ((Env.suffixAfter env.consts n).drop caps.blockPos))).rulesFor := by
        funext c
        unfold FEnv.rulesFor
        rw [mkFEnv_below_rls, hf, mkFEnv_base]
      rw [(knotI_congr hf ht hru).2.1] at hrun
      obtain ⟨hs₁, ⟨F, hF⟩, hwt⟩ :=
        triple_iff_run.mp (opW_spec henv' (flushC_csok hs.residue) hw) t s₁ hrun
      refine ⟨flushC_csok hs₁.residue, ⟨F, ?_⟩, hwt⟩
      show (fueledOps .verified F).whnfB env n d e = _
      simp only [fueledOps, hfb]
      exact hF
    all_goals exact nomatch hrun

end ConLeche.Cached
