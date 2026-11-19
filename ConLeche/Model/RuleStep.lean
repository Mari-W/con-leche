module

public import ConLeche.Model.Install
import ConLeche.Model.RecRulesCons
public import ConLeche.Model.Inductives.FamilyRan
import ConLeche.Model.NatEqs
import ConLeche.Verify.EnvWF

public section

/-!
# The P step at a rule record

`stepRules_cover`: a rewrite rule's registration and a `useRules` record change the environment's
rules alone (`Env.stepRules`).  Nothing the model reads looks at the rules: `Red.rewrite` asks only
that its theorem be stored, and a family's telescope is read without rules (`Env.cutAt`).  So
the carrier is the prefix's, every lookup and every reading is the same, and the recorded blocks
and their coverage carry over unchanged.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory

open ConLeche (Env Expr Name Level ConstantInfo ConstantVal Declaration)

universe w

variable {V : Type w} [SetTheory V] {env : Env}

/-- **A reading does not see the rules.** -/
theorem denote_stepRules (d : Declaration) (acval : Name → (Name → Nat) → Term) (ψ : Name → Nat)
    (k : Nat) {e : Expr} (hb : ConstsBound env e) :
    denote acval (env.stepRules d) ψ k e = denote acval env ψ k e :=
  (denote_envExtend (env₀ := env) (env := env.stepRules d) (fun h => h) ⟨rfl, rfl⟩
    (fun _ _ => rfl) k e hb).symm

/-- A name bound in the environment is bound after a rule record. -/
theorem constsBound_stepRules (d : Declaration) {e : Expr} (hb : ConstsBound env e) :
    ConstsBound (env.stepRules d) e :=
  ConstsBound.of_isSome (env₀ := env) (env₁ := env.stepRules d) (fun _ h => h) hb

/-- **The carrier after a rule record**: the prefix's. -/
@[expose] def EnvModel.stepRules (m : EnvModel V env) (d : Declaration) :
    EnvModel V (env.stepRules d) where
  wf := m.wf.stepRules d
  acval := m.acval
  cval_closed := m.cval_closed
  basis_pinned := m.basis_pinned
  proj_ok := m.proj_ok
  rec_ctors := m.rec_ctors
  acval_params := m.acval_params
  acval_wellDenoted := m.acval_wellDenoted

/-- A rule record keeps the prefix's readings. -/
theorem ModelExt.stepRules (mp : EnvModelM V env) (d : Declaration) :
    ModelExt mp (env.stepRules d) mp.base2.acval :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, fun hcb h => (denote_stepRules d _ _ _ hcb).trans h⟩

/-- `NatOps` across a rule record: the stored operations, their guards and their equations'
readings are the prefix's. -/
theorem natOps_stepRules (mp : EnvModelM V env) (d : Declaration)
    {m₂ : EnvModel V (env.stepRules d)} (hac : m₂.acval = mp.base2.acval)
    (φ : Name → Nat) : NatOps m₂ φ := by
  intro c hcN cv v hint hf
  obtain ⟨hg, hpin, hlaws⟩ := mp.nat_ops φ c hcN cv v hint hf
  obtain ⟨hN, -, -, -, -⟩ := ConLeche.Verify.natOpGuard_stored hg
  obtain ⟨ciN, hfN, -⟩ := ConLeche.Verify.storedNoLevels_exists hN
  refine ⟨hg, hpin, fun eq hq => ?_⟩
  obtain ⟨L, R, hL, hR, hlaw⟩ := hlaws eq hq
  obtain ⟨h1, h2⟩ := natOpEquations_frag_of_guard hg eq hq
  have hf0 : env.find? c = some (.defnInfo cv v hint) := hf
  have hfE : (env.find? c).isSome = true := by rw [hf0]; rfl
  have hfN' : (env.find? ConLeche.natName).isSome = true := by rw [hfN]; rfl
  refine ⟨L, R, ?_, ?_, ?_⟩
  · rw [hac, denote_stepRules d _ φ 2 (constsBound_of_natFragOk hfE hfN' h1)]
    exact hL
  · rw [hac, denote_stepRules d _ φ 2 (constsBound_of_natFragOk hfE hfN' h2)]
    exact hR
  · rw [hac]
    exact hlaw

/-- A theorem the rules name after a record: one named before, or the rule the record
registers.  A `useRules` activates registered rules only. -/
theorem ruleNamed_stepRules {d : Declaration} {t : Name} (h : RuleNamed (env.stepRules d) t) :
    RuleNamed env t ∨ ∃ head prio, d = .rewriteDecl t head prio := by
  cases d with
  | rewriteDecl thm head prio =>
    rcases h with ⟨r, hr, rfl⟩ | ⟨e, he, rfl⟩
    · rcases List.mem_cons.mp hr with rfl | hr
      · exact .inr ⟨head, prio, rfl⟩
      · exact .inl (.inl ⟨r, hr, rfl⟩)
    · exact .inl (.inr ⟨e, he, rfl⟩)
  | useRules S =>
    rcases h with ⟨r, hr, rfl⟩ | ⟨e, he, rfl⟩
    · exact .inl (.inl ⟨r, hr, rfl⟩)
    · simp only [Env.stepRules, ConLeche.RuleTable.step, ConLeche.activeTable, List.mem_map] at he
      obtain ⟨r, hr, rfl⟩ := he
      exact .inl (.inl ⟨r, (List.mem_filter.mp ((List.mergeSort_perm _ _).mem_iff.mp hr)).1, rfl⟩)
  | _ => exact .inl h

/-- **The P carrier after a rule record**: the prefix's leaves and recorded blocks, and a
registered rule's law (`hnew`, from its registration's runs). -/
theorem stepRules_model (mp : EnvModelM V env) (d : Declaration)
    (hnew : ∀ thm head prio, d = .rewriteDecl thm head prio → ∃ cv,
      env.find? thm = some (.thmInfo cv) ∧ (ConLeche.ruleSides cv.type).isSome = true ∧
        RuleLaw V mp.base2 cv.type) :
    ∃ mp' : EnvModelM V (env.stepRules d),
      mp'.base2.acval = mp.base2.acval ∧ mp'.lfpBlocks = mp.lfpBlocks := by
  let m₂ : EnvModel V (env.stepRules d) := mp.base2.stepRules d
  have hac : m₂.acval = mp.base2.acval := rfl
  have hx : ModelExt mp (env.stepRules d) m₂.acval := ModelExt.stepRules mp d
  have hbound := envWF_constsBound mp.base2.wf
  have hreadT : ∀ c ∈ env.consts, ∀ (ψ : Name → Nat) (ta : Term),
      denote m₂.acval (env.stepRules d) ψ 0 c.toConstantVal.type = some ta →
      denote mp.base2.acval env ψ 0 c.toConstantVal.type = some ta := by
    intro c hc ψ ta hta
    rwa [denote_stepRules d _ _ _ (hbound _ hc).1] at hta
  refine ⟨{
    base2 := m₂
    type_reads := fun c hc ψ => by
      obtain ⟨ta, hta⟩ := mp.type_reads c hc ψ
      exact ⟨ta, hx.denote (hbound _ hc).1 hta⟩
    type_wellDenotedTy := fun c hc ψ ta hta =>
      mp.type_wellDenotedTy c hc ψ ta (hreadT c hc ψ ta hta)
    mem_type := fun c hc ψ ta hta =>
      mp.mem_type c hc ψ ta (hreadT c hc ψ ta hta)
    defn_reads := fun ψ cv value hmem => by
      obtain ⟨hint, hdt⟩ := hmem
      exact hx.denote ((hbound _ hdt).2 cv value hint rfl) (mp.defn_reads ψ cv value ⟨hint, hdt⟩)
    nat_heads := mp.nat_heads
    nat_ops := natOps_stepRules mp d hac
    div_mod := mp.div_mod
    eq_law := mp.eq_law
    op_defn := fun c hn hs => mp.op_defn c hn hs
    rec_rules := fun φ n cv mI rP isK rules hf rl hmem =>
      recRuleLaw_ext mp hx φ hf hmem
    reduce_ops := mp.reduce_ops
    tower_ok := fun φ => ⟨fun T tbl hf => towerTableLaw_ext mp hx φ hf,
      fun T i entry hf => towerEntryLaw_ext mp hx φ hf⟩
    lfpBlocks := mp.lfpBlocks
    lfp_ok := mp.lfp_ok_transport (fun _ _ hf _ => hf) (fun _ _ _ _ => rfl)
      (fun ψ k _ _ hb hta => hx.denote hb hta)
      (fun _ hb => constsBound_stepRules d hb)
    rule_law := fun t ht => by
      have hread : ∀ (ψ : Name → Nat) (k : Nat) (e : Expr) (ta : Term), ConstsBound env e →
          denote mp.base2.acval env ψ k e = some ta →
          denote m₂.acval (env.stepRules d) ψ k e = some ta :=
        fun ψ k e ta hb h => (denote_stepRules d _ ψ k hb).trans h
      obtain ⟨cv, hf, hsome, hlaw⟩ : ∃ cv, env.find? t = some (.thmInfo cv) ∧
          (ConLeche.ruleSides cv.type).isSome = true ∧ RuleLaw V mp.base2 cv.type := by
        rcases ruleNamed_stepRules ht with ht | ⟨head, prio, hd⟩
        · exact mp.rule_law t ht
        · exact hnew t head prio hd
      have hres : cv.type.constsResolve env = true :=
        (mp.base2.wf.consts _ (ConLeche.Env.find?_mem hf)).2.2.1
      exact ⟨cv, hf, hsome, hlaw.transport hres hread⟩ }, rfl, rfl⟩

/-- **The coverage step at a rule record.** -/
theorem stepRules_cover (mp : EnvModelM V env) (d : Declaration)
    (hnew : ∀ thm head prio, d = .rewriteDecl thm head prio → ∃ cv,
      env.find? thm = some (.thmInfo cv) ∧ (ConLeche.ruleSides cv.type).isSome = true ∧
        RuleLaw V mp.base2 cv.type) : CoverStep mp (env.stepRules d) := by
  obtain ⟨mp', hac, hlb⟩ := stepRules_model mp d hnew
  refine ⟨mp', ⟨fun _ _ h => h, fun n _ => by rw [hac], fun ψ k e ta hb h => by
    rw [hac, denote_stepRules d _ _ _ hb]; exact h, fun D hD => .inl (hlb ▸ hD)⟩, fun hc => ?_⟩
  exact ⟨fun n cv caps h hn hq => hlb ▸ hc.cover n cv caps h hn hq,
    fun D hD => hc.nodup D (hlb ▸ hD), fun D hD => hc.len D (hlb ▸ hD),
    fun D hD => hc.all D (hlb ▸ hD), fun D hD => hc.fresh D (hlb ▸ hD),
    fun D hD => (hc.own D (hlb ▸ hD)).monoOn (fun _ _ => rfl) (fun _ _ _ _ => rfl)
      (fun _ _ => rfl), fun D hD => hc.wid D (hlb ▸ hD)⟩

/-- A rule record is an extension under fresh names: it pushes nothing, and a `useRules` records
its table at the current number of constants. -/
theorem freshExt_stepRules (env : Env) (d : Declaration) : FreshExt env (env.stepRules d) :=
  ⟨⟨[], rfl, fun _ h => nomatch h⟩, ⟨[], rfl, fun _ h => nomatch h⟩, by
    cases d with
    | useRules S => exact ⟨[_], rfl, fun s hs => by simp at hs; simp [hs]⟩
    | _ => exact ⟨[], rfl, fun _ h => nomatch h⟩, by
    cases d with
    | rewriteDecl _ _ _ => exact ⟨[], rfl, fun _ h => nomatch h⟩
    | useRules _ => exact ⟨[], rfl, fun _ h => nomatch h⟩
    | abstractDecl _ _ => exact ⟨[], rfl, fun _ h => nomatch h⟩
    | _ =>
      simp only [Env.stepRules, RuleTable.step, pushBlkOn]
      split
      · exact ⟨[], rfl, fun _ h => nomatch h⟩
      · exact ⟨[_], rfl, fun s hs => by simp at hs; simp [hs]⟩⟩

end ConLeche.Model
