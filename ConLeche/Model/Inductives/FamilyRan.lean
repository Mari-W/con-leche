module

public import ConLeche.Model.Env.CanonCrest
public import ConLeche.Model.Cover
public import ConLeche.Verify.EnvExt
import ConLeche.Verify.BridgeDecl
import ConLeche.Verify.Cached.BridgeCS4
import ConLeche.Verify.Inductives.NestContInv

public section

/-!
# A recorded family's telescope, run

A member whose declared type does not show its telescope has it read at use, by a reduction
below its block (`familyTelescope`, `Env.famBelow`): at the environment the block's check reduced
it at, cut again from the family's own entry.  A later declaration installs under fresh names, so
the cut stays the same and every later reading finds what the check found (`FamilyRan.read`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.Term ConLeche.Verify

open ConLeche (Env Expr Name ConstantVal ConstantInfo IndCaps fueledOps reducedFormer)

universe w

variable {V : Type w} [SetTheory V]

/-- A family's telescope is one, at every fuel a run has. -/
theorem familyTelescope_unique {env : Env} {cv : ConstantVal} {caps : IndCaps} {F₁ F₂ : Nat}
    {t₁ t₂ : Expr}
    (h₁ : ConLeche.familyTelescope (fueledOps .verified F₁) env cv caps = .ok t₁)
    (h₂ : ConLeche.familyTelescope (fueledOps .verified F₂) env cv caps = .ok t₂) : t₁ = t₂ := by
  rcases ConLeche.familyTelescope_cases h₁ with ⟨hfl, rfl⟩ | ⟨hfl, r₁, hr₁, rfl⟩ <;>
  rcases ConLeche.familyTelescope_cases h₂ with ⟨hfl', rfl⟩ | ⟨hfl', r₂, hr₂, rfl⟩
  · rfl
  · rw [hfl] at hfl'; exact nomatch hfl'
  · rw [hfl] at hfl'; exact nomatch hfl'
  · have g₁ : reducedFormer ((fueledOps .verified (max F₁ F₂)).below cv.name) env cv
        (caps.nparams + caps.nIdx) = .ok r₁ := by
      rw [← reducedFormer_below_datF]
      exact ConLeche.Cached.FueledM.up (Nat.le_max_left _ _)
        (by rw [reducedFormer_below_datF]; exact hr₁)
    have g₂ : reducedFormer ((fueledOps .verified (max F₁ F₂)).below cv.name) env cv
        (caps.nparams + caps.nIdx) = .ok r₂ := by
      rw [← reducedFormer_below_datF]
      exact ConLeche.Cached.FueledM.up (Nat.le_max_right _ _)
        (by rw [reducedFormer_below_datF]; exact hr₂)
    rw [g₁] at g₂
    obtain rfl : r₁ = r₂ := by simpa using g₂
    rfl

open Classical in
/-- **A family's telescope, as any run reads it** (its declared type where no run reaches one). -/
noncomputable def readTelescope (env : Env) (cv : ConstantVal) (caps : IndCaps) : Expr :=
  if h : ∃ F ty, ConLeche.familyTelescope (fueledOps .verified F) env cv caps = .ok ty then
    h.choose_spec.choose
  else cv.type

theorem readTelescope_eq {env : Env} {cv : ConstantVal} {caps : IndCaps} {F : Nat} {ty : Expr}
    (h : ConLeche.familyTelescope (fueledOps .verified F) env cv caps = .ok ty) :
    readTelescope env cv caps = ty := by
  have hx : ∃ F ty, ConLeche.familyTelescope (fueledOps .verified F) env cv caps = .ok ty :=
    ⟨F, ty, h⟩
  unfold readTelescope
  rw [dite_eq_left hx]
  exact familyTelescope_unique hx.choose_spec.choose_spec h

/-- **An extension under fresh names**: the constants and the tables pushed name nothing the
environment stores.  The rules are free to change: a family's telescope is read without them
(`Env.cutAt`). -/
structure FreshExt (env env' : Env) : Prop where
  consts : ∃ new, env'.consts = new ++ env.consts ∧ ∀ c ∈ new, env.find? c.name = none
  tables : ∃ newT, env'.tables = newT ++ env.tables ∧ ∀ t ∈ newT, env.find? t.structName = none

/-- A stored name keeps its constant across fresh pushes. -/
theorem FreshExt.find {env env' : Env} (hx : FreshExt env env') {n : Name} {ci : ConstantInfo}
    (h : env.find? n = some ci) : env'.find? n = some ci := by
  obtain ⟨new, hc, hfr⟩ := hx.consts
  show env'.consts.find? _ = _
  rw [hc, List.find?_append]
  have : new.find? (·.name == n) = none := List.find?_eq_none.mpr fun c hc' he => by
    have := hfr c hc'
    rw [show c.name = n by simpa using he, h] at this
    exact nomatch this
  rw [this, Option.none_or]
  exact h

/-- An extension of an extension under fresh names. -/
theorem FreshExt.trans {env₁ env₂ env₃ : Env} (h₁ : FreshExt env₁ env₂) (h₂ : FreshExt env₂ env₃) :
    FreshExt env₁ env₃ := by
  obtain ⟨new₁, hc₁, hf₁⟩ := h₁.consts
  obtain ⟨new₂, hc₂, hf₂⟩ := h₂.consts
  obtain ⟨T₁, ht₁, hg₁⟩ := h₁.tables
  obtain ⟨T₂, ht₂, hg₂⟩ := h₂.tables
  have hnone : ∀ n, env₂.find? n = none → env₁.find? n = none := fun n h => by
    cases hc : env₁.find? n with
    | none => rfl
    | some ci => rw [h₁.find hc] at h; exact nomatch h
  refine ⟨⟨new₂ ++ new₁, by rw [hc₂, hc₁, List.append_assoc], fun c hc => ?_⟩,
    ⟨T₂ ++ T₁, by rw [ht₂, ht₁, List.append_assoc], fun t ht => ?_⟩⟩
  · rcases List.mem_append.mp hc with hc | hc
    · exact hnone _ (hf₂ c hc)
    · exact hf₁ c hc
  · rcases List.mem_append.mp ht with ht | ht
    · exact hnone _ (hg₂ t ht)
    · exact hg₁ t ht

/-- **The environment below a stored family's block across pushes**: constants under fresh names,
tables of structures outside the cut. -/
theorem Env.famBelow_push {env env' : Env} {new : List ConstantInfo} {newT : List ProjTable}
    {n : Name} (hc : env'.consts = new ++ env.consts) (hne : ∀ c ∈ new, c.name ≠ n)
    (ht : env'.tables = newT ++ env.tables)
    {ci : ConstantInfo} (h : env.find? n = some ci)
    (hT : ∀ t ∈ newT, ∀ E, env.famBelow n = some E → E.consts.find? (·.name == t.structName) = none) :
    env'.famBelow n = env.famBelow n := by
  have hfind : env'.find? n = env.find? n := by
    show env'.consts.find? _ = env.consts.find? _
    rw [hc, List.find?_append, List.find?_eq_none.mpr (fun c hc' he => hne c hc' (by simpa using he)),
      Option.none_or]
  have hT' := hT
  unfold Env.famBelow at hT' ⊢
  rw [hfind, h] at *
  cases ci
  case indInfo cv caps =>
    simp only at hT' ⊢
    congr 1
    unfold Env.cutAt at hT' ⊢
    rw [hc, Env.suffixAfter_append_of_ne _ hne, ht]
    congr 1
    exact Env.liveTables_append_dead _ fun t htm => hT' t htm _ rfl
  all_goals rfl

/-- **The environment below a stored family's block is the same across fresh pushes.** -/
theorem FreshExt.famBelow {env env' : Env} (hx : FreshExt env env') {n : Name} {ci : ConstantInfo}
    (h : env.find? n = some ci) : env'.famBelow n = env.famBelow n := by
  obtain ⟨new, hc, hfr⟩ := hx.consts
  obtain ⟨newT, ht, hgt⟩ := hx.tables
  have hne : ∀ c ∈ new, c.name ≠ n := fun c hc' he => by
    have := hfr c hc'
    rw [he, h] at this
    exact nomatch this
  -- a name absent from the environment is absent from every cut below a family
  have hcut : ∀ m : Name, env.find? m = none → ∀ E, env.famBelow n = some E →
      E.consts.find? (·.name == m) = none := by
    intro m hm E hE
    unfold Env.famBelow at hE
    rw [h] at hE
    cases ci
    case indInfo cv caps =>
      obtain rfl := Option.some.inj hE
      have hsuf : (Env.suffixAfter env.consts n).drop caps.blockPos <:+ env.consts :=
        (List.drop_suffix _ _).trans (Env.suffixAfter_suffix _ _)
      refine List.find?_eq_none.mpr fun c hcm he => ?_
      have hfound : (env.consts.find? (·.name == m)).isSome = true := by
        rw [List.find?_isSome]
        exact ⟨c, hsuf.subset hcm, he⟩
      rw [show env.find? m = env.consts.find? (·.name == m) from rfl] at hm
      rw [hm] at hfound
      exact nomatch hfound
    all_goals exact nomatch hE
  exact Env.famBelow_push hc hne ht h (fun t htm => hcut _ (hgt t htm))

/-- No push is an extension under fresh names. -/
theorem FreshExt.refl (env : Env) : FreshExt env env :=
  ⟨⟨[], rfl, fun _ h => nomatch h⟩, ⟨[], rfl, fun _ h => nomatch h⟩⟩

/-- Head normalization's equations do not see the environment where `whnf` does not. -/
theorem whnfTelescope_congr_whnf {ops₁ ops₂ : ConLeche.CheckerOps ConLeche.CheckM}
    {env₁ env₂ : Env} (h : ops₁.whnf env₁ = ops₂.whnf env₂) :
    ∀ (i n : Nat) (e : Expr), ConLeche.whnfTelescope ops₁ env₁ i n e
      = ConLeche.whnfTelescope ops₂ env₂ i n e := by
  intro i n
  induction n generalizing i with
  | zero => intro e; simp only [ConLeche.whnfTelescope, h]
  | succ n ih => intro e; simp only [ConLeche.whnfTelescope, h, ih]

/-- **A family's telescope reads its environment only below its block.** -/
theorem familyTelescope_congr_famBelow {mode : ConLeche.CheckMode} {F : Nat} {env₁ env₂ : Env}
    {cv : ConstantVal} (caps : IndCaps) (h : env₁.famBelow cv.name = env₂.famBelow cv.name) :
    ConLeche.familyTelescope (fueledOps mode F) env₁ cv caps
      = ConLeche.familyTelescope (fueledOps mode F) env₂ cv caps := by
  have hw : ((fueledOps mode F).below cv.name).whnf env₁
      = ((fueledOps mode F).below cv.name).whnf env₂ := by
    funext d e
    show (fueledOps mode F).whnfB env₁ cv.name d e = (fueledOps mode F).whnfB env₂ cv.name d e
    simp only [fueledOps, h]
  unfold ConLeche.familyTelescope ConLeche.reducedFormer
  rw [whnfTelescope_congr_whnf hw]

/-- A stored family's telescope reads alike across fresh pushes. -/
theorem FreshExt.familyTelescope {env env' : Env} (hx : FreshExt env env') {mode : ConLeche.CheckMode}
    {F : Nat} {cv : ConstantVal} {caps : IndCaps} {ci : ConstantInfo}
    (h : env.find? cv.name = some ci) :
    ConLeche.familyTelescope (fueledOps mode F) env' cv caps
      = ConLeche.familyTelescope (fueledOps mode F) env cv caps :=
  familyTelescope_congr_famBelow caps (hx.famBelow h)

/-- The reduced former below a block is the reduced former at the environment below it. -/
theorem reducedFormer_below_eq {mode : ConLeche.CheckMode} {F : Nat} {env E : Env} {n : Name}
    (h : env.famBelow n = some E) (cv : ConstantVal) (k : Nat) :
    reducedFormer ((fueledOps mode F).below n) env cv k = reducedFormer (fueledOps mode F) E cv k := by
  have hw : ((fueledOps mode F).below n).whnf env = (fueledOps mode F).whnf E := by
    funext d e
    show (fueledOps mode F).whnfB env n d e = _
    simp only [fueledOps, h]
  unfold ConLeche.reducedFormer
  rw [whnfTelescope_congr_whnf hw]

/-- The environment cut at all its constants extends it while no rule is active: the same
constants, every stored structure's table live, and no rule on either side. -/
theorem envExt_cutAt_self {env : Env} (hsf : StoredFacts env) (hnil : env.rules.active = []) :
    EnvExt env (env.cutAt env.consts) where
  find := fun _ _ h => h
  table := fun T hT => by
    unfold Env.findTable? Env.cutAt
    simp only [show ∀ (ts : List ProjTable) (rs : ConLeche.RuleTable),
      Env.find? ⟨env.consts, ts, rs⟩ T = env.find? T from fun _ _ => rfl, hT, ↓reduceIte]
    rw [Env.liveTables_find]
    cases ht : env.tables.find? (·.structName == T) with
    | none => rfl
    | some t =>
      have hm := List.mem_of_find?_eq_some ht
      obtain ⟨h0, -, h2⟩ := hsf.wf.tables t hm
      have hres : Env.tableOkAt env.consts t = true := by
        simp only [Env.tableOkAt, Bool.and_eq_true]
        refine ⟨h0, Array.all_eq_true_iff_forall_mem.mpr fun b hb => ?_⟩
        obtain ⟨i, hi⟩ := Array.getElem?_of_mem hb
        exact (ConLeche.Expr.constsResolve_eq_of_find (env := env) (env' := ⟨env.consts, [], {}⟩) rfl b).trans
          (h2 i b hi).2.2.1
      simp [Option.filter, hres]
  rules := fun c => by simp [Env.rulesFor, Env.cutAt, hnil]
  facts := hsf

/-- **The reductions behind a carrier's recorded telescopes**: a member whose declared type does
not show its telescope reads, below its block, what its block read. -/
@[expose] def FamilyRan {env : Env} (mp : EnvModelM V env) : Prop :=
  ∀ D ∈ mp.lfpBlocks, ∀ (mm : Nat) (f : ConstantVal), mm < D.k → D.telescope mm = some f →
    ∀ (cv : ConstantVal) (caps : IndCaps), env.find? (D.member mm) = some (.indInfo cv caps) →
    ConLeche.formerDefHeaded cv = true →
    ∃ F : Nat, ConLeche.familyTelescope (fueledOps .verified F) env cv caps = .ok f.type

/-- **What a run reads of a recorded family's telescope is what its block read**, at an
extension under fresh names, with the carrier's blocks. -/
theorem FamilyRan.read {env env' : Env} {mp : EnvModelM V env} {mk : EnvModelM V env'}
    (hS : FamilyRan mp) (hx : FreshExt env env')
    (hb : ∀ D ∈ mk.lfpBlocks, D ∈ mp.lfpBlocks) (F : Nat) : FamilyRead mk F := by
  intro D hD mm cv caps ty hmm hf hfam
  obtain ⟨-, -, hrd, -⟩ := mk.lfp_ok D hD
  obtain ⟨cv', caps', hf', ⟨hsame, hsh⟩, -⟩ := hrd mm hmm
  rw [hf] at hf'
  obtain ⟨rfl, rfl⟩ : cv = cv' ∧ caps = caps' := by simpa using hf'
  rcases ConLeche.familyTelescope_cases hfam with ⟨hfl, rfl⟩ | ⟨hfl, cvR, hrun, rfl⟩
  · rw [hsame hfl]
  · rcases hsh with ⟨-, hn⟩ | ⟨f, hs, -⟩
    · rw [hfl] at hn; exact nomatch hn
    · obtain ⟨cv₀, caps₀, hf₀⟩ := (mp.lfp_ok D (hb D hD)).2.1.1 mm hmm
      have hf₁ := hx.find hf₀
      rw [hf] at hf₁
      obtain ⟨rfl, rfl⟩ : cv = cv₀ ∧ caps = caps₀ := by simpa using hf₁
      obtain ⟨F₁, hrun₁⟩ := hS D (hb D hD) mm f hmm hs cv caps hf₀ hfl
      have hfam₁ : ConLeche.familyTelescope (fueledOps .verified F₁) env' cv caps = .ok f.type := by
        rw [hx.familyTelescope (show env.find? cv.name = _ by
          rw [← ConLeche.Env.find?_name hf₀] at hf₀; exact hf₀)]
        exact hrun₁
      rw [familyTelescope_unique hfam hfam₁]
      simp [LfpDatum.formerAt, hs]

/-- The tables on the old names across added constants and no table. -/
theorem findTable_of_added {env env₂ : Env} {new : List ConstantInfo}
    (hnew : env₂.consts = new ++ env.consts) (htab : env₂.tables = env.tables) (T : Name)
    (hT : (env.find? T).isSome = true) : env₂.findTable? T = env.findTable? T := by
  have hs₂ : (env₂.find? T).isSome = true := by
    show (env₂.consts.find? (·.name == T)).isSome = true
    rw [hnew, List.find?_append, Option.isSome_or]
    exact Bool.or_eq_true_iff.mpr (Or.inr hT)
  unfold Env.findTable?
  rw [hs₂, hT, htab]

/-- **What a run needs of an environment to be read at its extensions.** -/
structure NatFacts (env : Env) : Prop where
  trio : (env.find? ConLeche.natName).isSome = true ∨ (env.find? ConLeche.natZeroName).isSome = true ∨
      (env.find? ConLeche.natSuccName).isSome = true →
    (env.find? ConLeche.natName).isSome = true ∧ (env.find? ConLeche.natZeroName).isSome = true ∧
      (env.find? ConLeche.natSuccName).isSome = true

/-- **What the knot reads of an environment past the term in hand**, off the carrier. -/
theorem EnvModelM.storedFacts {env : Env} (mp : EnvModelM V env) (hN : NatFacts env) :
    StoredFacts env where
  wf := mp.base2.wf
  natTrio := hN.trio
  recCtors := mp.base2.rec_ctors
  opDefn := mp.op_defn
  tableCtors := fun _ _ hf => by
    obtain ⟨-, -, -, -, cvC, _, hc, -⟩ := mp.base2.proj_ok _ _ hf
    rw [hc]; rfl
  boolCtors := by
    have hg : ∀ c, c ∈ ConLeche.natOpNames → (c = ConLeche.natBeqName ∨ c = ConLeche.natBleName) →
        ConLeche.isDefinitionAt env c = true →
        (env.find? ConLeche.boolTrueName).isSome = true ∧
          (env.find? ConLeche.boolFalseName).isSome = true := by
      intro c hmemc hc hs
      obtain ⟨-, -, hb⟩ := ConLeche.natOpGuard_inv (natOpGuardLaw_of mp c (Or.inl hmemc) hs)
      obtain ⟨⟨ciT, hT, -⟩, ⟨ciF, hF', -⟩⟩ := hb (by rcases hc with h | h <;> simp [h])
      rw [hT, hF']
      exact ⟨rfl, rfl⟩
    rintro (h | h)
    · exact hg _ (by simp [ConLeche.natOpNames]) (Or.inl rfl) h
    · exact hg _ (by simp [ConLeche.natOpNames]) (Or.inr rfl) h

omit [SetTheory V] in
/-- An unreserved name is none of `Nat`'s block's three. -/
theorem nat_names_of_unreserved {n : Name} (h : ConLeche.reservedBasisNames.contains n = false) :
    n ≠ ConLeche.natName ∧ n ≠ ConLeche.natZeroName ∧ n ≠ ConLeche.natSuccName := by
  refine ⟨?_, ?_, ?_⟩ <;> (rintro rfl; revert h; decide)

omit [SetTheory V] in
/-- New constants named none of `Nat`'s block's names. -/
theorem NatFacts.append {env env₂ : Env} {new : List ConstantInfo} (hN : NatFacts env)
    (hnew : env₂.consts = new ++ env.consts)
    (hres : ∀ c ∈ new, c.name ≠ ConLeche.natName ∧ c.name ≠ ConLeche.natZeroName ∧
      c.name ≠ ConLeche.natSuccName) : NatFacts env₂ := by
  have hf : ∀ n, (∀ c ∈ new, c.name ≠ n) → env₂.find? n = env.find? n := by
    intro n hn
    show env₂.consts.find? (·.name == n) = _
    rw [hnew, List.find?_append]
    rw [List.find?_eq_none.mpr (fun c hc => by
      intro he
      exact hn c hc (by simpa using he))]
    rfl
  have h₁ := hf ConLeche.natName fun c hc => (hres c hc).1
  have h₂ := hf ConLeche.natZeroName fun c hc => (hres c hc).2.1
  have h₃ := hf ConLeche.natSuccName fun c hc => (hres c hc).2.2
  exact ⟨by rw [h₁, h₂, h₃]; exact hN.trio⟩

/-- **Shown telescopes across a step that records none.** -/
theorem FamilyRan.step {env env' : Env} {mp : EnvModelM V env} {mp' : EnvModelM V env'}
    (hS : FamilyRan mp) (r : CoverRel mp mp') (hx : FreshExt env env') :
    FamilyRan mp' := by
  intro D hD mm f hmm hs cv caps hf hdh
  rcases r.blocks D hD with h₀ | h₀
  · obtain ⟨cv₀, caps₀, hf₀⟩ := (mp.lfp_ok D h₀).2.1.1 mm hmm
    have hf₁ := r.find _ _ hf₀
    rw [hf] at hf₁
    obtain ⟨rfl, rfl⟩ : cv = cv₀ ∧ caps = caps₀ := by simpa using hf₁
    obtain ⟨F, hrun⟩ := hS D h₀ mm f hmm hs cv caps hf₀ hdh
    refine ⟨F, ?_⟩
    rw [hx.familyTelescope (show env.find? cv.name = _ by
      rw [← ConLeche.Env.find?_name hf₀] at hf₀; exact hf₀)]
    exact hrun
  · rw [h₀] at hs; exact nomatch hs

end ConLeche.Model
