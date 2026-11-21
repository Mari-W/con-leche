module

public import ConLeche.Verify.Rules.Defs
public import ConLeche.Verify.Knot
import ConLeche.Verify.Rules.Certs
import ConLeche.Rules.Derived
import ConLeche.Verify.InferLemmas

public section

/-!
# The reduction bridges (task #305, lane B2)

`whnfCore` and `whnf` at `fuel + 1` from the five bridges at `fuel`,
through the reduction helpers: literal acceleration, the literal
expansions, the projection certificate, the stuck-major rescues, the
major's preparation, ι, and the two loops.

Inversions: `whnf_app_inv` (the `.app` clause: β, ι,
stuck), `whnf_proj_inv` (the `.proj` clause), `whnfCore_letE_inv`, `whnfStep_inv`,
`whnfLoopFuel_succ`, `reduceNat`'s branches (no inversion lemma:
split inline), `litMajorToCtorFueled_inv`, `projLitToCtorFueled_inv`,
`projCertAt_verified_inv`, `majorToCtor_inv`,
`prepareMajorFueled_ind`, `iotaRec_inv`, `iotaIndexOk_inv`.
-/

namespace ConLeche.Rules

variable {μ : CheckMode} {eager : Bool} {env : Env} {fuel : Nat}

/-- `reduceNat` ⇒ `Red.natSucc` / `Red.natOp` (the two accelerated
shapes; the WF-names safety net throws or answers `none`). -/
theorem reduceNat_bridge (hw : WhnfBridge μ eager env fuel)
    {d : Nat} {e e₂ : Expr}
    (h : reduceNatFueled μ eager env fuel d e = .ok (some e₂)) :
    Red env d e e₂ := by
  match e, h with
  | .app (.const c []) a, h =>
    simp only [reduceNatFueled, reduceNat, Bind.bind, Except.bind, whnf_def] at h
    split at h
    · next hcond =>
      obtain ⟨rfl, hnat⟩ := hcond
      cases hwa : whnf μ eager env fuel d a with
      | error err => rw [hwa] at h; exact nomatch h
      | ok a0 =>
      rw [hwa] at h
      dsimp only at h
      cases hra : rawNatLit? a0 with
      | none => rw [hra] at h; simp [pure, Except.pure] at h
      | some n =>
        rw [hra] at h
        simp only [pure, Except.pure, Except.ok.injEq, Option.some.injEq] at h
        subst h
        exact .natSucc hnat (hw hwa) hra
    · simp [pure, Except.pure] at h
  | .app (.app (.const c []) a) b, h =>
    simp only [reduceNatFueled, reduceNat, Bind.bind, Except.bind, whnf_def] at h
    split at h
    · next hnames =>
      have hmem : c ∈ natBinOpNames := by
        rcases hnames with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      cases hwa : whnf μ eager env fuel d a with
      | error err => rw [hwa] at h; exact nomatch h
      | ok a0 =>
      rw [hwa] at h
      dsimp only at h
      cases hra : rawNatLit? a0 with
      | none => rw [hra] at h; simp [pure, Except.pure] at h
      | some n₁ =>
      rw [hra] at h
      dsimp only at h
      cases hwb : whnf μ eager env fuel d b with
      | error err => rw [hwb] at h; exact nomatch h
      | ok b0 =>
      rw [hwb] at h
      dsimp only at h
      cases hrb : rawNatLit? b0 with
      | none => rw [hrb] at h; simp [pure, Except.pure] at h
      | some n₂ =>
        rw [hrb] at h
        dsimp only at h
        cases hres : natOpResult c n₁ n₂ with
        | none => rw [hres] at h; simp [pure, Except.pure] at h
        | some r =>
          rw [hres] at h
          simp only [pure, Except.pure, Except.ok.injEq, Option.some.injEq] at h
          subst h
          exact .natOp hmem (hw hwa) hra (hw hwb) hrb hres
    · simp [pure, Except.pure] at h
  | .bvar _, h | .fvar _ _, h | .sort _, h | .lam _ _, h
  | .forallE _ _, h | .letE _ _ _, h | .lit _, h
  | .proj _ _ _, h | .const _ _, h =>
    simp [reduceNatFueled, reduceNat, pure, Except.pure] at h
  | .app (.bvar _) _, h | .app (.fvar _ _) _, h
  | .app (.sort _) _, h | .app (.lam _ _) _, h
  | .app (.forallE _ _) _, h | .app (.letE _ _ _) _, h
  | .app (.lit _) _, h | .app (.proj _ _ _) _, h =>
    simp [reduceNatFueled, reduceNat, pure, Except.pure] at h
  | .app (.const c (_ :: _)) _, h =>
    simp [reduceNatFueled, reduceNat, pure, Except.pure] at h
  | .app (.app (.bvar _) _) _, h | .app (.app (.fvar _ _) _) _, h
  | .app (.app (.sort _) _) _, h | .app (.app (.app _ _) _) _, h
  | .app (.app (.lam _ _) _) _, h
  | .app (.app (.forallE _ _) _) _, h
  | .app (.app (.letE _ _ _) _) _, h
  | .app (.app (.lit _) _) _, h
  | .app (.app (.proj _ _ _) _) _, h =>
    simp [reduceNatFueled, reduceNat, pure, Except.pure] at h
  | .app (.app (.const c (_ :: _)) _) _, h =>
    simp [reduceNatFueled, reduceNat, pure, Except.pure] at h

/-- `litMajorToCtor` ⇒ `Red.litToCtorIfNat` or `Red.strLitWhnf`
(`litMajorToCtorFueled_inv`). -/
theorem litMajorToCtor_bridge (hw : WhnfBridge μ eager env fuel)
    {d : Nat} {e e₁ : Expr}
    (h : litMajorToCtorFueled μ eager env fuel d e = .ok e₁) :
    Red env d e e₁ := by
  rcases litMajorToCtorFueled_inv h with rfl | ⟨s, rfl, hsup, hwh⟩
  · exact .litToCtorIfNat e
  · exact .strLitWhnf hsup (hw hwh)

/-- `projLitToCtor` ⇒ `Red.refl` or `Red.strLitWhnf`
(`projLitToCtorFueled_inv`). -/
theorem projLitToCtor_bridge (hw : WhnfBridge μ eager env fuel)
    {d : Nat} {e e₁ : Expr}
    (h : projLitToCtorFueled μ eager env fuel d e = .ok e₁) :
    Red env d e e₁ := by
  rcases projLitToCtorFueled_inv h with rfl | ⟨s, rfl, hsup, hwh⟩
  · exact .refl
  · exact .strLitWhnf hsup (hw hwh)

/-- `majorToCtor` ⇒ `Red.refl` or one of the three rescues
(`majorToCtor_inv`; the K and `And` rescues' proof-irrelevance
certificate becomes the `DefEq fab major` premise through
`proofIrrel_bridge`).

**`hrec`**: the three `Red.rescue*` rules open with `env.find? recName
= some (.recInfo cv mI rP isK [rl])` — the rule bit `isK` is
honest only at a stored recursor, which is what the soundness lane
reads them from.  `majorToCtor` itself ignores its `_recName` argument
(`Core.lean:556`), so the inversion cannot supply the fact and the
caller must: `iotaRec_inv` hands it over at the one site that runs the
chain (through `prepareMajor_bridge`, which passes it through). -/
theorem majorToCtor_bridge (hw : WhnfBridge .verified eager env fuel)
    (hd : DefEqBridge .verified eager env fuel) (hio : InferIOBridge .verified eager env fuel)
    {d : Nat} {recName : Name} {isK : Bool} {rules : List RecRule} {major major' : Expr}
    (hrec : ∃ cv mI rP, env.find? recName = some (.recInfo cv mI rP isK rules))
    (h : majorToCtorFueled .verified eager env fuel d recName isK rules major = .ok major') :
    Red env d major major' := by
  obtain ⟨cv, mI, rP, hfr⟩ := hrec
  rcases majorToCtor_inv h with rfl | ⟨hsc1, hsc2, hsc3, rl, cvj, cnP, cnF,
    tmaj₀, tmaj, T, ust, cvT, caps, rfl, hfj, hfT, hinf, hwh, hfn, harm⟩
  · exact .refl
  rcases harm with ⟨hk, hlps, hle, rfl, ⟨tf, htf, hdq⟩, hpirr⟩ |
    ⟨tbl, heta, hlen, hlps, rfl⟩ |
    ⟨rfl, hlen, hlps, hslots, rfl, ⟨tf, htf, hdq⟩, hpirr⟩
  · -- the major's half of the `proofIrrel (fab, major)` run: a proof
    obtain ⟨-, -, -, tb, stb, vT, -, -, -, -, htb, hstb, hwstb, hvT⟩ :=
      proofIrrel_inv (hpirr rfl)
    exact .rescueK hfr hk hfj hfT (inferTypeIO_bridge hio hinf) (hw hwh) hfn
      hlps hle rfl hsc1 hsc2 hsc3
      (inferTypeIO_bridge hio htf) (hd hdq) (inferTypeIO_bridge hio htb)
      (inferTypeIO_bridge hio hstb) (hw hwstb) hvT
  · exact .rescueEta hfr hfj hfT heta (inferTypeIO_bridge hio hinf) (hw hwh)
      hfn hlen hlps rfl hsc1 hsc2 hsc3
  · obtain ⟨-, -, -, tb, stb, vT, -, -, -, -, htb, hstb, hwstb, hvT⟩ :=
      proofIrrel_inv (hpirr rfl)
    exact .rescueAnd hfr hfj hfT (inferTypeIO_bridge hio hinf) (hw hwh) hfn
      hlen hlps hslots rfl hsc1 hsc2 hsc3
      (inferTypeIO_bridge hio htf) (hd hdq) (inferTypeIO_bridge hio htb)
      (inferTypeIO_bridge hio hstb) (hw hwstb) hvT

/-- `prepareMajor` ⇒ a `Red` chain (`prepareMajorFueled_ind` with the
motive `Red env d a ·`: each of the three steps is a `Red.trans`).
`hrec` is `majorToCtor_bridge`'s, passed through. -/
theorem prepareMajor_bridge (hw : WhnfBridge .verified eager env fuel)
    (hd : DefEqBridge .verified eager env fuel) (hio : InferIOBridge .verified eager env fuel)
    {d : Nat} {recName : Name} {isK : Bool} {rules : List RecRule} {a m : Expr}
    (hrec : ∃ cv mI rP, env.find? recName = some (.recInfo cv mI rP isK rules))
    (h : prepareMajorFueled .verified eager env fuel d recName isK rules a = .ok m) :
    Red env d a m :=
  prepareMajorFueled_ind h (Red env d a)
    (fun hwh hp => .trans hp (hw hwh))
    (fun hl hp => .trans hp (litMajorToCtor_bridge hw hl))
    (fun hm hp => .trans hp (majorToCtor_bridge hw hd hio hrec hm))
    .refl

/-- Level instantiation keeps a telescope's syntactic arity. -/
theorem peelPis_isSome_instantiateLevelParams (ks : List Name) (us : List Level) :
    ∀ (k : Nat) {e : Expr}, (Expr.peelPis k e).isSome = true →
      (Expr.peelPis k (e.instantiateLevelParams ks us)).isSome = true
  | 0, _, _ => rfl
  | k + 1, .forallE _ b, h => by
    simp only [Expr.instantiateLevelParams, Expr.peelPis] at h ⊢
    exact peelPis_isSome_instantiateLevelParams ks us k h
  | _ + 1, .bvar _, h | _ + 1, .fvar _ _, h | _ + 1, .sort _, h
  | _ + 1, .const _ _, h | _ + 1, .app _ _, h | _ + 1, .lam _ _, h
  | _ + 1, .letE _ _ _, h | _ + 1, .lit _, h | _ + 1, .proj _ _ _, h => by
    simp [Expr.peelPis] at h

/-- The walk to a family's sort is `FormerSort`. -/
theorem formerSortLoop_bridge (hw : WhnfBridge .verified eager env fuel) :
    ∀ {n d : Nat} {e : Expr} {s : Level},
      formerSortLoop (pureFns .verified eager env fuel).whnf d n e = .ok (some s) →
      FormerSort env d n e s
  | 0, d, e, s, h => by
    unfold formerSortLoop at h
    cases hr : (pureFns .verified eager env fuel).whnf d e with
    | error err => rw [hr] at h; exact nomatch h
    | ok w =>
      rw [hr] at h
      cases w with
      | sort s' =>
        cases Option.some.inj (Except.ok.inj h)
        exact .sort (hw hr)
      | _ => exact nomatch h
  | n + 1, d, e, s, h => by
    unfold formerSortLoop at h
    cases hr : (pureFns .verified eager env fuel).whnf d e with
    | error err => rw [hr] at h; exact nomatch h
    | ok w =>
      rw [hr] at h
      cases w with
      | forallE dom b => exact .pi (hw hr) (formerSortLoop_bridge hw h)
      | _ => exact nomatch h

/-- A family's sort reached at a use: never zero, by the type's shape or by the
walk. -/
theorem formerNeverZeroAt_bridge (hw : WhnfBridge .verified eager env fuel)
    {cvT : ConstantVal} {caps : IndCaps} {us : List Level}
    (h : formerNeverZeroAt (pureFns .verified eager env fuel).whnf cvT caps us = .ok true) :
    formerNeverZero cvT us = true ∨
      formerResSort cvT.type = none ∧ ∃ s, FormerSort env 0 (caps.nparams + caps.nIdx)
          (cvT.type.instantiateLevelParams cvT.levelParams us) s ∧
        (Level.zeronessOf s).isNever = true := by
  unfold formerNeverZeroAt at h
  split at h
  · exact .inl (Except.ok.inj h)
  · next hnone =>
    cases hr : formerSortLoop (pureFns .verified eager env fuel).whnf 0
        (caps.nparams + caps.nIdx) (cvT.type.instantiateLevelParams cvT.levelParams us) with
    | error err => rw [hr] at h; exact nomatch h
    | ok o =>
      rw [hr] at h
      cases o with
      | none => exact nomatch h
      | some s => exact .inr ⟨hnone, s, formerSortLoop_bridge hw hr, Except.ok.inj h⟩

/-- The ι case split's verdict is `IotaCase`. -/
theorem iotaCase3At_bridge (hw : WhnfBridge .verified eager env fuel)
    {isK : Bool} {induct : Name} {us : List Level} {c3 : Bool}
    (h : iotaCase3At (pureFns .verified eager env fuel).whnf env.find? isK induct us = .ok c3) :
    IotaCase env isK induct us c3 := by
  cases c3 with
  | true => exact .three
  | false =>
    unfold iotaCase3At at h
    split at h
    · next hk => rw [show isK = true from hk]; exact .k
    · next hk =>
      rw [show isK = false by simpa using hk]
      split at h
      · next cvT caps hfam =>
        split at h
        · next hlen =>
          cases hr : formerNeverZeroAt (pureFns .verified eager env fuel).whnf cvT caps us with
          | error err => rw [hr] at h; exact nomatch h
          | ok nz =>
            rw [hr] at h
            have hnz : nz = true := by
              cases nz with
              | true => rfl
              | false => exact nomatch h
            subst hnz
            have hlen' : cvT.levelParams.length = us.length := by simpa using hlen
            rcases formerNeverZeroAt_bridge hw hr with h' | ⟨hnone, s, hs, hn⟩
            · exact .never hfam hlen' h'
            · exact .walk hfam hlen' hnone hs hn
        · exact nomatch h
      · exact nomatch h


/-- The ι case split at the stored facts first is `IotaCaseS`. -/
theorem iotaCaseAt_bridge (hw : WhnfBridge .verified eager env fuel)
    {isK : Bool} {induct : Name} {us : List Level} {c3 : Bool}
    (h : iotaCaseAt (pureFns .verified eager env fuel).whnf env.find? isK induct us = .ok c3) :
    IotaCaseS env isK induct us c3 := by
  unfold iotaCaseAt at h
  split at h
  · next hn =>
    cases Except.ok.inj h
    exact .stored hn
  · exact .use (iotaCase3At_bridge hw h)
/-- `iotaRec` ⇒ `Red.iota` (`iotaRec_inv`, `prepareMajor_bridge`,
`defEqList_bridge`, the arity-checked recursor spine, and at a case-3 redex
`iotaCertsFull_bridge` and `iotaIndexOk_inv`). -/
theorem iotaRec_bridge (hw : WhnfBridge .verified eager env fuel)
    (hd : DefEqBridge .verified eager env fuel) (hi : InferBridge .verified eager env fuel)
    (hio : InferIOBridge .verified eager env fuel)
    {d : Nat} {e e'' : Expr}
    (h : iotaRecFueled .verified eager env fuel d e = .ok (some e'')) :
    Red env d e e'' := by
  obtain ⟨c, us, cv, mI, rP, isK, rules, major, cj, usj, cvj, cnP, cnF, induct, rl,
    hfn, hfc, hlen, hlvl, hprep, hmfn, hfj, hrule, hml, h3, rfl⟩ := iotaRec_inv h
  have hmaj : Red env d (e.getAppArgs.getD mI (.bvar 0)) major :=
    prepareMajor_bridge hw hd hio ⟨cv, mI, rP, hfc⟩ hprep
  -- the arity-checked recursor spine's arity: the checker's test on the
  -- stored type (task #342 L18)
  have harity : (Expr.peelPis e.getAppArgs.length
      (cv.type.instantiateLevelParams cv.levelParams us)).isSome = true := by
    rw [hlen]
    exact peelPis_isSome_instantiateLevelParams _ _ _ (iotaRec_arity h hfn hfc)
  obtain ⟨c3, hrun, h3⟩ := h3 rfl
  have hcase := iotaCaseAt_bridge hw hrun
  cases c3 with
  | true =>
    obtain ⟨hlev, hpeq, hcerts, hidx⟩ := h3 rfl
    by_cases hne : mI = rP
    · exact .iota (residual := .bvar 0) hfn hfc hlen hlvl hmaj hmfn hfj hrule hml hcase
        (fun _ => hlev) (fun _ => defEqList_bridge hd hpeq)
        harity
        (fun _ => iotaCertsFull_bridge hd hi hcerts)
        (fun _ hc => absurd hne hc) (fun _ hc => absurd hne hc)
    · obtain ⟨residual, hres, hdl⟩ := iotaIndexOk_inv hidx hne
      exact .iota hfn hfc hlen hlvl hmaj hmfn hfj hrule hml hcase
        (fun _ => hlev) (fun _ => defEqList_bridge hd hpeq)
        harity
        (fun _ => iotaCertsFull_bridge hd hi hcerts)
        (fun _ _ => hres) (fun _ _ => defEqList_bridge hd hdl)
  | false =>
    exact .iota (residual := .bvar 0) hfn hfc hlen hlvl hmaj hmfn hfj hrule hml hcase
      (fun hc => nomatch hc) (fun hc => nomatch hc)
      harity
      (fun hc => nomatch hc)
      (fun hc => nomatch hc) (fun hc => nomatch hc)

/-- A firing projection rule (`reduceProjCore`) is a `Red` chain: the
string-literal expansion, then `Red.proj` under its certificate. -/
theorem reduceProjCore_bridge (hw : WhnfBridge .verified eager env fuel)
    {d : Nat} {sn : Name} {i : Nat} {c m : Expr}
    (h : reduceProjCoreFueled .verified eager env fuel d sn i c = .ok (some m)) :
    Red env d (.proj sn i c) m := by
  obtain ⟨e₃, us, entry, hlit, hfn, hfp, hi, hlen, hus, rfl, hcert⟩ :=
    reduceProjCore_inv h
  obtain ⟨cvC, nP, nF, _, hc, harity⟩ := projCertAt_verified_inv hcert
  exact .trans (.projArg (projLitToCtor_bridge hw hlit))
    (.proj hfp hfn hi hlen hus hc
      (peelPis_isSome_instantiateLevelParams _ _ _ harity))

/-- **The pool invariant** of a rule's match: every binding of the binder slots is a subterm of
the application tree of a pool term. -/
@[expose] def SlotsIn (P : List Expr) (st : List (Option Expr) × List (Option Level)) : Prop :=
  ∀ x, some x ∈ st.1 → ∃ q ∈ P, x ∈ appSubterms q

theorem SlotsIn.replicate (P : List Expr) (n : Nat) (lv : List (Option Level)) :
    SlotsIn P (List.replicate n none, lv) := fun _ hx =>
  nomatch List.eq_of_mem_replicate (show _ ∈ List.replicate n none from hx)

theorem SlotsIn.cons {P : List Expr} {q : Expr} {st : List (Option Expr) × List (Option Level)}
    (h : SlotsIn P st) : SlotsIn (q :: P) st := fun x hx =>
  let ⟨q', hq', hx'⟩ := h x hx
  ⟨q', List.mem_cons_of_mem _ hq', hx'⟩

/-- The pool after an application position: the bindings in the function's view, the argument's
view or the pool before lie in the application's view or the pool before. -/
theorem SlotsIn.app {P : List Expr} {f₁ a₁ : Expr} {st : List (Option Expr) × List (Option Level)}
    (h : SlotsIn (a₁ :: f₁ :: P) st) : SlotsIn (.app f₁ a₁ :: P) st := fun x hx => by
  obtain ⟨q, hq, hxq⟩ := h x hx
  simp only [List.mem_cons] at hq
  rcases hq with rfl | rfl | hq
  · exact ⟨_, List.mem_cons_self, by
      simp only [appSubterms, List.mem_cons, List.mem_append]; exact Or.inr (Or.inr hxq)⟩
  · exact ⟨_, List.mem_cons_self, by
      simp only [appSubterms, List.mem_cons, List.mem_append]; exact Or.inr (Or.inl hxq)⟩
  · exact ⟨q, List.mem_cons_of_mem _ hq, hxq⟩

theorem mem_appSubterms_self (e : Expr) : e ∈ appSubterms e := by
  cases e <;> simp [appSubterms]

/-- **A rule's match is `MatchRel`**: the spine position by position, an argument equal, matched
after its retry (`whnf` through the bridge, then the literal conversion), or, at a repeated
variable, definitionally equal to its binding (through the `isDefEq` bridge), which the pool
invariant places in the application tree of an earlier view. -/
theorem ruleMatchM_bridge (hw : WhnfBridge μ eager env fuel) (hd : DefEqBridge μ eager env fuel)
    {d n : Nat} {lps : List Name} :
    ∀ (pat : Expr) (P : List Expr) {st st' : List (Option Expr) × List (Option Level)}
      {e e₁ : Expr}, SlotsIn P st →
      ruleMatchM (pureFns μ eager env fuel) env d n lps pat st e = .ok (some (st', e₁)) →
      MatchRel env d P e e₁ ∧ SlotsIn (e₁ :: P) st' := by
  intro pat
  induction pat with
  | app f p ihf ihp =>
    intro P st st' e e₁ hst h
    cases e with
    | app f' a =>
      simp only [ruleMatchM] at h
      obtain ⟨o, ho, h⟩ := bindM_ok h
      cases o with
      | none => simp [pure, Except.pure] at h
      | some sf =>
        obtain ⟨st₁, f₁⟩ := sf
        obtain ⟨o', ho', h⟩ := bindM_ok h
        cases o' with
        | none => simp [pure, Except.pure] at h
        | some sa =>
          obtain ⟨st₂, a₁⟩ := sa
          simp only [pure, Except.pure, Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨hmf, hst₁⟩ := ihf P hst ho
          suffices hA : MatchArg env d (f₁ :: P) a a₁ ∧ SlotsIn (a₁ :: f₁ :: P) st₂ from
            ⟨.app hmf hA.1, hA.2.app⟩
          unfold ruleArgStep at ho'
          split at ho'
          · rcases ruleBindVar_inv ho' with ⟨rfl, rfl⟩ | ⟨rfl, hmem, hor⟩
            · refine ⟨.spine .refl, fun x hx => ?_⟩
              rcases List.mem_or_eq_of_mem_set hx with hx | hx
              · exact hst₁.cons x hx
              · exact ⟨a₁, List.mem_cons_self, (Option.some.inj hx) ▸ mem_appSubterms_self _⟩
            · refine ⟨?_, hst₁.cons⟩
              rcases hor with rfl | hdq
              · exact .spine .refl
              · exact .defeq (hd hdq) (hst₁ _ hmem)
          · unfold ruleOrRetry at ho'
            obtain ⟨o, ho, h⟩ := bindM_ok ho'
            cases o with
            | some x =>
              simp only [pure, Except.pure, Except.ok.injEq] at h
              obtain rfl := Option.some.inj h
              obtain ⟨hm, hs⟩ := ihp _ hst₁ ho
              exact ⟨.spine hm, hs⟩
            | none =>
              obtain ⟨a', ha', h⟩ := bindM_ok h
              unfold ruleRetry at ha'
              obtain ⟨w, hwh, ha'⟩ := bindM_ok ha'
              simp only [pure, Except.pure, Except.ok.injEq] at ha'
              subst ha'
              obtain ⟨hm, hs⟩ := ihp _ hst₁ h
              refine ⟨.red (.trans (hw hwh) ?_) hm, hs⟩
              rcases litToCtor_cases env w with h' | ⟨s, rfl, hss, h'⟩
              · rw [h']; exact .litToCtorIfNat w
              · rw [h']; exact .strLit hss
    | _ => simp [ruleMatchM, pure, Except.pure] at h
  | const c ls =>
    intro P st st' e e₁ hst h
    obtain ⟨sl, lv⟩ := st
    cases e with
    | const c' ls' =>
      simp only [ruleMatchM, pure, Except.pure, Except.ok.injEq] at h
      split at h
      · obtain ⟨lv', -, h⟩ := Option.map_eq_some_iff.mp h
        simp only [Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨.refl, hst.cons⟩
      · exact nomatch h
    | _ => simp [ruleMatchM, pure, Except.pure] at h
  | _ => intro P st st' e e₁ _ h; simp [ruleMatchM, pure, Except.pure] at h

/-- A firing rewrite rule is `Red.rewrite`: `rewriteAttempt_inv` hands every premise, the
certificates and the match through the bridges, and `rewriteStep_mem` the rule's place in the
table. -/
theorem rewriteAttempt_bridge (hw : WhnfBridge μ eager env fuel)
    (hd : DefEqBridge μ eager env fuel) (hi : InferBridge μ eager env fuel)
    {d : Nat} {e e₂ : Expr} {t : Name} {c' : Name} {ls' : List Level}
    (hfn' : e.getAppFn = .const c' ls') (hmem : t ∈ env.rulesFor c')
    (h : rewriteAttempt (pureFns μ eager env fuel) env d e t = .ok (some e₂)) :
    Red env d e e₂ := by
  obtain ⟨cv, args, us, u, A, c, ls, e₁, l, hf, hm, hres, -, hlen, hsub, hcert, hlf⟩ :=
    rewriteAttempt_inv h
  obtain ⟨l₀, st', hm'⟩ := ruleArgsM_inv hm
  exact .rewrite hf hlen (iotaCertsFull_bridge hd hi hcert) hres hfn'
    (ruleMatchM_bridge hw hd l₀ [] (SlotsIn.replicate _ _ _) hm').1
    hlf hsub hmem

theorem rewriteStep_bridge (hw : WhnfBridge μ eager env fuel) (hd : DefEqBridge μ eager env fuel)
    (hi : InferBridge μ eager env fuel)
    {d : Nat} {stuck : Bool} {e e₂ : Expr} {t : Name}
    (h : rewriteStep (pureFns μ eager env fuel) env d stuck e = .ok (some (t, e₂))) :
    Red env d e e₂ := by
  obtain ⟨c', ls', hfn', hmem⟩ := rewriteStep_mem h
  -- the firing at a prefix: every prefix of the spine has the spine's head
  refine rewriteAt_ind (fun x y => x.getAppFn = .const c' ls' → Red env d x y)
    (fun ha hx => rewriteAttempt_bridge hw hd hi hx hmem ha)
    (fun hf hx => .appFn (hf hx)) e (rewriteStep_inv h) hfn'

/-- The rules fired again are a `Red` chain. -/
theorem fireMore_bridge (hw : WhnfBridge μ eager env fuel) (hd : DefEqBridge μ eager env fuel)
    (hi : InferBridge μ eager env fuel) {d k : Nat} {e e' : Expr}
    (h : fireMore (pureFns μ eager env fuel) env d k e = .ok e') : Red env d e e' :=
  fireMore_ind (fun x y => Red env d x y) (fun _ => .refl)
    (fun hrw hyz => .trans (rewriteStep_bridge hw hd hi hrw) hyz) h

/-- A reduction of the head is a reduction of the spine. -/
theorem Red.mkAppN_fn {d : Nat} : ∀ (args : List Expr) {f f' : Expr},
    Red env d f f' → Red env d (Expr.mkAppN f args) (Expr.mkAppN f' args)
  | [], _, _, h => h
  | _ :: as, _, _, h => Red.mkAppN_fn as (.appFn h)

/-- ι-then-rules ⇒ `Red.iota` or `Red.rewrite`. -/
theorem iotaThenRule_bridge (hw : WhnfBridge .verified eager env fuel)
    (hd : DefEqBridge .verified eager env fuel) (hi : InferBridge .verified eager env fuel)
    (hio : InferIOBridge .verified eager env fuel)
    {d : Nat} {e e'' : Expr}
    (h : iotaThenRule .verified (pureFns .verified eager env fuel) env d e = .ok (some e'')) :
    Red env d e e'' := by
  rcases iotaThenRule_inv h with hι | ⟨-, t, e₂, hrw, hfm⟩
  · exact iotaAt_ind (fun x y => Red env d x y) (fun h' => iotaRec_bridge hw hd hi hio h')
      (fun hf => .appFn hf) e hι
  · exact .trans (rewriteStep_bridge hw hd hi hrw) (fireMore_bridge hw hd hi hfm)

/-- **`whnfCore` at `fuel + 1`**: the eleven shapes (`whnf_app_inv`,
`whnf_proj_inv`, `whnfCore_const_inv`, the five other leaves, `whnfCore_letE_inv`, the `.bvar`
throw). -/
theorem whnfCore_bridge_succ (hwc : WhnfCoreBridge .verified eager env fuel)
    (hw : WhnfBridge .verified eager env fuel) (hd : DefEqBridge .verified eager env fuel)
    (hi : InferBridge .verified eager env fuel) (hio : InferIOBridge .verified eager env fuel) :
    WhnfCoreBridge .verified eager env (fuel + 1) := by
  intro c d e e' h
  match e, h with
  | .sort _, h | .fvar _ _, h | .forallE _ _, h | .lam _ _, h
  | .lit _, h =>
    cases Except.ok.inj h; exact .refl
  | .const _ _, h =>
    rcases whnfCore_const_inv h with ⟨t, e₂, e₃, hrw, hfm, hk⟩ | ⟨-, rfl⟩
    · exact .trans (rewriteStep_bridge hw hd hi hrw) (.trans (fireMore_bridge hw hd hi hfm) (hwc hk))
    · exact .refl
  | .bvar _, h =>
    rw [whnfCore_succ] at h
    simp [whnfCoreBody, throw, throwThe, MonadExceptOf.throw] at h
  | .letE _ _ _, h => exact .trans .zeta (hwc (whnfCore_letE_inv h))
  | .app f a, h =>
    obtain ⟨v, hf, hcase⟩ := whnf_app_inv h
    -- the spine's head reduced to `v`: the spine to `v` applied to the arguments
    have hRf : Red env d (.app f a) (Expr.mkAppN v (Expr.app f a).getAppArgs) := by
      have := Red.mkAppN_fn (Expr.app f a).getAppArgs (hwc hf)
      rwa [Expr.mkAppN_getApp] at this
    rcases hcase with ⟨ty, body, a₁, rest, rfl, hargs, hbody⟩ |
      ⟨-, ⟨e'', hiota, hcont⟩ | ⟨-, rfl⟩⟩ | ⟨-, -, hk⟩
    · rw [hargs] at hRf
      exact .trans hRf (.trans (Red.mkAppN_fn rest .beta) (hwc hbody))
    · exact .trans (iotaThenRule_bridge hw hd hi hio hiota) (hwc hcont)
    · exact .refl
    · exact .trans hRf (hwc hk)
  | .proj sn i pe, h =>
    obtain ⟨e₂, hst, hcase⟩ := whnf_proj_inv h
    have hR : Red env d (.proj sn i pe) (.proj sn i e₂) := by
      rcases hst with ⟨-, h2⟩ | ⟨-, h2⟩
      · exact .projArg (hwc h2)
      · exact .projArg (hw h2)
    rcases hcase with rfl | ⟨m, hr, hcont⟩
    · exact .refl
    · exact .trans hR (.trans (reduceProjCore_bridge hw hr) (hwc hcont))

/-- **A key argument is a reduct** of the original one: `whnf` through the bridge, the literal
reading by `Red.natLit`. -/
private theorem KeyArg.red (hw : WhnfBridge μ eager env fuel) {d : Nat} {a b : Expr}
    (h : KeyArg (pureFns μ eager env fuel) env d a b) : Red env d a b := by
  induction h with
  | refl => exact .refl
  | lit kc _ ih =>
    rcases keyLit_cases env kc _ with h' | h' <;> rw [h']
    · exact ih
    · exact .trans ih (.litToCtorIfNat _)
  | whnf _ hwh ih => exact .trans ih (hw hwh)

/-- **Arguments replaced by key arguments match position by position**: each replaced position
is `MatchArg.red`. -/
private theorem matchRel_keyArgs (hw : WhnfBridge μ eager env fuel) {d : Nat} {P : List Expr} :
    ∀ (args args' : List Expr) {f f' : Expr}, MatchRel env d P f f' →
      args'.length = args.length →
      (∀ (i : Nat) (h : i < args.length) (h' : i < args'.length),
        KeyArg (pureFns μ eager env fuel) env d args[i] args'[i]) →
      MatchRel env d P (Expr.mkAppN f args) (Expr.mkAppN f' args')
  | [], [], _, _, hf, _, _ => hf
  | a :: as, a' :: as', _, _, hf, hlen, hk => by
    simp only [Expr.mkAppN]
    refine matchRel_keyArgs hw as as' (.app hf (.red (KeyArg.red hw (hk 0 (by simp) (by simp))) .refl))
      (by simpa using hlen) (fun i h h' => ?_)
    exact hk (i + 1) (by simp; omega) (by simp; omega)
  | [], _ :: _, _, _, _, hlen, _ => by simp at hlen
  | _ :: _, [], _, _, _, hlen, _ => by simp at hlen

/-- A view related by `MatchRel` to an application relates its function part, or is the same
application. -/
theorem MatchRel.app_inv {d : Nat} {P : List Expr} {f a f' a' : Expr}
    (h : MatchRel env d P (.app f a) (.app f' a')) : MatchRel env d P f f' := by
  cases h with
  | refl => exact .refl
  | app hf _ => exact hf

/-- **A firing before unfolding is `Red.rewrite`**: the rule matched the spine with its key
arguments replaced (`MatchRel` through `matchRel_keyArgs`), at the prefix of its arity, and the
reduct takes the remaining original arguments (`Red.appFn`). -/
theorem preFire_bridge (hw : WhnfBridge μ eager env fuel) (hd : DefEqBridge μ eager env fuel)
    (hi : InferBridge μ eager env fuel) {d : Nat} {e e₂ : Expr} {t : Name}
    (h : preFire (pureFns μ eager env fuel) env d e = .ok (some (t, e₂))) : Red env d e e₂ := by
  obtain ⟨c, us, args', hc, hmem, hka, hat⟩ := preFire_inv h
  have hm : MatchRel env d [] e (Expr.mkAppN (.const c us) args') := by
    have h0 : Expr.mkAppN (.const c us) e.getAppArgs = e := by rw [← hc, Expr.mkAppN_getApp]
    have := matchRel_keyArgs (P := []) hw e.getAppArgs args' (f := .const c us) .refl hka.1 hka.2
    rwa [h0] at this
  refine preAt_ind (fun x x' y => MatchRel env d [] x x' → x.getAppFn = .const c us → Red env d x y)
    (fun ha hm' hfn => ?_) (fun ih hm' hfn => .appFn (ih hm'.app_inv hfn)) e _ hat hm hc
  obtain ⟨cv, args, us', hf, -, hfire⟩ := preAttempt_inv ha
  obtain ⟨u, A, c', ls, l, hres, -, hlen, hsub, hcert, hlf⟩ := rewriteFire_inv hfire
  exact .rewrite hf hlen (iotaCertsFull_bridge hd hi hcert) hres hfn hm' hlf hsub hmem

/-- The rules at an origin the chain from `e₀` passed through reduce `e₀` (`Red.rewrite` at the
origin). -/
theorem originFire_bridge (hw : WhnfBridge μ eager env fuel) (hd : DefEqBridge μ eager env fuel)
    (hi : InferBridge μ eager env fuel) {d : Nat} {o : Option Expr} {e₀ e e₂ : Expr} {t : Name}
    (h : originFire (pureFns μ eager env fuel) env d o e = .ok (some (t, e₂)))
    (ho : OriginP (Red env d e₀) o) : Red env d e₀ e₂ := by
  obtain ⟨o', e₃, rfl, -, hrw, hfm⟩ := originFire_inv h
  exact .trans (ho _ rfl) (.trans (rewriteStep_bridge hw hd hi hrw) (fireMore_bridge hw hd hi hfm))

/-- One `whnfStep` under a bridged continuation is a `Red` chain from the loop's input `e₀`
(`whnfStep_inv`: `whnfCore`, then acceleration (a literal is final) or δ into `k`, the fixpoint,
or the rules at the origin into `k`).  The origin, a term of the chain, is a reduct of `e₀`, and
so is the rule's right side there. -/
theorem whnfStep_bridge (hwc : WhnfCoreBridge μ eager env fuel) (hw : WhnfBridge μ eager env fuel)
    (hd : DefEqBridge μ eager env fuel) (hi : InferBridge μ eager env fuel)
    {d : Nat} {e₀ : Expr} {k : Option Expr → Expr → CheckM Expr}
    (hk : ∀ {o : Option Expr} {e e' : Expr}, k o e = .ok e' → Red env d e₀ e →
      OriginP (Red env d e₀) o → Red env d e₀ e')
    {o : Option Expr} {e e' : Expr}
    (h : whnfStep (pureFns μ eager env fuel) env d k o e = .ok e')
    (he : Red env d e₀ e) (ho : OriginP (Red env d e₀) o) :
    Red env d e₀ e' := by
  obtain ⟨e₁, hwc₁, hrest⟩ := whnfStep_inv h
  have h₁ : Red env d e₀ e₁ := .trans he (hwc hwc₁)
  rcases hrest with ⟨e₂, hnat, ⟨-, rfl⟩ | hk₂⟩ | ⟨-, e₂, hδ, hk₂⟩ |
    ⟨-, -, ⟨-, rfl⟩ | ⟨t, e₂, hof, hk₂⟩⟩ | ⟨-, t, e₂, hpf, hk₂⟩
  · exact .trans h₁ (reduceNat_bridge hw hnat)
  · exact hk hk₂ (.trans h₁ (reduceNat_bridge hw hnat)) ho
  · exact hk hk₂ (.trans h₁ (.delta hδ)) (ho.note h₁)
  · exact h₁
  · exact hk hk₂ (originFire_bridge hw hd hi hof ho) (OriginP.none _)
  · exact hk hk₂ (.trans h₁ (preFire_bridge hw hd hi hpf)) ho

/-- The loop at every budget. -/
theorem whnfLoop_bridge (hwc : WhnfCoreBridge μ eager env fuel) (hw : WhnfBridge μ eager env fuel)
    (hd : DefEqBridge μ eager env fuel) (hi : InferBridge μ eager env fuel)
    {d : Nat} {e₀ : Expr} : ∀ (n : Nat) {o : Option Expr} {e e' : Expr},
      whnfLoop (pureFns μ eager env fuel) env d n o e = .ok e' →
      Red env d e₀ e → OriginP (Red env d e₀) o → Red env d e₀ e'
  | 0, _, _, _, h, _, _ => by
    simp [whnfLoop, throw, throwThe, MonadExceptOf.throw] at h
  | n + 1, _, _, _, h, he, ho =>
    whnfStep_bridge hwc hw hd hi (whnfLoop_bridge hwc hw hd hi n) h he ho

/-- **`whnf` at `fuel + 1`**: the loop at its budget, from the input with no origin. -/
theorem whnf_bridge_succ (hwc : WhnfCoreBridge μ eager env fuel) (hw : WhnfBridge μ eager env fuel)
    (hd : DefEqBridge μ eager env fuel) (hi : InferBridge μ eager env fuel) :
    WhnfBridge μ eager env (fuel + 1) := by
  intro d e e' h
  rw [whnf_succ] at h
  exact whnfLoop_bridge hwc hw hd hi _ h .refl (OriginP.none _)

end ConLeche.Rules
