module

public import ConLeche.Kernel.Core
public import ConLeche.Verify.Inductives.NestedRead

public section

/-!
# Environment well-formedness

`EnvWF` collects the syntactic facts the checker establishes for every
accepted constant — closed, level parameters within the declared list,
referenced constants resolving — as an invariant of the environment.  The
delta-unfolding and monotonicity lemmas need it.
-/

namespace ConLeche

/-- Unfold a successful projection-table lookup to the stored table:
the structure's table is stored, the index is in range, and the entry
is the table's view at it (task #175 S1). -/
theorem Env.findProj?_some {env : Env} {T : Name} {i : Nat}
    {entry : ProjEntry} (h : env.findProj? T i = some entry) :
    ∃ tbl : ProjTable, env.findTable? T = some tbl ∧
      i < tbl.numFields ∧ entry = tbl.entry i := by
  unfold Env.findProj? at h
  split at h
  next tbl heq =>
    split at h
    · next hi => exact ⟨tbl, heq, hi, (Option.some.inj h).symm⟩
    · exact nomatch h
  next => exact nomatch h

/-- The lookup at a stored table, in range. -/
theorem Env.findProj?_of_table {env : Env} {T : Name} {tbl : ProjTable}
    (h : env.findTable? T = some tbl) {i : Nat}
    (hi : i < tbl.numFields) : env.findProj? T i = some (tbl.entry i) := by
  unfold Env.findProj?
  rw [h]
  exact ite_eq_left hi

/-- A stored table is a member of the table component, under its
structure's name, and the structure is stored. -/
theorem Env.findTable?_mem {env : Env} {T : Name} {tbl : ProjTable}
    (h : env.findTable? T = some tbl) :
    tbl ∈ env.tables ∧ tbl.structName = T ∧ (env.find? T).isSome = true := by
  unfold Env.findTable? at h
  split at h
  · next hT =>
    exact ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h, hT⟩
  · exact nomatch h

/-- The table lookup at a stored structure is the table component's. -/
theorem Env.findTable?_of_isSome {env : Env} {T : Name} (hT : (env.find? T).isSome = true) :
    env.findTable? T = env.tables.find? (·.structName == T) := by
  unfold Env.findTable?
  rw [ite_eq_left hT]

/-- A table install leaves the constant lookups alone. -/
@[simp] theorem Env.find?_pushTable (env : Env) (t : ProjTable) :
    Env.find? ⟨env.consts, t :: env.tables, env.rules⟩ = env.find? := rfl

/-- A table install answers its structure's name (where it is stored),
and leaves every other table lookup alone. -/
theorem Env.findTable?_pushTable (env : Env) (t : ProjTable) (T : Name) :
    Env.findTable? ⟨env.consts, t :: env.tables, env.rules⟩ T =
      if t.structName = T ∧ (env.find? T).isSome = true then some t
      else env.findTable? T := by
  unfold Env.findTable?
  show (if (env.find? T).isSome = true then (t :: env.tables).find? _ else none) = _
  rw [List.find?_cons]
  by_cases hs : (env.find? T).isSome = true
  · by_cases hT : t.structName = T
    · simp [hT, hs]
    · have hb : (t.structName == T) = false := by simpa using hT
      simp only [hs, hb, hT, false_and, ↓reduceIte]
  · simp [hs]

@[simp] theorem ProjTable.entry_levelParams (tbl : ProjTable) (i : Nat) :
    (tbl.entry i).levelParams = tbl.levelParams := rfl
@[simp] theorem ProjTable.entry_numParams (tbl : ProjTable) (i : Nat) :
    (tbl.entry i).numParams = tbl.numParams := rfl
@[simp] theorem ProjTable.entry_body (tbl : ProjTable) (i : Nat) :
    (tbl.entry i).body = tbl.bodies.getD i default := rfl
/-- A `stripPis` at a larger count strips at a smaller one. -/
theorem stripPis_isSome_of_le :
    ∀ {k n : Nat} {e : Expr}, k ≤ n → (e.stripPis n).isSome = true →
      (e.stripPis k).isSome = true := by
  intro k
  induction k with
  | zero => intro n e _ _; simp [Expr.stripPis]
  | succ k ih =>
    intro n e hle h
    match n, hle with
    | n + 1, hle =>
      match e, h with
      | .forallE d bo, h =>
        simp only [Expr.stripPis, Option.isSome_map] at h ⊢
        exact ih (by omega) h

/-- Syntactic well-formedness of one stored constant w.r.t. `env`. -/
@[expose] def ConstWF (env : Env) (c : ConstantInfo) : Prop :=
  c.toConstantVal.type.hasFvar = false ∧
  c.toConstantVal.type.allLevelParamsDefined c.toConstantVal.levelParams = true ∧
  c.toConstantVal.type.constsResolve env = true ∧
  c.toConstantVal.type.looseBVarsBounded 0 = true ∧
  (∀ cv value hint, c = .defnInfo cv value hint →
    value.hasFvar = false ∧
    value.allLevelParamsDefined cv.levelParams = true ∧
    value.constsResolve env = true ∧
    value.looseBVarsBounded 0 = true) ∧
  (∀ cv mI rP isK rules, c = .recInfo cv mI rP isK rules →
    ∀ r, r ∈ rules →
      (RecRule.rhs r).hasFvar = false ∧
      (RecRule.rhs r).allLevelParamsDefined cv.levelParams = true ∧
      (RecRule.rhs r).constsResolve env = true ∧
      (RecRule.rhs r).looseBVarsBounded 0 = true ∧
      -- a nested rule's datum reads off the recursor type
      -- (`NestedRead`: the pins are well formed in the rule-prefix
      -- context, and the major's domain applies the class's inductive
      -- at the levels to the pins' liftings past the index binders,
      -- followed by the index variables; what the generated stage
      -- stores, `genStage_nestedRead`)
      ∀ lvls pins, RecRule.fire r = .nested lvls pins →
        NestedRead (·.constsResolve env) cv.levelParams cv.type mI rP pins.length lvls pins)
  -- (a theorem's stored value carries NO clause: a theorem is opaque
  -- to reduction and stored by its statement — the value is the
  -- record's own, unread by the kernel and by the invariant)

/-- **Syntactic well-formedness of one stored projection table** w.r.t.
`env` (task #175 S1; task #362 for the first clause): its structure is
a stored constant, and its bodies are closed with respect to free
variables, level parameters within the structure's list, resolving,
and scoped at the parameters and the subject; there are exactly
`numFields` of them. -/
@[expose] def TableWF (env : Env) (tbl : ProjTable) : Prop :=
  (env.find? tbl.structName).isSome = true ∧
  tbl.bodies.size = tbl.numFields ∧
  ∀ (i : Nat) (b : Expr), tbl.bodies[i]? = some b →
    b.hasFvar = false ∧
    b.allLevelParamsDefined tbl.levelParams = true ∧
    b.constsResolve env = true ∧
    b.looseBVarsBounded (tbl.numParams + 1) = true

/-- `c` is stored as a definition. -/
@[expose] def isDefinitionAt (env : Env) (c : Name) : Bool :=
  match env.find? c with
  | some (.defnInfo _ _ _) => true
  | _ => false

/-- **A stored certified operation's name holds a definition.**  The fast path fires by name; every
other kind of declaration is refused at such a name (`checkConstantVal`, `reservedRecName`). -/
@[expose] def OpDefn (env : Env) : Prop :=
  ∀ c, natOpName c = true → (env.find? c).isSome = true → isDefinitionAt env c = true

/-- A certified operation's name is not a pinned basis name. -/
theorem natOpName_not_reserved {c : Name} (h : natOpName c = true) :
    reservedBasisNames.contains c = false := by
  simp only [natOpName, Bool.or_eq_true, List.contains_iff_mem] at h
  rcases h with h | h
  · exact (by decide : ∀ c ∈ natOpNames, reservedBasisNames.contains c = false) c h
  · exact (by decide : ∀ c ∈ natDivModNames, reservedBasisNames.contains c = false) c h

/-- `OpDefn` across a change that keeps which names are stored and every definition. -/
theorem OpDefn.of_same {env₀ env₃ : Env} (h : OpDefn env₀)
    (hs : ∀ n, (env₃.find? n).isSome = true → (env₀.find? n).isSome = true)
    (hd : ∀ n cv v hh, env₀.find? n = some (.defnInfo cv v hh) →
      env₃.find? n = some (.defnInfo cv v hh)) : OpDefn env₃ := by
  intro c hn hc
  have h₀ := h c hn (hs c hc)
  unfold isDefinitionAt at h₀ ⊢
  cases hx : env₀.find? c with
  | none => rw [hx] at h₀; exact nomatch h₀
  | some ci =>
    rw [hx] at h₀
    cases ci with
    | defnInfo cv v hh => rw [hd c cv v hh hx]
    | _ => exact nomatch h₀

/-- **What a stored family's recorded sort fact says** (task #573): a family
recorded as never zero (`IndCaps.neverZero`) has a type ending in a sort
whose zero-ness datum is `never`.  The ι step's case split reads it in place
of the walk to the family's sort. -/
@[expose] def IndWF (c : ConstantInfo) : Prop :=
  ∀ cv caps, c = .indInfo cv caps → caps.neverZero = true → (formerZ cv).isNever = true

/-- A constant that is no family has no sort fact to keep. -/
theorem IndWF.of_not_ind {c : ConstantInfo} (h : ∀ cv caps, c ≠ .indInfo cv caps) : IndWF c :=
  fun cv caps heq => absurd heq (h cv caps)

/-- **What a stored constructor's family name says** (task #573): a constructor record's
`induct` is the head constant of its type's result.  The readers of the family (the ι case
split, the rescues, η) look it up by this name in place of the walk to the head. -/
@[expose] def CtorWF (c : ConstantInfo) : Prop :=
  ∀ cv nP nF T, c = .ctorInfo cv nP nF T → ∃ us, cv.type.piResult.getAppFn = .const T us

/-- A constant that is no constructor has no family name to keep. -/
theorem CtorWF.of_not_ctor {c : ConstantInfo} (h : ∀ cv nP nF T, c ≠ .ctorInfo cv nP nF T) :
    CtorWF c :=
  fun cv nP nF T heq => absurd heq (h cv nP nF T)

/-- **A constructor installed at the family its type concludes in.** -/
theorem CtorWF.of_head {cv : ConstantVal} {nP nF : Nat} {T : Name} {us : List Level}
    (h : cv.type.piResult.getAppFn = .const T us) : CtorWF (.ctorInfo cv nP nF T) := by
  intro cv' nP' nF' T' heq
  injection heq with h1 _ _ h4
  subst h1 h4
  exact ⟨us, h⟩

/-- **What a stored recursor's rules bind** (task #585): at a recursor with rules, the rule
prefix is a prefix of the major's telescope (`rulePrefix ≤ majorIdx`), and each rule's
right-hand side has `rulePrefix + nfields` manifest λs, the ones the ι step peels (`lamBody`,
lean4 PR #10565's shape) — so the reduct substitutes every bound variable of the peeled body.  A property of
the record alone, as `CtorWF` is; the install establishes it syntactically (the parse sums the
counts, `ruleBinds` counts a stored rule's λs, the generated rules are built over the prefix and
the fields, the pins are evaluated). -/
@[expose] def RuleWF (c : ConstantInfo) : Prop :=
  ∀ cv mI rP isK rules, c = .recInfo cv mI rP isK rules → ∀ r ∈ rules,
    rP ≤ mI ∧ (r.rhs.stripLams (rP + r.nfields)).isSome = true

/-- A constant that is no recursor has no rules to keep. -/
theorem RuleWF.of_not_rec {c : ConstantInfo}
    (h : ∀ cv mI rP isK rules, c ≠ .recInfo cv mI rP isK rules) : RuleWF c :=
  fun cv mI rP isK rules heq => absurd heq (h cv mI rP isK rules)

/-- A recursor's rules bind its rule prefix and their fields (`RuleWF`), as a test (true at any
other kind of constant). -/
@[expose] def recRulesBindB : ConstantInfo → Bool
  | .recInfo _ mI rP _ rules => rules.all fun r =>
    decide (rP ≤ mI) && (r.rhs.stripLams (rP + r.nfields)).isSome
  | _ => true

/-- **The test, read**: the record's `RuleWF`. -/
theorem ruleWF_of_recRulesBindB {c : ConstantInfo} (h : recRulesBindB c = true) : RuleWF c := by
  intro cv mI rP isK rules heq r hr
  subst heq
  have hg := (List.all_eq_true.mp h) r hr
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hg
  exact hg

/-- **The cuts a family's telescope is read at** (`Env.famBelow`), from the constants `L`: `L`
itself, and below the block of every family stored in a reached cut. -/
inductive Env.Reach (L : List ConstantInfo) : List ConstantInfo → Prop
  | top : Env.Reach L L
  | step {cs : List ConstantInfo} {n : Name} {cv : ConstantVal} {caps : IndCaps} :
      Env.Reach L cs → cs.find? (·.name == n) = some (.indInfo cv caps) →
      Env.Reach L ((Env.suffixAfter cs n).drop caps.blockPos)

/-- **The rule tables an environment recorded**: each at a number of constants it has reached,
and the one in force at its own number the active one (`RuleTable.cut`). -/
structure RulesWF (env : Env) : Prop where
  le : ∀ s ∈ env.rules.snaps, s.1 ≤ env.consts.length
  active : activeAtS env.rules.snaps env.consts.length = env.rules.active

/-- A list whose every entry passes finds its head. -/
theorem find?_of_all {α : Type} {p : α → Bool} :
    ∀ {S : List α}, (∀ s ∈ S, p s = true) → S.find? p = S.head?
  | [], _ => rfl
  | a :: S, h => by simp [h a List.mem_cons_self]

/-- Past every recorded number, the table in force is the newest. -/
theorem activeAtS_of_le {S : List (Nat × List (Name × Name))} {k k' : Nat}
    (h : ∀ s ∈ S, s.1 ≤ k) (hk : k ≤ k') : activeAtS S k' = activeAtS S k := by
  unfold activeAtS
  rw [find?_of_all (fun s hs => by simpa using Nat.le_trans (h s hs) hk),
    find?_of_all (fun s hs => by simpa using h s hs)]

/-- Tables recorded past `k` leave the one in force at `k` alone. -/
theorem activeAtS_append_gt {N S : List (Nat × List (Name × Name))} {k : Nat}
    (h : ∀ s ∈ N, k < s.1) : activeAtS (N ++ S) k = activeAtS S k := by
  unfold activeAtS
  rw [List.find?_append, List.find?_eq_none.mpr (fun s hs => by simpa using h s hs), Option.none_or]

/-- The cut at `k` reads the tables recorded up to `k` alone. -/
theorem RuleTable.cut_append_gt {rt rt' : RuleTable} {N : List (Nat × List (Name × Name))} {k : Nat}
    (hs : rt'.snaps = N ++ rt.snaps) (h : ∀ s ∈ N, k < s.1) : rt'.cut k = rt.cut k := by
  unfold RuleTable.cut
  rw [hs, activeAtS_append_gt h, List.filter_append,
    List.filter_eq_nil_iff.mpr (fun s hs => by simpa using h s hs), List.nil_append]

/-- The empty environment records no table. -/
theorem RulesWF.empty : RulesWF Env.empty := ⟨fun _ h => (nomatch h), rfl⟩

/-- More constants under the same rules keep `RulesWF`. -/
theorem RulesWF.mono {env env' : Env} (h : RulesWF env) (hR : env'.rules = env.rules)
    (hl : env.consts.length ≤ env'.consts.length) : RulesWF env' := by
  refine ⟨fun s hs => Nat.le_trans (h.le s (hR ▸ hs)) hl, ?_⟩
  rw [hR, activeAtS_of_le h.le hl, h.active]

/-- A record's rule effect keeps `RulesWF`: a `useRules` records its table at the current number. -/
theorem RulesWF.stepRules {env : Env} (h : RulesWF env) (d : Declaration) :
    RulesWF (env.stepRules d) := by
  cases d with
  | useRules S =>
    refine ⟨fun s hs => ?_, ?_⟩
    · rcases List.mem_cons.mp hs with rfl | hs
      · exact Nat.le_refl _
      · exact h.le s hs
    · simp [Env.stepRules, RuleTable.step, activeAtS]
  | rewriteDecl t c p => exact ⟨h.le, h.active⟩
  | _ => exact h

/-- The recorded tables up to `k` find the one in force at `k` as all of them do. -/
theorem activeAtS_filter (S : List (Nat × List (Name × Name))) (k : Nat) :
    activeAtS (S.filter (fun s => decide (s.1 ≤ k))) k = activeAtS S k := by
  unfold activeAtS
  induction S with
  | nil => rfl
  | cons a S ih =>
    by_cases ha : a.1 ≤ k
    · simp [ha]
    · rw [List.filter_cons_of_neg (by simpa using ha), ih, List.find?_cons_of_neg (by simpa using ha)]

/-- Every cut keeps `RulesWF`: it records the tables up to its own number. -/
theorem RulesWF.cutAt (env : Env) (cs : List ConstantInfo) : RulesWF (env.cutAt cs) :=
  ⟨fun s hs => by simpa [Env.cutAt, RuleTable.cut] using (List.mem_filter.mp hs).2, activeAtS_filter _ _⟩

/-- Every stored constant and every stored table is syntactically
well-formed, every stored family's sort fact holds, and every stored constructor's family
name is its type's. -/
structure EnvWF (env : Env) : Prop where
  consts : ∀ c ∈ env.consts, ConstWF env c
  /-- a constant at a literal's name has the shape a literal's meaning reads -/
  shapes : ∀ c ∈ env.consts, litShapeOk c = true
  tables : ∀ t ∈ env.tables, TableWF env t
  /-- a stored family's sort fact -/
  inds : ∀ c ∈ env.consts, IndWF c
  /-- a stored constructor's family name -/
  ctors : ∀ c ∈ env.consts, CtorWF c
  /-- a stored recursor's rules' binders -/
  rules : ∀ c ∈ env.consts, RuleWF c
  /-- every cut a family's telescope is read at holds what its constants refer to -/
  below : ∀ cs, Env.Reach env.consts cs → ∀ c ∈ cs, ConstWF ⟨cs, [], {}⟩ c
  /-- the rule tables recorded, the active one in force -/
  ruleSnaps : RulesWF env

/-- The table of a stored structure, off `EnvWF`. -/
theorem EnvWF.table {env : Env} (henv : EnvWF env) {T : Name} {tbl : ProjTable}
    (h : env.findTable? T = some tbl) : TableWF env tbl :=
  henv.tables tbl (Env.findTable?_mem h).1



/-- **The three `Nat` names hold an inductive and two constructors**, where stored: what a
declaration's check cannot show (`litShapeOk` reads a type), and the pinned `Nat` block's
(`basisNamesOk`) does. -/
@[expose] def NatKinds (env : Env) : Prop :=
  (∀ c, env.find? natName = some c → ∃ cv caps, c = .indInfo cv caps) ∧
  (∀ c, env.find? natZeroName = some c → ∃ cv nP nF T, c = .ctorInfo cv nP nF T) ∧
  (∀ c, env.find? natSuccName = some c → ∃ cv nP nF T, c = .ctorInfo cv nP nF T)

/-- **A constant value's shape at a literal's name**, whatever kind of constant carries it. -/
@[expose] def LitShapeAt (cv : ConstantVal) : Prop :=
  ∀ c : ConstantInfo, c.toConstantVal = cv → litShapeOk c = true

/-- A constant's shape reads only its name, level parameters and type. -/
theorem litShapeAt_of_check {cv : ConstantVal}
    (h : litShapeOk (.axiomInfo cv) = true) : LitShapeAt cv := by
  intro c hc
  subst hc
  have hn : (ConstantInfo.axiomInfo c.toConstantVal).name = c.name := rfl
  unfold litShapeOk at h ⊢
  rw [hn] at h
  cases c <;> exact h

/-- A name off the ten has no shape to keep. -/
theorem litShapeOk_of_not_lit {c : ConstantInfo} (hn : litGuardNames.contains c.name = false) :
    litShapeOk c = true := by
  simp only [litGuardNames, List.contains_cons, List.contains_nil, Bool.or_false, Bool.or_eq_false_iff,
    beq_eq_false_iff_ne, ne_eq] at hn
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀⟩ := hn
  unfold litShapeOk
  simp only [h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, ↓reduceIte]

/-- A recursor's name is off the ten, so it has no shape to keep. -/
theorem litShapeAt_of_reservedRec {cv : ConstantVal} (h : reservedRecName cv.name = false) :
    LitShapeAt cv := by
  intro c hc
  subst hc
  refine litShapeOk_of_not_lit ?_
  simp only [reservedRecName, Bool.or_eq_false_iff] at h
  exact h.1.1.1.1.1

/-- `find?` on a cons. -/
theorem Env.find?_cons {c : ConstantInfo} {cs : List ConstantInfo} {ts : List ProjTable}
    {rs : ConLeche.RuleTable} {n : Name} :
    Env.find? ⟨c :: cs, ts, rs⟩ n = if c.name = n then some c else Env.find? ⟨cs, ts, rs⟩ n := by
  simp only [Env.find?, List.find?]
  split
  · next h => simp_all
  · next h => simp_all

/-- A cons finds its own head. -/
theorem Env.find?_cons_self (c : ConstantInfo) (env : Env) :
    Env.find? ⟨c :: env.consts, env.tables, env.rules⟩ c.name = some c := by
  rw [Env.find?_cons, ite_eq_left rfl]

/-- A cons of a *fresh* head does not find anything new. -/
theorem Env.find?_cons_of_fresh {c : ConstantInfo} {env : Env}
    {n : Name} {ci : ConstantInfo} (hfresh : env.find? c.name = none)
    (h : env.find? n = some ci) :
    Env.find? ⟨c :: env.consts, env.tables, env.rules⟩ n = some ci := by
  rw [Env.find?_cons]
  split
  · next heq => rw [heq, h] at hfresh; exact nomatch hfresh
  · exact h

/-- Extending the environment with a fresh constant does not change
successful lookups. -/
theorem Env.find?_cons_of_isSome {c : ConstantInfo} {env : Env} {n : Name}
    (hfresh : env.find? c.name = none) (h : (env.find? n).isSome = true) :
    Env.find? ⟨c :: env.consts, env.tables, env.rules⟩ n = env.find? n := by
  rw [Env.find?_cons]
  split
  · next heq => rw [← heq] at h; rw [hfresh] at h; simp at h
  · rfl

/-- **A push of a fresh constant leaves the table lookups alone**
(task #362): a stored table's structure is stored (`TableWF`), so no
table waits for the fresh name. -/
theorem EnvWF.findTable?_cons {env : Env} (henv : EnvWF env) {c : ConstantInfo}
    (hfresh : env.find? c.name = none) (T : Name) :
    Env.findTable? ⟨c :: env.consts, env.tables, env.rules⟩ T = env.findTable? T := by
  unfold Env.findTable?
  rw [Env.find?_cons]
  by_cases hT : c.name = T
  · subst hT
    rw [ite_eq_left rfl, hfresh]
    simp only [Option.isSome_some, ↓reduceIte, Option.isSome_none, Bool.false_eq_true]
    rw [List.find?_eq_none]
    intro t ht hq
    have hn : t.structName = c.name := by simpa using hq
    have := (henv.tables t ht).1
    rw [hn, hfresh] at this
    exact absurd this (by simp)
  · rw [ite_eq_right hT]

theorem EnvWF.findProj?_cons {env : Env} (henv : EnvWF env) {c : ConstantInfo}
    (hfresh : env.find? c.name = none) (T : Name) (i : Nat) :
    Env.findProj? ⟨c :: env.consts, env.tables, env.rules⟩ T i = env.findProj? T i := by
  unfold Env.findProj?
  rw [henv.findTable?_cons hfresh]

/-- **An extension that keeps the tables keeps the table lookups**
(task #362): a stored name stays stored, and a table waits for no name
the prefix lacks, since every stored table's structure is stored. -/
theorem EnvWF.findTable?_extend {env₀ env : Env} (henv : EnvWF env₀)
    (hF : ∀ n, (env₀.find? n).isSome = true → (env.find? n).isSome = true)
    (hT : env.tables = env₀.tables) (T : Name) :
    env.findTable? T = env₀.findTable? T := by
  unfold Env.findTable?
  by_cases h0 : (env₀.find? T).isSome = true
  · rw [ite_eq_left (hF T h0), ite_eq_left h0, hT]
  · rw [ite_eq_right h0]
    split
    · rw [hT, List.find?_eq_none]
      intro t ht hq
      have hn : t.structName = T := by simpa using hq
      have := (henv.tables t ht).1
      rw [hn] at this
      exact h0 this
    · rfl

theorem EnvWF.findProj?_extend {env₀ env : Env} (henv : EnvWF env₀)
    (hF : ∀ n, (env₀.find? n).isSome = true → (env.find? n).isSome = true)
    (hT : env.tables = env₀.tables) (T : Name) (i : Nat) :
    env.findProj? T i = env₀.findProj? T i := by
  unfold Env.findProj?
  rw [henv.findTable?_extend hF hT]

/-- Resolution depends on the environment only through which names it
finds: every name found in `env` being found in `env'` carries
resolution over. -/
theorem Expr.constsResolve_of_find {env env' : Env}
    (hf : ∀ n, (env.find? n).isSome = true → (env'.find? n).isSome = true) :
    ∀ {e : Expr}, e.constsResolve env = true → e.constsResolve env' = true := by
  intro e
  induction e with
  | bvar i => intro h; simp [Expr.constsResolve]
  | sort u => intro h; simp [Expr.constsResolve]
  | const n us =>
    intro h
    simp only [Expr.constsResolve] at h ⊢
    exact hf _ h
  | lit l =>
    cases l with
    | natVal n =>
      intro h
      simp only [Expr.constsResolve, Bool.and_eq_true] at h ⊢
      exact ⟨⟨hf _ h.1.1, hf _ h.1.2⟩, hf _ h.2⟩
    | strVal s =>
      intro h
      simp only [Expr.constsResolve, Bool.and_eq_true] at h ⊢
      exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨hf _ h.1.1.1.1.1.1.1.1.1, hf _ h.1.1.1.1.1.1.1.1.2⟩,
        hf _ h.1.1.1.1.1.1.1.2⟩, hf _ h.1.1.1.1.1.1.2⟩,
        hf _ h.1.1.1.1.1.2⟩, hf _ h.1.1.1.1.2⟩, hf _ h.1.1.1.2⟩,
        hf _ h.1.1.2⟩, hf _ h.1.2⟩, hf _ h.2⟩
  | fvar idx ty ih =>
    intro h
    simp only [Expr.constsResolve] at h ⊢
    exact ih h
  | app f a ihf iha =>
    intro h
    simp only [Expr.constsResolve, Bool.and_eq_true] at h ⊢
    exact ⟨ihf h.1, iha h.2⟩
  | lam ty body ihty ihbody =>
    intro h
    simp only [Expr.constsResolve, Bool.and_eq_true] at h ⊢
    exact ⟨ihty h.1, ihbody h.2⟩
  | forallE ty body ihty ihbody =>
    intro h
    simp only [Expr.constsResolve, Bool.and_eq_true] at h ⊢
    exact ⟨ihty h.1, ihbody h.2⟩
  | letE ty val body ihty ihval ihbody =>
    intro h
    simp only [Expr.constsResolve, Bool.and_eq_true] at h ⊢
    exact ⟨⟨ihty h.1.1, ihval h.1.2⟩, ihbody h.2⟩
  | proj s i e ih =>
    intro h
    simp only [Expr.constsResolve, Bool.and_eq_true] at h ⊢
    exact ⟨hf _ h.1, ih h.2⟩

/-- Resolution is monotone under environment extension. -/
theorem Expr.constsResolve_mono {c : ConstantInfo} {env : Env} :
    ∀ {e : Expr}, e.constsResolve env = true →
      e.constsResolve ⟨c :: env.consts, env.tables, env.rules⟩ = true :=
  Expr.constsResolve_of_find fun n h => by
    rw [Env.find?_cons]
    split <;> simp_all

/-- Resolution survives binder opening. -/
theorem Expr.constsResolve_instantiate1 {env : Env} {d : Nat} {ty : Expr}
    (hty : ty.constsResolve env = true) :
    ∀ {e : Expr} (k : Nat), e.constsResolve env = true →
      (e.instantiate1 (.fvar d ty) k).constsResolve env = true := by
  intro e
  induction e <;> intro k h <;> simp_all [Expr.instantiate1, Expr.constsResolve]
  case bvar i =>
    split
    · simpa [Expr.constsResolve] using hty
    · split <;> simp [Expr.constsResolve]

/-- Level instantiation does not change which constants occur. -/
theorem Expr.constsResolve_instantiateLevelParams {env : Env} (ks : List Name)
    (us : List Level) :
    ∀ {e : Expr}, (e.instantiateLevelParams ks us).constsResolve env = e.constsResolve env := by
  intro e
  induction e <;> simp_all [Expr.instantiateLevelParams, Expr.constsResolve]

/-- Resolution survives `piResult` (peeling leading `∀`s keeps every
constant the residual mentions — task #342 L10, the `RecRuleExtra`
transport's clause (S)). -/
theorem Expr.constsResolve_piResult {env : Env} :
    ∀ {e : Expr}, e.constsResolve env = true → e.piResult.constsResolve env = true
  | .forallE _ b, h => by
      have hb : b.constsResolve env = true := by
        simp only [Expr.constsResolve, Bool.and_eq_true] at h
        exact h.2
      exact Expr.constsResolve_piResult (e := b) hb
  | .bvar _, h | .sort _, h | .lit _, h | .const _ _, h | .fvar _ _, h
  | .app _ _, h | .lam _ _, h | .letE _ _ _, h | .proj _ _ _, h => by
      simpa [Expr.piResult] using h

/-- Resolution survives `getAppFn` (peeling an application spine's
head keeps every constant it mentions). -/
theorem Expr.constsResolve_getAppFn {env : Env} :
    ∀ {e : Expr}, e.constsResolve env = true → e.getAppFn.constsResolve env = true
  | .app f _, h => by
      have hf : f.constsResolve env = true := by
        simp only [Expr.constsResolve, Bool.and_eq_true] at h
        exact h.1
      exact Expr.constsResolve_getAppFn (e := f) hf
  | .bvar _, h | .sort _, h | .lit _, h | .const _ _, h | .fvar _ _, h
  | .lam _ _, h | .forallE _ _, h | .letE _ _ _, h | .proj _ _ _, h => by
      simpa [Expr.getAppFn] using h

/-- **A resolving expression's `piResult`'s head constant is stored**
(task #342 L10): the constructor's stored type resolves (`ConstWF`),
so the family name heading its result — the one `iotaCtorNeverProp`
looks up — is stored too, hence never the fresh name of a cons. -/
theorem Expr.find?_isSome_of_piResult_getAppFn_const {env : Env} {e : Expr}
    {T : Name} {us : List Level} (hres : e.constsResolve env = true)
    (heq : e.piResult.getAppFn = .const T us) : (env.find? T).isSome = true := by
  have h2 := Expr.constsResolve_getAppFn (Expr.constsResolve_piResult hres)
  rw [heq] at h2
  simpa [Expr.constsResolve] using h2

/-- A constant push keeps a table well formed (its structure stays
found, its bodies keep resolving). -/
theorem TableWF.cons {c : ConstantInfo} {env : Env} {t : ProjTable} (h : TableWF env t) :
    TableWF ⟨c :: env.consts, env.tables, env.rules⟩ t := by
  obtain ⟨h0, h1, h2⟩ := h
  refine ⟨?_, h1, fun i b hb => ?_⟩
  · rw [Env.find?_cons]; split <;> simp_all
  · obtain ⟨g1, g2, g3, g4⟩ := h2 i b hb
    exact ⟨g1, g2, Expr.constsResolve_mono g3, g4⟩

/-- Resolution reads the environment only through `find?`. -/
theorem Expr.constsResolve_eq_of_find {env env' : Env} (h : env'.find? = env.find?)
    (e : Expr) : e.constsResolve env' = e.constsResolve env := by
  cases h₁ : e.constsResolve env
  · cases h₂ : e.constsResolve env'
    · rfl
    · have := Expr.constsResolve_of_find (fun n hn => by rw [← h]; exact hn) h₂
      rw [h₁] at this; exact absurd this Bool.false_ne_true
  · exact Expr.constsResolve_of_find (fun n hn => by rw [h]; exact hn) h₁

/-- A constant's well-formedness reads the environment only through
`find?`. -/
theorem ConstWF.of_find {env env' : Env} (h : env'.find? = env.find?) {c : ConstantInfo}
    (hc : ConstWF env c) : ConstWF env' c := by
  unfold ConstWF at hc ⊢
  simp only [Expr.constsResolve_eq_of_find h]
  exact hc

/-! ## The cuts a family's telescope is read at -/

/-- The first entry of a name heading the constants is cut off with it alone. -/
theorem Env.suffixAfter_cons (c : ConstantInfo) (cs : List ConstantInfo) (n : Name) :
    Env.suffixAfter (c :: cs) n = if c.name = n then cs else Env.suffixAfter cs n := by
  unfold Env.suffixAfter
  by_cases h : c.name = n
  · simp [h]
  · simp [h]

/-- A cut is a suffix of the constants. -/
theorem Env.suffixAfter_suffix (n : Name) :
    ∀ cs : List ConstantInfo, Env.suffixAfter cs n <:+ cs
  | [] => by simp [Env.suffixAfter]
  | c :: cs => by
    rw [Env.suffixAfter_cons]
    split
    · exact List.suffix_cons c cs
    · exact (Env.suffixAfter_suffix n cs).trans (List.suffix_cons c cs)

/-- A reached cut is a suffix of the constants it starts from. -/
theorem Env.Reach.suffix {L : List ConstantInfo} :
    ∀ {cs : List ConstantInfo}, Env.Reach L cs → cs <:+ L
  | _, .top => List.suffix_refl _
  | _, .step h _ => ((List.drop_suffix _ _).trans (Env.suffixAfter_suffix _ _)).trans h.suffix

/-- A cut reached from a reached cut is reached. -/
theorem Env.Reach.trans {L cs : List ConstantInfo} (h : Env.Reach L cs) :
    ∀ {cs' : List ConstantInfo}, Env.Reach cs cs' → Env.Reach L cs'
  | _, .top => h
  | _, .step h' hf => .step (h.trans h') hf

/-- **The cuts after a constant's push**: the new constants, or a cut of the old ones, given that
a family pushed reads below its block at a cut of the old ones. -/
theorem Env.Reach.of_cons {L : List ConstantInfo} {c : ConstantInfo}
    (hb : ∀ cv caps, c = .indInfo cv caps → Env.Reach L (L.drop caps.blockPos)) :
    ∀ {cs : List ConstantInfo}, Env.Reach (c :: L) cs → cs = c :: L ∨ Env.Reach L cs
  | _, .top => .inl rfl
  | _, .step (cs := cs) (n := n) h hf => by
    rcases Env.Reach.of_cons hb h with rfl | h'
    · right
      rw [Env.suffixAfter_cons]
      rw [List.find?_cons] at hf
      by_cases hn : c.name = n
      · rw [ite_eq_left hn]
        simp only [hn, beq_self_eq_true] at hf
        exact hb _ _ (Option.some.inj hf)
      · rw [ite_eq_right hn]
        have hn' : (c.name == n) = false := by simpa using hn
        rw [hn'] at hf
        exact .step .top hf
    · exact .inr (.step h' hf)

/-- **The cuts after pushing constants none of which is a family**: the new constants, or a cut
of the old ones. -/
theorem Env.Reach.of_append {new L : List ConstantInfo}
    (hnew : ∀ c ∈ new, ∀ cv caps, c ≠ .indInfo cv caps) :
    ∀ {cs : List ConstantInfo}, Env.Reach (new ++ L) cs → cs = new ++ L ∨ Env.Reach L cs
  | _, .top => .inl rfl
  | _, .step (n := n) h hf => by
    rcases Env.Reach.of_append hnew h with rfl | h'
    · right
      rw [List.find?_append] at hf
      cases hn : new.find? (·.name == n) with
      | some c =>
        rw [hn] at hf
        exact absurd (Option.some.inj hf) (hnew c (List.mem_of_find?_eq_some hn) _ _)
      | none =>
        rw [hn] at hf
        have hnot : ∀ c ∈ new, c.name ≠ n := fun c hc he => by
          have := List.find?_eq_none.mp hn c hc
          simp [he] at this
        have hsa : Env.suffixAfter (new ++ L) n = Env.suffixAfter L n := by
          clear hn hf h
          induction new with
          | nil => rfl
          | cons c new ih =>
            rw [List.cons_append, Env.suffixAfter_cons, ite_eq_right (hnot c List.mem_cons_self)]
            exact ih (fun c hc => hnew c (List.mem_cons_of_mem _ hc))
              (fun c hc => hnot c (List.mem_cons_of_mem _ hc))
        rw [hsa]
        exact .step .top (by simpa using hf)
    · exact .inr (.step h' hf)

/-- A table answered at a cut is a stored one, live there. -/
theorem Env.mem_liveTables {cs : List ConstantInfo} :
    ∀ {ts : List ProjTable} {t : ProjTable}, t ∈ Env.liveTables cs ts →
      t ∈ ts ∧ Env.tableOkAt cs t = true
  | [], _, h => by simp [Env.liveTables] at h
  | t' :: ts, t, h => by
    simp only [Env.liveTables] at h
    have hrest : t ∈ (Env.liveTables cs ts).filter (·.structName != t'.structName) →
        t ∈ t' :: ts ∧ Env.tableOkAt cs t = true := fun hm => by
      obtain ⟨hm, -⟩ := List.mem_filter.mp hm
      obtain ⟨h1, h2⟩ := Env.mem_liveTables hm
      exact ⟨List.mem_cons_of_mem _ h1, h2⟩
    split at h
    · rcases List.mem_cons.mp h with rfl | hm
      · exact ⟨List.mem_cons_self, by assumption⟩
      · exact hrest hm
    · exact hrest h

/-- Extending with a fresh, well-formed constant preserves `EnvWF`.  A family pushed reads below
its block at a cut of the old constants (`hb`). -/
theorem EnvWF.cons {c : ConstantInfo} {env : Env} (hs : litShapeOk c = true)
    (henv : EnvWF env)
    (hc : ConstWF ⟨c :: env.consts, env.tables, env.rules⟩ c)
    (hi : IndWF c := by exact IndWF.of_not_ind (fun _ _ heq => nomatch heq))
    (hk : CtorWF c := by exact CtorWF.of_not_ctor (fun _ _ _ _ heq => nomatch heq))
    (hr : RuleWF c := by exact RuleWF.of_not_rec (fun _ _ _ _ _ heq => nomatch heq))
    (hb : ∀ cv caps, c = .indInfo cv caps → Env.Reach env.consts (env.consts.drop caps.blockPos) := by
      exact fun _ _ heq => nomatch heq) :
    EnvWF ⟨c :: env.consts, env.tables, env.rules⟩ := by
  have hcs : ∀ c' ∈ c :: env.consts, ConstWF ⟨c :: env.consts, env.tables, env.rules⟩ c' := by
    intro c' hc'
    rcases List.mem_cons.mp hc' with rfl | hmem
    · exact hc
    · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := henv.consts c' hmem
      refine ⟨h1, h2, Expr.constsResolve_mono h3, h4, fun cv value hint heq =>
        let ⟨g1, g2, g3, g4⟩ := h5 cv value hint heq
        ⟨g1, g2, Expr.constsResolve_mono g3, g4⟩, ?_⟩
      intro cv mI rP isK rules heq r hr
      obtain ⟨g1, g2, g3, g4, g5⟩ := h6 cv mI rP isK rules heq r hr
      refine ⟨g1, g2, Expr.constsResolve_mono g3, g4, ?_⟩
      intro lvls pins hfr
      obtain ⟨n1, n2, n3, n4⟩ := g5 lvls pins hfr
      exact ⟨n1, n2, fun pin hpin =>
        let ⟨p1, p2, p3, p4⟩ := n3 pin hpin
        ⟨p1, p2, Expr.constsResolve_mono p3, p4⟩, n4⟩
  refine ⟨hcs,
    fun c' hc' => (List.mem_cons.mp hc').elim (fun e => e ▸ hs) (henv.shapes c'),
    fun t ht => (henv.tables t ht).cons,
    fun c' hc' => (List.mem_cons.mp hc').elim (fun e => e ▸ hi) (henv.inds c'),
    fun c' hc' => (List.mem_cons.mp hc').elim (fun e => e ▸ hk) (henv.ctors c'),
    fun c' hc' => (List.mem_cons.mp hc').elim (fun e => e ▸ hr) (henv.rules c'), ?_,
    henv.ruleSnaps.mono rfl (Nat.le_succ _)⟩
  intro cs hcut
  rcases Env.Reach.of_cons hb hcut with rfl | hold
  · intro c' hc'
    exact ConstWF.of_find (env := ⟨c :: env.consts, env.tables, env.rules⟩) (env' := ⟨c :: env.consts, [], {}⟩) rfl (hcs c' hc')
  · exact henv.below cs hold

theorem Expr.constsResolve_eq_of_isSome {env env' : Env}
    (h : ∀ n, (env'.find? n).isSome = (env.find? n).isSome) (e : Expr) :
    e.constsResolve env' = e.constsResolve env := by
  cases h₂ : e.constsResolve env with
  | true => exact Expr.constsResolve_of_find (fun n hn => by rw [h]; exact hn) h₂
  | false =>
    cases h₁ : e.constsResolve env' with
    | true =>
      have := Expr.constsResolve_of_find (env := env') (env' := env)
        (fun n hn => by rw [← h]; exact hn) h₁
      rw [this] at h₂; exact nomatch h₂
    | false => rfl

/-- A constant's well-formedness reads which names are stored. -/
theorem ConstWF.of_isSome {env env' : Env} (h : ∀ n, (env'.find? n).isSome = (env.find? n).isSome)
    {c : ConstantInfo} (hc : ConstWF env c) : ConstWF env' c := by
  unfold ConstWF at hc ⊢
  simp only [Expr.constsResolve_eq_of_isSome h]
  exact hc

theorem TableWF.of_isSome {env env' : Env} (h : ∀ n, (env'.find? n).isSome = (env.find? n).isSome)
    {t : ProjTable} (ht : TableWF env t) : TableWF env' t := by
  unfold TableWF at ht ⊢
  simp only [Expr.constsResolve_eq_of_isSome h, h]
  exact ht

/-- A table's well-formedness reads the environment only through
`find?`. -/
theorem TableWF.of_find {env env' : Env} (h : env'.find? = env.find?) {t : ProjTable}
    (ht : TableWF env t) : TableWF env' t := by
  unfold TableWF at ht ⊢
  simp only [Expr.constsResolve_eq_of_find h, h]
  exact ht

/-- **A record's rule effect keeps `EnvWF`**: the constants and the tables stay, and nothing
well-formedness reads looks at the rules. -/
theorem EnvWF.stepRules {env : Env} (h : EnvWF env) (d : Declaration) : EnvWF (env.stepRules d) :=
  ⟨fun c hc => ConstWF.of_find (env := env) (env' := env.stepRules d) rfl (h.consts c hc), h.shapes,
    fun t ht => TableWF.of_find (env := env) (env' := env.stepRules d) rfl (h.tables t ht), h.inds, h.ctors, h.rules, h.below,
    h.ruleSnaps.stepRules d⟩

/-- **Installing a well-formed table preserves `EnvWF`** (task #362): the
constants read the environment only through `find?`, which a table
install leaves alone. -/
theorem EnvWF.pushTable {env : Env} {t : ProjTable} (henv : EnvWF env)
    (ht : TableWF env t) : EnvWF ⟨env.consts, t :: env.tables, env.rules⟩ :=
  ⟨fun c hc => (henv.consts c hc).of_find (Env.find?_pushTable env t), henv.shapes, fun t' ht' => by
    rcases List.mem_cons.mp ht' with rfl | hmem
    · exact ht.of_find (Env.find?_pushTable env _)
    · exact (henv.tables t' hmem).of_find (Env.find?_pushTable env t), henv.inds, henv.ctors,
    henv.rules, henv.below, ⟨henv.ruleSnaps.le, henv.ruleSnaps.active⟩⟩

/-- **Tables pushed onto a well-formed environment, each well formed there, keep it well
formed**: a table install changes no lookup. -/
theorem EnvWF.pushTables {env : Env} (henv : EnvWF env) {Q : List ProjTable}
    (hQ : ∀ t ∈ Q, TableWF env t) : EnvWF ⟨env.consts, Q ++ env.tables, env.rules⟩ := by
  have hf : Env.find? ⟨env.consts, Q ++ env.tables, env.rules⟩ = env.find? := rfl
  refine ⟨fun c hc => (henv.consts c hc).of_find hf, henv.shapes, fun t ht => ?_, henv.inds,
    henv.ctors, henv.rules, henv.below, ⟨henv.ruleSnaps.le, henv.ruleSnaps.active⟩⟩
  rcases List.mem_append.mp ht with ht | ht
  · exact (hQ t ht).of_find hf
  · exact (henv.tables t ht).of_find hf

/-- The kernel's name-list distinctness check is `List.Nodup`'s. -/
theorem nodup_of_nameNodup : ∀ {ns : List Name}, ConLeche.Name.nodup ns = true → ns.Nodup
  | [], _ => List.nodup_nil
  | n :: ns, h => by
    simp only [ConLeche.Name.nodup, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h
    refine List.nodup_cons.mpr ⟨fun hm => ?_, nodup_of_nameNodup h.2⟩
    have := h.1
    simp [hm] at this

/-! ## Two `find?` readings -/

/-- A `find?` hit names the stored constant. -/
theorem Env.find?_name {env : Env} {n : Name} {ci : ConstantInfo}
    (h : env.find? n = some ci) : ci.name = n := by
  unfold ConLeche.Env.find? at h
  have := List.find?_some h
  simpa using this

/-- A `find?` hit is a stored constant. -/
theorem Env.find?_mem {env : Env} {n : Name} {ci : ConstantInfo}
    (h : env.find? n = some ci) : ci ∈ env.consts := by
  unfold ConLeche.Env.find? at h
  exact List.mem_of_find?_eq_some h

/-- **A stored constructor's family name is its type's head**, off `EnvWF`. -/
theorem EnvWF.ctorHead {env : Env} (henv : EnvWF env) {c : Name} {cv : ConstantVal}
    {nP nF : Nat} {T : Name} (h : env.find? c = some (.ctorInfo cv nP nF T)) :
    ∃ us, cv.type.piResult.getAppFn = .const T us :=
  henv.ctors _ (Env.find?_mem h) cv nP nF T rfl

/-- **The table lookup at a cut**: the name's first table, where it is live there. -/
theorem Env.liveTables_find (cs : List ConstantInfo) (T : Name) :
    ∀ ts : List ProjTable, (Env.liveTables cs ts).find? (·.structName == T)
      = (ts.find? (·.structName == T)).filter (Env.tableOkAt cs)
  | [] => rfl
  | t :: ts => by
    have hrest : ∀ q : ProjTable → Bool,
        ((Env.liveTables cs ts).filter (·.structName != t.structName)).find? q
          = (Env.liveTables cs ts).find? (fun x => (x.structName != t.structName) && q x) := by
      intro q
      induction Env.liveTables cs ts with
      | nil => rfl
      | cons x xs ih =>
        simp only [List.filter_cons]
        by_cases hx : (x.structName != t.structName) = true
        · simp only [hx, ↓reduceIte, List.find?_cons, Bool.true_and, ih]
        · simp only [hx, Bool.false_eq_true, ↓reduceIte, List.find?_cons, Bool.false_and, ih]
    simp only [Env.liveTables, List.find?_cons]
    by_cases hT : t.structName = T
    · subst hT
      have hnone : ((Env.liveTables cs ts).filter (·.structName != t.structName)).find?
          (·.structName == t.structName) = none := by
        rw [hrest]
        simp
      split
      · rename_i hok
        simp [Option.filter, hok]
      · rename_i hok
        simp [Option.filter, hok, List.find?_eq_none]
    · have hTb : (t.structName == T) = false := by simpa using hT
      have hq : (fun x : ProjTable => (x.structName != t.structName) && (x.structName == T))
          = (fun x => x.structName == T) := by
        funext x
        by_cases hx : x.structName = T
        · simp [hx, Ne.symm hT]
        · simp [hx]
      simp only [hTb]
      split
      · rw [List.find?_cons, hTb]
        simp only
        rw [hrest, hq, Env.liveTables_find cs T ts]
      · rw [hrest, hq, Env.liveTables_find cs T ts]

/-! ## Well-formedness at a cut -/

/-- **A reached cut of a well-formed environment is well formed**: its constants hold what they
refer to (`EnvWF.below`), its tables are live there, and every cut it reaches is reached. -/
theorem EnvWF.cut {env : Env} (henv : EnvWF env) {cs : List ConstantInfo}
    (hr : Env.Reach env.consts cs) : EnvWF (env.cutAt cs) := by
  have hsub : ∀ c ∈ cs, c ∈ env.consts := fun c hc => hr.suffix.subset hc
  refine ⟨fun c hc => ConstWF.of_find (env := ⟨cs, [], {}⟩) (env' := env.cutAt cs) rfl (henv.below cs hr c hc), fun c hc => henv.shapes c (hsub c hc),
    fun t ht => ?_, fun c hc => henv.inds c (hsub c hc), fun c hc => henv.ctors c (hsub c hc),
    fun c hc => henv.rules c (hsub c hc), fun cs' hr' => henv.below cs' (hr.trans hr'),
    RulesWF.cutAt env cs⟩
  obtain ⟨htm, hok⟩ := Env.mem_liveTables ht
  obtain ⟨-, h1, h2⟩ := henv.tables t htm
  simp only [Env.tableOkAt, Bool.and_eq_true] at hok
  refine ⟨hok.1, h1, fun i b hb => ?_⟩
  obtain ⟨g1, g2, -, g4⟩ := h2 i b hb
  have hres := (Array.all_eq_true_iff_forall_mem.mp hok.2) b (Array.mem_of_getElem? hb)
  exact ⟨g1, g2, (Expr.constsResolve_eq_of_find (env := ⟨cs, [], {}⟩) (env' := env.cutAt cs) rfl b).trans hres, g4⟩

/-- **The environment a family's telescope is read at is well formed.** -/
theorem EnvWF.famBelow {env env' : Env} (henv : EnvWF env) {n : Name}
    (h : env.famBelow n = some env') : EnvWF env' := by
  unfold Env.famBelow at h
  split at h
  · rename_i cv caps hf
    obtain rfl := Option.some.inj h
    exact henv.cut (.step .top hf)
  · exact nomatch h

/-- **Well-formedness after pushing constants none of which is a family**, from the six
clauses at the new environment: the cuts a telescope is read at are the old ones. -/
theorem EnvWF.of_append {env E : Env} {new : List ConstantInfo} (henv : EnvWF env)
    (hsplit : E.consts = new ++ env.consts) (hnew : ∀ c ∈ new, ∀ cv caps, c ≠ .indInfo cv caps)
    (hc : ∀ c ∈ E.consts, ConstWF E c) (hs : ∀ c ∈ E.consts, litShapeOk c = true)
    (ht : ∀ t ∈ E.tables, TableWF E t) (hi : ∀ c ∈ E.consts, IndWF c)
    (hk : ∀ c ∈ E.consts, CtorWF c) (hr : ∀ c ∈ E.consts, RuleWF c) (hR : E.rules = env.rules) :
    EnvWF E := by
  refine ⟨hc, hs, ht, hi, hk, hr, fun cs hcs => ?_,
    henv.ruleSnaps.mono hR (by rw [hsplit, List.length_append]; exact Nat.le_add_left _ _)⟩
  rw [hsplit] at hcs
  rcases Env.Reach.of_append hnew hcs with rfl | h
  · intro c hc'
    exact ConstWF.of_find (env := E) (env' := ⟨new ++ env.consts, [], {}⟩)
      (by funext n; show (new ++ env.consts).find? _ = E.consts.find? _; rw [hsplit])
      (hc c (hsplit ▸ hc'))
  · exact henv.below cs h

/-! ## Cuts across pushes under fresh names -/

/-- Constants pushed under other names leave the cut past a name alone. -/
theorem Env.suffixAfter_append_of_ne {n : Name} :
    ∀ {new : List ConstantInfo} (cs : List ConstantInfo), (∀ c ∈ new, c.name ≠ n) →
      Env.suffixAfter (new ++ cs) n = Env.suffixAfter cs n
  | [], _, _ => rfl
  | c :: new, cs, h => by
    rw [List.cons_append, Env.suffixAfter_cons, ite_eq_right (h c List.mem_cons_self)]
    exact Env.suffixAfter_append_of_ne cs (fun c' hc' => h c' (List.mem_cons_of_mem _ hc'))

/-- The constants past a stored name are fewer than all of them. -/
theorem Env.suffixAfter_length_lt {cs : List ConstantInfo} {n : Name} {ci : ConstantInfo}
    (h : cs.find? (·.name == n) = some ci) : (Env.suffixAfter cs n).length < cs.length := by
  induction cs with
  | nil => exact nomatch h
  | cons c cs ih =>
    rw [Env.suffixAfter_cons]
    split
    · simp
    · rename_i hc
      rw [List.find?_cons_of_neg (by simpa using hc)] at h
      exact Nat.lt_succ_of_lt (ih h)

/-- Tables of structures absent from a cut leave its tables alone. -/
theorem Env.liveTables_append_dead {cs : List ConstantInfo} :
    ∀ {newT : List ProjTable} (ts : List ProjTable),
      (∀ t ∈ newT, cs.find? (·.name == t.structName) = none) →
      Env.liveTables cs (newT ++ ts) = Env.liveTables cs ts
  | [], _, _ => rfl
  | t :: newT, ts, h => by
    have ht : Env.tableOkAt cs t = false := by
      simp [Env.tableOkAt, h t List.mem_cons_self]
    rw [List.cons_append, Env.liveTables, ite_eq_right (by simp [ht]),
      Env.liveTables_append_dead ts (fun t' ht' => h t' (List.mem_cons_of_mem _ ht'))]
    refine List.filter_eq_self.mpr fun t' ht' => ?_
    obtain ⟨-, hok⟩ := Env.mem_liveTables ht'
    simp only [Env.tableOkAt, Bool.and_eq_true] at hok
    have hn := h t List.mem_cons_self
    simp only [bne_iff_ne, ne_eq]
    intro he
    rw [he, hn] at hok
    exact nomatch hok.1

end ConLeche
