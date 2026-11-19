module

public import ConLeche.Kernel.DeclCheck

public section

/-!
# The index answers as the environment

`FEnv` (`ConLeche/Kernel/FEnv.lean`) keeps a name index and a table map beside the environment; for
`mkFEnv` they answer as `Env.find?` and `Env.findTable?` do (`mkFEnv_find?`, `mkFEnv_findTable?`), and
the guard twins that read through them as the `Env` guards do.

Spec-side only: nothing here is called by the checker.
-/

namespace ConLeche

/-- Name uniqueness of an environment's constants: what the fold keeps
(`ConLeche/Verify/Cached/PushChain.lean`), so that a stream's first entry of a name is its only one. -/
@[expose] def NodupNames (env : Env) : Prop := (env.consts.map (·.name)).Nodup

/-- The empty base layer answers nothing. -/
@[simp] theorem FBase.find?_empty (n : Name) : ({} : FBase).find? n = none := by
  simp [FBase.find?]

/-- `mkFEnv` has the empty base layer. -/
@[simp] theorem mkFEnv_base (env : Env) : (mkFEnv env).base =
    { rls := mkRlsGo env.rules.active, abs := env.rules.abstracts, blks := env.rules.blks,
      blk := blkHead env.rules.blks } := rfl

/-- `mkFEnv`'s blocked set is the environment's. -/
@[simp] theorem mkFEnv_blk_elem (env : Env) (n : Name) :
    List.elem n (mkFEnv env).base.blk = env.blocked n := rfl

/-- A base layer carrying only rules answers no constant. -/
@[simp] theorem FBase.find?_rls (r : Std.HashMap Name (List Name)) (a : List (Name × List Name))
    (b : List (Nat × List Name)) (k : List Name) (n : Name) :
    ({ rls := r, abs := a, blks := b, blk := k } : FBase).find? n = none := by
  simp [FBase.find?]

/-- A base layer carrying only rules answers no table. -/
@[simp] theorem FBase.findTable?_rls (r : Std.HashMap Name (List Name)) (a : List (Name × List Name))
    (b : List (Nat × List Name)) (k : List Name) (T : Name) :
    ({ rls := r, abs := a, blks := b, blk := k } : FBase).findTable? T = none := by
  simp [FBase.findTable?]

/-- The index's specification: `List.find?` (the build inserts from the back, so the newest constant
of a name wins). -/
theorem mkIdxGo_getElem? (n : Name) : ∀ l : List ConstantInfo,
    (mkIdxGo l)[n]? = l.find? (·.name == n)
  | [] => by simp [mkIdxGo]
  | ci :: cs => by
    show ((mkIdxGo cs).insert ci.name ci)[n]? = _
    rw [Std.HashMap.getElem?_insert, List.find?_cons, mkIdxGo_getElem? n cs]
    by_cases hn : ci.name == n <;> simp [hn]

/-- The per-entry-call name index computes `Env.find?`. -/
theorem mkFEnv_find? (env : Env) (n : Name) :
    (mkFEnv env).find? n = env.find? n := by
  show (mkFEnv env).lookup n = _
  rw [FEnv.lookup_eq]
  show (match (mkIdxGo env.consts)[n]? with
        | some ci => some ci
        | none => ({ rls := mkRlsGo env.rules.active, abs := env.rules.abstracts, blks := env.rules.blks, blk := blkHead env.rules.blks } : FBase).find? n) = _
  rw [mkIdxGo_getElem?, FBase.find?_rls, Env.find?]
  cases env.consts.find? (·.name == n) <;> rfl

/-- **Entering changes nothing where nothing is blocked** (`FEnv.quiet`), for a record whose rule
effect is the declaration arm of `RuleTable.step`. -/
theorem FEnv.enterRec_quiet {fe : FEnv} (h : fe.quiet = true) (d : Declaration)
    (hd : fe.env.rules.step fe.env.consts.length d = { fe.env.rules with
      blks := pushBlkOn fe.env.rules.blks fe.env.consts.length
        (blockedFor fe.env.rules.abstracts d.mainName) }) :
    fe.enterRec d = fe := by
  simp only [FEnv.quiet, Bool.and_eq_true, List.isEmpty_iff] at h
  obtain ⟨⟨⟨⟨ha, hb⟩, hh⟩, hea⟩, heh⟩ := h
  have hrt : fe.env.rules.step fe.env.consts.length d = fe.env.rules := by
    rw [hd, hea]
    simp only [blockedFor, List.filterMap_nil, pushBlkOn, heh, ↓reduceIte]
  have hbase : { fe.base with
      blks := pushBlkOn fe.base.blks fe.cnt (blockedFor fe.base.abs d.mainName),
      blk := blkHead (pushBlkOn fe.base.blks fe.cnt (blockedFor fe.base.abs d.mainName)) } =
      fe.base := by
    simp only [ha, blockedFor, List.filterMap_nil, pushBlkOn, hh, ↓reduceIte]
    rw [← hb, ← ha]
  rcases fe with ⟨⟨cs, ts, rt⟩, idx, base, ovl, tbls, nl, sl, hnl, hsl⟩
  simp only [FEnv.enterRec, Env.stepRules] at hrt hbase ⊢
  simp only [hrt]
  congr

/-- `stepRules` on a declaration record is `enterRec`: the skip it makes where nothing is blocked
(`FEnv.quiet`) returns what `enterRec` would. -/
theorem FEnv.stepRules_enterRec (fe : FEnv) (d : Declaration)
    (hd : fe.env.rules.step fe.env.consts.length d = { fe.env.rules with
      blks := pushBlkOn fe.env.rules.blks fe.env.consts.length
        (blockedFor fe.env.rules.abstracts d.mainName) }) :
    (if fe.quiet then fe else fe.enterRec d) = fe.enterRec d := by
  split
  · next h => exact (FEnv.enterRec_quiet h d hd).symm
  · rfl

/-- **The index a record is checked at**, with the skip folded away. -/
theorem FEnv.enter_eq (fe : FEnv) (d : Declaration) :
    fe.enter d = match d with
      | .rewriteDecl .. | .useRules _ | .abstractDecl .. => fe
      | _ => fe.enterRec d := by
  cases d <;> first | rfl | exact FEnv.stepRules_enterRec fe _ rfl

/-- A record's rule effect on the index is its rule effect on the environment. -/
theorem stepRules_env (fe : FEnv) (pd : Declaration) : (fe.stepRules pd).env = fe.env.stepRules pd := by
  cases pd <;> first | rfl | exact congrArg FEnv.env (FEnv.stepRules_enterRec fe _ rfl)

/-- A canonical index stays canonical across a record's rule effect. -/
theorem stepRules_mkFEnv (env : Env) (pd : Declaration) :
    (mkFEnv env).stepRules pd = mkFEnv (env.stepRules pd) := by
  cases pd <;> first | rfl | exact FEnv.ext_parts rfl rfl rfl rfl rfl |
    exact (FEnv.stepRules_enterRec _ _ rfl).trans (FEnv.ext_parts rfl rfl (by
      simp only [FEnv.enterRec, mkFEnv_base, FEnv.cnt, Nat.zero_add]
      rfl) rfl rfl)

/-- `mkFEnv`'s abstract definitions are the environment's. -/
@[simp] theorem mkFEnv_abs (env : Env) : (mkFEnv env).base.abs = env.rules.abstracts := rfl

/-- A canonical index stays canonical when a record is entered. -/
theorem enter_mkFEnv (env : Env) (pd : Declaration) :
    (mkFEnv env).enter pd = mkFEnv (env.enter pd) := by
  cases pd <;> first | rfl | (dsimp only [FEnv.enter, Env.enter]; exact stepRules_mkFEnv env _)

/-! ## The rule map agrees with `Env.rulesFor` -/

/-- The rule map's specification: the rules of a head, newest first. -/
theorem mkRlsGo_getD (c : Name) : ∀ rs : List (Name × Name),
    (mkRlsGo rs).getD c [] = rs.filterMap fun r => if r.1 == c then some r.2 else none
  | [] => by simp [mkRlsGo]
  | (c', t) :: rs => by
    show ((mkRlsGo rs).insert c' (t :: (mkRlsGo rs).getD c' [])).getD c [] = _
    rw [Std.HashMap.getD_insert, List.filterMap_cons]
    by_cases hc : c' == c
    · have : c' = c := by simpa using hc
      subst this
      simp [mkRlsGo_getD c' rs]
    · simp [hc, mkRlsGo_getD c rs]

/-- The rule map is empty exactly at an empty table. -/
theorem mkRlsGo_isEmpty : ∀ rs : List (Name × Name), (mkRlsGo rs).isEmpty = rs.isEmpty
  | [] => by simp [mkRlsGo]
  | (c, t) :: rs => by simp [mkRlsGo]

/-- The per-entry-call rule map computes `Env.rulesFor`. -/
theorem mkFEnv_rulesFor (env : Env) (c : Name) : (mkFEnv env).rulesFor c = env.rulesFor c := by
  unfold FEnv.rulesFor Env.rulesFor
  rw [mkFEnv_base]
  show ((mkRlsGo env.rules.active).getD c []).filter _ = _
  rw [mkRlsGo_getD]
  simp only [mkFEnv_find?]
  induction env.rules.active with
  | nil => rfl
  | cons r rs ih =>
    rw [List.filterMap_cons, List.filterMap_cons]
    by_cases hc : r.1 == c
    · simp only [hc, ↓reduceIte, Bool.true_and, List.filter_cons]
      cases (env.find? r.2).isSome <;> simp_all
    · simp_all

theorem mkFEnv_rulesFor_fun (env : Env) : (mkFEnv env).rulesFor = env.rulesFor :=
  funext (mkFEnv_rulesFor env)

/-! ## The table map agrees with `Env.findTable?` -/

/-- The table map's specification: `List.find?` (the build inserts from
the back, so the newest table of a name wins). -/
theorem mkTblsGo_getElem? (T : Name) : ∀ ts : List ProjTable,
    (mkTblsGo ts)[T]? = ts.find? (·.structName == T)
  | [] => by simp [mkTblsGo]
  | t :: ts => by
    show ((mkTblsGo ts).insert t.structName t)[T]? = _
    rw [Std.HashMap.getElem?_insert, List.find?_cons, mkTblsGo_getElem? T ts]
    by_cases hT : t.structName == T <;> simp [hT]

/-- The empty base layer has no tables. -/
@[simp] theorem FBase.findTable?_empty (T : Name) : ({} : FBase).findTable? T = none := by
  simp [FBase.findTable?]

/-- The raw table lookup of `mkFEnv` is the table component's. -/
theorem mkFEnv_rawTable? (env : Env) (T : Name) :
    (mkFEnv env).rawTable? T = env.tables.find? (·.structName == T) := by
  show (match (mkTblsGo env.tables)[T]? with
    | some t => some t
    | none => ({ rls := mkRlsGo env.rules.active, abs := env.rules.abstracts, blks := env.rules.blks, blk := blkHead env.rules.blks } : FBase).findTable? T) = _
  rw [mkTblsGo_getElem?, FBase.findTable?_rls]
  cases env.tables.find? (·.structName == T) <;> rfl

/-- **The index's table lookup is the environment's** (both gate on the
structure's constant). -/
theorem mkFEnv_findTable? (env : Env) (T : Name) :
    (mkFEnv env).findTable? T = env.findTable? T := by
  rw [FEnv.findTable?_of_chk rfl]
  unfold Env.findTable?
  rw [mkFEnv_find?, mkFEnv_rawTable?]

/-- The indexed projection lookup computes `Env.findProj?`. -/
theorem mkFEnv_findProj? (env : Env) (T : Name) (i : Nat) :
    (mkFEnv env).findProj? T i = env.findProj? T i := by
  rw [FEnv.findProj?, Env.findProj?, mkFEnv_findTable?]
  cases env.findTable? T <;> rfl

/-! ## Guard twins agree with the `Env` versions -/

theorem natLitSupportedF_eq (env : Env) :
    natLitSupportedF (mkFEnv env) = natLitSupported env := by
  simp only [natLitSupportedF, natLitSupported, mkFEnv_find?]

/-- The index's `Nat`-literal flag is `natLitStored` of its environment. -/
theorem mkFEnv_natLit (env : Env) : (mkFEnv env).natLit = natLitStored env := by
  rw [(mkFEnv env).natLit_eq]
  show natLitStoredBy (mkFEnv env).find? = _
  simp only [natLitStoredBy, natLitStored, mkFEnv_find?]

/-- The index's string-literal flag is `strLitStored` of its environment. -/
theorem mkFEnv_strLit (env : Env) : (mkFEnv env).strLit = strLitStored env := by
  rw [(mkFEnv env).strLit_eq]
  show strLitStoredBy (mkFEnv env).find? = _
  simp only [strLitStoredBy, natLitStoredBy, strLitStored, natLitStored, mkFEnv_find?]

theorem natOpGuardF_eq (env : Env) (c : Name) :
    natOpGuardF (mkFEnv env) c = natOpGuard env c := by
  simp only [natOpGuardF, natOpGuard, mkFEnv_find?, natLitSupportedF_eq]
  rfl

end ConLeche
