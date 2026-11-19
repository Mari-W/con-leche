module

public import ConLeche.Cached.StreamIndex
public import ConLeche.Verify.Cached.ViewCongr
public import ConLeche.Verify.Cached.PushChain
import ConLeche.Verify.Cached.WalkersC
import ConLeche.Verify.CheckerF
import ConLeche.Verify.EnvWF

/-!
# Every job passing is an accept of the fold

`checkDecls_of_jobs`: if every record's job (`recordJob`, `ConLeche/Cached/StreamIndex.lean`) passes,
the fold `checkDecls` accepts the stream with the environment the records denote.  By induction along
the stream: the steps so far having accepted, the names so far are distinct (`PushChain`), so the
view of the next position answers every lookup as the fold's index does (`viewTwin`), so the job's
verdict is the fold's step (`checkDeclStepC_twin`).

The index's first-entry-wins builder enters through what it answers (`firstOcc`, `firstTbl`).  Nothing
here mentions a thread: the driver's jobs are values.
-/

public section

namespace ConLeche.Cached

open ConLeche

variable {mode : CheckMode} {pins : List NatOpPinSet}

/-! ## What the index answers -/

/-- The first constant named `n` in `L`, whose head has counter `c`. -/
def firstOcc (n : Name) : Nat → List ConstantInfo → Option (Nat × ConstantInfo)
  | _, [] => none
  | c, ci :: L => if ci.name = n then some (c, ci) else firstOcc n (c + 1) L

theorem firstOcc_append (n : Name) (c : Nat) (A B : List ConstantInfo) :
    firstOcc n c (A ++ B) = (firstOcc n c A).or (firstOcc n (c + A.length) B) := by
  induction A generalizing c with
  | nil => simp [firstOcc]
  | cons a A ih =>
    simp only [List.cons_append, firstOcc, List.length_cons]
    split
    · rfl
    · rw [ih]
      congr 2
      omega

theorem firstOcc_ge {n : Name} {c c' : Nat} {ci : ConstantInfo} :
    ∀ {L : List ConstantInfo}, firstOcc n c L = some (c', ci) → c ≤ c' ∧ c' < c + L.length
  | [], h => by simp [firstOcc] at h
  | a :: L, h => by
    simp only [firstOcc] at h
    split at h
    · cases h; simp
    · have := firstOcc_ge h
      simp only [List.length_cons]
      omega

/-- The insertion keeps the map's answers the first occurrences. -/
theorem insertConsts_spec {A : List ConstantInfo} :
    ∀ (L : List ConstantInfo) (idx : Std.HashMap Name (Nat × ConstantInfo)),
      (∀ n, idx[n]? = firstOcc n 0 A) →
      (insertConsts idx A.length L).2 = A.length + L.length ∧
      ∀ n, (insertConsts idx A.length L).1[n]? = firstOcc n 0 (A ++ L) := by
  intro L
  induction L generalizing A with
  | nil =>
    intro idx h
    simpa [insertConsts] using h
  | cons ci L ih =>
    intro idx h
    have hstep : ∀ n, (idx.insertIfNew ci.name (A.length, ci))[n]? = firstOcc n 0 (A ++ [ci]) := by
      intro n
      rw [Std.HashMap.getElem?_insertIfNew, firstOcc_append]
      simp only [firstOcc, Nat.zero_add]
      by_cases hn : ci.name = n
      · subst hn
        cases hf : firstOcc ci.name 0 A with
        | none =>
          have hm : ci.name ∉ idx := by
            intro hmem
            have := (Std.HashMap.mem_iff_isSome_getElem?).mp hmem
            rw [h, hf] at this
            exact absurd this (by simp)
          simp [hm]
        | some p =>
          have hm : ci.name ∈ idx := by
            rw [Std.HashMap.mem_iff_isSome_getElem?, h, hf]; rfl
          rw [ite_eq_right (by simp [hm]), h, hf]
          rfl
      · simp [hn, h]
    have := ih (A := A ++ [ci]) (idx.insertIfNew ci.name (A.length, ci)) hstep
    simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add,
      List.append_assoc, List.cons_append, List.nil_append] at this
    simp only [insertConsts, List.length_cons]
    exact ⟨by rw [this.1]; omega, this.2⟩

/-- The first table of `T` among records' tables, each with its record's position. -/
def firstTbl (T : Name) : List (Nat × ProjTable) → Option (Nat × ProjTable)
  | [] => none
  | e :: L => if e.2.structName = T then some e else firstTbl T L

theorem firstTbl_append (T : Name) (A B : List (Nat × ProjTable)) :
    firstTbl T (A ++ B) = (firstTbl T A).or (firstTbl T B) := by
  induction A with
  | nil => simp [firstTbl]
  | cons a A ih =>
    simp only [List.cons_append, firstTbl]
    split
    · rfl
    · exact ih

theorem insertTables_spec (r : Nat) {A : List (Nat × ProjTable)} :
    ∀ (Q : List ProjTable) (tbls : Std.HashMap Name (Nat × ProjTable)),
      (∀ T, tbls[T]? = firstTbl T A) →
      ∀ T, (insertTables tbls r Q)[T]? = firstTbl T (A ++ Q.map (r, ·)) := by
  intro Q
  induction Q generalizing A with
  | nil =>
    intro tbls h
    simpa [insertTables] using h
  | cons t Q ih =>
    intro tbls h
    have hstep : ∀ T, (tbls.insertIfNew t.structName (r, t))[T]? = firstTbl T (A ++ [(r, t)]) := by
      intro T
      rw [Std.HashMap.getElem?_insertIfNew, firstTbl_append]
      simp only [firstTbl]
      by_cases hn : t.structName = T
      · subst hn
        cases hf : firstTbl t.structName A with
        | none =>
          have hm : t.structName ∉ tbls := by
            intro hmem
            have := (Std.HashMap.mem_iff_isSome_getElem?).mp hmem
            rw [h, hf] at this
            exact absurd this (by simp)
          simp [hm]
        | some p =>
          have hm : t.structName ∈ tbls := by
            rw [Std.HashMap.mem_iff_isSome_getElem?, h, hf]; rfl
          rw [ite_eq_right (by simp [hm]), h, hf]
          rfl
      · simp [hn, h]
    intro T
    have := ih (A := A ++ [(r, t)]) (tbls.insertIfNew t.structName (r, t)) hstep T
    simpa [insertTables] using this

/-- The constants of records, in order. -/
def recsConsts (ds : List Declaration) : List ConstantInfo := ds.flatMap declConstants

/-- The tables of records from position `r` on, each with its record's position. -/
def recsTables : Nat → List Declaration → List (Nat × ProjTable)
  | _, [] => []
  | r, pd :: ds => (declTables pd).map (r, ·) ++ recsTables (r + 1) ds

theorem recsConsts_snoc (ds : List Declaration) (pd : Declaration) :
    recsConsts (ds ++ [pd]) = recsConsts ds ++ declConstants pd := by
  simp [recsConsts]

theorem recsTables_append (r : Nat) (A B : List Declaration) :
    recsTables r (A ++ B) = recsTables r A ++ recsTables (r + A.length) B := by
  induction A generalizing r with
  | nil => simp [recsTables]
  | cons d A ih =>
    simp only [List.cons_append, recsTables, List.length_cons, ih, List.append_assoc]
    congr 3
    omega

theorem recsTables_snoc (r : Nat) (ds : List Declaration) (pd : Declaration) :
    recsTables r (ds ++ [pd]) = recsTables r ds ++ (declTables pd).map (r + ds.length, ·) := by
  simp [recsTables_append, recsTables]

theorem recsTables_bounds {e : Nat × ProjTable} :
    ∀ {ds : List Declaration} {r : Nat}, e ∈ recsTables r ds → r ≤ e.1 ∧ e.1 < r + ds.length
  | [], _, h => nomatch h
  | pd :: ds, r, h => by
    simp only [recsTables, List.mem_append, List.mem_map] at h
    rcases h with ⟨t, -, rfl⟩ | h
    · simp
    · have := recsTables_bounds h
      simp only [List.length_cons]
      omega

theorem recsTables_snd :
    ∀ (ds : List Declaration) (r : Nat), (recsTables r ds).map (·.2) = ds.flatMap declTables
  | [], _ => rfl
  | pd :: ds, r => by
    simp [recsTables, recsTables_snd ds (r + 1), List.map_map, Function.comp_def]

theorem streamEnv_consts (ds : List Declaration) (env : Env) :
    (streamEnv ds env).consts = (recsConsts ds).reverse ++ env.consts := by
  induction ds generalizing env with
  | nil => rfl
  | cons pd ds ih =>
    simp only [streamEnv, List.foldl_cons] at ih ⊢
    rw [ih]
    simp [recsConsts, Env.pushDelta, Env.stepRules]

theorem streamEnv_tables (ds : List Declaration) (env : Env) :
    (streamEnv ds env).tables = (ds.flatMap declTables).reverse ++ env.tables := by
  induction ds generalizing env with
  | nil => rfl
  | cons pd ds ih =>
    simp only [streamEnv, List.foldl_cons] at ih ⊢
    rw [ih]
    simp [Env.pushDelta, Env.stepRules]

/-- The rules after a record: its rule effect on the rules before it, at the constants so far. -/
theorem streamEnv_rules_snoc (ds : List Declaration) (pd : Declaration) :
    (streamEnv (ds ++ [pd])).rules = (streamEnv ds).rules.step (recsConsts ds).length pd := by
  have h : (streamEnv ds).consts = (recsConsts ds).reverse := by
    simpa [Env.empty] using streamEnv_consts ds Env.empty
  rw [show (streamEnv (ds ++ [pd])).rules = (streamEnv ds).rules.step (streamEnv ds).consts.length pd by
    simp [streamEnv, List.foldl_append, Env.pushDelta, Env.stepRules], h, List.length_reverse]

/-- **What the index of records holds.** -/
structure IndexSpec (ds : List Declaration) (I : StreamIndex) : Prop where
  next : I.next = (recsConsts ds).length
  firsts : ∀ k, (hk : k < ds.length) → I.firsts[k]? = some (recsConsts (ds.take k)).length
  size : I.firsts.size = ds.length
  idx : ∀ n, I.base.idx[n]? = firstOcc n 0 (recsConsts ds)
  tbls : ∀ T, I.base.tbls[T]? = firstTbl T (recsTables 0 ds)
  chk : I.base.chk = false
  rules : I.rules = (streamEnv ds).rules
  cur : I.rlsCur = mkRlsGo (streamEnv ds).rules.active
  rlsSize : I.rlsAt.size = ds.length
  rlsAt : ∀ k, (hk : k < ds.length) → I.rlsAt[k]? = some (mkRlsGo (streamEnv (ds.take k)).rules.active)
  snapsSize : I.snapsAt.size = ds.length
  snapsAt : ∀ k, (hk : k < ds.length) → I.snapsAt[k]? = some (streamEnv (ds.take k)).rules.snaps
  absSize : I.absAt.size = ds.length
  absAt : ∀ k, (hk : k < ds.length) → I.absAt[k]? = some (streamEnv (ds.take k)).rules.abstracts
  blksSize : I.blksAt.size = ds.length
  blksAt : ∀ k, (hk : k < ds.length) → I.blksAt[k]? = some (streamEnv (ds.take k)).rules.blks

theorem IndexSpec.add {ds : List Declaration} {I : StreamIndex} (h : IndexSpec ds I)
    (pd : Declaration) : IndexSpec (ds ++ [pd]) (I.add pd) := by
  have hc := insertConsts_spec (A := recsConsts ds) (declConstants pd) I.base.idx h.idx
  have hnext : I.next = (recsConsts ds).length := h.next
  have ht := insertTables_spec ds.length (A := recsTables 0 ds) (declTables pd) I.base.tbls h.tbls
  have hsz := h.size
  constructor
  · simp only [StreamIndex.add, hnext, declConstantsC_eq]
    rw [hc.1, recsConsts_snoc, List.length_append]
  · intro k hk
    simp only [StreamIndex.add, List.length_append, List.length_cons, List.length_nil] at hk ⊢
    rw [Array.getElem?_push]
    by_cases hk' : k = ds.length
    · subst hk'
      simp [hsz, hnext]
    · have hlt : k < ds.length := by omega
      rw [ite_eq_right (by omega), h.firsts k hlt, List.take_append_of_le_length (by omega)]
  · simp [StreamIndex.add, hsz]
  · intro n
    simp only [StreamIndex.add, hnext, declConstantsC_eq]
    rw [hc.2 n, recsConsts_snoc]
  · intro T
    simp only [StreamIndex.add, hsz, declTablesC_eq]
    rw [ht T, recsTables_snoc]
    simp
  · exact h.chk
  · simp only [StreamIndex.add]
    rw [h.rules, streamEnv_rules_snoc, hnext]
  · simp only [StreamIndex.add]
    rw [streamEnv_rules_snoc]
    cases pd <;> dsimp only <;> first | (rw [h.cur]; try rfl) | (rw [h.rules]; try rfl)
  · simp [StreamIndex.add, h.rlsSize]
  · intro k hk
    simp only [StreamIndex.add, List.length_append, List.length_cons, List.length_nil] at hk ⊢
    rw [Array.getElem?_push]
    by_cases hk' : k = ds.length
    · subst hk'
      simp [h.rlsSize, h.cur]
    · have hlt : k < ds.length := by omega
      rw [ite_eq_right (by rw [h.rlsSize]; omega), h.rlsAt k hlt, List.take_append_of_le_length (by omega)]
  · simp [StreamIndex.add, h.snapsSize]
  · intro k hk
    simp only [StreamIndex.add, List.length_append, List.length_cons, List.length_nil] at hk ⊢
    rw [Array.getElem?_push]
    by_cases hk' : k = ds.length
    · subst hk'
      simp [h.snapsSize, h.rules]
    · have hlt : k < ds.length := by omega
      rw [ite_eq_right (by rw [h.snapsSize]; omega), h.snapsAt k hlt,
        List.take_append_of_le_length (by omega)]
  · simp [StreamIndex.add, h.absSize]
  · intro k hk
    simp only [StreamIndex.add, List.length_append, List.length_cons, List.length_nil] at hk ⊢
    rw [Array.getElem?_push]
    by_cases hk' : k = ds.length
    · subst hk'
      simp [h.absSize, h.rules]
    · have hlt : k < ds.length := by omega
      rw [ite_eq_right (by rw [h.absSize]; omega), h.absAt k hlt,
        List.take_append_of_le_length (by omega)]
  · simp [StreamIndex.add, h.blksSize]
  · intro k hk
    simp only [StreamIndex.add, List.length_append, List.length_cons, List.length_nil] at hk ⊢
    rw [Array.getElem?_push]
    by_cases hk' : k = ds.length
    · subst hk'
      simp [h.blksSize, h.rules]
    · have hlt : k < ds.length := by omega
      rw [ite_eq_right (by rw [h.blksSize]; omega), h.blksAt k hlt,
        List.take_append_of_le_length (by omega)]

theorem buildIndex_spec (ds : Array Declaration) : IndexSpec ds.toList (buildIndex ds) := by
  unfold buildIndex
  rw [← Array.foldl_toList]
  suffices ∀ (l acc : List Declaration) (I : StreamIndex), IndexSpec acc I →
      IndexSpec (acc ++ l) (l.foldl StreamIndex.add I) from
    by simpa using this ds.toList [] {} ⟨rfl, by simp, rfl, by simp [recsConsts, firstOcc],
      by simp [recsTables, firstTbl], rfl, rfl, rfl, rfl, by simp, rfl, by simp, rfl, by simp, rfl,
      by simp⟩
  intro l
  induction l with
  | nil => intro acc I h; simpa using h
  | cons pd l ih =>
    intro acc I h
    have := ih (acc ++ [pd]) (I.add pd) (h.add pd)
    simpa using this

/-! ## The view of a position -/

/-- A list whose keys are distinct: the last with a key is the first. -/
theorem find?_reverse_of_nodup {α : Type} (f : α → Name) (n : Name) :
    ∀ {L : List α}, (L.map f).Nodup → L.reverse.find? (f · == n) = L.find? (f · == n)
  | [], _ => rfl
  | a :: L, h => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and] at h
    simp only [List.reverse_cons, List.find?_append, List.find?_cons, List.find?_nil,
      find?_reverse_of_nodup f n h.2]
    by_cases ha : f a = n
    · have hnone : L.find? (f · == n) = none := by
        rw [List.find?_eq_none]
        intro b hb hq
        have hfb : f b = n := by simpa using hq
        exact h.1 b hb (hfb.trans ha.symm)
      simp [hnone, ha]
    · have hb : (f a == n) = false := by simpa using ha
      simp [hb]

theorem firstOcc_map (n : Name) :
    ∀ (L : List ConstantInfo) (c : Nat),
      (firstOcc n c L).map (·.2) = L.find? (·.name == n)
  | [], _ => rfl
  | ci :: L, c => by
    simp only [firstOcc, List.find?_cons]
    by_cases h : ci.name = n
    · simp [h]
    · have hb : (ci.name == n) = false := by simpa using h
      simp [h, hb, firstOcc_map n L (c + 1)]

theorem firstTbl_map (T : Name) :
    ∀ L : List (Nat × ProjTable),
      (firstTbl T L).map (·.2) = (L.map (·.2)).find? (·.structName == T)
  | [] => rfl
  | e :: L => by
    simp only [firstTbl, List.map_cons, List.find?_cons]
    by_cases h : e.2.structName = T
    · simp [h]
    · have hb : (e.2.structName == T) = false := by simpa using h
      simp [h, hb, firstTbl_map T L]

theorem firstTbl_mem {T : Name} {e : Nat × ProjTable} :
    ∀ {L : List (Nat × ProjTable)}, firstTbl T L = some e → e ∈ L
  | [], h => by simp [firstTbl] at h
  | a :: L, h => by
    simp only [firstTbl] at h
    split at h
    · cases h; simp
    · exact List.mem_cons_of_mem _ (firstTbl_mem h)

/-- The rule map a view reads is the one the fold's environment there has. -/
theorem view_rls {pre rest : List Declaration} {I : StreamIndex}
    (hI : IndexSpec (pre ++ rest) I) :
    I.rlsAt.getD pre.length I.rlsCur = mkRlsGo (streamEnv pre).rules.active := by
  by_cases hk : pre.length < (pre ++ rest).length
  · have h := hI.rlsAt pre.length hk
    rw [List.take_left] at h
    simp [Array.getD_eq_getD_getElem?, h]
  · have hr : rest = [] := by
      simp only [List.length_append] at hk
      exact List.eq_nil_of_length_eq_zero (by omega)
    subst hr
    have hsz := hI.rlsSize
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by simp at hsz; omega)]
    simpa using hI.cur

/-- The abstract definitions a view records are the ones the fold's environment there has. -/
theorem view_abs {pre rest : List Declaration} {I : StreamIndex}
    (hI : IndexSpec (pre ++ rest) I) :
    I.absAt.getD pre.length I.rules.abstracts = (streamEnv pre).rules.abstracts := by
  by_cases hk : pre.length < (pre ++ rest).length
  · have h := hI.absAt pre.length hk
    rw [List.take_left] at h
    simp [Array.getD_eq_getD_getElem?, h]
  · have hr : rest = [] := by
      simp only [List.length_append] at hk
      exact List.eq_nil_of_length_eq_zero (by omega)
    subst hr
    have hsz := hI.absSize
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by simp at hsz; omega)]
    simpa using congrArg RuleTable.abstracts hI.rules

/-- The blocked sets a view records are the ones the fold's environment there has. -/
theorem view_blks {pre rest : List Declaration} {I : StreamIndex}
    (hI : IndexSpec (pre ++ rest) I) :
    I.blksAt.getD pre.length I.rules.blks = (streamEnv pre).rules.blks := by
  by_cases hk : pre.length < (pre ++ rest).length
  · have h := hI.blksAt pre.length hk
    rw [List.take_left] at h
    simp [Array.getD_eq_getD_getElem?, h]
  · have hr : rest = [] := by
      simp only [List.length_append] at hk
      exact List.eq_nil_of_length_eq_zero (by omega)
    subst hr
    have hsz := hI.blksSize
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by simp at hsz; omega)]
    simpa using congrArg RuleTable.blks hI.rules

/-- The rule tables a view records are the ones the fold's environment there has. -/
theorem view_snaps {pre rest : List Declaration} {I : StreamIndex}
    (hI : IndexSpec (pre ++ rest) I) :
    I.snapsAt.getD pre.length I.rules.snaps = (streamEnv pre).rules.snaps := by
  by_cases hk : pre.length < (pre ++ rest).length
  · have h := hI.snapsAt pre.length hk
    rw [List.take_left] at h
    simp [Array.getD_eq_getD_getElem?, h]
  · have hr : rest = [] := by
      simp only [List.length_append] at hk
      exact List.eq_nil_of_length_eq_zero (by omega)
    subst hr
    have hsz := hI.snapsSize
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by simp at hsz; omega)]
    simpa using congrArg RuleTable.snaps hI.rules

/-! ## Tables are named after a record's constants -/

theorem blockTables_sublist (p : BlockShape) :
    ∀ l : List MemberShape,
      (((blockTables p l).getD []).map (·.structName)).Sublist (l.map (·.declared.name))
  | [] => .refl _
  | ms :: rest => by
    have ih := blockTables_sublist p rest
    simp only [blockTables, List.map_cons]
    split
    · rename_i c _
      cases structProjBodies ms.declared.name p.nP c.2 c.1.type with
      | none => exact List.nil_sublist _
      | some bodies =>
        cases h : blockTables p rest with
        | none => exact List.nil_sublist _
        | some Qr =>
          rw [h] at ih
          exact ih.cons_cons _
    · exact ih.cons _

theorem declTables_sublist (pd : Declaration) :
    ((declTables pd).map (·.structName)).Sublist ((declConstants pd).map (·.name)) := by
  cases pd with
  | indDecl block nP =>
    simp only [declTables, declConstants]
    cases readBlock nP block with
    | error _ => simp
    | ok p =>
      simp only
      rw [blockConstants_names, List.append_assoc]
      exact (blockTables_sublist p p.members).trans (List.sublist_append_left _ _)
  | _ => simp [declTables]

theorem recsTables_sublist :
    ∀ ds : List Declaration,
      ((ds.flatMap declTables).map (·.structName)).Sublist ((recsConsts ds).map (·.name))
  | [] => .refl _
  | pd :: ds => by
    simp only [recsConsts, List.flatMap_cons, List.map_append]
    exact (declTables_sublist pd).append (recsTables_sublist ds)

/-! ## The view of a position answers as the fold's index -/

theorem view_counter {pre rest : List Declaration} {I : StreamIndex}
    (hI : IndexSpec (pre ++ rest) I) :
    I.firsts.getD pre.length I.next = (recsConsts pre).length := by
  by_cases hk : pre.length < (pre ++ rest).length
  · have h := hI.firsts pre.length hk
    rw [List.take_left] at h
    simp [Array.getD_eq_getD_getElem?, h]
  · have hr : rest = [] := by
      simp only [List.length_append] at hk
      exact List.eq_nil_of_length_eq_zero (by omega)
    subst hr
    have hsz := hI.size
    have : ¬ pre.length < I.firsts.size := by rw [hsz]; simp
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega)]
    simpa using hI.next

theorem view_eq {pre rest : List Declaration} {I : StreamIndex}
    (hI : IndexSpec (pre ++ rest) I) :
    I.freeze.view pre.length = FEnv.ofParts ⟨[], [], {}⟩ {}
      { I.base with
        below := (recsConsts pre).length, belowRec := pre.length,
        rls := mkRlsGo (streamEnv pre).rules.active, snaps := (streamEnv pre).rules.snaps,
        abs := (streamEnv pre).rules.abstracts, blks := (streamEnv pre).rules.blks,
        blk := blkHead (streamEnv pre).rules.blks } [] {} := by
  refine FEnv.ext_parts rfl rfl ?_ rfl rfl
  show { I.base with
    below := I.firsts.getD pre.length I.next, belowRec := pre.length,
    rls := I.rlsAt.getD pre.length I.rlsCur, snaps := I.snapsAt.getD pre.length I.rules.snaps,
    abs := I.absAt.getD pre.length I.rules.abstracts, blks := I.blksAt.getD pre.length I.rules.blks,
    blk := blkHead (I.blksAt.getD pre.length I.rules.blks) } = _
  rw [view_counter hI, view_rls hI, view_snaps hI, view_abs hI, view_blks hI]
  rfl

theorem view_find {pre rest : List Declaration} {I : StreamIndex}
    (hI : IndexSpec (pre ++ rest) I) (n : Name) :
    (I.freeze.view pre.length).find? n = (firstOcc n 0 (recsConsts pre)).map (·.2) := by
  rw [view_eq hI]
  dsimp only [FEnv.find?, FEnv.ofParts_idx, FEnv.ofParts_base, FEnv.ofParts_ovl]
  simp only [findIn, lookupIn_eq, Std.HashMap.getElem?_empty, FBase.find?]
  rw [hI.idx n]
  have hsplit : recsConsts (pre ++ rest) = recsConsts pre ++ recsConsts rest := by
    simp [recsConsts]
  rw [hsplit, firstOcc_append, Nat.zero_add]
  cases hp : firstOcc n 0 (recsConsts pre) with
  | some p =>
    obtain ⟨c, ci⟩ := p
    have := (firstOcc_ge hp).2
    simp only [Option.or, Option.map_some]
    rw [ite_eq_left (by omega)]
  | none =>
    simp only [Option.or, Option.map_none]
    cases hr : firstOcc n (recsConsts pre).length (recsConsts rest) with
    | none => rfl
    | some p =>
      obtain ⟨c, ci⟩ := p
      have := (firstOcc_ge hr).1
      simp only
      rw [ite_eq_right (by omega)]

theorem view_rawTable {pre rest : List Declaration} {I : StreamIndex}
    (hI : IndexSpec (pre ++ rest) I) (T : Name) :
    (I.freeze.view pre.length).rawTable? T = (firstTbl T (recsTables 0 pre)).map (·.2) := by
  rw [view_eq hI]
  dsimp only [FEnv.rawTable?, FEnv.ofParts_tbls, FEnv.ofParts_base]
  simp only [Std.HashMap.getElem?_empty, FBase.findTable?]
  rw [hI.tbls T, recsTables_append, firstTbl_append, Nat.zero_add]
  cases hp : firstTbl T (recsTables 0 pre) with
  | some e =>
    obtain ⟨r, t⟩ := e
    have := recsTables_bounds (firstTbl_mem hp)
    simp only [Option.or, Option.map_some]
    rw [ite_eq_left (by simp only at this; omega)]
  | none =>
    simp only [Option.or, Option.map_none]
    cases hr : firstTbl T (recsTables pre.length rest) with
    | none => rfl
    | some e =>
      obtain ⟨r, t⟩ := e
      have := recsTables_bounds (firstTbl_mem hr)
      simp only
      rw [ite_eq_right (by simp only at this; omega)]

/-- **A view of the frozen layer at a counter `b` answers the first `b` constants of the
stream.** -/
theorem view_base_find {pre rest : List Declaration} {I : StreamIndex}
    (hI : IndexSpec (pre ++ rest) I) (b r : Nat) (c : Bool) (q : Std.HashMap Name (List Name))
    (sn : List (Nat × List (Name × Name))) (ab : List (Name × List Name))
    (bl : List (Nat × List Name)) (bk : List Name) (hle : b ≤ (recsConsts pre).length) (m : Name) :
    FBase.find?
      { I.base with below := b, belowRec := r, chk := c, rls := q, snaps := sn, abs := ab, blks := bl, blk := bk }
      m
      = ((recsConsts pre).take b).find? (·.name == m) := by
  unfold FBase.find?
  simp only
  rw [hI.idx m]
  have hsplit : recsConsts (pre ++ rest)
      = (recsConsts pre).take b ++ ((recsConsts pre).drop b ++ recsConsts rest) := by
    rw [show recsConsts (pre ++ rest) = recsConsts pre ++ recsConsts rest by simp [recsConsts],
      ← List.append_assoc, List.take_append_drop]
  have hlen : ((recsConsts pre).take b).length = b := by simp; omega
  rw [hsplit, firstOcc_append, Nat.zero_add, hlen]
  rw [← firstOcc_map m ((recsConsts pre).take b) 0]
  cases hp : firstOcc m 0 ((recsConsts pre).take b) with
  | some p =>
    obtain ⟨c, ci⟩ := p
    have := (firstOcc_ge hp).2
    simp only [Option.or, Option.map_some]
    rw [ite_eq_left (by omega)]
  | none =>
    simp only [Option.or, Option.map_none]
    cases hr : firstOcc m b ((recsConsts pre).drop b ++ recsConsts rest) with
    | none => rfl
    | some p =>
      obtain ⟨c, ci⟩ := p
      have := (firstOcc_ge hr).1
      simp only
      rw [ite_eq_right (by omega)]

/-- A name's first entry splits the list there. -/
theorem firstOcc_split {n : Name} :
    ∀ {L : List ConstantInfo} {c₀ c : Nat} {x : ConstantInfo}, firstOcc n c₀ L = some (c, x) →
      L = L.take (c - c₀) ++ x :: L.drop (c - c₀ + 1) ∧ x.name = n ∧ c₀ ≤ c ∧
        ∀ y ∈ L.take (c - c₀), y.name ≠ n
  | [], _, _, _, h => by simp [firstOcc] at h
  | a :: L, c₀, c, x, h => by
    simp only [firstOcc] at h
    split at h
    · rename_i ha
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      simp [ha]
    · rename_i ha
      obtain ⟨h1, h2, h3, h4⟩ := firstOcc_split h
      have hc : c - c₀ = (c - (c₀ + 1)) + 1 := by omega
      refine ⟨?_, h2, by omega, ?_⟩
      · rw [hc, List.take_succ_cons, List.drop_succ_cons, List.cons_append, ← h1]
      · rw [hc, List.take_succ_cons]
        intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact ha
        · exact h4 y hy

/-- The constants past a name's only entry, in a reversed list. -/
theorem suffixAfter_reverse {n : Name} {L : List ConstantInfo} (hnd : (L.map (·.name)).Nodup)
    {c : Nat} {x : ConstantInfo} (h : firstOcc n 0 L = some (c, x)) :
    Env.suffixAfter L.reverse n = (L.take c).reverse := by
  obtain ⟨h1, h2, -, -⟩ := firstOcc_split h
  simp only [Nat.sub_zero] at h1
  have hB : ∀ y ∈ L.drop (c + 1), y.name ≠ n := by
    intro y hy he
    rw [h1, List.map_append, List.map_cons] at hnd
    have := (List.nodup_append.mp hnd).2.1
    rw [List.nodup_cons] at this
    exact this.1 (by rw [h2, ← he]; exact List.mem_map_of_mem hy)
  conv => lhs; rw [h1]
  rw [List.reverse_append, List.reverse_cons, List.append_assoc, List.singleton_append]
  have : ∀ P : List ConstantInfo, (∀ y ∈ P, y.name ≠ n) →
      Env.suffixAfter (P ++ x :: (L.take c).reverse) n = (L.take c).reverse := by
    intro P
    induction P with
    | nil => intro _; rw [List.nil_append, Env.suffixAfter_cons, ite_eq_left h2]
    | cons y P ih =>
      intro hP
      rw [List.cons_append, Env.suffixAfter_cons, ite_eq_right (hP y List.mem_cons_self)]
      exact ih (fun z hz => hP z (List.mem_cons_of_mem _ hz))
  rw [this _ (fun y hy => hB y (List.mem_reverse.mp hy))]

/-- **The view of a position is a twin of the fold's index there**, the names so far being
distinct. -/
theorem viewTwin {pre rest : List Declaration} {I : StreamIndex} (hI : IndexSpec (pre ++ rest) I)
    {fe : FEnv} (hfe : fe = mkFEnv (streamEnv pre))
    (hnd : ((recsConsts pre).map (·.name)).Nodup) : Twin fe (I.freeze.view pre.length) := by
  have hcons : (streamEnv pre).consts = (recsConsts pre).reverse := by
    simpa [Env.empty] using streamEnv_consts pre Env.empty
  have htabs : (streamEnv pre).tables = (pre.flatMap declTables).reverse := by
    simpa [Env.empty] using streamEnv_tables pre Env.empty
  subst hfe
  have hview := view_eq hI
  have hve : (I.freeze.view pre.length).env = ⟨[], [], {}⟩ := rfl
  have hvb : (I.freeze.view pre.length).base
      = { I.base with
          below := (recsConsts pre).length, belowRec := pre.length,
          rls := mkRlsGo (streamEnv pre).rules.active, snaps := (streamEnv pre).rules.snaps,
          abs := (streamEnv pre).rules.abstracts, blks := (streamEnv pre).rules.blks,
          blk := blkHead (streamEnv pre).rules.blks } := by
    rw [hview]; rfl
  have hfind_take : ∀ b, b ≤ (recsConsts pre).length → ∀ m,
      ((recsConsts pre).take b).find? (·.name == m)
        = ((recsConsts pre).reverse.drop ((recsConsts pre).length - b)).find? (·.name == m) := by
    intro b hb m
    rw [List.drop_reverse, show (recsConsts pre).length - ((recsConsts pre).length - b) = b by omega]
    exact (find?_reverse_of_nodup (fun ci : ConstantInfo => ci.name) m
      ((List.take_sublist _ _).map _ |>.nodup hnd)).symm
  refine ⟨?_, ?_, rfl, rfl, rfl, by rw [hview]; rfl, fun k => ?_, fun n k => ?_, rfl,
    by rw [hview]; exact hI.chk, ?_, ?_, ?_, fun n k => ?_, by rw [hvb]; rfl, by rw [hvb]; rfl,
    by rw [hvb]; rfl, fun n k => ?_⟩
  · funext n
    rw [mkFEnv_find?, view_find hI, firstOcc_map]
    unfold Env.find?
    rw [hcons]
    exact find?_reverse_of_nodup (fun ci : ConstantInfo => ci.name) n hnd
  · funext T
    rw [mkFEnv_rawTable?, view_rawTable hI, firstTbl_map, recsTables_snd, htabs]
    exact find?_reverse_of_nodup (fun t : ProjTable => t.structName) T ((recsTables_sublist pre).nodup hnd)
  · -- under the `k` newest constants: the first `|R| - k` of the stream
    rw [mkFEnv_dropTop_find, hcons]
    funext m
    unfold FEnv.dropTop
    rw [hve, hvb]
    by_cases hk0 : k = 0
    · subst hk0
      simp only [List.length_nil, Nat.le_refl, ↓reduceIte, List.drop_zero]
      rw [FEnv.find?_ofParts_nil, show mkIdxGo ([] : List ConstantInfo) = ∅ from rfl,
        Std.HashMap.getElem?_empty]
      simp only
      rw [view_base_find hI _ _ _ _ _ _ _ _ (Nat.le_refl _), hfind_take _ (Nat.le_refl _), Nat.sub_self]
      rfl
    · rw [ite_eq_right (by simp; omega), FEnv.find?_ofParts_nil, Std.HashMap.getElem?_empty]
      simp only [List.length_nil, Nat.sub_zero]
      rw [view_base_find hI _ _ _ _ _ _ _ _ (Nat.sub_le _ _)]
      by_cases hk : k ≤ (recsConsts pre).length
      · rw [hfind_take _ (Nat.sub_le _ _), show (recsConsts pre).length -
          ((recsConsts pre).length - k) = k by omega]
      · rw [List.drop_eq_nil_of_le (by simp; omega), show (recsConsts pre).length - k = 0 by omega]
        rfl
  · -- below a name's entry: the stream's constants before it, less `k`
    rw [mkFEnv_below_find, hcons]
    funext m
    unfold FEnv.below
    rw [hve, hvb]
    simp only [List.findIdx?_nil]
    rw [FEnv.find?_ofParts_nil, Std.HashMap.getElem?_empty]
    simp only
    have hidx : I.base.idx[n]? = (firstOcc n 0 (recsConsts pre)).or
        (firstOcc n (recsConsts pre).length (recsConsts rest)) := by
      rw [hI.idx n, show recsConsts (pre ++ rest) = recsConsts pre ++ recsConsts rest by
        simp [recsConsts], firstOcc_append, Nat.zero_add]
    cases hp : firstOcc n 0 (recsConsts pre) with
    | some p =>
      obtain ⟨c, x⟩ := p
      have hc := (firstOcc_ge hp).2
      have hcR : c < (recsConsts pre).length := by omega
      rw [hidx, hp]
      simp only [Option.some_or, hcR, ↓reduceIte]
      rw [view_base_find hI _ _ _ _ _ _ _ _ (Nat.le_trans (Nat.sub_le c k) (Nat.le_of_lt hcR)),
        suffixAfter_reverse hnd hp, List.drop_reverse,
        List.length_take, find?_reverse_of_nodup (fun ci : ConstantInfo => ci.name) m
          ((List.take_sublist _ _).map _ |>.nodup ((List.take_sublist _ _).map _ |>.nodup hnd)),
        List.take_take]
      congr 2
      have : min c (recsConsts pre).length = c := Nat.min_eq_left (Nat.le_of_lt hcR)
      rw [this]
      exact Nat.min_eq_left (Nat.sub_le c k)
    | none =>
      have hnot : Env.suffixAfter (recsConsts pre).reverse n = [] := by
        rw [Env.suffixAfter_eq_findIdx]
        have : (recsConsts pre).reverse.findIdx? (·.name == n) = none := by
          rw [List.findIdx?_eq_none_iff]
          intro y hy
          have := firstOcc_map n (recsConsts pre) 0
          rw [hp] at this
          have hf := (List.find?_eq_none.mp this.symm) y (List.mem_reverse.mp hy)
          simpa using hf
        rw [this]
      rw [hnot, hidx, hp, Option.none_or]
      cases hr : firstOcc n (recsConsts pre).length (recsConsts rest) with
      | none =>
        simp only
        rw [view_base_find hI _ _ _ _ _ _ _ _ (Nat.zero_le _)]
        simp
      | some p =>
        obtain ⟨c, x⟩ := p
        have hge := (firstOcc_ge hr).1
        have hnlt : ¬ c < (recsConsts pre).length := by omega
        simp only [hnlt, ↓reduceIte]
        rw [view_base_find hI _ _ _ _ _ _ _ _ (Nat.zero_le _)]
        simp
  · rw [hvb]
    rfl
  · show 0 + (streamEnv pre).consts.length = (I.freeze.view pre.length).base.below + 0
    rw [hvb, hcons, List.length_reverse]
    simp
  · show (streamEnv pre).rules.snaps ++ ({ rls := mkRlsGo (streamEnv pre).rules.active } : FBase).snaps
      = [] ++ (I.freeze.view pre.length).base.snaps
    rw [hvb]
    simp
  · -- the rule map below a name's entry: the one in force at the cut's counter
    rw [mkFEnv_below_rls, hcons]
    unfold FEnv.below
    rw [hve, hvb]
    simp only [List.findIdx?_nil]
    have hidx : I.base.idx[n]? = (firstOcc n 0 (recsConsts pre)).or
        (firstOcc n (recsConsts pre).length (recsConsts rest)) := by
      rw [hI.idx n, show recsConsts (pre ++ rest) = recsConsts pre ++ recsConsts rest by
        simp [recsConsts], firstOcc_append, Nat.zero_add]
    have hrl : ∀ c, (I.freeze.view pre.length).rlsAt c
        = mkRlsGo (activeAtS (streamEnv pre).rules.snaps c) := fun c => by
      rw [hview]; rfl
    simp only [FEnv.ofParts_base, hrl, Env.cutAt, RuleTable.cut]
    congr 2
    cases hp : firstOcc n 0 (recsConsts pre) with
    | some p =>
      obtain ⟨c, x⟩ := p
      have hc := (firstOcc_ge hp).2
      have hcR : c < (recsConsts pre).length := by omega
      rw [hidx, hp]
      simp only [Option.some_or, hcR, ↓reduceIte]
      rw [suffixAfter_reverse hnd hp, List.length_drop, List.length_reverse, List.length_take,
        Nat.min_eq_left (Nat.le_of_lt hcR)]
    | none =>
      have hnot : Env.suffixAfter (recsConsts pre).reverse n = [] := by
        rw [Env.suffixAfter_eq_findIdx]
        have : (recsConsts pre).reverse.findIdx? (·.name == n) = none := by
          rw [List.findIdx?_eq_none_iff]
          intro y hy
          have := firstOcc_map n (recsConsts pre) 0
          rw [hp] at this
          have hf := (List.find?_eq_none.mp this.symm) y (List.mem_reverse.mp hy)
          simpa using hf
        rw [this]
      rw [hnot, hidx, hp, Option.none_or]
      cases hr : firstOcc n (recsConsts pre).length (recsConsts rest) with
      | none => simp
      | some p =>
        obtain ⟨c, x⟩ := p
        have hge := (firstOcc_ge hr).1
        have hnlt : ¬ c < (recsConsts pre).length := by omega
        simp [hnlt]
  · -- the number of constants below a name's entry: the cut's
    rw [mkFEnv_below_cnt, hcons]
    unfold FEnv.below
    rw [hve, hvb]
    simp only [List.findIdx?_nil, FEnv.cnt, FEnv.ofParts, List.length_nil, Nat.add_zero]
    have hidx : I.base.idx[n]? = (firstOcc n 0 (recsConsts pre)).or
        (firstOcc n (recsConsts pre).length (recsConsts rest)) := by
      rw [hI.idx n, show recsConsts (pre ++ rest) = recsConsts pre ++ recsConsts rest by
        simp [recsConsts], firstOcc_append, Nat.zero_add]
    cases hp : firstOcc n 0 (recsConsts pre) with
    | some p =>
      obtain ⟨c, x⟩ := p
      have hc := (firstOcc_ge hp).2
      have hcR : c < (recsConsts pre).length := by omega
      rw [hidx, hp]
      simp only [Option.some_or, hcR, ↓reduceIte]
      rw [suffixAfter_reverse hnd hp, List.length_drop, List.length_reverse, List.length_take,
        Nat.min_eq_left (Nat.le_of_lt hcR)]
    | none =>
      have hnot : Env.suffixAfter (recsConsts pre).reverse n = [] := by
        rw [Env.suffixAfter_eq_findIdx]
        have : (recsConsts pre).reverse.findIdx? (·.name == n) = none := by
          rw [List.findIdx?_eq_none_iff]
          intro y hy
          have := firstOcc_map n (recsConsts pre) 0
          rw [hp] at this
          have hf := (List.find?_eq_none.mp this.symm) y (List.mem_reverse.mp hy)
          simpa using hf
        rw [this]
      rw [hnot, hidx, hp, Option.none_or]
      cases hr : firstOcc n (recsConsts pre).length (recsConsts rest) with
      | none => simp
      | some p =>
        obtain ⟨c, x⟩ := p
        have hge := (firstOcc_ge hr).1
        have hnlt : ¬ c < (recsConsts pre).length := by omega
        simp [hnlt]

/-! ## The jobs and the fold -/

/-- **Every job passing is an accepting run**, position by position. -/
theorem jobs_run {ds : Array Declaration}
    (h : ∀ k (hk : k < ds.size), recordJob mode pins maxNatSize (buildIndex ds).freeze k ds[k] = .ok ()) :
    ∀ k, k ≤ ds.size → ∃ fe,
      DeclsRun mode pins maxNatSize (ds.toList.take k) (0, mkFEnv Env.empty) (k, fe) ∧
      PushChain Env.empty fe ∧ fe = mkFEnv (streamEnv (ds.toList.take k))
  | 0, _ => ⟨mkFEnv Env.empty, by simpa using DeclsRun.nil _, PushChain.refl _, rfl⟩
  | k + 1, hk => by
    obtain ⟨fe, hrun, hchain, hfe⟩ := jobs_run h k (by omega)
    have hk' : k < ds.size := by omega
    have hkl : (ds.toList.take k).length = k := by simp; omega
    have hsplit : ds.toList.take k ++ ds.toList.drop k = ds.toList := List.take_append_drop k _
    have hI : IndexSpec (ds.toList.take k ++ ds.toList.drop k) (buildIndex ds) := by
      rw [hsplit]; exact buildIndex_spec ds
    have hnd : ((recsConsts (ds.toList.take k)).map (·.name)).Nodup := by
      have hN : NodupNames fe.env := hchain.2.2.1 (by simp [NodupNames, Env.empty])
      have hc : fe.env.consts = (recsConsts (ds.toList.take k)).reverse := by
        rw [hfe]
        show (streamEnv (ds.toList.take k)).consts = _
        simpa [Env.empty] using streamEnv_consts (ds.toList.take k) Env.empty
      unfold NodupNames at hN
      rw [hc, List.map_reverse] at hN
      exact (List.reverse_perm _).nodup_iff.mp hN
    have ht : Twin fe ((buildIndex ds).freeze.view k) := hkl ▸ viewTwin hI hfe hnd
    have hjob := h k hk'
    unfold recordJob at hjob
    split at hjob
    case isFalse => exact nomatch hjob
    rename_i hand
    rcases checkDeclStepC_twin (mode := mode) pins ht ds[k] { maxNatSize := maxNatSize } with
      ⟨e, -, h₂⟩ | ⟨a₁, a₂, s', h₁, h₂, -⟩
    · rw [h₂] at hjob; exact nomatch hjob
    · have hpush := checkDeclStepC_pushes (pins := pins) mode fe ds[k] { maxNatSize := maxNatSize } _ s' h₁
      have hstep : declStep mode pins maxNatSize (k, fe) ds[k] = .ok (k + 1, a₁) := by
        unfold declStep
        simp only [hand, ↓reduceIte, h₁]
      have hL : ds.toList.take (k + 1) = ds.toList.take k ++ [ds[k]] := by
        rw [List.take_add_one]
        simp [Array.getElem?_eq_getElem hk']
      have hchain' := checkDeclStepC_push (pins := pins) mode hchain ds[k] { maxNatSize := maxNatSize } _ s' h₁
      have hfe' : a₁ = mkFEnv (streamEnv (ds.toList.take (k + 1))) := by
        rw [hpush, hfe, stepRules_mkFEnv, pushDelta_mkFEnv, hL]
        congr 1
        simp [streamEnv, List.foldl_append]
      refine ⟨_, ?_, hchain', hfe'⟩
      rw [hL]; exact hrun.snoc mode hstep

/-- **Every job passing is an accept of the fold**, at the environment the records denote. -/
theorem checkDecls_of_jobs {ds : Array Declaration}
    (h : ∀ k (hk : k < ds.size), recordJob mode pins maxNatSize (buildIndex ds).freeze k ds[k] = .ok ()) :
    checkDecls mode pins maxNatSize ds = .ok (streamEnv ds.toList) := by
  obtain ⟨fe, hrun, -, hfe⟩ := jobs_run h ds.size (Nat.le_refl _)
  rw [List.take_of_length_le (by simp)] at hrun hfe
  rw [checkDecls_of_run mode hrun, hfe]
  rfl

end ConLeche.Cached
