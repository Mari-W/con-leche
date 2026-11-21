/- The rewrite-rule e2e fixtures `tests/e2e/rewrite_rule_pre_*.ndjson`: rules marked to fire
   before their head unfolds (`@[rewrite ↓]`), mirroring lean4 tests/elab/rewriteRulesBeforeDelta.lean.
   Exported with the rr-dev toolchain, one export per theorem, and patched by `mk.py pre`:
       lean +rr-dev -o RrPre.olean RrPre.lean
       LEAN_PATH=.:<rr-dev>/lib/lean leanexport RrPre -- <theorem> > <theorem>.ndjson
       python3 -I scripts/rewrite-fixtures/mk.py pre <dir of the exports> tests/e2e
   Accepted: `pre_f` (a marked rule fires where unfolding gives a value), `pre_same` (the same head
   on both sides fires on both), `pre_key` (a constructor key reduces its argument first),
   `pre_lit` (a `Nat` literal at a `Nat.zero` key), `pre_cond` (a key argument that computes),
   `pre_foldr` and `pre_foldr_map` (a list fold, every step a firing), `pre_prio` (the marked
   rule fires before the unmarked one of higher priority gets a turn).  `mk.py` gives `pre_unmarked`
   and `pre_nonkey` the false statements of `unmarkedTgt` and `nonkeyTgt`, which only a firing
   would make true: an unmarked rule waits for a stuck unfolding, and `!false` at a position that
   is not the key is not reduced.  `pre_loop` gets the statement of `loopTgt`, where two marked
   rules fire into each other until the budget of 2^24 firings per declaration stops them. -/

def f (l : List Nat) : List Nat × Nat := (l ++ [], 0)
@[rewrite ↓] theorem f_eq (l : List Nat) : f l = (l, 0) := by simp [f]
rewrite_rules f_eq in
theorem pre_f : ∀ l, f l = (l, 0) := fun _ => rfl

def f' (l : List Nat) : List Nat × Nat := (l ++ [], 0)
@[rewrite] theorem f'_eq (l : List Nat) : f' l = (l, 0) := by simp [f']
def unmarkedTgt : Prop := ∀ l, f' l = (l, 0)
rewrite_rules f'_eq in
theorem pre_unmarked : ∀ l, f' l = f' l := fun _ => rfl

def p (_ : Bool) (l : List Nat) : List Nat × Nat := (l ++ [], 0)
@[rewrite ↓] theorem p_true (l : List Nat) : p true l = (l, 0) := by simp [p]
rewrite_rules p_true in
theorem pre_same : ∀ l, p true l = p false l := fun _ => rfl
rewrite_rules p_true in
theorem pre_key : ∀ l, p (!false) l = (l, 0) := fun _ => rfl

def p2 (_ _ : Bool) (l : List Nat) : List Nat × Nat := (l ++ [], 0)
@[rewrite ↓] theorem p2_tt (l : List Nat) : p2 true true l = (l, 0) := by simp [p2]
def nonkeyTgt : Prop := ∀ l, p2 true (!false) l = (l, 0)
rewrite_rules p2_tt in
theorem pre_nonkey : ∀ l, p2 true (!false) l = p2 true (!false) l := fun _ => rfl

def z : Nat → List Nat → List Nat × Nat
  | 0, l => (l ++ [], 0)
  | _ + 1, _ => ([], 1)
@[rewrite ↓] theorem z_zero (l : List Nat) : z .zero l = (l, 0) := by simp [z]
rewrite_rules z_zero in
theorem pre_lit : ∀ l, z (id 0) l = (l, 0) := fun _ => rfl

def isTrue (_ : List Nat) : Bool := true
@[rewrite ↓] theorem cond_tt {α : Type} (a b : α) : cond true a b = a := rfl
rewrite_rules cond_tt in
theorem pre_cond : ∀ l, cond (isTrue l) l [] = l := fun _ => rfl

def two (n : Nat) : List Nat := [n, n]
@[rewrite ↓] theorem foldr_nil' {α β : Type} (f : α → β → β) (i : β) :
    List.foldr f i [] = i := rfl
@[rewrite ↓] theorem foldr_cons' {α β : Type} (f : α → β → β) (i : β) (a : α) (l : List α) :
    List.foldr f i (a :: l) = f a (List.foldr f i l) := rfl
rewrite_rules foldr_nil' foldr_cons' in
theorem pre_foldr : ∀ (f : Nat → Nat → Nat) n, List.foldr f 0 (two n) = f n (f n 0) :=
  fun _ _ => rfl
rewrite_rules foldr_nil' foldr_cons' in
theorem pre_foldr_map : List.foldr (· + ·) 0 (List.map (· * 2) [1, 2, 3]) = 12 := rfl

def q (l : List Nat) : List Nat := l ++ []
@[rewrite ↓ 100] theorem q_id (l : List Nat) : q l = l := List.append_nil l
@[rewrite 2000] theorem q_def (l : List Nat) : q l = l ++ [] := rfl
rewrite_rules q_id q_def in
theorem pre_prio : ∀ l, q l = l := fun _ => rfl

def loopA (n : Nat) : Nat := n
def loopB (n : Nat) : Nat := n
@[rewrite ↓] theorem loopA_B (n : Nat) : loopA n = loopB n := rfl
@[rewrite ↓] theorem loopB_A (n : Nat) : loopB n = loopA n := rfl
def loopTgt : Prop := loopA 0 = 0
theorem pre_loop : loopA 0 = loopA 0 := rfl
