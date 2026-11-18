/- The rewrite-rule e2e fixtures `tests/e2e/rewrite_rule_match_*.ndjson` and
   `tests/e2e/rewrite_rule_nonlinear_*.ndjson`, exported with the rr-dev toolchain, one export
   per theorem (the theorem and its dependencies):

       lean +rr-dev -o RrMatch.olean RrMatch.lean
       LEAN_PATH=.:<rr-dev>/lib/lean leanexport RrMatch -- <theorem> > <fixture>.ndjson
       LEAN_PATH=.:<rr-dev>/lib/lean leanexport RrMatch -- nlDiffTgt nl_diff > nl_diff.ndjson
       python3 -I scripts/rewrite-fixtures/mk.py match nl_diff.ndjson tests/e2e

   `lit_zero`, `lit_succ`, `whnf_delta` and `whnf_iota` need a pattern position matched up to
   whnf: a raw literal against `Nat.zero`/`Nat.succ m`, a δ step and an ι step on the argument.
   `nl_syn` and `nl_defeq` need the non-linear rule `myEq_self`, its two arguments syntactically
   equal and definitionally equal.  `mk.py match` gives `nl_diff` the statement of `nlDiffTgt`,
   whose two arguments differ, so the rule does not fire. -/
def myAdd : Nat → Nat → Nat
  | n, .zero => n
  | n, .succ m => .succ (myAdd n m)

@[rewrite] theorem myAdd_zero_left (n : Nat) : myAdd Nat.zero n = n := by
  induction n with
  | zero => rfl
  | succ m ih => exact congrArg Nat.succ ih

@[rewrite] theorem myAdd_succ_left (m n : Nat) : myAdd (Nat.succ m) n = Nat.succ (myAdd m n) := by
  induction n with
  | zero => rfl
  | succ k ih => exact congrArg Nat.succ ih

def zero' : Nat := Nat.zero

rewrite_rules myAdd_zero_left in
theorem lit_zero (n : Nat) : myAdd (nat_lit 0) n = n := rfl

rewrite_rules myAdd_succ_left in
theorem lit_succ (n : Nat) : myAdd (nat_lit 3) n = Nat.succ (myAdd (nat_lit 2) n) := rfl

rewrite_rules myAdd_zero_left in
theorem whnf_delta (n : Nat) : myAdd zero' n = n := rfl

rewrite_rules myAdd_zero_left in
theorem whnf_iota (n : Nat) : myAdd (@Bool.rec (fun _ => Nat) Nat.zero Nat.zero true) n = n := rfl

def myEq (a b : Nat) : Bool := Nat.beq a b

@[rewrite] theorem myEq_self (n : Nat) : myEq n n = true := Nat.beq_refl n

rewrite_rules myEq_self in
theorem nl_syn (k : Nat) : myEq k k = true := rfl

rewrite_rules myEq_self in
theorem nl_defeq (k : Nat) : myEq k (id k) = true := rfl

def nlDiffTgt (k m : Nat) : Prop := myEq k m = true

rewrite_rules myEq_self in
theorem nl_diff (k _m : Nat) : myEq k k = true := rfl
