/- The rewrite-rule e2e fixtures `tests/e2e/rewrite_rule_prio_*.ndjson`: the order in which the
   rules of one head fire, and the rules firing again on their own reduct.  Exported with the
   rr-dev toolchain, one export per theorem (the theorem and its dependencies):

       lean +rr-dev -o RrPrio.olean RrPrio.lean
       LEAN_PATH=.:<rr-dev>/lib/lean leanexport RrPrio -- <theorem> > <theorem>.ndjson
       python3 -I scripts/rewrite-fixtures/mk.py prio <dir of the exports> tests/e2e

   The Lean kernel tries the rules of a head highest priority first, then by name, each against
   the prefix of the application its left side has the arity of, and fires the first that
   matches.  `fa_one` and `fa_two` overlap at `fa 0 0` and disagree, so the order decides:
   `arity_hi` holds where the arity-2 rule of higher priority fires first, `arity_lo` where the
   arity-1 rule has the higher priority.  `prio_name` holds where `pk_b` beats `pk_a` by
   priority although `pk_a` comes first by name, `name_order` where equal priorities fall back
   to the name.  `refire` holds where a firing tries the rules again on its reduct before ι:
   `hh n` rewrites to a `Bx.rec` redex, and the rule `bx_tt` on `Bx.rec` fires there before ι.
   `iota_first` is the same redex written out, where ι comes first.  `prefix` holds where a rule
   of arity 1 fires on a stuck unfolding of a definition applied to two arguments.  `exposure`
   holds where β at a prefix exposes `fa 0` with an argument left over, and the head
   normalization continues on the whole spine `fa 0 b`, so `fa_two` fires.  The heads
   are abstract, so their rules fire at once, and each pair of overlapping rules ends in two
   terms that are equal but not convertible at a variable (`n` and `0 + n`). -/
abstract_block

def fa (_a b : Nat) : Nat := b
@[rewrite 10] theorem fa_one (a : Nat) : fa a = fun b => b := rfl
@[rewrite 2000] theorem fa_two (a b : Nat) : fa a b = 0 + b := (Nat.zero_add b).symm

def gb (_a b : Nat) : Nat := b
@[rewrite 2000] theorem gb_one (a : Nat) : gb a = fun b => b := rfl
@[rewrite 10] theorem gb_two (a b : Nat) : gb a b = 0 + b := (Nat.zero_add b).symm

def pk (n : Nat) : Nat := n
@[rewrite 10] theorem pk_a (n : Nat) : pk n = n := rfl
@[rewrite 2000] theorem pk_b (n : Nat) : pk n = 0 + n := (Nat.zero_add n).symm

def pn (n : Nat) : Nat := n
@[rewrite] theorem pn_a (n : Nat) : pn n = n := rfl
@[rewrite] theorem pn_b (n : Nat) : pn n = 0 + n := (Nat.zero_add n).symm

end

rewrite_rules fa_one fa_two in
theorem arity_hi : ∀ b, fa 0 b = 0 + b := fun _ => rfl

rewrite_rules gb_one gb_two in
theorem arity_lo : ∀ b, gb 0 b = b := fun _ => rfl

rewrite_rules pk_a pk_b in
theorem prio_name : ∀ n, pk n = 0 + n := fun _ => rfl

rewrite_rules pn_a pn_b in
theorem name_order : ∀ n, pn n = n := fun _ => rfl

inductive Bx where
  | tt
  | ff

def BxNat : Bx → Type := fun _ => Nat

@[rewrite] theorem bx_tt (a b : Nat) : @Bx.rec BxNat a b Bx.tt = (0 + a : Nat) :=
  (Nat.zero_add a).symm

abstract_block

def hh (n : Nat) : Nat := n
@[rewrite] theorem h_rec (n : Nat) : hh n = @Bx.rec BxNat n n Bx.tt := rfl

end

rewrite_rules h_rec bx_tt in
theorem refire : ∀ n, hh n = 0 + n := fun _ => rfl

rewrite_rules h_rec bx_tt in
theorem iota_first : ∀ n, @Bx.rec BxNat n n Bx.tt = n := fun _ => rfl

def d : Nat → Nat → Nat
  | 0, m => m
  | n + 1, m => d n m

@[rewrite] theorem d_one (n : Nat) : d n = fun m => m := by
  funext m; induction n with
  | zero => rfl
  | succ n ih => exact ih

rewrite_rules d_one in
theorem «prefix» : ∀ n, d n 5 = 5 := fun _ => rfl

rewrite_rules fa_one fa_two in
theorem exposure : ∀ b, (fun x => fa x) 0 b = 0 + b := fun _ => rfl
