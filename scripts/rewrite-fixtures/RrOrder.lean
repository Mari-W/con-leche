/- The rewrite-rule e2e fixtures `tests/e2e/rewrite_rule_order_*.ndjson`: the reduction order,
   δ first and a rule on a definition only where its unfolding gets stuck.  Exported with the
   rr-dev toolchain, one export per theorem (the theorem and its dependencies):

       lean +rr-dev -o RrOrder.olean RrOrder.lean
       LEAN_PATH=.:<rr-dev>/lib/lean leanexport RrOrder -- swap_val > swap.ndjson
       LEAN_PATH=.:<rr-dev>/lib/lean leanexport RrOrder -- stuck > stuck.ndjson
       LEAN_PATH=.:<rr-dev>/lib/lean leanexport RrOrder -- catNilTgt cat_nil' > cat.ndjson
       python3 -I scripts/rewrite-fixtures/mk.py order swap.ndjson stuck.ndjson cat.ndjson tests/e2e

   `swap_val` holds by δ alone.  Its rule `swap_loop` restates `swap (a, b)` with `swap` again
   on the right, so a rule that fired before δ would loop until the firing budget.  `stuck` is
   `∀ n, 0 + n = n` by `rfl`: `+` recurses on its second argument, so unfolding `0 + n` gets
   stuck on `n` and the rule `zero_add'` fires there.  `mk.py order` also writes it without its
   rule list, which the checker rejects.  `cat_nil'` is the global rule's case: `cat xs []`
   unfolds to a recursor stuck on `xs`, and the global rule `cat_nil` fires.  The elaborator
   does not fire the global rule there, so `cat_nil'` is stated `xs = xs` and `mk.py order`
   gives it the statement of `catNilTgt`. -/
def swap (p : Nat × Nat) : Nat × Nat := (p.2, p.1)

@[rewrite] theorem swap_loop (a b : Nat) : swap (a, b) = swap (swap (b, a)) := rfl

rewrite_rules swap_loop in
theorem swap_val : swap (1, 2) = (2, 1) := rfl

@[rewrite] theorem zero_add' (n : Nat) : Nat.zero + n = n := Nat.zero_add n

rewrite_rules zero_add' in
theorem stuck : ∀ n : Nat, 0 + n = n := fun _ => rfl

def cat : List Nat → List Nat → List Nat
  | [], ys => ys
  | x :: xs, ys => x :: cat xs ys

theorem cat_nil (xs : List Nat) : cat xs [] = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => exact congrArg (x :: ·) ih

attribute [global_rewrite] cat_nil

def catNilTgt (xs : List Nat) : Prop := cat xs [] = xs

theorem cat_nil' (xs : List Nat) : xs = xs := rfl
