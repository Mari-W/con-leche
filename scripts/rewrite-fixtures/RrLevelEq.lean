/- The rewrite-rule e2e fixtures `tests/e2e/rewrite_rule_level_equiv*.ndjson`, exported with the
   lean4 fork at branch `fix-round` (21fd9d17c6), whose elaborator and kernel compare a repeated
   rule level parameter up to level equivalence:

       lean -o RrLevelEq.olean RrLevelEq.lean
       LEAN_PATH=.:<fix-round>/lib/lean leanexport RrLevelEq -- lvl_equiv > lvl_equiv.ndjson
       python3 -I scripts/rewrite-fixtures/mk.py leveleq lvl_equiv.ndjson tests/e2e

   `H_mk`'s pattern `H.{l} n (Box.mk.{l} y)` binds `l := max a b` at `H` and meets
   `Box.mk.{max b a}`, the same value in another form, so the rule fires and `lvl_equiv` holds by
   `rfl`.  `mk.py leveleq` also writes the same theorem with no rule in force, which is rejected. -/
universe u v

structure Box (α : Type u) : Type u where
  val : α

def H.{l} (n : Nat) {β : Type l} (_b : Box.{l} β) : Nat := Nat.rec 0 (fun _ ih => ih + 1) n

@[rewrite] theorem H_mk.{l} (n : Nat) (β : Type l) (y : β) : H.{l} n (Box.mk.{l} y) = n := by
  induction n with
  | zero => rfl
  | succ k ih => exact congrArg Nat.succ ih

set_option linter.checkUnivs false in
rewrite_rules H_mk in
theorem lvl_equiv.{a, b} (n : Nat) (β : Type (max a b)) (y : β) :
    H.{max a b} n (@Box.mk.{max b a} β y) = n := rfl
