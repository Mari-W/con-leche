/- The rewrite-rule e2e fixtures `tests/e2e/rewrite_rule_level_*.ndjson`, exported with the rr-dev
   toolchain:

       lean +rr-dev -o RrLevel.olean RrLevel.lean
       LEAN_PATH=.:<rr-dev>/lib/lean leanexport RrLevel -- lvl_inst > lvl_inst.ndjson
       LEAN_PATH=.:<rr-dev>/lib/lean leanexport RrLevel -- lvlSwapTgt lvl_swap > lvl_swap.ndjson
       python3 -I scripts/rewrite-fixtures/mk.py level lvl_inst.ndjson lvl_swap.ndjson tests/e2e

   The official kernel simplifies a level when it instantiates level parameters (`mk_max`:
   `max u 0` is `u`), and its matcher compares levels as they are then.  `lvl_inst` unfolds
   `lift.{u, 0}`, whose value is `Box.mk.{max a b}`, to `Box.mk.{u}` there, so `H_mk`'s pattern
   `H.{l} n (Box.mk.{l} y)` matches with `l := u` after the retry on whnf.  `mk.py level` gives
   `lvl_swap` the statement of `lvlSwapTgt`: `H.{max a b}` against `Box.mk.{max b a}`, levels of
   the same value that the official kernel does not simplify into each other. The proof stays
   `trivial`, so the declaration is rejected whether or not the rule fires (`RrLevelEq.lean` has
   the same match with an `rfl` proof). -/
universe u v

structure Box (α : Type u) : Type u where
  val : α

def lift.{a, b} (α : Type b) (x : α) : Box.{max b a} (ULift.{a} α) := ⟨⟨x⟩⟩

def H.{l} (n : Nat) {β : Type l} (_b : Box.{l} β) : Nat := Nat.rec 0 (fun _ ih => ih + 1) n

@[rewrite] theorem H_mk.{l} (n : Nat) (β : Type l) (y : β) : H.{l} n (Box.mk.{l} y) = n := by
  induction n with
  | zero => rfl
  | succ k ih => exact congrArg Nat.succ ih

rewrite_rules H_mk in
theorem lvl_inst (n : Nat) : H.{u} n (lift.{u, 0} PUnit PUnit.unit) = n := rfl

set_option linter.checkUnivs false in
def lvlSwapTgt.{a, b} (n : Nat) (β : Type (max a b)) (y : β) : Prop :=
  H.{max a b} n (@Box.mk.{max b a} β y) = n

set_option linter.checkUnivs false in
rewrite_rules H_mk in
theorem lvl_swap.{a, b} (_n : Nat) (β : Type (max a b)) (_y : β) : True := trivial
