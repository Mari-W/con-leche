/- The abstract-definition e2e fixtures `tests/e2e/abstract_block_*.ndjson`, after lean4's
   `tests/elab/abstractBlock.lean`.  Exported with the rr-dev toolchain, one export per theorem
   (the theorem and its dependencies):

       lean +rr-dev -o RrAbstract.olean RrAbstract.lean
       LEAN_PATH=.:<rr-dev>/lib/lean leanexport RrAbstract -- double_two > member.ndjson
       LEAN_PATH=.:<rr-dev>/lib/lean leanexport RrAbstract -- outTgt abs_out > out.ndjson
       LEAN_PATH=.:<rr-dev>/lib/lean leanexport RrAbstract -- abs_rules > rules.ndjson
       LEAN_PATH=.:<rr-dev>/lib/lean leanexport RrAbstract -- abs_zero > zero.ndjson
       python3 -I scripts/rewrite-fixtures/mk.py abstract member.ndjson out.ndjson rules.ndjson \
         zero.ndjson tests/e2e

   `double` is abstract after its block.  `double_two` is a member and unfolds it.  `abs_out`
   is outside the block and needs the body: the elaborator rejects `double 3 = 6` by `rfl`, so
   it is stated `6 = 6` and `mk.py abstract` gives it the statement of `outTgt`.  `abs_rules`
   proves the same under `double`'s rules, which fire at the stuck head, and `abs_zero` fires
   `double_zero` at `double .zero` directly.  `mk.py abstract` also writes the member with its
   name dropped from the member list, an abstract line naming a theorem, and one before its
   definition. -/
abstract_block

def double (n : Nat) : Nat := n + n

theorem double_two : double 2 = 4 := rfl

@[rewrite] theorem double_zero : double .zero = .zero := rfl

@[rewrite] theorem double_succ (n : Nat) : double n.succ = (double n).succ.succ := by
  unfold double; omega

end

def outTgt : Prop := double 3 = 6

theorem abs_out : 6 = 6 := rfl

rewrite_rules double_zero double_succ in
theorem abs_rules : double 3 = 6 := rfl

rewrite_rules double_zero in
theorem abs_zero : double .zero = .zero := rfl
