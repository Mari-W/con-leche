/- The rewrite-rule e2e fixture `tests/e2e/rewrite_rule_decl_budget.ndjson`, exported with the
   rr-dev toolchain and patched by `mk.py loop`:

       lean +rr-dev -o RrLoop.olean RrLoop.lean
       LEAN_PATH=.:<rr-dev>/lib/lean leanexport RrLoop -- loopTgt loopBad > loop.ndjson
       python3 -I scripts/rewrite-fixtures/mk.py loop loop.ndjson tests/e2e

   `op_apply` rewrites `o.op a` to `apply' o a`, whose δ step gives `o.op a` back.  `mk.py` gives
   `loopBad` the statement of `loopTgt`, the false `o.op a = o.op (a + 1)`, so its `rfl` sends
   the definitional-equality check around the cycle firing, then lazy δ.  Each `whnfCore` call
   fires once, so only the per-declaration budget stops it. -/
structure Op where
  op : Nat → Nat

def apply' (o : Op) (a : Nat) : Nat := o.op a

@[rewrite] theorem op_apply (o : Op) (a : Nat) : o.op a = apply' o a := rfl

def loopTgt (o : Op) (a : Nat) : Prop := o.op a = o.op (a + 1)

rewrite_rules op_apply in
theorem loopBad (o : Op) (a : Nat) : o.op a = o.op a := rfl
