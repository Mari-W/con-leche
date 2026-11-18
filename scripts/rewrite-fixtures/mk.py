"""The rewrite-rule e2e fixtures (tests/e2e/rewrite_rule_*.ndjson), from a lean4export stream.

lean4export at v4.35.0 writes no rule records yet, so the fixtures are the export of
`RrBase.lean` with the records a 3.2.0 export would add written in by hand
(`notes/format.md`): `rewrite` lines after the theorems, and a `rewrites` field on `rr_use`,
whose value is replaced by `fun n g => g 0` (it types only when `rrT n` reduces to a function
type, which no unfolding of `rrT` gives at a variable `n`).

    elan run leanprover/lean4:v4.35.0 lean -o RrBase.olean RrBase.lean
    LEAN_PATH=.:<lean4export LEAN_PATH> lean4export RrBase -- rr_use rrT_pi rrT_refl rrT_succ \
      > tests/e2e/rewrite_rule_base.ndjson
    python3 -I scripts/rewrite-fixtures/mk.py tests/e2e/rewrite_rule_base.ndjson tests/e2e
"""
import json, sys

def stmt_patch(src, out, pairs):
    """Give each theorem in `pairs` (theorem, definition) the statement the definition's value
    states: its leading lambdas become the theorem's binders.  The theorem keeps its proof, so
    the record is the false declaration the fixture wants rejected."""
    recs = [json.loads(l) for l in open(src).read().splitlines()]
    names = {r["in"]: r for r in recs if "in" in r}
    exprs = {r["ie"]: r for r in recs if "ie" in r}
    def nid(s):
        for k, r in names.items():
            if r.get("str", {}).get("str") == s and r["str"]["pre"] == 0: return k
        raise KeyError(s)
    nxt = max(exprs) + 1
    new = []
    for thm, dfn in pairs:
        T, D = nid(thm), nid(dfn)
        d = next(r["def"] for r in recs if "def" in r and r["def"]["name"] == D)
        v = exprs[d["value"]]; lams = []
        while "lam" in v:
            lams.append(v["lam"]); v = exprs[v["lam"]["body"]]
        ty = v["ie"]
        for l in reversed(lams):
            ty_r = {"forallE": {"name": l["name"], "type": l["type"], "body": ty,
                                "binderInfo": l["binderInfo"]}, "ie": nxt}
            new.append(ty_r); ty = nxt; nxt += 1
        t = next(r["thm"] for r in recs if "thm" in r and r["thm"]["name"] == T)
        t["type"] = ty
    J = lambda r: json.dumps(r, separators=(",", ":"))
    # the new types go right before the first patched theorem, after everything they mention
    i = min(i for i, r in enumerate(recs) if "thm" in r and r["thm"]["name"] in {nid(t) for t, _ in pairs})
    lines = [J(r) for r in recs[:i]] + [J(r) for r in new] + [J(r) for r in recs[i:]]
    open(out, "w").write("\n".join(lines) + "\n")

if sys.argv[1] == "match":
    # RrMatch.lean: the non-linear rule at two different arguments, which does not fire
    stmt_patch(sys.argv[2], f"{sys.argv[3]}/rewrite_rule_nonlinear_diff.ndjson", [("nl_diff", "nlDiffTgt")])
    sys.exit(0)

if sys.argv[1] == "loop":
    # RrLoop.lean: a rule whose right side unfolds back to its left side, in a false conversion
    stmt_patch(sys.argv[2], f"{sys.argv[3]}/rewrite_rule_decl_budget.ndjson", [("loopBad", "loopTgt")])
    sys.exit(0)

src, outdir = sys.argv[1], sys.argv[2]
recs = [json.loads(l) for l in open(src).read().splitlines()]
names = {r["in"]: r for r in recs if "in" in r}
exprs = {r["ie"]: r for r in recs if "ie" in r}
def nid(s):
    for k, r in names.items():
        if r.get("str", {}).get("str") == s and r["str"]["pre"] == 0: return k
    raise KeyError(s)
T, EQ, PI, REFL, SUCC, USE, FN = (nid(x) for x in ["rrT", "rrT_eq", "rrT_pi", "rrT_refl", "rrT_succ", "rr_use", "rrFn"])
use_i = next(i for i, r in enumerate(recs) if "def" in r and r["def"]["name"] == USE)
use = recs[use_i]["def"]
nxt = max(exprs) + 1
new = []
t = exprs[use["type"]]
doms = []
while "forallE" in t:
    doms.append(t["forallE"]); t = exprs[t["forallE"]["body"]]
def add(r):
    global nxt
    r = dict(r); r["ie"] = nxt; new.append(r); nxt += 1; return nxt - 1
b0 = add({"bvar": 0}); z = add({"natVal": "0"}); body = add({"app": {"fn": b0, "arg": z}})
for d in reversed(doms):
    body = add({"lam": {"name": d["name"], "type": d["type"], "body": body, "binderInfo": "default"}})
# the conversion variant: `rr_use : (n : Nat) → rrT n → B := fun n g => g`, which types only when
# the definitional-equality check turns `rrT n` into `B` (`rrFn`, or `Nat → Nat`)
base_new = list(new)
NAT = nid("Nat")
natc = add({"const": {"name": NAT, "us": []}})
fnc = add({"const": {"name": FN, "us": []}})
pic = add({"forallE": {"name": doms[0]["name"], "type": natc, "body": natc, "binderInfo": "default"}})
def conv(B):
    ty = B
    for d in reversed(doms):
        ty = add({"forallE": {"name": d["name"], "type": d["type"], "body": ty, "binderInfo": "default"}})
    v = b0
    for d in reversed(doms):
        v = add({"lam": {"name": d["name"], "type": d["type"], "body": v, "binderInfo": "default"}})
    return ty, v
conv_fn = conv(fnc)
conv_pi = conv(pic)
J = lambda r: json.dumps(r, separators=(",", ":"))
def emit(name, rules, scope, kind=None):
    out = [J(r) for r in recs[:use_i] + recs[use_i + 1:]] + \
        [J(r) for r in (base_new if kind is None else new)]
    for (t_, h_, p_) in rules:
        out.append(J({"rewrite": {"name": t_, "head": h_, "prio": p_}}))
    u = dict(use); u["value"] = body
    if kind is not None: u["type"], u["value"] = kind
    if scope: u["rewrites"] = scope
    out.append(J({"def": u}))
    open(f"{outdir}/{name}.ndjson", "w").write("\n".join(out) + "\n")
emit("rewrite_rule_accept", [(EQ, T, 1000)], [EQ])
emit("rewrite_rule_omitted", [(EQ, T, 1000)], None)
emit("rewrite_rule_priority", [(EQ, T, 2000), (REFL, T, 1000)], [EQ, REFL])
emit("rewrite_rule_priority_loop", [(EQ, T, 1000), (REFL, T, 2000)], [EQ, REFL])
emit("rewrite_rule_bad_head", [(EQ, FN, 1000)], [EQ])
emit("rewrite_rule_not_thm", [(FN, FN, 1000)], [FN])
emit("rewrite_rule_pi", [(PI, T, 1000)], [PI])
emit("rewrite_rule_unregistered", [], [EQ])
emit("rewrite_rule_conv", [(EQ, T, 1000)], [EQ], conv_fn)
emit("rewrite_rule_conv_omitted", [(EQ, T, 1000)], None, conv_fn)
emit("rewrite_rule_pi_conv", [(PI, T, 1000)], [PI], conv_pi)
