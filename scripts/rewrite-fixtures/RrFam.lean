/- The rewrite-rule e2e fixture `tests/e2e/rewrite_rule_family.ndjson`, exported with the
   rr-dev toolchain (Lean with rewrite rules, lean4export 3.2.0 records):

       lean +rr-dev -o RrFam.olean RrFam.lean
       LEAN_PATH=.:<rr-dev>/lib/lean leanexport RrFam -- famUse Box boxUse \
         > tests/e2e/rewrite_rule_family.ndjson

   `Fam` is a family stored at a definition (`Code`), checked under `code_eq`; `Box` reads its
   telescope below its block under another rule set (`code_eq`, `code_eq2`). -/
def Code : Type 1 := Nat → Type
@[rewrite] theorem code_eq : Code = (Nat → Type) := rfl
@[rewrite] theorem code_eq2 : Code = (Nat → Type) := rfl

rewrite_rules code_eq in
inductive Fam : Code
  | mk : Fam 0

rewrite_rules code_eq in
noncomputable def famUse (x : Fam 0) : Nat := Fam.rec 7 x

set_option genSizeOf false in
rewrite_rules code_eq2 in
inductive Box : Type
  | mk : Fam 0 → Box

noncomputable def boxUse (b : Box) : Nat := Box.rec (fun x => famUse x) b
