module

public import ConLeche
public import ConLeche.Cached.Decls
/- The `#guard`s below are EVALUATED, so the constants they name have to
be reachable from meta code too; a module needed at both levels is
imported twice. -/
meta import ConLeche
meta import ConLeche.Cached.Decls

public section

/-!
# User rewrite rules, unit tests

A hand-built environment registers stored theorems as rewrite rules (`Env.rules`). The guards
check one declaration against it with both checkers, the pure one (`checkDecl` at `pureOps`) and
the cached one (`declStep` at the environment's index). The rule `code = Fn` with
`Fn := T → T` makes `code` a function type for `whnf`, so `g a` with `g : code` types. An
argument of the wrong type stays rejected, a rule whose sides have different types never fires,
and a rule that rewrites a term to itself exhausts the firing budget.
-/

namespace ConLecheTests.Rewrite

open ConLeche

@[expose] def nm (s : String) : Name := .str .anonymous s
@[expose] def ty0 : Expr := .sort (.succ .zero)
@[expose] def cT : Expr := .const (nm "T") []
@[expose] def cCode : Expr := .const (nm "code") []
@[expose] def cG : Expr := .const (nm "g") []
@[expose] def cA : Expr := .const (nm "a") []
@[expose] def cFn : Expr := .const (nm "Fn") []
/-- `@Eq.{2} Type l r`. -/
@[expose] def eqTy (l r : Expr) : Expr :=
  .app (.app (.app (.const eqName [.succ (.succ .zero)]) ty0) l) r

/-- `Eq`, a type `T` with an inhabitant `a`, the definition `Fn := T → T`, a type `code` with an
inhabitant `g`, and four stored theorems, `code_eq : code = Fn`, `code_bad : code = a` (whose
right side is no type), `code_refl : code = code` and `code_vac : ∀ x : T, code = Fn` (whose
binder the left side does not bind). -/
@[expose] def baseConsts : List ConstantInfo := [
  .thmInfo ⟨nm "code_vac", [], .forallE cT (eqTy cCode cFn)⟩,
  .thmInfo ⟨nm "code_refl", [], eqTy cCode cCode⟩,
  .thmInfo ⟨nm "code_bad", [], eqTy cCode cA⟩,
  .thmInfo ⟨nm "code_eq", [], eqTy cCode cFn⟩,
  .defnInfo ⟨nm "Fn", [], ty0⟩ (.forallE cT cT) .opaque,
  .axiomInfo ⟨nm "g", [], cCode⟩,
  .axiomInfo ⟨nm "code", [], ty0⟩,
  .axiomInfo ⟨nm "a", [], cT⟩,
  .axiomInfo ⟨nm "T", [], ty0⟩,
  .indInfo ⟨eqName, [nm "u"], .forallE (.sort (.param (nm "u")))
    (.forallE (.bvar 0) (.forallE (.bvar 1) (.sort .zero)))⟩ {}]

/-- The environment with the given rules (head, theorem). -/
@[expose] def envR (rs : List (Name × Name)) : Env := ⟨baseConsts, [], { active := rs }⟩

@[expose] def pureRun (rs : List (Name × Name)) (d : Declaration) : Except CheckError Env :=
  checkDecl .verified (pureOps .verified) [] (envR rs) d

@[expose] def cachedRun (rs : List (Name × Name)) (d : Declaration) :
    Except (CheckError × Nat) (Nat × FEnv) :=
  Cached.declStep .verified [] 1024 (0, mkFEnv (envR rs)) d

/-- `y : T := g a`. -/
@[expose] def declY : Declaration := .defnDecl ⟨nm "y", [], cT⟩ (.app cG cA) .opaque
/-- `z : T := g T`, whose argument is a type and no inhabitant of `T`. -/
@[expose] def declZ : Declaration := .defnDecl ⟨nm "z", [], cT⟩ (.app cG cT) .opaque

/-- The verdict's error message, or `"ok"`. -/
@[expose] def verdict {α ε : Type} (msg : ε → CheckError) : Except ε α → String
  | .ok _ => "ok"
  | .error e => match msg e with
    | .invalid m => m
    | _ => "other"

@[expose] def pureV (rs : List (Name × Name)) (d : Declaration) : String :=
  verdict id (pureRun rs d)

@[expose] def cachedV (rs : List (Name × Name)) (d : Declaration) : String :=
  verdict (·.1) (cachedRun rs d)

-- the rule fires: `g a` types at `T`
#guard pureV [(nm "code", nm "code_eq")] declY == "ok"
#guard cachedV [(nm "code", nm "code_eq")] declY == "ok"
-- without the rule `code` is no function type
#guard pureV [] declY == "function expected"
#guard cachedV [] declY == "function expected"
-- an ill-typed argument stays rejected under the rule
#guard pureV [(nm "code", nm "code_eq")] declZ == "application type mismatch"
#guard cachedV [(nm "code", nm "code_eq")] declZ == "application type mismatch"
-- a rule whose right side has another type fails its typing check and never fires
#guard pureV [(nm "code", nm "code_bad")] declY == "function expected"
#guard cachedV [(nm "code", nm "code_bad")] declY == "function expected"
-- a looping rule set is rejected by the firing budget, naming the rule
#guard pureV [(nm "code", nm "code_refl")] declY ==
  "rewrite rule budget exhausted: code_refl would fire past 65536 firings"
#guard cachedV [(nm "code", nm "code_refl")] declY ==
  "rewrite rule budget exhausted: code_refl would fire past 65536 firings"

/-! ### Registration and rule sets

The same declarations as records: a rule is registered (`rewriteDecl`) and fires only under a
`useRules` that names it; the firing order is priority descending (`activeTable`). -/

@[expose] def pureSeq (ds : List Declaration) : Except CheckError Env :=
  ds.foldlM (checkDecl .verified (pureOps .verified) []) (envR [])

@[expose] def cachedSeq (ds : List Declaration) : Except (CheckError × Nat) (Nat × FEnv) :=
  ds.foldlM (Cached.declStep .verified [] 1024) (0, mkFEnv (envR []))

@[expose] def seqV (ds : List Declaration) : String × String :=
  (verdict id (pureSeq ds), verdict (·.1) (cachedSeq ds))

@[expose] def reg (thm : String) (prio : Nat := 1000) : Declaration :=
  .rewriteDecl (nm thm) (nm "code") prio

-- registered and in force: the rule fires
#guard seqV [reg "code_eq", .useRules [nm "code_eq"], declY] == ("ok", "ok")
-- registered but not in the declaration's rule set: no firing
#guard seqV [reg "code_eq", declY] == ("function expected", "function expected")
#guard seqV [reg "code_eq", .useRules [nm "code_eq"], .useRules [], declY] ==
  ("function expected", "function expected")
-- a rule set naming an unregistered theorem activates nothing
#guard seqV [.useRules [nm "code_eq"], declY] == ("function expected", "function expected")
-- priority: the higher rule is tried first
#guard seqV [reg "code_eq" 2000, reg "code_refl" 1000,
    .useRules [nm "code_eq", nm "code_refl"], declY] == ("ok", "ok")
#guard seqV [reg "code_eq" 1000, reg "code_refl" 2000,
    .useRules [nm "code_eq", nm "code_refl"], declY] ==
  ("rewrite rule budget exhausted: code_refl would fire past 65536 firings",
   "rewrite rule budget exhausted: code_refl would fire past 65536 firings")
-- equal priorities: `Name.cmp` (`code_eq` before `code_refl`)
#guard seqV [reg "code_refl", reg "code_eq", .useRules [nm "code_refl", nm "code_eq"], declY] ==
  ("ok", "ok")
-- malformed registrations
#guard seqV [.rewriteDecl (nm "a") (nm "code") 1000] ==
  ("rewrite rule a: no stored theorem of that name", "rewrite rule a: no stored theorem of that name")
#guard seqV [.rewriteDecl (nm "code_vac") (nm "code") 1000] ==
  ("rewrite rule code_vac: a variable of its statement does not occur in its left side",
   "rewrite rule code_vac: a variable of its statement does not occur in its left side")
#guard seqV [.rewriteDecl (nm "code_eq") (nm "g") 1000] ==
  ("rewrite rule code_eq: declared head g, but its left side is headed by code",
   "rewrite rule code_eq: declared head g, but its left side is headed by code")

end ConLecheTests.Rewrite
