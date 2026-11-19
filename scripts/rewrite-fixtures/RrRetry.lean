/- The rewrite-rule e2e fixtures `tests/e2e/rewrite_rule_retry_*.ndjson`, exported with the rr-dev
   toolchain:

       lean +rr-dev -o RrRetry.olean RrRetry.lean
       LEAN_PATH=.:<rr-dev>/lib/lean leanexport RrRetry -- strRetryTgt str_retry > str_retry.ndjson
       LEAN_PATH=.:<rr-dev>/lib/lean leanexport RrRetry -- strEmptyTgt str_empty > str_empty.ndjson
       python3 -I scripts/rewrite-fixtures/mk.py retry <dir of the exports> tests/e2e

   `mk.py retry` gives `str_retry` the statement of `strRetryTgt`, `sf "ab" = 0`, which holds
   where a `String` literal that fails to match a constructor pattern is read as its characters
   under `String.ofList` and matched again (official `match_rewrite_pattern`,
   `string_lit_to_constructor`).  `str_empty` gets `sf "" = 0`: the empty literal's
   `String.ofList []` does not match `c :: cs`, so the conversion fails. -/
abstract_block

def sf (_s : String) : Nat := 0
@[rewrite] theorem sf_cons (c : Char) (cs : List Char) : sf (String.ofList (c :: cs)) = 0 := rfl

end

def strRetryTgt : Prop := sf "ab" = 0
def strEmptyTgt : Prop := sf "" = 0

rewrite_rules sf_cons in
theorem str_retry : sf "ab" = sf "ab" := rfl

rewrite_rules sf_cons in
theorem str_empty : sf "" = sf "" := rfl
