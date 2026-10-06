(* Independently frozen bridge from actual covered decodes to the generic V5
   omitted-state rule. No preservation or execution invariant is a premise. *)
let cleanse_access_covered_decode_qualified_statement =
 `!pc rp wp xp remaining (s:x86state) s'.
    cleanse_access_covered_step pc rp wp xp remaining s s'
    ==> abi_all_decodes_cleanse_scalar s`;;
let cleanse_access_checked_run_qualified_statement =
 `!n pc rp wp xp P (s:x86state).
    assurance_checked_run n P (cleanse_access_covered_step pc rp wp xp) s
    ==> assurance_checked_run n P
      (\k source target. cleanse_access_covered_step pc rp wp xp k source target /\
                         abi_all_decodes_cleanse_scalar source) s`;;
