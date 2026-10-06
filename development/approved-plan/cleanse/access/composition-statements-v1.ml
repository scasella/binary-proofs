(* Frozen composition targets before their proof search. *)
needs "/work/development/approved-plan/cleanse/functional/bounded/statements-v1.ml";;
let cleanse_access_count_agreement_statement =
 `!p n. cleanse_access_count p n=cleanse_functional_steps p n`;;
let cleanse_access_original_return_statement =
 `!pc stackpointer ra p n m rp wp xp ordinary (s:x86state).
    bp_e2_cleanse_pre pc stackpointer ra p n m rp wp xp ordinary s
    ==> eventually_n x86 (cleanse_functional_steps p n)
      (cleanse_access_return_post pc stackpointer ra) s`;;
let cleanse_access_qualified_return_statement =
 `!pc stackpointer ra p n m rp wp xp ordinary (s:x86state).
    bp_e2_cleanse_pre pc stackpointer ra p n m rp wp xp ordinary s
    ==> assurance_checked_run (cleanse_functional_steps p n)
      (cleanse_access_return_post pc stackpointer ra)
      (\k source target.
        cleanse_access_covered_step pc
          (bp_e2_cleanse_allowed_read rp ordinary stackpointer)
          (bp_e2_cleanse_allowed_write wp ordinary p n)
          (bp_e2_cleanse_allowed_fetch xp ordinary pc) k source target /\
        abi_all_decodes_cleanse_scalar source) s`;;
let cleanse_access_extended_return_statement =
 `!pc stackpointer ra p n m rp wp xp ordinary (s:x86state) (a:abi_omitted_state).
    bp_e2_cleanse_pre pc stackpointer ra p n m rp wp xp ordinary s
    ==> eventually_n abi_cleanse_scalar_extended_step (cleanse_functional_steps p n)
      (\t. cleanse_access_return_post pc stackpointer ra (FST t) /\ SND t=a) (s,a)`;;
