let abi_cleanse_projection_statement =
 `!s a s' a'. abi_cleanse_scalar_extended_step (s,a) (s',a') ==> x86 s s'`;;
let abi_cleanse_backlift_all_statement =
 `!s s' a. x86 s s' ==> abi_cleanse_scalar_extended_step (s,a) (s',a)`;;
let abi_cleanse_equivalence_statement =
 `!s s' a. (?a'. abi_cleanse_scalar_extended_step (s,a) (s',a')) <=> x86 s s'`;;
let abi_cleanse_progress_statement =
 `!s a. (?s'. x86 s s') <=>
        ?s' a'. abi_cleanse_scalar_extended_step (s,a) (s',a')`;;
let abi_cleanse_refines_v4_statement =
 `!s a s' a'. abi_cleanse_scalar_extended_step (s,a) (s',a')
    ==> abi_scalar_extended_step (s,a) (s',a')`;;
let abi_cleanse_preserves_omitted_statement =
 `!s a s' a'. abi_cleanse_scalar_extended_step (s,a) (s',a') /\
             abi_all_decodes_cleanse_scalar s ==> a' = a`;;
let abi_cleanse_equal_controls_statement =
 `!a a'. a' = a ==> abi_required_controls_preserved a a'`;;
let abi_cleanse_site_scalar_statement =
 `!off len inst. abi_cleanse_site off len inst ==> abi_cleanse_scalar_instruction inst`;;
let abi_cleanse_decoded_scalar_unique_statement =
 `!len inst s. x86_decode s (read RIP s) (len,inst) /\
              abi_cleanse_scalar_instruction inst ==> abi_all_decodes_cleanse_scalar s`;;
let abi_cleanse_checked_run_lift_statement =
 `!n P C s a.
    assurance_checked_run n P
      (\k source target. C k source target /\ abi_all_decodes_cleanse_scalar source) s
    ==> eventually_n abi_cleanse_scalar_extended_step n
          (\t. P(FST t) /\ SND t = a) (s,a)`;;
