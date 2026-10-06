let cleanse_aggregate_abi_claims=[
 ("ABI_CLEANSE_EXTENDED_PROJECTION",`!s a s' a'. abi_cleanse_scalar_extended_step (s,a) (s',a') ==> x86 s s'`,ABI_CLEANSE_EXTENDED_PROJECTION);
 ("ABI_CLEANSE_EXTENDED_BACKLIFT_ALL",`!s s' a. x86 s s' ==> abi_cleanse_scalar_extended_step (s,a) (s',a)`,ABI_CLEANSE_EXTENDED_BACKLIFT_ALL);
 ("ABI_CLEANSE_EXTENDED_EQUIVALENCE",`!s s' a. (?a'. abi_cleanse_scalar_extended_step (s,a) (s',a')) <=> x86 s s'`,ABI_CLEANSE_EXTENDED_EQUIVALENCE);
 ("ABI_CLEANSE_EXTENDED_PROGRESS",`!s a. (?s'. x86 s s') <=>
        ?s' a'. abi_cleanse_scalar_extended_step (s,a) (s',a')`,ABI_CLEANSE_EXTENDED_PROGRESS);
 ("ABI_CLEANSE_EXTENDED_REFINES_V4",`!s a s' a'. abi_cleanse_scalar_extended_step (s,a) (s',a')
    ==> abi_scalar_extended_step (s,a) (s',a')`,ABI_CLEANSE_EXTENDED_REFINES_V4);
 ("ABI_CLEANSE_STEP_PRESERVES_OMITTED",`!s a s' a'. abi_cleanse_scalar_extended_step (s,a) (s',a') /\
             abi_all_decodes_cleanse_scalar s ==> a' = a`,ABI_CLEANSE_STEP_PRESERVES_OMITTED);
 ("ABI_CLEANSE_EQUAL_IMPLIES_REQUIRED_CONTROLS",`!a a'. a' = a ==> abi_required_controls_preserved a a'`,ABI_CLEANSE_EQUAL_IMPLIES_REQUIRED_CONTROLS);
 ("ABI_CLEANSE_REGISTERED_SITE_IS_SCALAR",`!off len inst. abi_cleanse_site off len inst ==> abi_cleanse_scalar_instruction inst`,ABI_CLEANSE_REGISTERED_SITE_IS_SCALAR);
 ("ABI_CLEANSE_DECODED_SCALAR_UNIQUE",`!len inst s. x86_decode s (read RIP s) (len,inst) /\
              abi_cleanse_scalar_instruction inst ==> abi_all_decodes_cleanse_scalar s`,ABI_CLEANSE_DECODED_SCALAR_UNIQUE);
 ("ABI_CLEANSE_CHECKED_RUN_LIFT",`!n P C s a.
    assurance_checked_run n P
      (\k source target. C k source target /\ abi_all_decodes_cleanse_scalar source) s
    ==> eventually_n abi_cleanse_scalar_extended_step n
          (\t. P(FST t) /\ SND t = a) (s,a)`,ABI_CLEANSE_CHECKED_RUN_LIFT);
 ("ABI_CLEANSE_REGISTERED_DECODE_QUALIFIED",`!pc off s.
    bytes_loaded s (word pc) openssl_cleanse_mc /\
    read RIP (s:x86state) = word(pc+off) /\
    MEM off [0;4;7;11;13;17;19;21;25;29;31;48;55;57;59;63;67;69;72;76;83;87;89;93;95]
    ==> abi_all_decodes_cleanse_scalar s`,ABI_CLEANSE_REGISTERED_DECODE_QUALIFIED)];;
