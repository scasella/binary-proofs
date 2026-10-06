(* Requires the generic V2 ABI bridge and assurance/path.ml. This propagates
   documented scalar effects through every original successor. It cannot be
   used without a checked qualified-decode invariant at EACH source state. *)

let ABI_CLEANSE_CHECKED_RUN_LIFT = prove
 (`!n P C s a.
    assurance_checked_run n P
      (\k source target. C k source target /\ abi_all_decodes_cleanse_scalar source) s
    ==> eventually_n abi_cleanse_scalar_extended_step n
          (\t. P(FST t) /\ SND t = a) (s,a)`,
  INDUCT_TAC THENL
   [REWRITE_TAC[assurance_checked_run; EVENTUALLY_N_TRIVIAL; FST; SND];
    REPEAT GEN_TAC THEN REWRITE_TAC[assurance_checked_run] THEN
    STRIP_TAC THEN
    REWRITE_TAC[ARITH_RULE `SUC n = 1+n`; EVENTUALLY_N_STEP] THEN
    CONJ_TAC THENL
     [ASM_MESON_TAC[ABI_CLEANSE_EXTENDED_BACKLIFT_ALL];
      REWRITE_TAC[FORALL_PAIR_THM] THEN
      MAP_EVERY X_GEN_TAC [`next:x86state`; `next_a:abi_omitted_state`] THEN
      DISCH_TAC THEN
      SUBGOAL_THEN `x86 s next` ASSUME_TAC THENL
       [ASM_MESON_TAC[ABI_CLEANSE_EXTENDED_PROJECTION]; ALL_TAC] THEN
      SUBGOAL_THEN `abi_all_decodes_cleanse_scalar s` ASSUME_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `next_a:abi_omitted_state = a` SUBST_ALL_TAC THENL
       [ASM_MESON_TAC[ABI_CLEANSE_STEP_PRESERVES_OMITTED]; ALL_TAC] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]]]);;
