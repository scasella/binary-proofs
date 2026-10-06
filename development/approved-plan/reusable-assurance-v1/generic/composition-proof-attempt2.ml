(* Literal frozen in expected-v2.json before this proof source was written.
   Segment policies are obligations on every original successor. *)
let RA_CHECKED_RUN_THREE_SEGMENT = prove
 (ra_checked_run_three_segment_statement,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!t:x86state. B t ==> assurance_checked_run c P C t` ASSUME_TAC THENL
   [X_GEN_TAC `t:x86state` THEN DISCH_TAC THEN
    MATCH_MP_TAC (ISPECL
      [`c:num`; `P:x86state->bool`;
       `C3:num->x86state->x86state->bool`;
       `C:num->x86state->x86state->bool`; `t:x86state`]
      RA_CHECKED_RUN_POLICY_MONO) THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t:x86state. A t ==> assurance_checked_run (b+c) P C t`
   ASSUME_TAC THENL
   [X_GEN_TAC `t:x86state` THEN DISCH_TAC THEN
    MATCH_MP_TAC (ISPECL
      [`b:num`; `c:num`; `P:x86state->bool`;
       `C:num->x86state->x86state->bool`; `t:x86state`]
      RA_CHECKED_RUN_APPEND) THEN
    MATCH_MP_TAC (ISPECL
      [`b:num`; `B:x86state->bool`;
       `\u:x86state. assurance_checked_run c P C u`;
       `\k source target. (C:num->x86state->x86state->bool) (c+k) source target`; `t:x86state`]
      RA_CHECKED_RUN_POST_MONO) THEN CONJ_TAC THENL
     [ASM_MESON_TAC[];
      MATCH_MP_TAC (ISPECL
        [`b:num`; `B:x86state->bool`;
         `C2:num->x86state->x86state->bool`;
         `\k source target. (C:num->x86state->x86state->bool) (c+k) source target`; `t:x86state`]
        RA_CHECKED_RUN_POLICY_MONO) THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC (ISPECL
    [`a:num`; `(b+c):num`; `P:x86state->bool`;
     `C:num->x86state->x86state->bool`; `s:x86state`]
    RA_CHECKED_RUN_APPEND) THEN
  MATCH_MP_TAC (ISPECL
    [`a:num`; `H:x86state->bool`;
     `\t:x86state. assurance_checked_run (b+c) P C t`;
     `\k source target. (C:num->x86state->x86state->bool) ((b+c)+k) source target`; `s:x86state`]
    RA_CHECKED_RUN_POST_MONO) THEN CONJ_TAC THENL
   [ASM_MESON_TAC[];
    MATCH_MP_TAC (ISPECL
      [`a:num`; `H:x86state->bool`;
       `C1:num->x86state->x86state->bool`;
       `\k source target. (C:num->x86state->x86state->bool) ((b+c)+k) source target`; `s:x86state`]
      RA_CHECKED_RUN_POLICY_MONO) THEN ASM_MESON_TAC[]]);;
