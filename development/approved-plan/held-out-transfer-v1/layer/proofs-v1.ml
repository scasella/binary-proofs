(* Candidate preparation: exact address-free accepted C2 fragments; identifier renaming only. *)
let HT_POLICY_EVENT_MONO = prove
 (ht_policy_event_mono_statement,
  REPEAT GEN_TAC THEN SPEC_TAC (`e:uarch_event`,`e:uarch_event`) THEN
  MATCH_MP_TAC uarch_event_INDUCT THEN REPEAT CONJ_TAC THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[assurance_event_policy] THEN
  REPEAT STRIP_TAC THEN ASM_MESON_TAC[R1_SECRET_SPAN_MONO]);;
let HT_POLICY_ALL_MONO = prove
 (ht_policy_all_mono_statement,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[ALL] THEN ASM_MESON_TAC[]);;
let HT_POLICY_STEP_MONO = prove
 (ht_policy_step_mono_statement,
  REPEAT GEN_TAC THEN REWRITE_TAC[assurance_step_policy] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`len:num`;`inst:instruction`;`d:uarch_event list`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[R1_SECRET_SPAN_MONO];
    SUBGOAL_THEN
     `!e:uarch_event. assurance_event_policy rp0 wp0 e ==>
                       assurance_event_policy rp wp e` ASSUME_TAC THENL
     [ASM_MESON_TAC[HT_POLICY_EVENT_MONO];
      ASM_MESON_TAC[HT_POLICY_ALL_MONO]]]);;
let HT_POLICY_SPAN = prove
 (ht_policy_span_statement,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC R1_SECRET_SPAN_MONO THEN
  EXISTS_TAC `\(addr:num). P addr /\ assurance_region (p:int64) n addr` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC R1_SECRET_SPAN_REGION THEN
  ASM_REWRITE_TAC[]);;
let HT_SPAN_POINT = prove
 (ht_span_point_statement,
  REWRITE_TAC[assurance_span_ok;assurance_region] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM (MP_TAC o SPEC `addr-val(p:int64)`) THEN
  ASM_SIMP_TAC[ARITH_RULE `a <= b ==> a+(b-a)=b`] THEN
  ANTS_TAC THENL [ASM_ARITH_TAC;MESON_TAC[]]);;
let HT_REGION_NONOVERLAPPING = prove
 (ht_region_nonoverlapping_statement,
  REWRITE_TAC[assurance_region;NONOVERLAPPING_QFREE;
              VAL_WORD_SUB_CASES;DIMINDEX_64] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `val(p:int64)`) THEN
  FIRST_ASSUM(MP_TAC o SPEC `val(q:int64)`) THEN
  COND_CASES_TAC THEN ASM_ARITH_TAC);;
let HT_SPAN_WORD_ADD_REGION = prove
 (ht_span_word_add_region_statement,
  REPEAT GEN_TAC THEN REWRITE_TAC[assurance_span_ok;assurance_region] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `i<2 EXP 64 /\ val(p:int64)+i<2 EXP 64` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC;ALL_TAC] THEN
  ASM_SIMP_TAC[VAL_WORD_ADD;VAL_WORD;DIMINDEX_64;MOD_LT] THEN ASM_ARITH_TAC);;
let HT_REGION_DISJOINT = prove
 (ht_region_disjoint_statement,
  REWRITE_TAC[assurance_region;NONOVERLAPPING_QFREE;
              VAL_WORD_SUB_CASES;DIMINDEX_64] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REPEAT STRIP_TAC THEN TRY COND_CASES_TAC THEN ASM_ARITH_TAC);;
let HT_FRAME_CANCEL_COMPONENT = prove
 (ht_frame_cancel_component_statement,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `(R ,, MAYCHANGE [c:(A,B)component]) (s:A) t` THEN
  REWRITE_TAC[MAYCHANGE_SING;seq;ASSIGNS_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:A`
    (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `y:B` ASSUME_TAC))) THEN
  SUBGOAL_THEN `read (c:(A,B)component) (u:A)=read c s` ASSUME_TAC THENL
   [ASM_MESON_TAC[];ALL_TAC] THEN
  let valid=REWRITE_RULE[EXTENSIONALLY_VALID_COMPONENT]
    (ASSUME `extensionally_valid_component (c:(A,B)component)`) in
  let overwrite_read=CONJUNCT1(CONJUNCT2 valid)
  and overwrite_write=CONJUNCT2(CONJUNCT2 valid) in
  SUBGOAL_THEN `write (c:(A,B)component) (read c (t:A)) t=t` ASSUME_TAC THENL
   [MATCH_ACCEPT_TAC overwrite_read;ALL_TAC] THEN
  SUBGOAL_THEN `write (c:(A,B)component) (read c (t:A)) (write c (y:B) (u:A))=
    write c (read c t) u` ASSUME_TAC THENL
   [MATCH_ACCEPT_TAC overwrite_write;ALL_TAC] THEN
  SUBGOAL_THEN `write (c:(A,B)component) (read c (u:A)) u=u` ASSUME_TAC THENL
   [MATCH_ACCEPT_TAC overwrite_read;ALL_TAC] THEN
  SUBGOAL_THEN `(t:A)=u` ASSUME_TAC THENL
   [ASM_MESON_TAC[];ASM_MESON_TAC[]]);;
(* Pure foundation frame algebra. *)
let HT_ORIGINAL_RET =
 let pth = prove
  (`read RIP (s:x86state)=word pc ==> x86_decode s (word pc) (n,instr) ==>
    (x86 s t <=> (RIP := word(pc+n) ,, x86_execute instr) s t)`,
   REPEAT STRIP_TAC THEN REWRITE_TAC[x86] THEN
   ASM_REWRITE_TAC[GSYM WORD_ADD] THEN
   ASM_MESON_TAC[PAIR_EQ;x86_decode_unique]) in
 prove(ht_original_ret_statement,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  let step = MATCH_MP (MATCH_MP pth
    (ASSUME `read RIP (s:x86state)=word pc`))
    (ASSUME `x86_decode s (word pc) (1,RET)`) in
  let step = EQ_MP step (ASSUME `x86 (s:x86state) t`) in
  REWRITE_TAC[assurance_actual_ret] THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    MP_TAC step THEN ASM_REWRITE_TAC[assoc "RET" X86_EXECUTE_CASES;GSYM WORD_ADD;ETA_AX]]);;
