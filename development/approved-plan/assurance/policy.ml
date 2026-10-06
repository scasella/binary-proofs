(* Mathematical access policy on observations of the original relation.
   Permissions remain explicit environment predicates. No new memory
   interpreter and no predicate filters the x86 successor relation. *)

let assurance_canonical48 = new_definition
 `assurance_canonical48 a <=>
    a < 2 EXP 64 /\ (a < 2 EXP 47 \/ 2 EXP 64 - 2 EXP 47 <= a)`;;

let assurance_region = new_definition
 `assurance_region (p:int64) n a <=> val p <= a /\ a < val p+n`;;

let assurance_span_ok = new_definition
 `assurance_span_ok perm a width <=>
    a+width <= 2 EXP 64 /\
    !j. j < width ==> assurance_canonical48 (a+j) /\ perm(a+j)`;;

let assurance_event_policy = new_definition
 `assurance_event_policy rp wp e <=>
    match e with
    | EventLoad(adr,width) -> assurance_span_ok rp (val adr) width
    | EventStore(adr,width) -> assurance_span_ok wp (val adr) width
    | _ -> T`;;

let assurance_fetch_policy = new_definition
 `assurance_fetch_policy xp
      (obs:int64#num#instruction#uarch_event list) <=>
    assurance_span_ok xp (val(FST obs)) (FST(SND obs))`;;

let ASSURANCE_SPAN_SUBRANGE = prove
 (`!perm a width offset count.
    assurance_span_ok perm a width /\ offset+count <= width
    ==> assurance_span_ok perm (a+offset) count`,
  REWRITE_TAC[assurance_span_ok] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [ASM_ARITH_TAC;
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `offset+j:num`) THEN
    ASM_REWRITE_TAC[ADD_ASSOC] THEN ANTS_TAC THENL
     [ASM_ARITH_TAC; MESON_TAC[]]]);;

let ASSURANCE_ZERO_STACK_EVENT_POLICY = prove
 (`!rp wp ip ra sp.
    assurance_span_ok rp (val(sp:int64)) 8
    ==> ALL (assurance_event_policy rp wp)
        [EventJump(ip,ra);EventLoad(sp,8)]`,
  REWRITE_TAC[ALL; assurance_event_policy] THEN MESON_TAC[]);;

let ASSURANCE_RET_EVENT_POLICY = prove
 (`!rp wp len s s'.
    assurance_actual_ret len s s' /\
    assurance_span_ok rp (val(read RSP s)) 8
    ==> ALL (assurance_event_policy rp wp)
              (assurance_delta s s')`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP ASSURANCE_ACTUAL_RET_EFFECTS) THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP ASSURANCE_DELTA_EXACT) THEN
  ASM_REWRITE_TAC[ALL; assurance_event_policy]);;

let ASSURANCE_STACK_ADVANCE_NONWRAP = prove
 (`!stackpointer:int64. val stackpointer + 8 < 2 EXP 64
    ==> val(word_add stackpointer (word 8)) = val stackpointer + 8`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[VAL_WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  MATCH_MP_TAC MOD_LT THEN
  RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN ASM_REWRITE_TAC[]);;

let ASSURANCE_FETCH_INTERVAL_FROM_REGION = prove
 (`!xp codebase codesize ip len inst es.
    assurance_span_ok xp (val(codebase:int64)) codesize /\
    val codebase <= val(ip:int64) /\
    val ip+len <= val codebase+codesize
    ==> assurance_fetch_policy xp (ip,len,inst,es)`,
  REWRITE_TAC[assurance_fetch_policy; FST; SND] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`xp:num->bool`; `val(codebase:int64)`; `codesize:num`;
    `val(ip:int64)-val(codebase:int64)`; `len:num`]
    ASSURANCE_SPAN_SUBRANGE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
    `val(codebase:int64)+(val(ip:int64)-val(codebase:int64)) = val ip`
    SUBST1_TAC THENL [ASM_ARITH_TAC; MESON_TAC[]]);;

let ASSURANCE_SPAN_SELF_REGION = prove
 (`!rp p n. assurance_span_ok rp (val(p:int64)) n
    ==> assurance_span_ok
          (\a. rp a /\ assurance_region p n a) (val p) n`,
  REWRITE_TAC[assurance_span_ok; assurance_region] THEN
  REPEAT STRIP_TAC THEN
  ASM_MESON_TAC[ARITH_RULE
   `j < n ==> p <= p+j /\ p+j < p+n`]);;

let ASSURANCE_SPAN_MONO = prove
 (`!rp rp' a width.
    assurance_span_ok rp a width /\ (!x. rp x ==> rp' x)
    ==> assurance_span_ok rp' a width`,
  REWRITE_TAC[assurance_span_ok] THEN MESON_TAC[]);;

let ASSURANCE_SPAN_WORD_OFFSET_8 = prove
 (`!rp p. assurance_span_ok rp (val(p:int64)) 16
    ==> assurance_span_ok rp (val(word_add p (word 8))) 8`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `val(p:int64)+8 < 2 EXP 64` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[assurance_span_ok]) THEN
    ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[ASSURANCE_STACK_ADVANCE_NONWRAP] THEN
  MATCH_MP_TAC ASSURANCE_SPAN_SUBRANGE THEN
  EXISTS_TAC `16` THEN ASM_REWRITE_TAC[] THEN ARITH_TAC);;

let ASSURANCE_SPAN_PREFIX = prove
 (`!rp a width count.
    assurance_span_ok rp a width /\ count <= width
    ==> assurance_span_ok rp a count`,
  REWRITE_TAC[assurance_span_ok] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [ASM_ARITH_TAC;
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    ASM_MESON_TAC[LTE_TRANS]]);;

let ASSURANCE_CRYPTO_16_DATA_POLICY = prove
 (`!rp wp p q stackpointer ip ra.
    assurance_span_ok rp (val(p:int64)) 16 /\
    assurance_span_ok rp (val(q:int64)) 16 /\
    assurance_span_ok rp (val(stackpointer:int64)) 8
    ==> ALL (assurance_event_policy
          (\a. rp a /\ (assurance_region p 16 a \/
                        assurance_region q 16 a \/
                        assurance_region stackpointer 8 a)) wp)
        [EventJump(ip,ra);EventLoad(stackpointer,8);
         EventLoad(word_add q (word 8),8);EventLoad(q,8);
         EventLoad(word_add p (word 8),8);EventLoad(p,8)]`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `assurance_span_ok
      (\a. rp a /\ (assurance_region p 16 a \/
                    assurance_region q 16 a \/
                    assurance_region stackpointer 8 a)) (val(p:int64)) 16 /\
    assurance_span_ok
      (\a. rp a /\ (assurance_region p 16 a \/
                    assurance_region q 16 a \/
                    assurance_region stackpointer 8 a)) (val(q:int64)) 16 /\
    assurance_span_ok
      (\a. rp a /\ (assurance_region p 16 a \/
                    assurance_region q 16 a \/
                    assurance_region stackpointer 8 a)) (val(stackpointer:int64)) 8`
   STRIP_ASSUME_TAC THENL
    [REPEAT CONJ_TAC THEN MATCH_MP_TAC ASSURANCE_SPAN_MONO THENL
      [EXISTS_TAC `\a. rp a /\ assurance_region (p:int64) 16 a`;
       EXISTS_TAC `\a. rp a /\ assurance_region (q:int64) 16 a`;
       EXISTS_TAC `\a. rp a /\ assurance_region (stackpointer:int64) 8 a`] THEN
     ASM_SIMP_TAC[ASSURANCE_SPAN_SELF_REGION] THEN MESON_TAC[];
     REWRITE_TAC[ALL; assurance_event_policy] THEN
     ASM_SIMP_TAC[ASSURANCE_SPAN_WORD_OFFSET_8] THEN
     REPEAT CONJ_TAC THEN
     MATCH_MP_TAC ASSURANCE_SPAN_PREFIX THEN
     EXISTS_TAC `16` THEN ASM_REWRITE_TAC[] THEN ARITH_TAC]);;
