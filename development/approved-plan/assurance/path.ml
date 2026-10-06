(* Exact finite runs over every original successor. Policy is an obligation on
   each successor, never a guard that changes the original x86 relation. *)
let assurance_checked_run = new_recursive_definition num_RECURSION
 `(assurance_checked_run 0 (P:x86state->bool)
      (C:num->x86state->x86state->bool) s <=> P s) /\
  (assurance_checked_run (SUC n) P C s <=>
     (?s'. x86 s s') /\
     !s'. x86 s s' ==> C (SUC n) s s' /\
                        assurance_checked_run n P C s')`;;

let ASSURANCE_RUN_PROJECT = prove
 (`!n P C s. assurance_checked_run n P C s
    ==> eventually_n x86 n P s`,
  INDUCT_TAC THENL
   [REWRITE_TAC[assurance_checked_run; EVENTUALLY_N_TRIVIAL];
    REPEAT GEN_TAC THEN REWRITE_TAC[assurance_checked_run] THEN
    REWRITE_TAC[ARITH_RULE `SUC n = 1+n`; EVENTUALLY_N_STEP] THEN
    STRIP_TAC THEN CONJ_TAC THENL
     [ASM_MESON_TAC[];
      X_GEN_TAC `next:x86state` THEN DISCH_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]]]);;

let ASSURANCE_RUN_EVENTUALLY = prove
 (`!n P C s. assurance_checked_run n P C s ==> eventually x86 P s`,
  MESON_TAC[ASSURANCE_RUN_PROJECT; EVENTUALLY_N_EVENTUALLY]);;

let ASSURANCE_RUN_ALL_SUCCESSORS = prove
 (`!n P C s. assurance_checked_run (SUC n) P C s
    ==> (?s'. x86 s s') /\
        !s'. x86 s s' ==> C (SUC n) s s' /\
                           assurance_checked_run n P C s'`,
  REWRITE_TAC[assurance_checked_run]);;

let assurance_step_policy = new_definition
 `assurance_step_policy rp wp xp (s:x86state) (s':x86state) <=>
   ?len inst d.
     x86_decode s (read RIP s) (len,inst) /\
     assurance_span_ok xp (val(read RIP s)) len /\
     read events s' = APPEND d (read events s) /\
     ALL (assurance_event_policy rp wp) d`;;

let assurance_zero_step = new_definition
 `assurance_zero_step rp wp xp remaining s s' <=>
   assurance_step_policy rp wp xp s s' /\
   (remaining = 1 ==> assurance_actual_ret 2 s s')`;;

let ASSURANCE_DECODED_OBSERVATION_ALL_SUCCESSORS = prove
 (`!len inst s s'.
    x86_decode s (read RIP s) (len,inst) /\ x86 s s'
    ==> assurance_observed_step s
          (assurance_observation s len inst s') s'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[x86] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `n:num`
      (X_CHOOSE_THEN `decoded:instruction` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `(n:num) = (len:num) /\ (decoded:instruction) = (inst:instruction)`
    (CONJUNCTS_THEN SUBST_ALL_TAC) THENL
   [MP_TAC(ISPECL [`s:x86state`; `read RIP s`;
      `(len:num,inst:instruction)`; `(n:num,decoded:instruction)`]
      x86_decode_unique) THEN ASM_REWRITE_TAC[PAIR_EQ] THEN MESON_TAC[];
    REWRITE_TAC[assurance_observed_step] THEN
    MAP_EVERY EXISTS_TAC [`len:num`; `inst:instruction`] THEN
    ASM_REWRITE_TAC[]]);;

let ASSURANCE_ALL_REVERSE = prove
 (`!P (l:A list). ALL P (REVERSE l) <=> ALL P l`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[REVERSE; ALL_APPEND; ALL] THEN MESON_TAC[]);;

let ASSURANCE_STEP_POLICY_OBSERVED = prove
 (`!rp wp xp s s'.
    x86 s s' /\ assurance_step_policy rp wp xp s s'
    ==> ?obs. assurance_observed_step s obs s' /\
              assurance_fetch_policy xp obs /\
              ALL (assurance_event_policy rp wp) (SND(SND(SND obs))) /\
              read events s' = APPEND (REVERSE(SND(SND(SND obs))))
                                      (read events s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[assurance_step_policy] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `len:num` (X_CHOOSE_THEN `inst:instruction`
      (X_CHOOSE_THEN `d:uarch_event list` STRIP_ASSUME_TAC)))) THEN
  EXISTS_TAC `assurance_observation s len inst s'` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC ASSURANCE_DECODED_OBSERVATION_ALL_SUCCESSORS THEN
    ASM_REWRITE_TAC[];
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP ASSURANCE_DELTA_EXACT) THEN
    ASM_REWRITE_TAC[assurance_observation; assurance_fetch_policy;
      FST; SND; ASSURANCE_ALL_REVERSE; REVERSE_REVERSE]]);;

let ASSURANCE_CODE_OFFSET_VALUE = prove
 (`!pc offset. pc+95 <= 2 EXP 64 /\ offset < 95
    ==> val(word(pc+offset):int64) = pc+offset`,
  REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC);;

let ASSURANCE_CODE_BASE_VALUE = prove
 (`!pc. pc+95 <= 2 EXP 64 ==> val(word pc:int64) = pc`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`pc:num`; `0`] ASSURANCE_CODE_OFFSET_VALUE) THEN
  ASM_REWRITE_TAC[ADD_CLAUSES; ARITH_RULE `0 < 95`]);;

let ASSURANCE_RUN_STEP = prove
 (`!n P C s. assurance_checked_run (1+n) P C s <=>
     (?s'. x86 s s') /\
     !s'. x86 s s' ==> C (1+n) s s' /\
                        assurance_checked_run n P C s'`,
  REWRITE_TAC[ARITH_RULE `1+n = SUC n`; assurance_checked_run]);;

(* The stepping tactic reuses the pinned decoder/executor conversion and state
   update machinery. It adds a proved obligation on each original successor.
   No original successor is discarded to make the obligation true. *)
let ASSURANCE_RET_FROM_DECODE_AND_STEP = prove
 (`!len s s'. x86_decode s (read RIP s) (len,RET) /\ x86 s s'
    ==> assurance_actual_ret len s s'`,
  MESON_TAC[ASSURANCE_DECODED_RET_ALL_SUCCESSORS]);;

let ASSURANCE_ZERO_LOCAL_POLICY_TAC decode_ths offset original_step update =
  let dt = Option.get decode_ths.(offset) in
  let _,conseq = dest_imp(snd(strip_forall(concl dt))) in
  let len,inst = dest_pair(rand conseq) in
  let d = if offset = 14 then
      `[EventJump(word(pc+16),word(pc+93))]`
    else if offset = 93 then
      `[EventJump(word(pc+95),ra);EventLoad(stackpointer:int64,8)]`
    else `[]:uarch_event list` in
  GEN_REWRITE_TAC I [assurance_zero_step] THEN CONJ_TAC THENL
   [REWRITE_TAC[assurance_step_policy] THEN
    MAP_EVERY EXISTS_TAC [len; inst; d] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(REWRITE_RULE[ADD_CLAUSES] dt) THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[] THEN
      ASM_SIMP_TAC[ASSURANCE_CODE_OFFSET_VALUE; ASSURANCE_CODE_BASE_VALUE;
        ARITH_RULE(mk_binary "<" (mk_numeral(num offset),`95`))] THEN
      MP_TAC(ISPECL [`xp:num->bool`; `pc:num`; `95`;
                     mk_numeral(num offset); len] ASSURANCE_SPAN_SUBRANGE) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN ARITH_TAC;
        REWRITE_TAC[ADD_CLAUSES]];
      SUBST1_TAC(SYM update) THEN
      ASM_REWRITE_TAC[APPEND] THEN
      CONV_TAC(TOP_DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV) THEN
      ASM_REWRITE_TAC[APPEND];
      REWRITE_TAC[ALL; assurance_event_policy] THEN ASM_REWRITE_TAC[]];
    (if offset <> 93 then
       CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]
     else REPEAT STRIP_TAC THEN
    MATCH_MP_TAC ASSURANCE_RET_FROM_DECODE_AND_STEP THEN
    CONJ_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(Option.get decode_ths.(93)) THEN ASM_REWRITE_TAC[];
      ACCEPT_TAC original_step])];;

let ASSURANCE_ZERO_BASIC_STEP_TAC offset decode_ths sname
      (store_inst_term_to:term ref option) (asl,w) =
  let _,args = strip_comb w in
  let stepn = dest_numeral(hd args) in
  let count = stepn -/ num 1 in
  let n_th = GSYM(NUM_ADD_CONV(mk_binary "+" (`1:num`,mk_numeral count))) in
  let sv = last args and sv' = mk_var(sname,`:x86state`) in
  let eth = X86_CONV decode_ths (map snd asl)
      (mk_comb(mk_comb(`x86`,sv),sv')) in
  (GEN_REWRITE_TAC
     (RATOR_CONV o RATOR_CONV o RATOR_CONV o RAND_CONV) [n_th] THEN
   GEN_REWRITE_TAC I [ASSURANCE_RUN_STEP] THEN CONJ_TAC THENL
    [GEN_REWRITE_TAC BINDER_CONV [eth] THEN
     CONV_TAC EXISTS_NONTRIVIAL_CONV;
     X_GEN_TAC sv' THEN DISCH_THEN(fun original_step ->
       MP_TAC(EQ_MP eth original_step) THEN
       REPEAT X86_UNDEFINED_CHOOSE_TAC THEN
       DISCH_THEN(fun update -> CONJ_TAC THENL
        [ASSURANCE_ZERO_LOCAL_POLICY_TAC decode_ths offset original_step update;
         MP_TAC update]))]) (asl,w);;

let ASSURANCE_ZERO_STEP_TAC offset (length_th,decode_ths) sname =
  ASSURANCE_ZERO_BASIC_STEP_TAC offset decode_ths sname None THEN
  NONSELFMODIFYING_STATE_UPDATE_TAC
    (MATCH_MP bytes_loaded_update length_th) THEN
  ASSUMPTION_STATE_UPDATE_TAC THEN
  DISCH_THEN(fun update ->
    let reads = STATE_UPDATE_NEW_RULE update in
    if reads = [] then ALL_TAC else
    MP_TAC(end_itlist CONJ reads) THEN
    ASSEMBLER_SIMPLIFY_TAC THEN STRIP_TAC);;

let ASSURANCE_CRYPTO_ZERO_COMPLETE_POLICY = prove
 (`!pc stackpointer ra p q xp rp e s.
    pc+95 <= 2 EXP 64 /\ assurance_span_ok xp pc 95 /\
    assurance_span_ok
      (\a. rp a /\ assurance_region stackpointer 8 a)
      (val(stackpointer:int64)) 8 /\
    bytes_loaded s (word pc) crypto_memcmp_mc /\
    read RIP s = word pc /\ read RSP s = stackpointer /\
    read (memory :> bytes64 stackpointer) s = ra /\
    C_ARGUMENTS [p;q;word 0] s /\ read events s = e
    ==> assurance_checked_run 6
      (\s'. read RIP s' = ra /\
            read RSP s' = word_add stackpointer (word 8) /\
            read RAX s' = word 0 /\
            bytes_loaded s' (word pc) crypto_memcmp_mc /\
            read events s' = APPEND
              [EventJump(word(pc+95),ra);EventLoad(stackpointer,8);
               EventJump(word(pc+16),word(pc+93))] e)
      (assurance_zero_step
        (\a. rp a /\ assurance_region stackpointer 8 a) (\a. F) xp) s`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; fst ASSURANCE_CRYPTO_EXEC] THEN STRIP_TAC THEN
  MAP_EVERY (fun (offset,sname) ->
    ASSURANCE_ZERO_STEP_TAC offset ASSURANCE_CRYPTO_EXEC sname)
    [0,"z1";4,"z2";7,"z3";10,"z4";14,"z5";93,"z6"] THEN
  REWRITE_TAC[assurance_checked_run] THEN ASM_REWRITE_TAC[APPEND]);;
