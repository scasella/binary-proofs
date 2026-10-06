(* Fifteen original transitions, including the actual decoded RET at +50.
   Physical data loads are full-width words; buffers may overlap or misalign. *)
let ASSURANCE_CRYPTO_16_STRICT_SPANS = prove
 (`!rp p q stackpointer.
    assurance_span_ok rp (val(p:int64)) 16 /\
    assurance_span_ok rp (val(q:int64)) 16 /\
    assurance_span_ok rp (val(stackpointer:int64)) 8
    ==> assurance_span_ok
         (\a. rp a /\ (assurance_region p 16 a \/ assurance_region q 16 a \/
                       assurance_region stackpointer 8 a)) (val p) 8 /\
        assurance_span_ok
         (\a. rp a /\ (assurance_region p 16 a \/ assurance_region q 16 a \/
                       assurance_region stackpointer 8 a))
         (val(word_add p (word 8))) 8 /\
        assurance_span_ok
         (\a. rp a /\ (assurance_region p 16 a \/ assurance_region q 16 a \/
                       assurance_region stackpointer 8 a)) (val q) 8 /\
        assurance_span_ok
         (\a. rp a /\ (assurance_region p 16 a \/ assurance_region q 16 a \/
                       assurance_region stackpointer 8 a))
         (val(word_add q (word 8))) 8 /\
        assurance_span_ok
         (\a. rp a /\ (assurance_region p 16 a \/ assurance_region q 16 a \/
                       assurance_region stackpointer 8 a)) (val stackpointer) 8`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`rp:num->bool`; `\a:num. F`; `p:int64`; `q:int64`;
    `stackpointer:int64`; `word 0:int64`; `word 0:int64`]
    ASSURANCE_CRYPTO_16_DATA_POLICY) THEN
  ASM_REWRITE_TAC[ALL; assurance_event_policy] THEN MESON_TAC[]);;

let ASSURANCE_16_LOCAL_POLICY_TAC decode_ths offset original_step update =
  let dt = Option.get decode_ths.(offset) in
  let _,conseq = dest_imp(snd(strip_forall(concl dt))) in
  let len,inst = dest_pair(rand conseq) in
  let d = match offset with
    | 14 -> `[EventJump(word(pc+16),word(pc+16))]`
    | 20 -> `[EventJump(word(pc+22),word(pc+22))]`
    | 22 -> `[EventLoad(p:int64,8)]`
    | 25 -> `[EventLoad(word_add p (word 8),8)]`
    | 36 -> `[EventLoad(q:int64,8)]`
    | 39 -> `[EventLoad(word_add q (word 8),8)]`
    | 50 -> `[EventJump(word(pc+52),ra);EventLoad(stackpointer:int64,8)]`
    | _ -> `[]:uarch_event list` in
  GEN_REWRITE_TAC I [assurance_zero_step] THEN CONJ_TAC THENL
   [REWRITE_TAC[assurance_step_policy] THEN
    MAP_EVERY EXISTS_TAC [len; inst; d] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(REWRITE_RULE[ADD_CLAUSES] dt) THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[] THEN
      ASM_SIMP_TAC[ASSURANCE_CODE_OFFSET_VALUE; ASSURANCE_CODE_BASE_VALUE;
        ARITH_RULE(mk_binary "<" (mk_numeral(num offset),`95`))] THEN
      MP_TAC(ISPECL [`xp:num->bool`; `pc:num`; `95`;
        mk_numeral(num offset); len] ASSURANCE_SPAN_SUBRANGE) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN ARITH_TAC; REWRITE_TAC[ADD_CLAUSES]];
      SUBST1_TAC(SYM update) THEN ASM_REWRITE_TAC[APPEND] THEN
      CONV_TAC(TOP_DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV) THEN
      ASM_REWRITE_TAC[APPEND; WORD_ADD_0];
      REWRITE_TAC[ALL; assurance_event_policy] THEN ASM_REWRITE_TAC[]];
    (if offset <> 50 then CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]
     else REPEAT STRIP_TAC THEN
      MATCH_MP_TAC ASSURANCE_RET_FROM_DECODE_AND_STEP THEN CONJ_TAC THENL
       [ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC(Option.get decode_ths.(50)) THEN ASM_REWRITE_TAC[];
        ACCEPT_TAC original_step])];;

(* Reusable checked-run step adapter for a supplied checked local obligation.
   It uses the original X86_CONV for progress AND every successor. *)
let ASSURANCE_FINITE_BASIC_STEP_TAC local_tac offset decode_ths sname
      (asl,w) =
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
    [GEN_REWRITE_TAC BINDER_CONV [eth] THEN CONV_TAC EXISTS_NONTRIVIAL_CONV;
     X_GEN_TAC sv' THEN DISCH_THEN(fun original_step ->
       MP_TAC(EQ_MP eth original_step) THEN
       REPEAT X86_UNDEFINED_CHOOSE_TAC THEN
       DISCH_THEN(fun update -> CONJ_TAC THENL
        [local_tac decode_ths offset original_step update;
         MP_TAC update]))]) (asl,w);;

let ASSURANCE_FINITE_STEP_TAC local_tac offset (length_th,decode_ths) sname =
  ASSURANCE_FINITE_BASIC_STEP_TAC local_tac offset decode_ths sname THEN
  NONSELFMODIFYING_STATE_UPDATE_TAC
    (MATCH_MP bytes_loaded_update length_th) THEN
  ASSUMPTION_STATE_UPDATE_TAC THEN
  DISCH_THEN(fun update ->
    let reads = STATE_UPDATE_NEW_RULE update in
    if reads = [] then ALL_TAC else
    MP_TAC(end_itlist CONJ reads) THEN ASSEMBLER_SIMPLIFY_TAC THEN STRIP_TAC);;

let ASSURANCE_CRYPTO_16_COMPLETE_POLICY = prove
 (`!pc stackpointer ra p q xp rp a0 a1 b0 b1 e s.
    pc+95 <= 2 EXP 64 /\ assurance_span_ok xp pc 95 /\
    assurance_span_ok rp (val(p:int64)) 16 /\
    assurance_span_ok rp (val(q:int64)) 16 /\
    assurance_span_ok rp (val(stackpointer:int64)) 8 /\
    bytes_loaded s (word pc) crypto_memcmp_mc /\
    read RIP s = word pc /\ read RSP s = stackpointer /\
    read (memory :> bytes64 stackpointer) s = ra /\
    C_ARGUMENTS [p;q;word 16] s /\
    read (memory :> bytes64 p) s = a0 /\
    read (memory :> bytes64 (word_add p (word 8))) s = a1 /\
    read (memory :> bytes64 q) s = b0 /\
    read (memory :> bytes64 (word_add q (word 8))) s = b1 /\
    read events s = e
    ==> assurance_checked_run 15
      (\s'. read RIP s' = ra /\
            read RSP s' = word_add stackpointer (word 8) /\
            read RAX s' = (if a0 = b0 /\ a1 = b1 then word 0 else word 1) /\
            bytes_loaded s' (word pc) crypto_memcmp_mc /\
            read events s' = APPEND
              [EventJump(word(pc+52),ra);EventLoad(stackpointer,8);
               EventLoad(word_add q (word 8),8);EventLoad(q,8);
               EventLoad(word_add p (word 8),8);EventLoad(p,8);
               EventJump(word(pc+22),word(pc+22));
               EventJump(word(pc+16),word(pc+16))] e)
      (assurance_zero_step
        (\a. rp a /\ (assurance_region p 16 a \/ assurance_region q 16 a \/
                      assurance_region stackpointer 8 a)) (\a. F) xp) s`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; fst ASSURANCE_CRYPTO_EXEC] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`rp:num->bool`; `p:int64`; `q:int64`; `stackpointer:int64`]
    ASSURANCE_CRYPTO_16_STRICT_SPANS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MAP_EVERY (fun (offset,sname) ->
    ASSURANCE_FINITE_STEP_TAC ASSURANCE_16_LOCAL_POLICY_TAC
      offset ASSURANCE_CRYPTO_EXEC sname)
    [0,"v1";4,"v2";7,"v3";10,"v4";14,"v5";16,"v6";20,"v7";
     22,"v8";25,"v9";29,"v10";36,"v11";39,"v12";43,"v13";
     46,"v14";50,"v15"] THEN
  REWRITE_TAC[assurance_checked_run] THEN
  ASM_REWRITE_TAC[APPEND; WORD_ADD_0; VAL_EQ_0; WORD_OR_EQ_0; WORD_XOR_EQ_0] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[]);;
