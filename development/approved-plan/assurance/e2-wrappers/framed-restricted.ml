(* New recipes extend the checked restricted runs with a modeled scalar frame.
   They retain all original successors and use no target axioms. *)
let ASSURANCE_FRAMED_FINITE_STEP_TAC local_tac offset (length_th,decode_ths) sname =
  ASSURANCE_FINITE_BASIC_STEP_TAC local_tac offset decode_ths sname THEN
  NONSELFMODIFYING_STATE_UPDATE_TAC
    (MATCH_MP bytes_loaded_update length_th) THEN
  ASSUMPTION_STATE_UPDATE_TAC THEN MAYCHANGE_STATE_UPDATE_TAC THEN
  DISCH_THEN(fun update ->
    let reads = STATE_UPDATE_NEW_RULE update in
    if reads = [] then ALL_TAC else
    MP_TAC(end_itlist CONJ reads) THEN ASSEMBLER_SIMPLIFY_TAC THEN STRIP_TAC);;

let ASSURANCE_CRYPTO_ZERO_FRAMED_POLICY = prove
 (`!pc stackpointer ra p q xp rp e m s.
    pc+95 <= 2 EXP 64 /\ assurance_span_ok xp pc 95 /\
    assurance_span_ok
      (\a. rp a /\ assurance_region stackpointer 8 a)
      (val(stackpointer:int64)) 8 /\
    bytes_loaded s (word pc) crypto_memcmp_mc /\
    read RIP s = word pc /\ read RSP s = stackpointer /\
    read (memory :> bytes64 stackpointer) s = ra /\
    C_ARGUMENTS [p;q;word 0] s /\ read events s = e /\ read memory s = m
    ==> assurance_checked_run 6
      (\s'. read RIP s' = ra /\
            read RSP s' = word_add stackpointer (word 8) /\
            read RAX s' = word 0 /\
            bytes_loaded s' (word pc) crypto_memcmp_mc /\
            read events s' = APPEND
              [EventJump(word(pc+95),ra);EventLoad(stackpointer,8);
               EventJump(word(pc+16),word(pc+93))] e /\ read memory s' = m /\
            (MAYCHANGE [RIP;RSP;RAX;RDI;RSI;RDX;R10;R11] ,,
             MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events]) s s')
      (assurance_zero_scalar_step
        (\a. rp a /\ assurance_region stackpointer 8 a) (\a. F) xp) s`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; fst ASSURANCE_CRYPTO_EXEC] THEN STRIP_TAC THEN
  ASSUME_TAC(ISPEC `s:x86state` MAYCHANGE_STARTER) THEN
  MAP_EVERY (fun (offset,sname) ->
    ASSURANCE_FRAMED_FINITE_STEP_TAC ASSURANCE_ZERO_SCALAR_LOCAL_TAC
      offset ASSURANCE_CRYPTO_EXEC sname)
    [0,"zs1";4,"zs2";7,"zs3";10,"zs4";14,"zs5";93,"zs6"] THEN
  REWRITE_TAC[assurance_checked_run] THEN ASM_REWRITE_TAC[APPEND] THEN REWRITE_TAC[SOME_FLAGS] THEN MONOTONE_MAYCHANGE_TAC);;

let ASSURANCE_CRYPTO_16_FRAMED_POLICY = prove
 (`!pc stackpointer ra p q xp rp a0 a1 b0 b1 e m s.
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
    read events s = e /\ read memory s = m
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
               EventJump(word(pc+16),word(pc+16))] e /\ read memory s' = m /\
            (MAYCHANGE [RIP;RSP;RAX;RDI;RSI;RDX;R10;R11] ,,
             MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events]) s s')
      (assurance_zero_scalar_step
        (\a. rp a /\ (assurance_region p 16 a \/ assurance_region q 16 a \/
                      assurance_region stackpointer 8 a)) (\a. F) xp) s`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; fst ASSURANCE_CRYPTO_EXEC] THEN STRIP_TAC THEN
  ASSUME_TAC(ISPEC `s:x86state` MAYCHANGE_STARTER) THEN
  MP_TAC(ISPECL [`rp:num->bool`; `p:int64`; `q:int64`; `stackpointer:int64`]
    ASSURANCE_CRYPTO_16_STRICT_SPANS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MAP_EVERY (fun (offset,sname) ->
    ASSURANCE_FRAMED_FINITE_STEP_TAC
      (ASSURANCE_SCALAR_LOCAL_TAC ASSURANCE_16_LOCAL_POLICY_TAC)
      offset ASSURANCE_CRYPTO_EXEC sname)
    [0,"v1";4,"v2";7,"v3";10,"v4";14,"v5";16,"v6";20,"v7";
     22,"v8";25,"v9";29,"v10";36,"v11";39,"v12";43,"v13";
     46,"v14";50,"v15"] THEN
  REWRITE_TAC[assurance_checked_run] THEN
  ASM_REWRITE_TAC[APPEND; WORD_ADD_0; VAL_EQ_0; WORD_OR_EQ_0; WORD_XOR_EQ_0] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN REWRITE_TAC[SOME_FLAGS] THEN MONOTONE_MAYCHANGE_TAC);;
