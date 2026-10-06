(* Requires zero-scalar-qualified.ml, n16-policy.ml and ABI generic V3 rules.
   Actual pinned decodes qualify EVERY original source in the 15-step run. *)
let ASSURANCE_SCALAR_LOCAL_TAC local_policy decode_ths offset original_step update =
  let dt = Option.get decode_ths.(offset) in
  let _,conseq = dest_imp(snd(strip_forall(concl dt))) in
  let len,inst = dest_pair(rand conseq) in
  let _,step_args = strip_comb(concl original_step) in
  let source = hd step_args in
  GEN_REWRITE_TAC I [assurance_zero_scalar_step] THEN CONJ_TAC THENL
   [local_policy decode_ths offset original_step update;
    MATCH_MP_TAC(ISPECL [len; inst; source] ASSURANCE_DECODED_SCALAR_UNIQUE) THEN
    CONJ_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(REWRITE_RULE[ADD_CLAUSES] dt) THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC(ISPECL [mk_numeral(num offset); len; inst]
        ABI_CRYPTO_REGISTERED_SITE_IS_SCALAR) THEN
      REWRITE_TAC[abi_crypto_site]]];;

let ASSURANCE_CRYPTO_16_SCALAR_QUALIFIED_POLICY = prove
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
      (assurance_zero_scalar_step
        (\a. rp a /\ (assurance_region p 16 a \/ assurance_region q 16 a \/
                      assurance_region stackpointer 8 a)) (\a. F) xp) s`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; fst ASSURANCE_CRYPTO_EXEC] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`rp:num->bool`; `p:int64`; `q:int64`; `stackpointer:int64`]
    ASSURANCE_CRYPTO_16_STRICT_SPANS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MAP_EVERY (fun (offset,sname) ->
    ASSURANCE_FINITE_STEP_TAC
      (ASSURANCE_SCALAR_LOCAL_TAC ASSURANCE_16_LOCAL_POLICY_TAC)
      offset ASSURANCE_CRYPTO_EXEC sname)
    [0,"v1";4,"v2";7,"v3";10,"v4";14,"v5";16,"v6";20,"v7";
     22,"v8";25,"v9";29,"v10";36,"v11";39,"v12";43,"v13";
     46,"v14";50,"v15"] THEN
  REWRITE_TAC[assurance_checked_run] THEN
  ASM_REWRITE_TAC[APPEND; WORD_ADD_0; VAL_EQ_0; WORD_OR_EQ_0; WORD_XOR_EQ_0] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[]);;
