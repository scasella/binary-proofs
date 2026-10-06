(* Requires path.ml and frozen SCALAR_ABI_EXTENSION_V2 definitions/rules.
   This is a target control-flow qualification, not an architectural axiom.
   All original successors remain universally quantified. *)

let ASSURANCE_DECODED_SCALAR_UNIQUE = prove
 (`!len inst s. x86_decode s (read RIP s) (len,inst) /\
                abi_scalar_instruction inst
    ==> abi_all_decodes_scalar s`,
  REWRITE_TAC[abi_all_decodes_scalar] THEN
  MESON_TAC[x86_decode_unique; PAIR_EQ]);;

let assurance_zero_scalar_step = new_definition
 `assurance_zero_scalar_step rp wp xp remaining s s' <=>
    assurance_zero_step rp wp xp remaining s s' /\
    abi_all_decodes_scalar s`;;

let ASSURANCE_ZERO_SCALAR_LOCAL_TAC decode_ths offset original_step update =
  let dt = Option.get decode_ths.(offset) in
  let _,conseq = dest_imp(snd(strip_forall(concl dt))) in
  let len,inst = dest_pair(rand conseq) in
  let _,step_args = strip_comb(concl original_step) in
  let source = hd step_args in
  GEN_REWRITE_TAC I [assurance_zero_scalar_step] THEN CONJ_TAC THENL
   [ASSURANCE_ZERO_LOCAL_POLICY_TAC decode_ths offset original_step update;
    MATCH_MP_TAC(ISPECL [len; inst; source] ASSURANCE_DECODED_SCALAR_UNIQUE) THEN
    CONJ_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(REWRITE_RULE[ADD_CLAUSES] dt) THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC(ISPECL [mk_numeral(num offset); len; inst]
        ABI_CRYPTO_REGISTERED_SITE_IS_SCALAR) THEN
      REWRITE_TAC[abi_crypto_site]]];;

let ASSURANCE_ZERO_SCALAR_BASIC_STEP_TAC offset decode_ths sname
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
        [ASSURANCE_ZERO_SCALAR_LOCAL_TAC decode_ths offset original_step update;
         MP_TAC update]))]) (asl,w);;

let ASSURANCE_ZERO_SCALAR_STEP_TAC offset (length_th,decode_ths) sname =
  ASSURANCE_ZERO_SCALAR_BASIC_STEP_TAC offset decode_ths sname None THEN
  NONSELFMODIFYING_STATE_UPDATE_TAC
    (MATCH_MP bytes_loaded_update length_th) THEN
  ASSUMPTION_STATE_UPDATE_TAC THEN
  DISCH_THEN(fun update ->
    let reads = STATE_UPDATE_NEW_RULE update in
    if reads = [] then ALL_TAC else
    MP_TAC(end_itlist CONJ reads) THEN
    ASSEMBLER_SIMPLIFY_TAC THEN STRIP_TAC);;

let ASSURANCE_CRYPTO_ZERO_SCALAR_QUALIFIED_POLICY = prove
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
      (assurance_zero_scalar_step
        (\a. rp a /\ assurance_region stackpointer 8 a) (\a. F) xp) s`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; fst ASSURANCE_CRYPTO_EXEC] THEN STRIP_TAC THEN
  MAP_EVERY (fun (offset,sname) ->
    ASSURANCE_ZERO_SCALAR_STEP_TAC offset ASSURANCE_CRYPTO_EXEC sname)
    [0,"zs1";4,"zs2";7,"zs3";10,"zs4";14,"zs5";93,"zs6"] THEN
  REWRITE_TAC[assurance_checked_run] THEN ASM_REWRITE_TAC[APPEND]);;
