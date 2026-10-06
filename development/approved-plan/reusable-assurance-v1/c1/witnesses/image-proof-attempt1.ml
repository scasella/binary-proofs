(* Memory/data binding only. Immutable bytes are arbitrary supplied file bytes. *)
let CW_MEMORY_IMMUTABLE = prove
 (cw_memory_immutable_statement,
  REPEAT GEN_TAC THEN CONJ_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `cw_memory lib_file client_file p k different (addr:int64)=
    cw_seed lib_file client_file p k different addr`
   SUBST1_TAC THENL
   [MATCH_MP_TAC CW_MEMORY_OUTSIDE THEN
    REWRITE_TAC[assurance_region;VAL_WORD;DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    FIRST_X_ASSUM MP_TAC THEN
    REWRITE_TAC[fb_immutable;c1_immutable] THEN ARITH_TAC;
    ASM_REWRITE_TAC[cw_seed];
    MATCH_MP_TAC CW_MEMORY_OUTSIDE THEN
    REWRITE_TAC[assurance_region;VAL_WORD;DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    FIRST_X_ASSUM MP_TAC THEN
    REWRITE_TAC[fb_immutable;c1_immutable] THEN ARITH_TAC;
    SUBGOAL_THEN `~fb_immutable (val(addr:int64))` ASSUME_TAC THENL
     [FIRST_X_ASSUM MP_TAC THEN
      REWRITE_TAC[fb_immutable;c1_immutable] THEN ARITH_TAC;
      ASM_REWRITE_TAC[cw_seed]]]);;
let CW_MEMORY_IMAGES = prove
 (cw_memory_images_statement,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[fb_full_image;fb_reference_image;
    c1_full_image;c1_reference_image] THEN
  CONJ_TAC THEN GEN_TAC THEN DISCH_TAC THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[CW_MEMORY_IMMUTABLE;COND_ID]);;


let cw_client_length_rewrites=map
 (fun th -> CONV_RULE
  (RAND_CONV (REWRITE_CONV[LENGTH] THENC NUM_REDUCE_CONV))
  (AP_TERM `LENGTH:byte list->num` th))
 [c1_crypto_caller_mc;c1_crypto_plt_prefix];;
let cw_load_immutable_block pc immutable immutable_def shift =
 MATCH_MP_TAC CW_BYTES_LOADED_READS THEN
 REWRITE_TAC(cw_client_length_rewrites @ [BP_PUBLIC_CRYPTO_MEMCMP_CODE_LENGTH]) THEN
 CONV_TAC NUM_REDUCE_CONV THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
 REWRITE_TAC[CW_STATE_PROJECTIONS] THEN
 let addr=subst[pc,`c:num`] `word_add (word c:int64) (word i)` in
 let nataddr=subst[pc,`c:num`] `c+i:num` in
 let value=mk_comb(`val:int64->num`,addr) in
 SUBGOAL_THEN (mk_eq(value,nataddr)) ASSUME_TAC THENL
  [REWRITE_TAC[GSYM WORD_ADD;VAL_WORD;DIMINDEX_64] THEN
   CONV_TAC NUM_REDUCE_CONV THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC;
   SUBGOAL_THEN (mk_comb(immutable,value)) ASSUME_TAC THENL
    [ASM_REWRITE_TAC[] THEN REWRITE_TAC[immutable_def] THEN ASM_ARITH_TAC;
     ASM_SIMP_TAC[CW_MEMORY_IMMUTABLE] THEN
     ASM_REWRITE_TAC[shift] THEN ASM_MESON_TAC[]]];;
let cw_file_offset_shift imagebase fileoffset =
 let i=`i:num` in GEN i
  (CONV_RULE (ONCE_DEPTH_CONV NUM_REDUCE_CONV)
   (REWRITE_RULE[ADD_ASSOC]
    (SPECL[imagebase;subst[fileoffset,`k:num`] `k+i:num`] ADD_SUB2)));;
let CW_LOADED_CODE = prove
 (cw_loaded_code_statement,
  REWRITE_TAC[fb_file_code;c1_file_code] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[c1_loaded_code] THEN
  REPEAT CONJ_TAC THENL
   [cw_load_immutable_block `0x21001110:num` `c1_immutable:num->bool`
     c1_immutable (cw_file_offset_shift `0x21000000:num` `0x1110:num`);
    cw_load_immutable_block `0x21001030:num` `c1_immutable:num->bool`
     c1_immutable (cw_file_offset_shift `0x21000000:num` `0x1030:num`);
    cw_load_immutable_block `0x10241840:num` `fb_immutable:num->bool`
     fb_immutable (cw_file_offset_shift `0x10000000:num` `0x241840:num`)]);;
