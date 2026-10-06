(* New C2 entrymembership attempt. Frozen beforehand; no execution or target-correctness premise. *)
(* Memory/data binding only. Immutable bytes are arbitrary supplied file bytes. *)
let C2W_MEMORY_IMMUTABLE = prove
 (c2w_memory_immutable_statement,
  REPEAT GEN_TAC THEN CONJ_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `c2w_memory lib_file client_file p k different (addr:int64)=
    c2w_seed lib_file client_file p k different addr`
   SUBST1_TAC THENL
   [MATCH_MP_TAC C2W_MEMORY_OUTSIDE THEN
    REWRITE_TAC[assurance_region;VAL_WORD;DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    FIRST_X_ASSUM MP_TAC THEN
    REWRITE_TAC[fb_immutable;c2_immutable] THEN ARITH_TAC;
    ASM_REWRITE_TAC[c2w_seed];
    MATCH_MP_TAC C2W_MEMORY_OUTSIDE THEN
    REWRITE_TAC[assurance_region;VAL_WORD;DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    FIRST_X_ASSUM MP_TAC THEN
    REWRITE_TAC[fb_immutable;c2_immutable] THEN ARITH_TAC;
    SUBGOAL_THEN `~fb_immutable (val(addr:int64))` ASSUME_TAC THENL
     [FIRST_X_ASSUM MP_TAC THEN
      REWRITE_TAC[fb_immutable;c2_immutable] THEN ARITH_TAC;
      ASM_REWRITE_TAC[c2w_seed]]]);;
let C2W_MEMORY_IMAGES = prove
 (c2w_memory_images_statement,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[fb_full_image;fb_reference_image;
    c2_full_image;c2_reference_image] THEN
  CONJ_TAC THEN GEN_TAC THEN DISCH_TAC THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[C2W_MEMORY_IMMUTABLE;COND_ID]);;


let c2w_client_length_rewrites=map
 (fun th -> CONV_RULE
  (RAND_CONV (REWRITE_CONV[LENGTH] THENC NUM_REDUCE_CONV))
  (AP_TERM `LENGTH:byte list->num` th))
 [c2_caller_mc;c2_crypto_plt_prefix;c2_cleanse_plt_prefix];;
let c2w_load_immutable_block pc immutable immutable_def shift =
 MATCH_MP_TAC C2W_BYTES_LOADED_READS THEN
 REWRITE_TAC(c2w_client_length_rewrites @ [BP_PUBLIC_CRYPTO_MEMCMP_CODE_LENGTH;BP_PUBLIC_OPENSSL_CLEANSE_CODE_LENGTH]) THEN
 CONV_TAC NUM_REDUCE_CONV THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
 REWRITE_TAC[C2W_STATE_PROJECTIONS] THEN
 let addr=subst[pc,`c:num`] `word_add (word c:int64) (word i)` in
 let nataddr=subst[pc,`c:num`] `c+i:num` in
 let value=mk_comb(`val:int64->num`,addr) in
 SUBGOAL_THEN (mk_eq(value,nataddr)) ASSUME_TAC THENL
  [REWRITE_TAC[GSYM WORD_ADD;VAL_WORD;DIMINDEX_64] THEN
   CONV_TAC NUM_REDUCE_CONV THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC;
   SUBGOAL_THEN (mk_comb(immutable,value)) ASSUME_TAC THENL
    [ASM_REWRITE_TAC[] THEN REWRITE_TAC[immutable_def] THEN ASM_ARITH_TAC;
     ASM_SIMP_TAC[C2W_MEMORY_IMMUTABLE] THEN
     ASM_REWRITE_TAC[shift] THEN ASM_MESON_TAC[]]];;
let c2w_file_offset_shift imagebase fileoffset =
 let i=`i:num` in GEN i
  (CONV_RULE (ONCE_DEPTH_CONV NUM_REDUCE_CONV)
   (REWRITE_RULE[ADD_ASSOC]
    (SPECL[imagebase;subst[fileoffset,`k:num`] `k+i:num`] ADD_SUB2)));;
let C2W_LOADED_CODE = prove
 (c2w_loaded_code_statement,
  REWRITE_TAC[fb_file_code;clw_file_code;c2_file_code] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[c2_loaded_code] THEN
  REPEAT CONJ_TAC THENL
   [c2w_load_immutable_block `0x22001120:num` `c2_immutable:num->bool`
     c2_immutable (c2w_file_offset_shift `0x22000000:num` `0x1120:num`);
    c2w_load_immutable_block `0x22001030:num` `c2_immutable:num->bool`
     c2_immutable (c2w_file_offset_shift `0x22000000:num` `0x1030:num`);
    c2w_load_immutable_block `0x22001040:num` `c2_immutable:num->bool`
     c2_immutable (c2w_file_offset_shift `0x22000000:num` `0x1040:num`);
    c2w_load_immutable_block `0x10241840:num` `fb_immutable:num->bool`
     fb_immutable (c2w_file_offset_shift `0x10000000:num` `0x241840:num`);
    c2w_load_immutable_block `0x102417d0:num` `fb_immutable:num->bool`
     fb_immutable (c2w_file_offset_shift `0x10000000:num` `0x2417d0:num`)]);;
