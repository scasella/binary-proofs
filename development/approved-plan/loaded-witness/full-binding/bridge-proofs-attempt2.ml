(* Additive recipe over bridge-freeze-v1.json, with unchanged full binding V2.
   Recover the literal file slice from the exact machine Pre and whole-image
   correspondence, rather than assuming a second file-slice premise. *)

let FB_CODE_LENGTH = prove
 (`LENGTH crypto_memcmp_mc = 95`,
  REWRITE_TAC[crypto_memcmp_mc; LENGTH] THEN CONV_TAC NUM_REDUCE_CONV);;

let FB_BYTES_LOADED_BYTE = prove
 (`!s pc i.
    bytes_loaded s pc crypto_memcmp_mc /\ i<95
    ==> read memory s (word_add pc (word i)) = EL i crypto_memcmp_mc`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:x86state`; `pc:int64`; `crypto_memcmp_mc:byte list`;
                 `i:num`; `1`] BYTES_LOADED_SUB_LIST) THEN
  ASM_REWRITE_TAC[SUB_LIST_1; FB_CODE_LENGTH] THEN
  REWRITE_TAC[bytes_loaded; LENGTH; READ_COMPONENT_COMPOSE;
              num_CONV `1`; bytelist_clauses; CONS_11]);;

let FB_CODE_IMAGE_TO_FILE = prove
 (`!file_bytes initial_rw padding image.
    fb_full_image file_bytes initial_rw padding image /\ lw_reference_code image
    ==> fb_file_code file_bytes`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[fb_file_code] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(image:int64->byte)(word(0x10241840+(i:num)):int64) =
                 EL i crypto_memcmp_mc`
    ASSUME_TAC THENL
   [MP_TAC(SPEC `i:num` (REWRITE_RULE[lw_reference_code]
      (ASSUME `lw_reference_code (image:int64->byte)`))) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `fb_immutable (0x10241840+(i:num))` ASSUME_TAC THENL
   [REWRITE_TAC[fb_immutable] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC `word(0x10241840+(i:num)):int64` (REWRITE_RULE[fb_full_image]
    (ASSUME `fb_full_image (file_bytes:num->byte) (initial_rw:int64->byte)
                   (padding:int64->byte) (image:int64->byte)`))) THEN
  ASM_SIMP_TAC[LW_CODE_VALUE; LW_CODE_IN_IMAGE; fb_reference_image;
    ARITH_RULE `(0x10241840+(i:num))-0x10000000 = 0x241840+i`] THEN
  MESON_TAC[]);;

let FB_PRE_FILE_CODE = prove
 (fb_pre_file_code_statement,
  REPEAT GEN_TAC THEN REWRITE_TAC[fb_pre] THEN STRIP_TAC THEN
  MATCH_MP_TAC (SPECL [`file_bytes:num->byte`; `initial_rw:int64->byte`;
    `padding:int64->byte`;
    `read memory (FST(fb_machine (image:int64->byte) (p:int64) (q:int64)
      (n:num) (different:bool))):int64->byte`]
    FB_CODE_IMAGE_TO_FILE) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `bytes_loaded (FST(fb_machine (image:int64->byte) (p:int64) (q:int64)
                         (n:num) (different:bool)))
      (word 0x10241840) crypto_memcmp_mc` ASSUME_TAC THENL
   [ASM_MESON_TAC[bp_e2_crypto_pre]; ALL_TAC] THEN
  REWRITE_TAC[lw_reference_code] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`FST(fb_machine (image:int64->byte) (p:int64) (q:int64)
                               (n:num) (different:bool)):x86state`;
                 `word 0x10241840:int64`; `i:num`] FB_BYTES_LOADED_BYTE) THEN
  ASM_REWRITE_TAC[GSYM WORD_ADD]);;
