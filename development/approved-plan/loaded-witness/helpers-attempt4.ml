(* Requires frozen definitions-v3/statements-v3 and the pinned x86 base,
   actual byte literal, assurance policy and unchanged scalar E2 Pre. *)

let LW_STACK_IN_OVERLAY = prove
 (`!p q n a. 0x300008 <= a /\ a < 0x300010
    ==> lw_overlay_domain p q n a`,
  REWRITE_TAC[lw_overlay_domain] THEN ARITH_TAC);;

let LW_PRESERVES_IMAGE = prove
 (lw_preserves_image_statement,
  REPEAT GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `~lw_overlay_domain p q n (val(a:int64))` ASSUME_TAC THENL
   [ASM_MESON_TAC[lw_layout]; ALL_TAC] THEN
  REWRITE_TAC[lw_memory] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[LW_STACK_IN_OVERLAY]);;

let LW_LAYOUT_EMPTY = prove
 (`!p q. lw_layout p q 0`,
  REWRITE_TAC[lw_layout; lw_overlay_domain; lw_pagecover; lw_image_domain] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC);;

let LW_CASE_LAYOUT = prove
 (`lw_layout (word 0x200001) (word 0x200041) 17 /\
   lw_layout (word 0x200003) (word 0x200003) 33 /\
   lw_layout (word 0x200001) (word 0x200002) 17 /\
   lw_layout (word 0x200007) (word 0x200087) 16 /\
   lw_layout (word (2 EXP 47-1)) (word 0x200001) 1 /\
   lw_layout (word (2 EXP 64-1)) (word 0x200001) 1 /\
   lw_layout (word 0x200fff) (word 0x210003) 17`,
  REWRITE_TAC[lw_layout; lw_overlay_domain; lw_pagecover; lw_image_domain;
              VAL_WORD; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REPEAT CONJ_TAC THEN ARITH_TAC);;

let LW_CODE_VALUE = prove
 (`!i. i<95 ==> val(word(0x10241840+i):int64) = 0x10241840+i`,
  REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC);;

let LW_CODE_IN_IMAGE = prove
 (`!i. i<95 ==> lw_image_domain (0x10241840+i)`,
  REWRITE_TAC[lw_image_domain] THEN ARITH_TAC);;

let LW_CODE_BYTE = prove
 (`!image p q n different i.
    lw_reference_code image /\ lw_layout p q n /\ i<95
    ==> lw_memory image p q n different (word(0x10241840+i)) =
        EL i crypto_memcmp_mc`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
    `lw_memory image p q n different (word(0x10241840+i)) =
     image(word(0x10241840+i))` SUBST1_TAC THENL
   [ASM_MESON_TAC[LW_PRESERVES_IMAGE; LW_CODE_VALUE; LW_CODE_IN_IMAGE];
    ASM_MESON_TAC[lw_reference_code]]);;

let rec LW_READ_BYTELIST_EXPAND_CONV tm =
 ((GEN_REWRITE_CONV I [List.nth(CONJUNCTS bytelist_clauses) 0]) ORELSEC
  (LAND_CONV(funpow 2 RAND_CONV num_CONV) THENC
   GEN_REWRITE_CONV I [List.nth(CONJUNCTS bytelist_clauses) 1] THENC
   RAND_CONV LW_READ_BYTELIST_EXPAND_CONV)) tm;;

let rec LW_READ_BYTES_EXPAND_CONV tm =
 ((GEN_REWRITE_CONV I [List.nth(CONJUNCTS bytes) 0]) ORELSEC
  (LAND_CONV(funpow 2 RAND_CONV num_CONV) THENC
   GEN_REWRITE_CONV I [List.nth(CONJUNCTS bytes) 1] THENC
   LAND_CONV LW_READ_BYTES_EXPAND_CONV)) tm;;

let lw_code_byte_numeral_ths = List.init 95 (fun i ->
  CONV_RULE (NUM_REDUCE_CONV THENC WORD_REDUCE_CONV)
    (SPECL [`image:int64->byte`; `p:int64`; `q:int64`; `n:num`;
            `different:bool`; mk_numeral(num i)] LW_CODE_BYTE));;

let LW_CODE_LOADED = prove
 (`!image p q n different.
    lw_reference_code image /\ lw_layout p q n
    ==> bytes_loaded (lw_state image p q n different)
          (word 0x10241840) crypto_memcmp_mc`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[bytes_loaded; lw_state; READ_COMPONENT_COMPOSE;
              x86state_COMPONENTS; crypto_memcmp_mc; LENGTH] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC(LAND_CONV LW_READ_BYTELIST_EXPAND_CONV) THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  ASM_SIMP_TAC lw_code_byte_numeral_ths THEN
  REWRITE_TAC[crypto_memcmp_mc] THEN
  CONV_TAC(DEPTH_CONV EL_CONV) THEN REWRITE_TAC[]);;

let LW_RETURN_SLOT = prove
 (`!image p q n different.
    read (bytes64 (word 0x300008)) (lw_memory image p q n different) =
      (word 0x400000:int64)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[bytes64; READ_COMPONENT_COMPOSE; asword; read; through] THEN
  CONV_TAC(LAND_CONV(RAND_CONV LW_READ_BYTES_EXPAND_CONV)) THEN
  REWRITE_TAC[lw_memory] THEN CONV_TAC WORD_REDUCE_CONV THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_REDUCE_CONV THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_REDUCE_CONV);;

let LW_REFERENCE_OVERLAY = prove
 (lw_reference_overlay_statement,
  REWRITE_TAC[lw_reference_code; lw_reference_overlay; VAL_WORD; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[MOD_LT;
    ARITH_RULE `(i:num)<95 ==> 270800960+i<18446744073709551616`] THEN
  ASM_REWRITE_TAC[ARITH_RULE `270800960 <= 270800960+(i:num)`;
                  ARITH_RULE `(270800960+i:num)-270800960 = i`] THEN
  ASM_ARITH_TAC);;

let LW_REFERENCE_EXISTS = prove
 (lw_reference_exists_statement,
  EXISTS_TAC `lw_reference_overlay (\a:int64. word 0)` THEN
  REWRITE_TAC[LW_REFERENCE_OVERLAY]);;

let LW_ZERO_SPAN = prove
 (`!perm p. assurance_span_ok perm (val(p:int64)) 0`,
  REWRITE_TAC[assurance_span_ok; ADD_CLAUSES; LT] THEN
  REPEAT GEN_TAC THEN MP_TAC(ISPEC `p:int64` VAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_64] THEN ARITH_TAC);;
