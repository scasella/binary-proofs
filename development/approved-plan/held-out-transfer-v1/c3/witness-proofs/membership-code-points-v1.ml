(* Only five frozen C3 initial-code sites/arrays; fixed numeric load-bias identities. *)
let C3W_CODE_BYTE_POINTS = prove
 (`!lib_file client_file payload.
    fb_file_code lib_file /\ clw_file_code lib_file /\ c3_file_code client_file
    ==> (!i. i<89 ==> c3w_memory lib_file client_file payload
          (word_add (word 0x23001120) (word i))=EL i c3_caller_mc) /\
        (!i. i<6 ==> c3w_memory lib_file client_file payload
          (word_add (word 0x23001030) (word i))=EL i c3_crypto_plt_prefix) /\
        (!i. i<6 ==> c3w_memory lib_file client_file payload
          (word_add (word 0x23001040) (word i))=EL i c3_cleanse_plt_prefix) /\
        (!i. i<95 ==> c3w_memory lib_file client_file payload
          (word_add (word 0x10241840) (word i))=EL i crypto_memcmp_mc) /\
        (!i. i<97 ==> c3w_memory lib_file client_file payload
          (word_add (word 0x102417d0) (word i))=EL i openssl_cleanse_mc),
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN
      `val(word_add (word 0x23001120) (word i):int64)=0x23001120+i`
      ASSUME_TAC THENL
     [REWRITE_TAC[GSYM WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
      CONV_TAC NUM_REDUCE_CONV THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `c3_immutable(val(word_add (word 0x23001120) (word i):int64))`
      ASSUME_TAC THENL
     [ASM_REWRITE_TAC[c3_immutable] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[C3W_MEMORY_IMMUTABLE;
      ARITH_RULE `!i. (0x23001120+i)-0x23000000=0x1120+i`] THEN
    ASM_MESON_TAC[c3_file_code];
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN
      `val(word_add (word 0x23001030) (word i):int64)=0x23001030+i`
      ASSUME_TAC THENL
     [REWRITE_TAC[GSYM WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
      CONV_TAC NUM_REDUCE_CONV THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `c3_immutable(val(word_add (word 0x23001030) (word i):int64))`
      ASSUME_TAC THENL
     [ASM_REWRITE_TAC[c3_immutable] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[C3W_MEMORY_IMMUTABLE;
      ARITH_RULE `!i. (0x23001030+i)-0x23000000=0x1030+i`] THEN
    ASM_MESON_TAC[c3_file_code];
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN
      `val(word_add (word 0x23001040) (word i):int64)=0x23001040+i`
      ASSUME_TAC THENL
     [REWRITE_TAC[GSYM WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
      CONV_TAC NUM_REDUCE_CONV THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `c3_immutable(val(word_add (word 0x23001040) (word i):int64))`
      ASSUME_TAC THENL
     [ASM_REWRITE_TAC[c3_immutable] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[C3W_MEMORY_IMMUTABLE;
      ARITH_RULE `!i. (0x23001040+i)-0x23000000=0x1040+i`] THEN
    ASM_MESON_TAC[c3_file_code];
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN
      `val(word_add (word 0x10241840) (word i):int64)=0x10241840+i`
      ASSUME_TAC THENL
     [REWRITE_TAC[GSYM WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
      CONV_TAC NUM_REDUCE_CONV THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `fb_immutable(val(word_add (word 0x10241840) (word i):int64))`
      ASSUME_TAC THENL
     [ASM_REWRITE_TAC[fb_immutable] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[C3W_MEMORY_IMMUTABLE;
      ARITH_RULE `!i. (0x10241840+i)-0x10000000=0x241840+i`] THEN
    ASM_MESON_TAC[fb_file_code];
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN
      `val(word_add (word 0x102417d0) (word i):int64)=0x102417d0+i`
      ASSUME_TAC THENL
     [REWRITE_TAC[GSYM WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
      CONV_TAC NUM_REDUCE_CONV THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `fb_immutable(val(word_add (word 0x102417d0) (word i):int64))`
      ASSUME_TAC THENL
     [ASM_REWRITE_TAC[fb_immutable] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[C3W_MEMORY_IMMUTABLE;
      ARITH_RULE `!i. (0x102417d0+i)-0x10000000=0x2417d0+i`] THEN
    ASM_MESON_TAC[clw_file_code]]);;
print_endline "C3W_MEMBERSHIP_CODE_BYTE_POINTS_V1_COMPLETE";;
