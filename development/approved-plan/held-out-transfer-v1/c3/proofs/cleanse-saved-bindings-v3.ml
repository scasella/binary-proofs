(* Concrete C3 stack/code/GOT bindings preserved by the actual cleanse.
 Named obligation: second comparison handoff and final return saved slots.
 Fixed component/region facts only; no new generic frame law or algorithm. *)
let C3_CLEANSE_SAVED_BINDINGS = prove
 (`!lib_file lib_rw lib_padding client_file client_rw client_padding
 stackpointer ra p q n m rp wp xp ordinary initial a entry returned.
 c3_pre lib_file lib_rw lib_padding client_file client_rw client_padding
   stackpointer ra p q n m rp wp xp ordinary(initial,a) /\
 c3_saved_prefix stackpointer p q n m initial entry /\
 bp_e2_cleanse_call_post 0x102417d0(word_sub stackpointer(word 48))
   (word 0x2300114c)p n(read memory entry)entry returned
 ==> read(memory :> bytes64(word_sub stackpointer(word 8)))returned=read R13 initial /\
     read(memory :> bytes64(word_sub stackpointer(word 16)))returned=read R12 initial /\
     read(memory :> bytes64(word_sub stackpointer(word 24)))returned=read RBP initial /\
     read(memory :> bytes64(word_sub stackpointer(word 32)))returned=read RBX initial /\
     read(memory :> bytes64 stackpointer)returned=ra /\
     c3_loaded_code returned /\ c3_got returned`,
 REPEAT GEN_TAC THEN STRIP_TAC THEN
 UNDISCH_TAC `c3_pre lib_file lib_rw lib_padding client_file client_rw client_padding
   stackpointer ra p q n m rp wp xp ordinary(initial,a)` THEN
 REWRITE_TAC[c3_pre] THEN STRIP_TAC THEN
 UNDISCH_TAC `c3_saved_prefix stackpointer p q n m (initial:x86state)(entry:x86state)` THEN
 REWRITE_TAC[c3_saved_prefix] THEN STRIP_TAC THEN
 UNDISCH_TAC `bp_e2_cleanse_call_post 0x102417d0(word_sub(stackpointer:int64)(word 48))
   (word 0x2300114c)p n(read memory(entry:x86state))entry returned` THEN
 REWRITE_TAC[bp_e2_cleanse_call_post] THEN STRIP_TAC THEN
 SUBGOAL_THEN `val(p:int64)+n<=2 EXP 64` ASSUME_TAC THENL
 [UNDISCH_TAC `assurance_span_ok(\addr. wp addr /\ ordinary addr)(val(p:int64))n` THEN
  REWRITE_TAC[assurance_span_ok] THEN DISCH_THEN(ACCEPT_TAC o CONJUNCT1);ALL_TAC] THEN
 SUBGOAL_THEN `32<=val(stackpointer:int64) /\ 24<=val stackpointer /\
               16<=val stackpointer /\ 8<=val stackpointer` STRIP_ASSUME_TAC THENL
 [ASM_ARITH_TAC;ALL_TAC] THEN
 SUBGOAL_THEN `nonoverlapping(p,n)(word_sub(stackpointer:int64)(word 48),48)` ASSUME_TAC THENL
 [MATCH_MP_TAC(ISPECL[`p:int64`;`word_sub(stackpointer:int64)(word 48)`;`n:num`;`48`]HT_REGION_NONOVERLAPPING) THEN
  ASM_SIMP_TAC[C3_STACK_SUB48_VALUE;GSYM c3_scratch] THEN
  MP_TAC(CONV_RULE NUM_REDUCE_CONV(SPEC `stackpointer:int64`VAL_BOUND_64)) THEN ASM_ARITH_TAC;
 ALL_TAC] THEN
 SUBGOAL_THEN `nonoverlapping(p,n)(stackpointer:int64,8)` ASSUME_TAC THENL
 [MATCH_MP_TAC(ISPECL[`p:int64`;`stackpointer:int64`;`n:num`;`8`]HT_REGION_NONOVERLAPPING) THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];ALL_TAC] THEN
 SUBGOAL_THEN `nonoverlapping(p,n)(word 0x23001120:int64,89)` ASSUME_TAC THENL
 [MATCH_MP_TAC(ISPECL[`p:int64`;`word 0x23001120:int64`;`n:num`;`89`]HT_REGION_NONOVERLAPPING) THEN
  ASM_REWRITE_TAC[VAL_WORD;DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_MESON_TAC[];ALL_TAC] THEN
 SUBGOAL_THEN `nonoverlapping(p,n)(word 0x23001030:int64,6)` ASSUME_TAC THENL
 [MATCH_MP_TAC(ISPECL[`p:int64`;`word 0x23001030:int64`;`n:num`;`6`]HT_REGION_NONOVERLAPPING) THEN
  ASM_REWRITE_TAC[VAL_WORD;DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_MESON_TAC[];ALL_TAC] THEN
 SUBGOAL_THEN `nonoverlapping(p,n)(word 0x23001040:int64,6)` ASSUME_TAC THENL
 [MATCH_MP_TAC(ISPECL[`p:int64`;`word 0x23001040:int64`;`n:num`;`6`]HT_REGION_NONOVERLAPPING) THEN
  ASM_REWRITE_TAC[VAL_WORD;DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_MESON_TAC[];ALL_TAC] THEN
 SUBGOAL_THEN `nonoverlapping(p,n)(word 0x23003fd0:int64,8)` ASSUME_TAC THENL
 [MATCH_MP_TAC(ISPECL[`p:int64`;`word 0x23003fd0:int64`;`n:num`;`8`]HT_REGION_NONOVERLAPPING) THEN
  ASM_REWRITE_TAC[VAL_WORD;DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_MESON_TAC[];ALL_TAC] THEN
 SUBGOAL_THEN `nonoverlapping(p,n)(word 0x23003fd8:int64,8)` ASSUME_TAC THENL
 [MATCH_MP_TAC(ISPECL[`p:int64`;`word 0x23003fd8:int64`;`n:num`;`8`]HT_REGION_NONOVERLAPPING) THEN
  ASM_REWRITE_TAC[VAL_WORD;DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_MESON_TAC[];ALL_TAC] THEN
 SUBGOAL_THEN `nonoverlapping(p,n)(word 0x10241840:int64,95)` ASSUME_TAC THENL
 [MATCH_MP_TAC(ISPECL[`p:int64`;`word 0x10241840:int64`;`n:num`;`95`]HT_REGION_NONOVERLAPPING) THEN
  ASM_REWRITE_TAC[VAL_WORD;DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_MESON_TAC[];ALL_TAC] THEN
 SUBGOAL_THEN `nonoverlapping(p,n)(word 0x102417d0:int64,97)` ASSUME_TAC THENL
 [MATCH_MP_TAC(ISPECL[`p:int64`;`word 0x102417d0:int64`;`n:num`;`97`]HT_REGION_NONOVERLAPPING) THEN
  ASM_REWRITE_TAC[VAL_WORD;DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_MESON_TAC[];ALL_TAC] THEN
 RULE_ASSUM_TAC(REWRITE_RULE[c3_loaded_code;c3_got;bytes_loaded]) THEN
 REWRITE_TAC[c3_loaded_code;c3_got;bytes_loaded] THEN REPEAT CONJ_TAC THENL
 [MP_TAC(ISPECL[`memory :> bytes64(word_sub(stackpointer:int64)(word 8))`;
  `[RIP;RSP;RAX;RDI;RSI]:((x86state,int64)component)list`;
  `SOME_FLAGS:((x86state,bool)component)list`;
  `[memory :> bytes(p,n)]:((x86state,num)component)list`;
  `[events]:((x86state,uarch_event list)component)list`;`entry:x86state`;`returned:x86state`]
  R1_SECRET_FOUR_FRAME_PRESERVATION) THEN
 REWRITE_TAC[ALL] THEN ANTS_TAC THENL
 [ASM_REWRITE_TAC[] THEN REWRITE_TAC[SOME_FLAGS;ALL] THEN REPEAT CONJ_TAC THEN
  ORTHOGONAL_COMPONENTS_TAC THEN
  ASM_SIMP_TAC[fst C3_CALLER_RAW_EXEC;fst C3_CRYPTO_PLT_RAW_EXEC;fst C3_CLEANSE_PLT_RAW_EXEC;
   BP_PUBLIC_CRYPTO_MEMCMP_CODE_LENGTH;BP_PUBLIC_OPENSSL_CLEANSE_CODE_LENGTH;
   VAL_WORD_SUB_CASES;VAL_WORD;DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[] THEN NONOVERLAPPING_TAC;
  ASM_REWRITE_TAC[]];
 MP_TAC(ISPECL[`memory :> bytes64(word_sub(stackpointer:int64)(word 16))`;
  `[RIP;RSP;RAX;RDI;RSI]:((x86state,int64)component)list`;
  `SOME_FLAGS:((x86state,bool)component)list`;
  `[memory :> bytes(p,n)]:((x86state,num)component)list`;
  `[events]:((x86state,uarch_event list)component)list`;`entry:x86state`;`returned:x86state`]
  R1_SECRET_FOUR_FRAME_PRESERVATION) THEN
 REWRITE_TAC[ALL] THEN ANTS_TAC THENL
 [ASM_REWRITE_TAC[] THEN REWRITE_TAC[SOME_FLAGS;ALL] THEN REPEAT CONJ_TAC THEN
  ORTHOGONAL_COMPONENTS_TAC THEN
  ASM_SIMP_TAC[fst C3_CALLER_RAW_EXEC;fst C3_CRYPTO_PLT_RAW_EXEC;fst C3_CLEANSE_PLT_RAW_EXEC;
   BP_PUBLIC_CRYPTO_MEMCMP_CODE_LENGTH;BP_PUBLIC_OPENSSL_CLEANSE_CODE_LENGTH;
   VAL_WORD_SUB_CASES;VAL_WORD;DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[] THEN NONOVERLAPPING_TAC;
  ASM_REWRITE_TAC[]];
 MP_TAC(ISPECL[`memory :> bytes64(word_sub(stackpointer:int64)(word 24))`;
  `[RIP;RSP;RAX;RDI;RSI]:((x86state,int64)component)list`;
  `SOME_FLAGS:((x86state,bool)component)list`;
  `[memory :> bytes(p,n)]:((x86state,num)component)list`;
  `[events]:((x86state,uarch_event list)component)list`;`entry:x86state`;`returned:x86state`]
  R1_SECRET_FOUR_FRAME_PRESERVATION) THEN
 REWRITE_TAC[ALL] THEN ANTS_TAC THENL
 [ASM_REWRITE_TAC[] THEN REWRITE_TAC[SOME_FLAGS;ALL] THEN REPEAT CONJ_TAC THEN
  ORTHOGONAL_COMPONENTS_TAC THEN
  ASM_SIMP_TAC[fst C3_CALLER_RAW_EXEC;fst C3_CRYPTO_PLT_RAW_EXEC;fst C3_CLEANSE_PLT_RAW_EXEC;
   BP_PUBLIC_CRYPTO_MEMCMP_CODE_LENGTH;BP_PUBLIC_OPENSSL_CLEANSE_CODE_LENGTH;
   VAL_WORD_SUB_CASES;VAL_WORD;DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[] THEN NONOVERLAPPING_TAC;
  ASM_REWRITE_TAC[]];
 MP_TAC(ISPECL[`memory :> bytes64(word_sub(stackpointer:int64)(word 32))`;
  `[RIP;RSP;RAX;RDI;RSI]:((x86state,int64)component)list`;
  `SOME_FLAGS:((x86state,bool)component)list`;
  `[memory :> bytes(p,n)]:((x86state,num)component)list`;
  `[events]:((x86state,uarch_event list)component)list`;`entry:x86state`;`returned:x86state`]
  R1_SECRET_FOUR_FRAME_PRESERVATION) THEN
 REWRITE_TAC[ALL] THEN ANTS_TAC THENL
 [ASM_REWRITE_TAC[] THEN REWRITE_TAC[SOME_FLAGS;ALL] THEN REPEAT CONJ_TAC THEN
  ORTHOGONAL_COMPONENTS_TAC THEN
  ASM_SIMP_TAC[fst C3_CALLER_RAW_EXEC;fst C3_CRYPTO_PLT_RAW_EXEC;fst C3_CLEANSE_PLT_RAW_EXEC;
   BP_PUBLIC_CRYPTO_MEMCMP_CODE_LENGTH;BP_PUBLIC_OPENSSL_CLEANSE_CODE_LENGTH;
   VAL_WORD_SUB_CASES;VAL_WORD;DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[] THEN NONOVERLAPPING_TAC;
  ASM_REWRITE_TAC[]];
 MP_TAC(ISPECL[`memory :> bytes64(stackpointer:int64)`;
  `[RIP;RSP;RAX;RDI;RSI]:((x86state,int64)component)list`;
  `SOME_FLAGS:((x86state,bool)component)list`;
  `[memory :> bytes(p,n)]:((x86state,num)component)list`;
  `[events]:((x86state,uarch_event list)component)list`;`entry:x86state`;`returned:x86state`]
  R1_SECRET_FOUR_FRAME_PRESERVATION) THEN
 REWRITE_TAC[ALL] THEN ANTS_TAC THENL
 [ASM_REWRITE_TAC[] THEN REWRITE_TAC[SOME_FLAGS;ALL] THEN REPEAT CONJ_TAC THEN
  ORTHOGONAL_COMPONENTS_TAC THEN
  ASM_SIMP_TAC[fst C3_CALLER_RAW_EXEC;fst C3_CRYPTO_PLT_RAW_EXEC;fst C3_CLEANSE_PLT_RAW_EXEC;
   BP_PUBLIC_CRYPTO_MEMCMP_CODE_LENGTH;BP_PUBLIC_OPENSSL_CLEANSE_CODE_LENGTH;
   VAL_WORD_SUB_CASES;VAL_WORD;DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[] THEN NONOVERLAPPING_TAC;
  ASM_REWRITE_TAC[]];
 MP_TAC(ISPECL[`memory :> bytelist(word 0x23001120:int64,LENGTH c3_caller_mc)`;
  `[RIP;RSP;RAX;RDI;RSI]:((x86state,int64)component)list`;
  `SOME_FLAGS:((x86state,bool)component)list`;
  `[memory :> bytes(p,n)]:((x86state,num)component)list`;
  `[events]:((x86state,uarch_event list)component)list`;`entry:x86state`;`returned:x86state`]
  R1_SECRET_FOUR_FRAME_PRESERVATION) THEN
 REWRITE_TAC[ALL] THEN ANTS_TAC THENL
 [ASM_REWRITE_TAC[] THEN REWRITE_TAC[SOME_FLAGS;ALL] THEN REPEAT CONJ_TAC THEN
  ORTHOGONAL_COMPONENTS_TAC THEN
  ASM_SIMP_TAC[fst C3_CALLER_RAW_EXEC;fst C3_CRYPTO_PLT_RAW_EXEC;fst C3_CLEANSE_PLT_RAW_EXEC;
   BP_PUBLIC_CRYPTO_MEMCMP_CODE_LENGTH;BP_PUBLIC_OPENSSL_CLEANSE_CODE_LENGTH;
   VAL_WORD_SUB_CASES;VAL_WORD;DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[] THEN NONOVERLAPPING_TAC;
  ASM_REWRITE_TAC[]];
 MP_TAC(ISPECL[`memory :> bytelist(word 0x23001030:int64,LENGTH c3_crypto_plt_prefix)`;
  `[RIP;RSP;RAX;RDI;RSI]:((x86state,int64)component)list`;
  `SOME_FLAGS:((x86state,bool)component)list`;
  `[memory :> bytes(p,n)]:((x86state,num)component)list`;
  `[events]:((x86state,uarch_event list)component)list`;`entry:x86state`;`returned:x86state`]
  R1_SECRET_FOUR_FRAME_PRESERVATION) THEN
 REWRITE_TAC[ALL] THEN ANTS_TAC THENL
 [ASM_REWRITE_TAC[] THEN REWRITE_TAC[SOME_FLAGS;ALL] THEN REPEAT CONJ_TAC THEN
  ORTHOGONAL_COMPONENTS_TAC THEN
  ASM_SIMP_TAC[fst C3_CALLER_RAW_EXEC;fst C3_CRYPTO_PLT_RAW_EXEC;fst C3_CLEANSE_PLT_RAW_EXEC;
   BP_PUBLIC_CRYPTO_MEMCMP_CODE_LENGTH;BP_PUBLIC_OPENSSL_CLEANSE_CODE_LENGTH;
   VAL_WORD_SUB_CASES;VAL_WORD;DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[] THEN NONOVERLAPPING_TAC;
  ASM_REWRITE_TAC[]];
 MP_TAC(ISPECL[`memory :> bytelist(word 0x23001040:int64,LENGTH c3_cleanse_plt_prefix)`;
  `[RIP;RSP;RAX;RDI;RSI]:((x86state,int64)component)list`;
  `SOME_FLAGS:((x86state,bool)component)list`;
  `[memory :> bytes(p,n)]:((x86state,num)component)list`;
  `[events]:((x86state,uarch_event list)component)list`;`entry:x86state`;`returned:x86state`]
  R1_SECRET_FOUR_FRAME_PRESERVATION) THEN
 REWRITE_TAC[ALL] THEN ANTS_TAC THENL
 [ASM_REWRITE_TAC[] THEN REWRITE_TAC[SOME_FLAGS;ALL] THEN REPEAT CONJ_TAC THEN
  ORTHOGONAL_COMPONENTS_TAC THEN
  ASM_SIMP_TAC[fst C3_CALLER_RAW_EXEC;fst C3_CRYPTO_PLT_RAW_EXEC;fst C3_CLEANSE_PLT_RAW_EXEC;
   BP_PUBLIC_CRYPTO_MEMCMP_CODE_LENGTH;BP_PUBLIC_OPENSSL_CLEANSE_CODE_LENGTH;
   VAL_WORD_SUB_CASES;VAL_WORD;DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[] THEN NONOVERLAPPING_TAC;
  ASM_REWRITE_TAC[]];
 MP_TAC(ISPECL[`memory :> bytelist(word 0x10241840:int64,LENGTH crypto_memcmp_mc)`;
  `[RIP;RSP;RAX;RDI;RSI]:((x86state,int64)component)list`;
  `SOME_FLAGS:((x86state,bool)component)list`;
  `[memory :> bytes(p,n)]:((x86state,num)component)list`;
  `[events]:((x86state,uarch_event list)component)list`;`entry:x86state`;`returned:x86state`]
  R1_SECRET_FOUR_FRAME_PRESERVATION) THEN
 REWRITE_TAC[ALL] THEN ANTS_TAC THENL
 [ASM_REWRITE_TAC[] THEN REWRITE_TAC[SOME_FLAGS;ALL] THEN REPEAT CONJ_TAC THEN
  ORTHOGONAL_COMPONENTS_TAC THEN
  ASM_SIMP_TAC[fst C3_CALLER_RAW_EXEC;fst C3_CRYPTO_PLT_RAW_EXEC;fst C3_CLEANSE_PLT_RAW_EXEC;
   BP_PUBLIC_CRYPTO_MEMCMP_CODE_LENGTH;BP_PUBLIC_OPENSSL_CLEANSE_CODE_LENGTH;
   VAL_WORD_SUB_CASES;VAL_WORD;DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[] THEN NONOVERLAPPING_TAC;
  ASM_REWRITE_TAC[]];
 MP_TAC(ISPECL[`memory :> bytelist(word 0x102417d0:int64,LENGTH openssl_cleanse_mc)`;
  `[RIP;RSP;RAX;RDI;RSI]:((x86state,int64)component)list`;
  `SOME_FLAGS:((x86state,bool)component)list`;
  `[memory :> bytes(p,n)]:((x86state,num)component)list`;
  `[events]:((x86state,uarch_event list)component)list`;`entry:x86state`;`returned:x86state`]
  R1_SECRET_FOUR_FRAME_PRESERVATION) THEN
 REWRITE_TAC[ALL] THEN ANTS_TAC THENL
 [ASM_REWRITE_TAC[] THEN REWRITE_TAC[SOME_FLAGS;ALL] THEN REPEAT CONJ_TAC THEN
  ORTHOGONAL_COMPONENTS_TAC THEN
  ASM_SIMP_TAC[fst C3_CALLER_RAW_EXEC;fst C3_CRYPTO_PLT_RAW_EXEC;fst C3_CLEANSE_PLT_RAW_EXEC;
   BP_PUBLIC_CRYPTO_MEMCMP_CODE_LENGTH;BP_PUBLIC_OPENSSL_CLEANSE_CODE_LENGTH;
   VAL_WORD_SUB_CASES;VAL_WORD;DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[] THEN NONOVERLAPPING_TAC;
  ASM_REWRITE_TAC[]];
 MP_TAC(ISPECL[`memory :> bytes64(word 0x23003fd0:int64)`;
  `[RIP;RSP;RAX;RDI;RSI]:((x86state,int64)component)list`;
  `SOME_FLAGS:((x86state,bool)component)list`;
  `[memory :> bytes(p,n)]:((x86state,num)component)list`;
  `[events]:((x86state,uarch_event list)component)list`;`entry:x86state`;`returned:x86state`]
  R1_SECRET_FOUR_FRAME_PRESERVATION) THEN
 REWRITE_TAC[ALL] THEN ANTS_TAC THENL
 [ASM_REWRITE_TAC[] THEN REWRITE_TAC[SOME_FLAGS;ALL] THEN REPEAT CONJ_TAC THEN
  ORTHOGONAL_COMPONENTS_TAC THEN
  ASM_SIMP_TAC[fst C3_CALLER_RAW_EXEC;fst C3_CRYPTO_PLT_RAW_EXEC;fst C3_CLEANSE_PLT_RAW_EXEC;
   BP_PUBLIC_CRYPTO_MEMCMP_CODE_LENGTH;BP_PUBLIC_OPENSSL_CLEANSE_CODE_LENGTH;
   VAL_WORD_SUB_CASES;VAL_WORD;DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[] THEN NONOVERLAPPING_TAC;
  ASM_REWRITE_TAC[]];
 MP_TAC(ISPECL[`memory :> bytes64(word 0x23003fd8:int64)`;
  `[RIP;RSP;RAX;RDI;RSI]:((x86state,int64)component)list`;
  `SOME_FLAGS:((x86state,bool)component)list`;
  `[memory :> bytes(p,n)]:((x86state,num)component)list`;
  `[events]:((x86state,uarch_event list)component)list`;`entry:x86state`;`returned:x86state`]
  R1_SECRET_FOUR_FRAME_PRESERVATION) THEN
 REWRITE_TAC[ALL] THEN ANTS_TAC THENL
 [ASM_REWRITE_TAC[] THEN REWRITE_TAC[SOME_FLAGS;ALL] THEN REPEAT CONJ_TAC THEN
  ORTHOGONAL_COMPONENTS_TAC THEN
  ASM_SIMP_TAC[fst C3_CALLER_RAW_EXEC;fst C3_CRYPTO_PLT_RAW_EXEC;fst C3_CLEANSE_PLT_RAW_EXEC;
   BP_PUBLIC_CRYPTO_MEMCMP_CODE_LENGTH;BP_PUBLIC_OPENSSL_CLEANSE_CODE_LENGTH;
   VAL_WORD_SUB_CASES;VAL_WORD;DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[] THEN NONOVERLAPPING_TAC;
  ASM_REWRITE_TAC[]]]);;
print_endline "C3_CLEANSE_SAVED_BINDINGS_V3_DEVELOPMENT_CHECKED";;
