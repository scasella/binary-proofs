let R1_EVENTUALLY_N_ONE = prove
 (r1_eventually_n_one_statement,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`x86`;`P:x86state->bool`;`0`;`s:x86state`] EVENTUALLY_N_STEP) THEN
  REWRITE_TAC[ADD_CLAUSES;EVENTUALLY_N_TRIVIAL]);;
let R1_CRYPTO_PLT_CHECKED_HOP = prove
 (r1_crypto_plt_checked_statement,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `x86_decode s (read RIP s)
     (6,JUMP Unconditional (Memop Quadword (Riprel(word 0x2f92))))`
   ASSUME_TAC THENL
   [ASM_MESON_TAC[R1_CRYPTO_PLT_EXECUTION_DECODE];ALL_TAC] THEN
  MP_TAC(SPECL [`pc:num`;`target:int64`;`e:uarch_event list`;
                `m:int64->byte`] R1_CRYPTO_PLT_TRANSFER_BOUNDED) THEN
  REWRITE_TAC[ensures_n] THEN
  DISCH_THEN(MP_TAC o SPEC `s:x86state`) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[R1_EVENTUALLY_N_ONE] THEN
  STRIP_TAC THEN
  REWRITE_TAC[num_CONV `1`;assurance_checked_run] THEN
  ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `next:x86state` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `read RIP next=target /\ read memory next=m /\
    read events next=APPEND
     [EventJump(word(pc+6),target);EventLoad(word(pc+6+0x2f92),8)] e`
    STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[];ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[assurance_step_policy] THEN
  MAP_EVERY EXISTS_TAC
   [`6`;`JUMP Unconditional (Memop Quadword (Riprel(word 0x2f92)))`;
    `[EventJump(word(pc+6),target);EventLoad(word(pc+6+0x2f92),8)]`] THEN
  ASM_REWRITE_TAC[ALL;assurance_event_policy]);;
let R1_CLEANSE_PLT_CHECKED_HOP = prove
 (r1_cleanse_plt_checked_statement,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `x86_decode s (read RIP s)
     (6,JUMP Unconditional (Memop Quadword (Riprel(word 0x2f8a))))`
   ASSUME_TAC THENL
   [ASM_MESON_TAC[R1_CLEANSE_PLT_EXECUTION_DECODE];ALL_TAC] THEN
  MP_TAC(SPECL [`pc:num`;`target:int64`;`e:uarch_event list`;
                `m:int64->byte`] R1_CLEANSE_PLT_TRANSFER_BOUNDED) THEN
  REWRITE_TAC[ensures_n] THEN
  DISCH_THEN(MP_TAC o SPEC `s:x86state`) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[R1_EVENTUALLY_N_ONE] THEN
  STRIP_TAC THEN
  REWRITE_TAC[num_CONV `1`;assurance_checked_run] THEN
  ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `next:x86state` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `read RIP next=target /\ read memory next=m /\
    read events next=APPEND
     [EventJump(word(pc+6),target);EventLoad(word(pc+6+0x2f8a),8)] e`
    STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[];ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[assurance_step_policy] THEN
  MAP_EVERY EXISTS_TAC
   [`6`;`JUMP Unconditional (Memop Quadword (Riprel(word 0x2f8a)))`;
    `[EventJump(word(pc+6),target);EventLoad(word(pc+6+0x2f8a),8)]`] THEN
  ASM_REWRITE_TAC[ALL;assurance_event_policy]);;
let R1_MEMCMP_PLT_CHECKED_HOP = prove
 (r1_memcmp_plt_checked_statement,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `x86_decode s (read RIP s)
     (6,JUMP Unconditional (Memop Quadword (Riprel(word 0x2f82))))`
   ASSUME_TAC THENL
   [ASM_MESON_TAC[R1_MEMCMP_PLT_EXECUTION_DECODE];ALL_TAC] THEN
  MP_TAC(SPECL [`pc:num`;`target:int64`;`e:uarch_event list`;
                `m:int64->byte`] R1_MEMCMP_PLT_TRANSFER_BOUNDED) THEN
  REWRITE_TAC[ensures_n] THEN
  DISCH_THEN(MP_TAC o SPEC `s:x86state`) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[R1_EVENTUALLY_N_ONE] THEN
  STRIP_TAC THEN
  REWRITE_TAC[num_CONV `1`;assurance_checked_run] THEN
  ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `next:x86state` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `read RIP next=target /\ read memory next=m /\
    read events next=APPEND
     [EventJump(word(pc+6),target);EventLoad(word(pc+6+0x2f82),8)] e`
    STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[];ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[assurance_step_policy] THEN
  MAP_EVERY EXISTS_TAC
   [`6`;`JUMP Unconditional (Memop Quadword (Riprel(word 0x2f82)))`;
    `[EventJump(word(pc+6),target);EventLoad(word(pc+6+0x2f82),8)]`] THEN
  ASM_REWRITE_TAC[ALL;assurance_event_policy]);;
