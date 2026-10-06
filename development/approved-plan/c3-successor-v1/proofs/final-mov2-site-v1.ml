(* Restricted fixed C3 offset73 integration work. The frozen generic qualifier
   is unchanged. This is a proof of the one actual MOV eax,2 site only. *)
let C3_FINAL_OFFSET73_MOV2_SCALAR = prove
 (`abi_caller_scalar_instruction
   (MOV (Register(Gpr(word 0)Lower_32)) (Imm32(word 2)))`,
 REWRITE_TAC[abi_caller_scalar_instruction;abi_cleanse_scalar_instruction;
  abi_scalar_instruction;abi_integer_operand;abi_integer_writable;
  abi_integer_immediate;abi_cmov_operand] THEN MESON_TAC[]);;
let C3_FINAL_OFFSET73_MOV2_POLICY = prove
 (`!stackpointer p q:int64 n m rp wp xp ordinary source target:x86state.
  bytes_loaded source (word 0x23001120) c3_caller_mc /\
  read RIP source=word 0x23001169 /\
  assurance_span_ok(c3_allowed_fetch xp ordinary)0x23001120 89 /\
  read events target=read events source
  ==> c3_step_policy stackpointer p q n m rp wp xp ordinary 7 source target`,
 REPEAT GEN_TAC THEN STRIP_TAC THEN
 SUBGOAL_THEN
  `x86_decode (source:x86state) (read RIP source)
    (5,MOV (Register(Gpr(word 0)Lower_32)) (Imm32(word 2)))`
  ASSUME_TAC THENL
 [let decoded=MATCH_MP(option_get((snd C3_CALLER_RAW_EXEC).(73)))
   (ASSUME `bytes_loaded (source:x86state)(word 0x23001120)c3_caller_mc`) in
  let normalized=CONV_RULE NUM_REDUCE_CONV
   (REWRITE_RULE([r1_near_operand64;r1_near_register] @ GPR_thms) decoded) in
  ASM_REWRITE_TAC[] THEN MATCH_ACCEPT_TAC normalized;
  ALL_TAC] THEN
 SUBGOAL_THEN `abi_all_decodes_caller_scalar(source:x86state)` ASSUME_TAC THENL
 [MATCH_MP_TAC(ISPECL[`5`;
   `MOV (Register(Gpr(word 0)Lower_32)) (Imm32(word 2))`;
   `source:x86state`]ABI_CALLER_DECODED_SCALAR_UNIQUE) THEN
  ASM_REWRITE_TAC[C3_FINAL_OFFSET73_MOV2_SCALAR];
  ALL_TAC] THEN
 SUBGOAL_THEN
  `assurance_span_ok(c3_allowed_fetch xp ordinary)0x23001169 5`
  ASSUME_TAC THENL
 [MP_TAC(SPECL[`c3_allowed_fetch(xp:num->bool)(ordinary:num->bool)`;
   `0x23001120`;`89`;`73`;`5`]R1_SECRET_SPAN_SUBSPAN) THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[];
  ALL_TAC] THEN
 REWRITE_TAC[c3_step_policy] THEN CONV_TAC NUM_REDUCE_CONV THEN
 ASM_REWRITE_TAC[] THEN REWRITE_TAC[assurance_step_policy] THEN
 EXISTS_TAC `5` THEN
 EXISTS_TAC `MOV (Register(Gpr(word 0)Lower_32)) (Imm32(word 2))` THEN
 EXISTS_TAC `[]:uarch_event list` THEN
 REPEAT CONJ_TAC THENL
 [ASM_REWRITE_TAC[];
  ASM_REWRITE_TAC[VAL_WORD;DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[];
  ASM_REWRITE_TAC[APPEND];
  REWRITE_TAC[ALL]]);;
print_endline "C3_SUCCESSOR_RESTRICTED_OFFSET73_MOV2_SITE_POLICY_CHECKED";;
