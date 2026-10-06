(* Trusted extraction supplies this separate exact byte definition.
   The checker must derive decoding from those six bytes, never an old PLT. *)
let BP_C1_PLT_RAW_EXEC = X86_MK_EXEC_RULE c1_crypto_plt_prefix;;
let BP_C1_PLT_EXEC =
 let len,decodes = BP_C1_PLT_RAW_EXEC in
 len,Array.map
  (function None -> None | Some th ->
    Some(REWRITE_RULE ([r1_near_operand64;r1_near_register] @ GPR_thms) th))
  decodes;;

let BP_C1_PLT_DECODE = prove
 (bp_c1_plt_decode_statement,
  MATCH_ACCEPT_TAC(Option.get (snd BP_C1_PLT_EXEC).(0)));;

let BP_C1_PLT_CHECKED_HOP = prove
 (bp_c1_plt_checked_hop_statement,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  CONJ_TAC THENL
   [REWRITE_TAC[assurance_canonical48; VAL_WORD; DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `x86_decode s (word 0x21001030)
    (6,JUMP Unconditional (Memop Quadword (Riprel(word 0x2fa2))))`
   ASSUME_TAC THENL [ASM_MESON_TAC[BP_C1_PLT_DECODE];ALL_TAC] THEN
  MP_TAC(ISPECL
   [`word 0x21001030:int64`;`word 0x2fa2:int64`;
    `word 0x10241840:int64`;`e:uarch_event list`;`m:int64->byte`;
    `rp:num->bool`;`xp:num->bool`;`s:x86state`]
   BP_REUSE_RIPREL_JUMP_CHECKED_HOP) THEN
  REWRITE_TAC[GSYM WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[]);;
