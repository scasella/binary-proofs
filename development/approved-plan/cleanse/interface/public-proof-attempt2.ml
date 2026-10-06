needs "/work/development/approved-plan/cleanse/interface/product-proof-attempt2.ml";;
let BP_E2_CLEANSE_PUBLIC_POLICY = prove
 (bp_e2_cleanse_public_policy_statement,
  REPEAT GEN_TAC THEN REWRITE_TAC[bp_e2_cleanse_public_pre] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`0x102417d0`;`stackpointer:int64`;`ra:int64`;`p:int64`;`n:num`;
    `m:int64->byte`;`rp:num->bool`;`wp:num->bool`;`xp:num->bool`;
    `ordinary:num->bool`;`s:x86state`] BP_E2_CLEANSE_POLICY_FRAME) THEN
  ASM_REWRITE_TAC[]);;
let BP_E2_CLEANSE_PUBLIC_INTERFACE = prove
 (bp_e2_cleanse_public_interface_statement,
  REPEAT GEN_TAC THEN REWRITE_TAC[bp_e2_cleanse_public_pre] THEN STRIP_TAC THEN
  GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) [GSYM ETA_AX] THEN
  REWRITE_TAC[bp_e2_cleanse_public_post] THEN
  MP_TAC(ISPECL [`0x102417d0`;`stackpointer:int64`;`ra:int64`;`p:int64`;`n:num`;
    `m:int64->byte`;`rp:num->bool`;`wp:num->bool`;`xp:num->bool`;
    `ordinary:num->bool`;`s:x86state`;`a:abi_omitted_state`] BP_E2_CLEANSE_EXTENDED) THEN
  ASM_REWRITE_TAC[]);;
print_endline "CLEANSE_INTERFACE_PUBLIC_ATTEMPT2_COMPLETE";;
