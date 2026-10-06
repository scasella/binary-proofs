needs "/work/development/approved-plan/crypto-loop/trace/noninterference/first-return/helpers-attempt2.ml";;
let CRYPTO_FIRST_RET_LOOP_SHAPE = prove
 (crypto_first_ret_loop_shape_statement,
  INDUCT_TAC THEN REPEAT GEN_TAC THEN
  ASM_REWRITE_TAC[crypto_public_loop;crypto_public_body7;crypto_public_exit;APPEND;
    crypto_ret_shape;crypto_observation_is_ret;crypto_public_observation;crypto_public_decode;
    FST;SND;NOT_CONS_NIL] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[distinctness "instruction";crypto_ret_shape]);;
let CRYPTO_FIRST_RET_CALL_SHAPE = prove
 (crypto_first_ret_call_shape_statement,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `n=0` THEN ASM_CASES_TAC `n=16` THEN
  ASM_REWRITE_TAC[crypto_public_call;crypto_public_entry5;crypto_public_entry7;APPEND;
    crypto_ret_shape;crypto_observation_is_ret;crypto_public_observation;crypto_public_decode;
    FST;SND;NOT_CONS_NIL;CRYPTO_FIRST_RET_LOOP_SHAPE] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[distinctness "instruction";crypto_ret_shape]);;
print_endline "CRYPTO_FIRST_RET_HELPERS_COMPLETE";;
