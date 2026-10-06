needs "/work/development/approved-plan/crypto-loop/trace/noninterference/components-v3.ml";;
needs "/work/development/approved-plan/crypto-loop/trace/noninterference/first-return/model.ml";;
needs "/work/development/approved-plan/crypto-loop/trace/noninterference/first-return/statements.ml";;
needs "/work/development/approved-plan/crypto-loop/trace/noninterference/first-return/auxiliary-statement.ml";;
let CRYPTO_FIRST_RET_SHAPE_CHARACTERIZATION = prove
 (crypto_first_ret_shape_characterization_statement,
  LIST_INDUCT_TAC THEN REWRITE_TAC[crypto_ret_shape;NOT_CONS_NIL;BUTLAST;LAST;ALL] THEN
  ASM_CASES_TAC `t:(int64#num#instruction#uarch_event list)list=[]` THEN
  ASM_REWRITE_TAC[ALL] THEN REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[ALL] THEN ITAUT_TAC);;
let CRYPTO_FIRST_RET_EXECUTION_EQUIVALENT = prove
 (crypto_first_ret_execution_equivalent_statement,
  REWRITE_TAC[crypto_first_ret_execution;CRYPTO_FIRST_RET_SHAPE_CHARACTERIZATION] THEN ITAUT_TAC);;
let CRYPTO_FIRST_RET_PREFIX = prove
 (crypto_first_ret_prefix_statement,
  LIST_INDUCT_TAC THEN REWRITE_TAC[ALL;APPEND;crypto_ret_shape] THEN
  ASM_MESON_TAC[]);;
print_endline "CRYPTO_FIRST_RET_HELPERS_ATTEMPT2_COMPLETE";;
