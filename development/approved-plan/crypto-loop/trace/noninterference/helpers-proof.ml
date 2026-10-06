needs "/work/development/approved-plan/crypto-loop/trace/noninterference/model.ml";;
needs "/work/development/approved-plan/crypto-loop/trace/noninterference/schema.ml";;
needs "/work/development/approved-plan/crypto-loop/trace/noninterference/helper-statements.ml";;
let CRYPTO_OBSERVATION_UNIQUE = prove
 (crypto_observation_unique_statement,
  REWRITE_TAC[assurance_observed_step] THEN MESON_TAC[x86_decode_unique;PAIR_EQ]);;
let CRYPTO_OBSERVATION_MONO = prove
 (crypto_observation_mono_statement,
  LIST_INDUCT_TAC THEN REWRITE_TAC[crypto_observed_run] THEN ASM_MESON_TAC[]);;
let CRYPTO_OBSERVATION_PROJECT = prove
 (crypto_observation_project_statement,
  LIST_INDUCT_TAC THEN REWRITE_TAC[crypto_observed_run;LENGTH;EVENTUALLY_N_TRIVIAL;
    ARITH_RULE `SUC n=1+n`;EVENTUALLY_N_STEP] THEN ASM_MESON_TAC[]);;
let CRYPTO_OBSERVATION_EXECUTION_EXACT = prove
 (crypto_observation_execution_exact_statement,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `other:(int64#num#instruction#uarch_event list)list` list_CASES) THEN
  REWRITE_TAC[crypto_observed_run;crypto_observed_execution;LENGTH;SUC_INJ;
    ARITH_RULE `0=SUC n <=> F`;ARITH_RULE `SUC n=0 <=> F`] THEN
  ASM_MESON_TAC[ASSURANCE_OBSERVED_PROJECTION;CRYPTO_OBSERVATION_UNIQUE]);;
let CRYPTO_OBSERVATION_LOOP_LENGTH = prove
 (crypto_observation_loop_length_statement,
  INDUCT_TAC THEN REPEAT GEN_TAC THEN
  ASM_REWRITE_TAC[crypto_public_loop;crypto_public_body7;crypto_public_exit;
    LENGTH_APPEND;LENGTH] THEN ARITH_TAC);;
let CRYPTO_OBSERVATION_CALL_LENGTH = prove
 (crypto_observation_call_length_statement,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `n=0` THEN ASM_CASES_TAC `n=16` THEN
  ASM_REWRITE_TAC[crypto_public_call;crypto_public_entry5;crypto_public_entry7;LENGTH_APPEND;LENGTH;
    CRYPTO_OBSERVATION_LOOP_LENGTH] THEN ASM_ARITH_TAC);;
print_endline "CRYPTO_OBSERVATION_HELPERS_COMPLETE";;
