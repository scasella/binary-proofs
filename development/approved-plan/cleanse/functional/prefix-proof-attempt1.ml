needs "/work/development/approved-plan/cleanse/functional/imports.ml";;
needs "/work/development/approved-plan/cleanse/functional/prefix-statement.ml";;
let CLEANSE_FUNCTIONAL_PREFIX_READ = prove
 (cleanse_functional_prefix_read_statement,
  REWRITE_TAC[READ_COMPONENT_COMPOSE;READ_BYTES_COMBINE;READ_BYTES_BYTES8] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[VAL_WORD_0;MULT_CLAUSES;ADD_CLAUSES]);;
print_endline "CLEANSE_FUNCTIONAL_PREFIX_READ_ATTEMPT1_COMPLETE";;
