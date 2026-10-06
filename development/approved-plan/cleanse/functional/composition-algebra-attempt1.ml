needs "/work/development/approved-plan/cleanse/functional/components-v3.ml";;
needs "/work/development/approved-plan/cleanse/functional/composition-statements.ml";;
let CLEANSE_FUNCTIONAL_CONCAT_ZERO = prove
 (cleanse_functional_concat_zero_statement,
  REPEAT GEN_TAC THEN REWRITE_TAC[READ_COMPONENT_COMPOSE;READ_BYTES_COMBINE] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[MULT_CLAUSES;ADD_CLAUSES]);;
print_endline "CLEANSE_FUNCTIONAL_COMPOSITION_ALGEBRA_ATTEMPT1_COMPLETE";;
