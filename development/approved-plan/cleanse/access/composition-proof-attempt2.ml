needs "/work/development/approved-plan/cleanse/access/all-length-attempt8.ml";;
needs "/work/development/approved-plan/cleanse/access/qualified-imports-v2.ml";;
needs "/work/development/approved-plan/cleanse/access/composition-statements-v1.ml";;
let CLEANSE_ACCESS_COUNT_AGREEMENT = prove
 (cleanse_access_count_agreement_statement,
  REWRITE_TAC[cleanse_access_count;cleanse_functional_steps;LET_DEF;LET_END_DEF]);;
let CLEANSE_ACCESS_ORIGINAL_RETURN = prove
 (cleanse_access_original_return_statement,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC(ISPECL [`cleanse_functional_steps p n`;`cleanse_access_return_post pc stackpointer ra`;`cleanse_access_covered_step pc (bp_e2_cleanse_allowed_read rp ordinary stackpointer) (bp_e2_cleanse_allowed_write wp ordinary p n) (bp_e2_cleanse_allowed_fetch xp ordinary pc)`;`s:x86state`]
    ASSURANCE_RUN_PROJECT) THEN
  MP_TAC(ISPECL [`pc:num`;`stackpointer:int64`;`ra:int64`;`p:int64`;`n:num`;`m:int64->byte`;`rp:num->bool`;`wp:num->bool`;`xp:num->bool`;`ordinary:num->bool`;`s:x86state`] CLEANSE_ACCESS_ALL_LENGTH) THEN
  ASM_REWRITE_TAC[CLEANSE_ACCESS_COUNT_AGREEMENT]);;
let CLEANSE_ACCESS_QUALIFIED_RETURN = prove
 (cleanse_access_qualified_return_statement,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC(ISPECL [`cleanse_functional_steps p n`;`pc:num`;`bp_e2_cleanse_allowed_read rp ordinary stackpointer`;`bp_e2_cleanse_allowed_write wp ordinary p n`;`bp_e2_cleanse_allowed_fetch xp ordinary pc`;`cleanse_access_return_post pc stackpointer ra`;`s:x86state`]
    CLEANSE_ACCESS_CHECKED_RUN_QUALIFIED) THEN
  MP_TAC(ISPECL [`pc:num`;`stackpointer:int64`;`ra:int64`;`p:int64`;`n:num`;`m:int64->byte`;`rp:num->bool`;`wp:num->bool`;`xp:num->bool`;`ordinary:num->bool`;`s:x86state`] CLEANSE_ACCESS_ALL_LENGTH) THEN
  ASM_REWRITE_TAC[CLEANSE_ACCESS_COUNT_AGREEMENT]);;
let CLEANSE_ACCESS_EXTENDED_RETURN = prove
 (cleanse_access_extended_return_statement,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC(ISPECL [`cleanse_functional_steps p n`;`cleanse_access_return_post pc stackpointer ra`;`cleanse_access_covered_step pc (bp_e2_cleanse_allowed_read rp ordinary stackpointer) (bp_e2_cleanse_allowed_write wp ordinary p n) (bp_e2_cleanse_allowed_fetch xp ordinary pc)`;`s:x86state`;`a:abi_omitted_state`]
    ABI_CLEANSE_CHECKED_RUN_LIFT) THEN
  MP_TAC(ISPECL [`pc:num`;`stackpointer:int64`;`ra:int64`;`p:int64`;`n:num`;`m:int64->byte`;`rp:num->bool`;`wp:num->bool`;`xp:num->bool`;`ordinary:num->bool`;`s:x86state`] CLEANSE_ACCESS_QUALIFIED_RETURN) THEN ASM_REWRITE_TAC[]);;
print_endline "CLEANSE_ACCESS_COMPOSITION_ATTEMPT2_COMPLETE";;
