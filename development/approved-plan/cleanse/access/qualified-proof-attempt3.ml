(* V4 state and generic clauses, V5 clauses and its structural bridge are
   required by the closed driver before this recipe is loaded. *)
needs "/work/development/approved-plan/cleanse/access/imports-v1.ml";;
needs "/work/development/approved-plan/cleanse/access/qualified-statements-v1.ml";;
let CLEANSE_ACCESS_COVERED_DECODE_QUALIFIED = prove
 (cleanse_access_covered_decode_qualified_statement,
  REPEAT GEN_TAC THEN REWRITE_TAC[cleanse_access_covered_step] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `off:num` (X_CHOOSE_THEN `len:num`
      (X_CHOOSE_THEN `inst:instruction` STRIP_ASSUME_TAC)))) THEN
  MATCH_MP_TAC(ISPECL [`len:num`;`inst:instruction`;`s:x86state`]
    ABI_CLEANSE_DECODED_SCALAR_UNIQUE) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(ISPECL [`off:num`;`len:num`;`inst:instruction`]
    ABI_CLEANSE_REGISTERED_SITE_IS_SCALAR) THEN ASM_REWRITE_TAC[]);;
let CLEANSE_ACCESS_CHECKED_RUN_QUALIFIED = prove
 (cleanse_access_checked_run_qualified_statement,
  INDUCT_TAC THENL [REWRITE_TAC[assurance_checked_run];ALL_TAC] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[assurance_checked_run] THEN STRIP_TAC THEN
  CONJ_TAC THENL [ASM_MESON_TAC[];ALL_TAC] THEN
  X_GEN_TAC `next:x86state` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `next:x86state`) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    MATCH_MP_TAC CLEANSE_ACCESS_COVERED_DECODE_QUALIFIED THEN
    MAP_EVERY EXISTS_TAC [`pc:num`;`rp:num->bool`;`wp:num->bool`;`xp:num->bool`;
      `SUC n`;`next:x86state`] THEN ASM_REWRITE_TAC[];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;
print_endline "CLEANSE_ACCESS_QUALIFIED_BRIDGE_ATTEMPT3_COMPLETE";;
