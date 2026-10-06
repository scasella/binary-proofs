needs "/work/development/approved-plan/cleanse/access/algebra-attempt3.ml";;
needs "/work/development/approved-plan/cleanse/helpers/frame/proof.ml";;
needs "/work/development/approved-plan/cleanse/access/public-algebra-statement-v1.ml";;
let CLEANSE_ACCESS_PRE_PERMISSIONS = prove
 (cleanse_access_pre_permissions_statement,
  REPEAT GEN_TAC THEN REWRITE_TAC[bp_e2_cleanse_pre] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN
     `bp_e2_cleanse_allowed_read rp ordinary stackpointer =
      (\a. (rp a /\ ordinary a) /\ assurance_region stackpointer 8 a)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM;bp_e2_cleanse_allowed_read;CONJ_ASSOC];ALL_TAC] THEN
    MP_TAC(ISPECL [`\a:num. (rp:num->bool) a /\ (ordinary:num->bool) a`;
      `stackpointer:int64`;`8`] ASSURANCE_SPAN_SELF_REGION) THEN ASM_REWRITE_TAC[];
    SUBGOAL_THEN
     `bp_e2_cleanse_allowed_write wp ordinary p n =
      (\a. (wp a /\ ordinary a) /\ assurance_region p n a)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM;bp_e2_cleanse_allowed_write;CONJ_ASSOC];ALL_TAC] THEN
    MP_TAC(ISPECL [`\a:num. (wp:num->bool) a /\ (ordinary:num->bool) a`;
      `p:int64`;`n:num`] ASSURANCE_SPAN_SELF_REGION) THEN ASM_REWRITE_TAC[];
    SUBGOAL_THEN
     `bp_e2_cleanse_allowed_fetch xp ordinary pc =
      (\a. (xp a /\ ordinary a) /\ assurance_region (word pc) 97 a)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM;bp_e2_cleanse_allowed_fetch;CONJ_ASSOC];ALL_TAC] THEN
    MP_TAC(ISPECL [`\a:num. (xp:num->bool) a /\ (ordinary:num->bool) a`;
      `word pc:int64`;`97`] ASSURANCE_SPAN_SELF_REGION) THEN
    ASM_SIMP_TAC[CLEANSE_ACCESS_CODE_BASE_VALUE];
    ONCE_REWRITE_TAC[NONOVERLAPPING_SYM] THEN
    MATCH_MP_TAC CLEANSE_REGIONS_DISJOINT_NONOVERLAPPING THEN
    ASM_SIMP_TAC[CLEANSE_ACCESS_CODE_BASE_VALUE] THEN
    UNDISCH_TAC `assurance_span_ok (\a. wp a /\ ordinary a) (val(p:int64)) n` THEN
    REWRITE_TAC[assurance_span_ok] THEN MESON_TAC[];
    ONCE_REWRITE_TAC[NONOVERLAPPING_SYM] THEN
    MATCH_MP_TAC CLEANSE_REGIONS_DISJOINT_NONOVERLAPPING THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `assurance_span_ok (\a. wp a /\ ordinary a) (val(p:int64)) n` THEN
      REWRITE_TAC[assurance_span_ok] THEN MESON_TAC[];
      ASM_ARITH_TAC]]);;
print_endline "CLEANSE_ACCESS_PUBLIC_ALGEBRA_ATTEMPT8_COMPLETE";;
