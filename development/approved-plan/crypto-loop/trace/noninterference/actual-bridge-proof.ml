needs "/work/development/approved-plan/crypto-loop/trace/noninterference/actual-bridge-statement.ml";;
let ASSURANCE_DECODED_OBSERVATION_ALL_SUCCESSORS = prove
 (crypto_observation_actual_bridge_statement,
  REPEAT GEN_TAC THEN REWRITE_TAC[x86] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `n:num`
      (X_CHOOSE_THEN `decoded:instruction` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `(n:num) = (len:num) /\ (decoded:instruction) = (inst:instruction)`
    (CONJUNCTS_THEN SUBST_ALL_TAC) THENL
   [MP_TAC(ISPECL [`s:x86state`; `read RIP s`;
      `(len:num,inst:instruction)`; `(n:num,decoded:instruction)`]
      x86_decode_unique) THEN ASM_REWRITE_TAC[PAIR_EQ] THEN MESON_TAC[];
    REWRITE_TAC[assurance_observed_step] THEN
    MAP_EVERY EXISTS_TAC [`len:num`; `inst:instruction`] THEN
    ASM_REWRITE_TAC[]]);;

