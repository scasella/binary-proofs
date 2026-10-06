let ASSURANCE_E2_PERMISSION_FUNCTIONS = prove
 (`(!xp ordinary pc. bp_e2_crypto_allowed_fetch xp ordinary pc =
     (\a. (xp a /\ ordinary a) /\ assurance_region (word pc) 95 a)) /\
   (!rp ordinary p q n stackpointer.
      bp_e2_crypto_allowed_read rp ordinary p q n stackpointer =
      (\a. (rp a /\ ordinary a) /\
        (assurance_region p n a \/ assurance_region q n a \/
         assurance_region stackpointer 8 a))) /\
   bp_e2_crypto_allowed_write = (\a:num. F)`,
  REWRITE_TAC[FUN_EQ_THM; bp_e2_crypto_allowed_fetch;
    bp_e2_crypto_allowed_read; bp_e2_crypto_allowed_write] THEN MESON_TAC[]);;

(* Same frozen E2 entry domain and permission functions, without hidden guards. *)
let ASSURANCE_E2_FETCH_SPAN = prove
 (`!pc stackpointer ra p q n m rp xp ordinary s.
    bp_e2_crypto_pre pc stackpointer ra p q n m rp xp ordinary s
    ==> assurance_span_ok (bp_e2_crypto_allowed_fetch xp ordinary pc) pc 95`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bp_e2_crypto_pre] THEN STRIP_TAC THEN
  SUBGOAL_THEN `val(word pc:int64) = pc` ASSUME_TAC THENL
   [MATCH_MP_TAC ASSURANCE_CODE_BASE_VALUE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`\a:num. xp a /\ ordinary a`; `word pc:int64`; `95`]
    ASSURANCE_SPAN_SELF_REGION) THEN
  ASM_REWRITE_TAC[ASSURANCE_E2_PERMISSION_FUNCTIONS]);;

let ASSURANCE_E2_READ_SPANS = prove
 (`!rp ordinary p q n stackpointer.
    assurance_span_ok (\a. rp a /\ ordinary a) (val(p:int64)) n /\
    assurance_span_ok (\a. rp a /\ ordinary a) (val(q:int64)) n /\
    assurance_span_ok (\a. rp a /\ ordinary a) (val(stackpointer:int64)) 8
    ==> assurance_span_ok
          (bp_e2_crypto_allowed_read rp ordinary p q n stackpointer) (val p) n /\
        assurance_span_ok
          (bp_e2_crypto_allowed_read rp ordinary p q n stackpointer) (val q) n /\
        assurance_span_ok
          (bp_e2_crypto_allowed_read rp ordinary p q n stackpointer)
          (val stackpointer) 8`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ASSURANCE_E2_PERMISSION_FUNCTIONS] THEN
  REPEAT CONJ_TAC THEN MATCH_MP_TAC ASSURANCE_SPAN_MONO THENL
   [EXISTS_TAC `\a:num. (rp a /\ ordinary a) /\ assurance_region (p:int64) n a`;
    EXISTS_TAC `\a:num. (rp a /\ ordinary a) /\ assurance_region (q:int64) n a`;
    EXISTS_TAC `\a:num. (rp a /\ ordinary a) /\ assurance_region (stackpointer:int64) 8 a`] THEN
  ASM_SIMP_TAC[ASSURANCE_SPAN_SELF_REGION] THEN MESON_TAC[]);;

let ASSURANCE_E2_ZERO_ALLOWED_READ = prove
 (`!rp ordinary p q stackpointer.
    bp_e2_crypto_allowed_read rp ordinary p q 0 stackpointer =
      (\a. (rp a /\ ordinary a) /\ assurance_region stackpointer 8 a)`,
  REWRITE_TAC[FUN_EQ_THM; bp_e2_crypto_allowed_read; assurance_region;
    ADD_CLAUSES; ARITH_RULE `~(a <= b /\ b < a)`] THEN MESON_TAC[]);;

let ASSURANCE_E2_POLICY_PRODUCT = prove
 (`!n P rp wp xp s a.
    assurance_checked_run n P (assurance_zero_scalar_step rp wp xp) s
    ==> eventually_n abi_scalar_extended_step n
          (\t. P(FST t) /\ SND t = a /\
               abi_required_controls_preserved a (SND t)) (s,a)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`abi_scalar_extended_step`;
    `\t:x86state#abi_omitted_state. P(FST t) /\ SND t = a`;
    `\t:x86state#abi_omitted_state. P(FST t) /\ SND t = a /\
        abi_required_controls_preserved a (SND t)`; `n:num`;
    `(s:x86state,a:abi_omitted_state)`] EVENTUALLY_N_MONO) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[abi_required_controls_preserved];
    DISCH_THEN MATCH_MP_TAC THEN
    MP_TAC(ISPECL [`n:num`; `P:x86state->bool`; `rp:num->bool`;
      `wp:num->bool`; `xp:num->bool`; `s:x86state`; `a:abi_omitted_state`]
      ASSURANCE_SCALAR_POLICY_RUN_LIFT) THEN ASM_REWRITE_TAC[]]);;

let ASSURANCE_E2_CHECKED_RUN_MONO = prove
 (`!n P Q C s. (!t. P t ==> Q t) /\ assurance_checked_run n P C s
    ==> assurance_checked_run n Q C s`,
  INDUCT_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[assurance_checked_run] THEN MESON_TAC[];
    REPEAT GEN_TAC THEN REWRITE_TAC[assurance_checked_run] THEN STRIP_TAC THEN
    CONJ_TAC THENL
     [ASM_MESON_TAC[];
      X_GEN_TAC `next:x86state` THEN DISCH_TAC THEN
      SUBGOAL_THEN
       `C (SUC n) s next /\ assurance_checked_run n P C next`
       STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o
        ISPECL [`P:x86state->bool`; `Q:x86state->bool`;
          `C:num->x86state->x86state->bool`; `next:x86state`]) THEN
      ASM_REWRITE_TAC[]]]);;
