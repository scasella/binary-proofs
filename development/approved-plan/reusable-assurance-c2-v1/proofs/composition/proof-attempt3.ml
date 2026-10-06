(* Unchanged generic checked-run composition rules; openly C2-specific
   instantiations and conditional branch routing. Supplier bodies opaque. *)
let C2_SHIFTED_SEGMENT_POLICY = prove
 (c2_shifted_segment_policy_statement,
  REPEAT GEN_TAC THEN REWRITE_TAC[c2_segment_policy;c2_step_policy] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;
(* Explicitly C2-specific source callback; it supplies the current k and
   remaining count to the unchanged generic policy/append rules. *)
let C2_SHIFT_CURRENT_POLICY_TAC (asl,w) =
 let _,args=strip_comb w in
 let remaining=el 9 args in
 (MATCH_MP_TAC(ISPECL [`stackpointer:int64`;`p:int64`;`q:int64`;`n:num`;`m:int64->byte`;
    `rp:num->bool`;`wp:num->bool`;`xp:num->bool`;`ordinary:num->bool`;
    `k:num`;remaining;`source:x86state`;`target:x86state`] C2_SHIFTED_SEGMENT_POLICY) THEN
  CONJ_TAC THENL [TRY COND_CASES_TAC THEN ARITH_TAC;ASM_REWRITE_TAC[]]) (asl,w);;
let C2_SUFFIX_TARGET_RUN_TAC finalfacts readyfacts =
 MATCH_MP_TAC(ISPECL [`5`;
  `c2_suffix_post stackpointer ra p q n m (initial:x86state) returned`;
  `c2_scalar_post stackpointer ra p q n m (initial:x86state)`;
  `c2_step_policy stackpointer p q n m rp wp xp ordinary:num->x86state->x86state->bool`;
  `returned:x86state`] RA_CHECKED_RUN_POST_MONO) THEN
 CONJ_TAC THENL
  [X_GEN_TAC `t:x86state` THEN DISCH_TAC THEN
   MATCH_MP_TAC(ISPECL [`lib_file:num->byte`;`lib_rw:int64->byte`;`lib_padding:int64->byte`;
    `client_file:num->byte`;`client_rw:int64->byte`;`client_padding:int64->byte`;
    `stackpointer:int64`;`ra:int64`;`p:int64`;`q:int64`;`n:num`;`m:int64->byte`;
    `rp:num->bool`;`wp:num->bool`;`xp:num->bool`;`ordinary:num->bool`;
    `initial:x86state`;`a:abi_omitted_state`;`returned:x86state`;`t:x86state`] finalfacts) THEN
   ASM_REWRITE_TAC[];
   MATCH_MP_TAC(ISPECL [`stackpointer:int64`;`ra:int64`;`p:int64`;`q:int64`;
    `n:num`;`m:int64->byte`;`rp:num->bool`;`wp:num->bool`;`xp:num->bool`;
    `ordinary:num->bool`;`initial:x86state`;`returned:x86state`] C2_SUFFIX) THEN
   MATCH_MP_TAC(ISPECL [`lib_file:num->byte`;`lib_rw:int64->byte`;`lib_padding:int64->byte`;
    `client_file:num->byte`;`client_rw:int64->byte`;`client_padding:int64->byte`;
    `stackpointer:int64`;`ra:int64`;`p:int64`;`q:int64`;`n:num`;`m:int64->byte`;
    `rp:num->bool`;`wp:num->bool`;`xp:num->bool`;`ordinary:num->bool`;
    `initial:x86state`;`a:abi_omitted_state`;`returned:x86state`] readyfacts) THEN
   ASM_REWRITE_TAC[]];;
let C2_FALSE_HEADER_TAIL_RUN = prove
 (c2_false_header_tail_run_statement,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  C2_SUFFIX_TARGET_RUN_TAC C2_FALSE_SUFFIX_SCALAR C2_HEADER_FALSE_SUFFIX_READY);;
let C2_TRUE_CLEANSE_TAIL_RUN = prove
 (c2_true_cleanse_tail_run_statement,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  C2_SUFFIX_TARGET_RUN_TAC C2_TRUE_SUFFIX_SCALAR C2_CLEANSE_SUFFIX_READY);;
let C2_TRUE_HEADER_TAIL_RUN = prove
 (c2_true_header_tail_run_statement,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(ISPECL [`4`;`cleanse_functional_steps p n`;`5`;
    `c2_cleanse_ready lib_file stackpointer p q n m rp wp xp ordinary initial a`;
    `c2_cleanse_ready lib_file stackpointer p q n m rp wp xp ordinary initial a`;
    `c2_cleanse_completed lib_file stackpointer p q n m rp wp xp ordinary initial a`;
    `c2_scalar_post stackpointer ra p q n m initial`;
    `c2_segment_policy stackpointer p q n m rp wp xp ordinary:num->x86state->x86state->bool`;
    `c2_segment_policy stackpointer p q n m rp wp xp ordinary:num->x86state->x86state->bool`;
    `c2_step_policy stackpointer p q n m rp wp xp ordinary:num->x86state->x86state->bool`;
    `c2_step_policy stackpointer p q n m rp wp xp ordinary:num->x86state->x86state->bool`;
    `returned:x86state`] RA_CHECKED_RUN_THREE_SEGMENT) THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC(ISPECL [`lib_file:num->byte`;`lib_rw:int64->byte`;`lib_padding:int64->byte`;
     `client_file:num->byte`;`client_rw:int64->byte`;`client_padding:int64->byte`;
     `stackpointer:int64`;`ra:int64`;`p:int64`;`q:int64`;`n:num`;`m:int64->byte`;
     `rp:num->bool`;`wp:num->bool`;`xp:num->bool`;`ordinary:num->bool`;
     `initial:x86state`;`a:abi_omitted_state`;`returned:x86state`] C2_TRUE_MIDDLE_HANDOFF) THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[];
     MATCH_MP_TAC(ISPECL [`lib_file:num->byte`;`lib_rw:int64->byte`;`lib_padding:int64->byte`;
      `client_file:num->byte`;`client_rw:int64->byte`;`client_padding:int64->byte`;
      `stackpointer:int64`;`ra:int64`;`p:int64`;`q:int64`;`n:num`;`m:int64->byte`;
      `rp:num->bool`;`wp:num->bool`;`xp:num->bool`;`ordinary:num->bool`;
      `initial:x86state`;`a:abi_omitted_state`;`returned:x86state`] C2_HEADER_TRUE_MIDDLE_READY) THEN
     ASM_REWRITE_TAC[]];
    MESON_TAC[];
    X_GEN_TAC `entry:x86state` THEN DISCH_TAC THEN
    MATCH_MP_TAC(ISPECL [`lib_file:num->byte`;`stackpointer:int64`;`p:int64`;`q:int64`;
     `n:num`;`m:int64->byte`;`rp:num->bool`;`wp:num->bool`;`xp:num->bool`;
     `ordinary:num->bool`;`initial:x86state`;`a:abi_omitted_state`;`entry:x86state`]
      C2_CLEANSE_COMPLETED_RUN) THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `cleaned:x86state` THEN DISCH_TAC THEN
    MATCH_MP_TAC(ISPECL [`lib_file:num->byte`;`lib_rw:int64->byte`;`lib_padding:int64->byte`;
     `client_file:num->byte`;`client_rw:int64->byte`;`client_padding:int64->byte`;
     `stackpointer:int64`;`ra:int64`;`p:int64`;`q:int64`;`n:num`;`m:int64->byte`;
     `rp:num->bool`;`wp:num->bool`;`xp:num->bool`;`ordinary:num->bool`;
     `initial:x86state`;`a:abi_omitted_state`;`cleaned:x86state`] C2_TRUE_CLEANSE_TAIL_RUN) THEN
    ASM_REWRITE_TAC[];
    REPEAT GEN_TAC THEN DISCH_TAC THEN
    MATCH_MP_TAC(ISPECL [`stackpointer:int64`;`p:int64`;`q:int64`;`n:num`;`m:int64->byte`;
     `rp:num->bool`;`wp:num->bool`;`xp:num->bool`;`ordinary:num->bool`;
     `k:num`;`(cleanse_functional_steps p n+5)+k`;`source:x86state`;`target:x86state`]
      C2_SHIFTED_SEGMENT_POLICY) THEN CONJ_TAC THENL [ARITH_TAC;ASM_REWRITE_TAC[]];
    REPEAT GEN_TAC THEN DISCH_TAC THEN
    MATCH_MP_TAC(ISPECL [`stackpointer:int64`;`p:int64`;`q:int64`;`n:num`;`m:int64->byte`;
     `rp:num->bool`;`wp:num->bool`;`xp:num->bool`;`ordinary:num->bool`;
     `k:num`;`5+k`;`source:x86state`;`target:x86state`]
      C2_SHIFTED_SEGMENT_POLICY) THEN CONJ_TAC THENL [ARITH_TAC;ASM_REWRITE_TAC[]];
    MESON_TAC[]]);;
let C2_AFTER_COMPARE_TAIL_RUN = prove
 (c2_after_compare_tail_run_statement,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `c2_equal (m:int64->byte) p q n` THEN ASM_REWRITE_TAC[] THEN
  (fun gl -> let tail=if can (find_term (fun t -> t=`12+cleanse_functional_steps p n`)) (snd gl)
     then `4+(cleanse_functional_steps p n+5)` else `5` in
   let total=if tail=`5` then `8` else `12+cleanse_functional_steps p n` in
   let tactic=SUBGOAL_THEN (mk_eq(total,mk_binop `(+):num->num->num` `3` tail)) SUBST1_TAC THENL
    [ARITH_TAC;MATCH_MP_TAC(ISPECL [`3`;tail;
      `c2_scalar_post stackpointer ra p q n m initial`;
      `c2_step_policy stackpointer p q n m rp wp xp ordinary:num->x86state->x86state->bool`;
      `returned:x86state`] RA_CHECKED_RUN_APPEND)] THEN
   MATCH_MP_TAC(ISPECL [`3`;
     `c2_header_completed lib_file stackpointer p q n m rp wp xp ordinary initial a`;
     mk_abs(`header:x86state`,list_mk_comb(`assurance_checked_run`,
       [tail;`c2_scalar_post stackpointer ra p q n m initial`;
        `c2_step_policy stackpointer p q n m rp wp xp ordinary`;
        `header:x86state`]));
     mk_abs(`k:num`,mk_abs(`source:x86state`,mk_abs(`target:x86state`,
       list_mk_comb(`c2_step_policy stackpointer p q n m rp wp xp ordinary`,
        [mk_binop `(+):num->num->num` tail `k:num`;`source:x86state`;`target:x86state`]))));
     `returned:x86state`] RA_CHECKED_RUN_POST_MONO) THEN
   CONJ_TAC THENL
    [X_GEN_TAC `header:x86state` THEN DISCH_TAC THEN BETA_TAC THEN
     MATCH_MP_TAC(ISPECL [`lib_file:num->byte`;`lib_rw:int64->byte`;`lib_padding:int64->byte`;
      `client_file:num->byte`;`client_rw:int64->byte`;`client_padding:int64->byte`;
      `stackpointer:int64`;`ra:int64`;`p:int64`;`q:int64`;`n:num`;`m:int64->byte`;
      `rp:num->bool`;`wp:num->bool`;`xp:num->bool`;`ordinary:num->bool`;
      `initial:x86state`;`a:abi_omitted_state`;`header:x86state`]
       (if tail=`5` then C2_FALSE_HEADER_TAIL_RUN else C2_TRUE_HEADER_TAIL_RUN)) THEN
     ASM_REWRITE_TAC[];
     MATCH_MP_TAC(ISPECL [`3`;
       `c2_header_completed lib_file stackpointer p q n m rp wp xp ordinary initial a`;
       `c2_segment_policy stackpointer p q n m rp wp xp ordinary:num->x86state->x86state->bool`;
       mk_abs(`k:num`,mk_abs(`source:x86state`,mk_abs(`target:x86state`,
        list_mk_comb(`c2_step_policy stackpointer p q n m rp wp xp ordinary`,
         [mk_binop `(+):num->num->num` tail `k:num`;`source:x86state`;`target:x86state`]))));
       `returned:x86state`] RA_CHECKED_RUN_POLICY_MONO) THEN
     CONJ_TAC THENL
      [REPEAT GEN_TAC THEN DISCH_TAC THEN BETA_TAC THEN
       C2_SHIFT_CURRENT_POLICY_TAC;
       MATCH_MP_TAC(ISPECL [`lib_file:num->byte`;`lib_rw:int64->byte`;`lib_padding:int64->byte`;
        `client_file:num->byte`;`client_rw:int64->byte`;`client_padding:int64->byte`;
        `stackpointer:int64`;`ra:int64`;`p:int64`;`q:int64`;`n:num`;`m:int64->byte`;
        `rp:num->bool`;`wp:num->bool`;`xp:num->bool`;`ordinary:num->bool`;
        `initial:x86state`;`a:abi_omitted_state`;`returned:x86state`] C2_HEADER_COMPLETED_RUN) THEN
       ASM_REWRITE_TAC[]]] in tactic gl));;
let C2_CALLER_CHECKED = prove
 (c2_checked_statement,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[c2_steps] THEN
  SUBGOAL_THEN
   `(if c2_equal m p q n then 20+bp_assurance_call_steps n+cleanse_functional_steps p n
      else 16+bp_assurance_call_steps n)=
    8+(bp_assurance_call_steps n+
       (if c2_equal m p q n then 12+cleanse_functional_steps p n else 8))` SUBST1_TAC THENL
   [COND_CASES_TAC THEN ARITH_TAC;ALL_TAC] THEN
  MATCH_MP_TAC(ISPECL [`8`;`bp_assurance_call_steps n`;
    `(if c2_equal m p q n then 12+cleanse_functional_steps p n else 8)`;
    `c2_crypto_ready lib_file stackpointer p q n m rp wp xp ordinary s a`;
    `c2_crypto_ready lib_file stackpointer p q n m rp wp xp ordinary s a`;
    `c2_crypto_completed lib_file stackpointer p q n m rp wp xp ordinary s a`;
    `c2_scalar_post stackpointer ra p q n m s`;
    `c2_segment_policy stackpointer p q n m rp wp xp ordinary:num->x86state->x86state->bool`;
    `c2_segment_policy stackpointer p q n m rp wp xp ordinary:num->x86state->x86state->bool`;
    `c2_step_policy stackpointer p q n m rp wp xp ordinary:num->x86state->x86state->bool`;
    `c2_step_policy stackpointer p q n m rp wp xp ordinary:num->x86state->x86state->bool`;
    `s:x86state`] RA_CHECKED_RUN_THREE_SEGMENT) THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC(ISPECL [`lib_file:num->byte`;`lib_rw:int64->byte`;`lib_padding:int64->byte`;
     `client_file:num->byte`;`client_rw:int64->byte`;`client_padding:int64->byte`;
     `stackpointer:int64`;`ra:int64`;`p:int64`;`q:int64`;`n:num`;`m:int64->byte`;
     `rp:num->bool`;`wp:num->bool`;`xp:num->bool`;`ordinary:num->bool`;
     `s:x86state`;`a:abi_omitted_state`] C2_INITIAL_COMPARE_HANDOFF) THEN ASM_REWRITE_TAC[];
    MESON_TAC[];
    X_GEN_TAC `entry:x86state` THEN DISCH_TAC THEN
    MATCH_MP_TAC(ISPECL [`lib_file:num->byte`;`stackpointer:int64`;`p:int64`;`q:int64`;
     `n:num`;`m:int64->byte`;`rp:num->bool`;`wp:num->bool`;`xp:num->bool`;
     `ordinary:num->bool`;`s:x86state`;`a:abi_omitted_state`;`entry:x86state`]
      C2_CRYPTO_COMPLETED_RUN) THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `returned:x86state` THEN DISCH_TAC THEN
    MATCH_MP_TAC(ISPECL [`lib_file:num->byte`;`lib_rw:int64->byte`;`lib_padding:int64->byte`;
     `client_file:num->byte`;`client_rw:int64->byte`;`client_padding:int64->byte`;
     `stackpointer:int64`;`ra:int64`;`p:int64`;`q:int64`;`n:num`;`m:int64->byte`;
     `rp:num->bool`;`wp:num->bool`;`xp:num->bool`;`ordinary:num->bool`;
     `s:x86state`;`a:abi_omitted_state`;`returned:x86state`] C2_AFTER_COMPARE_TAIL_RUN) THEN
    ASM_REWRITE_TAC[];
    REPEAT GEN_TAC THEN DISCH_TAC THEN
    C2_SHIFT_CURRENT_POLICY_TAC;
    REPEAT GEN_TAC THEN DISCH_TAC THEN
    C2_SHIFT_CURRENT_POLICY_TAC;
    MESON_TAC[]]);;
