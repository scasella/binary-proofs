(* Final functional/frame transport from proved public phase endpoints.
   No instruction-rule input appears in these endpoint implications. *)
let C2_FINAL_STACK_VALUE = prove
 (c2_final_stack_value_statement,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_SIMP_TAC[VAL_WORD_ADD_CASES;VAL_WORD;DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC);;
let C2_SUFFIX_SHARED_FINAL_FACTS_TAC =
 SUBGOAL_THEN `val(read RSP (t:x86state))=val(stackpointer:int64)+8`
  ASSUME_TAC THENL
  [MATCH_MP_TAC C2_FINAL_STACK_VALUE THEN CONJ_TAC THENL
   [C2_PRE_FACT_TAC;ASM_REWRITE_TAC[]];ALL_TAC] THEN
 SUBGOAL_THEN `c2_loaded_code (t:x86state) /\ c2_got t` STRIP_ASSUME_TAC THENL
  [ASM_MESON_TAC[C2_COMPARE_MEMORY_CODE_GOT_TRANSPORT];ALL_TAC] THEN
 SUBGOAL_THEN `read (memory :> bytes64 (stackpointer:int64)) (t:x86state)=ra`
  ASSUME_TAC THENL
  [MP_TAC(ISPECL [`returned:x86state`;`t:x86state`;`stackpointer:int64`]
    C2_COMPARE_MEMORY_SLOT_TRANSPORT) THEN ASM_REWRITE_TAC[] THEN MESON_TAC[];ALL_TAC] THEN
 SUBGOAL_THEN `c2_frame stackpointer p q n m (initial:x86state) t` ASSUME_TAC THENL
  [MATCH_MP_TAC(ISPECL [`stackpointer:int64`;`p:int64`;`q:int64`;`n:num`;
    `m:int64->byte`;`initial:x86state`;`t:x86state`] C2_RESTORED_FRAME_NARROW) THEN
   ASM_REWRITE_TAC[];ALL_TAC];;
let C2_FALSE_SUFFIX_SCALAR = prove
 (c2_false_suffix_scalar_statement,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`lib_file:num->byte`;`lib_rw:int64->byte`;`lib_padding:int64->byte`;
   `client_file:num->byte`;`client_rw:int64->byte`;`client_padding:int64->byte`;
   `stackpointer:int64`;`ra:int64`;`p:int64`;`q:int64`;`n:num`;`m:int64->byte`;
   `rp:num->bool`;`wp:num->bool`;`xp:num->bool`;`ordinary:num->bool`;
   `initial:x86state`;`a:abi_omitted_state`;`returned:x86state`] C2_HEADER_INITIAL_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `c2_saved_prefix stackpointer p q n m (initial:x86state) returned` THEN
  REWRITE_TAC[c2_saved_prefix] THEN STRIP_TAC THEN
  UNDISCH_TAC `c2_suffix_post stackpointer ra p q n m (initial:x86state) returned t` THEN
  REWRITE_TAC[c2_suffix_post] THEN STRIP_TAC THEN
  SUBGOAL_THEN `c2_accumulated_frame stackpointer p q n m (initial:x86state) t`
   ASSUME_TAC THENL
   [MATCH_MP_TAC(ISPECL [`stackpointer:int64`;`p:int64`;`q:int64`;`n:num`;
     `m:int64->byte`;`initial:x86state`;`returned:x86state`;`t:x86state`]
      C2_BEFORE_SUFFIX_ACCUMULATED_COMPOSE) THEN ASM_REWRITE_TAC[];ALL_TAC] THEN
  C2_SUFFIX_SHARED_FINAL_FACTS_TAC THEN
  REWRITE_TAC[c2_scalar_post] THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;
let C2_TRUE_SUFFIX_SCALAR = prove
 (c2_true_suffix_scalar_statement,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`lib_file:num->byte`;`lib_rw:int64->byte`;`lib_padding:int64->byte`;
   `client_file:num->byte`;`client_rw:int64->byte`;`client_padding:int64->byte`;
   `stackpointer:int64`;`ra:int64`;`p:int64`;`q:int64`;`n:num`;`m:int64->byte`;
   `rp:num->bool`;`wp:num->bool`;`xp:num->bool`;`ordinary:num->bool`;
   `initial:x86state`;`a:abi_omitted_state`;`returned:x86state`] C2_CLEANSE_RETURNED_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `c2_suffix_post stackpointer ra p q n m (initial:x86state) returned t` THEN
  REWRITE_TAC[c2_suffix_post] THEN STRIP_TAC THEN
  SUBGOAL_THEN `c2_accumulated_frame stackpointer p q n m (initial:x86state) t`
   ASSUME_TAC THENL
   [MATCH_MP_TAC(ISPECL [`stackpointer:int64`;`p:int64`;`q:int64`;`n:num`;
     `m:int64->byte`;`initial:x86state`;`returned:x86state`;`t:x86state`]
      C2_ACCUMULATED_SUFFIX_COMPOSE) THEN ASM_REWRITE_TAC[];ALL_TAC] THEN
  C2_SUFFIX_SHARED_FINAL_FACTS_TAC THEN
  REWRITE_TAC[c2_scalar_post] THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;
