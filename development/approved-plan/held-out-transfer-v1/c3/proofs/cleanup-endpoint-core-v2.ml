(* Concrete cleanup7 endpoint derivations from the unchanged original public post,
 actual local frame and frozen input-domain clauses. No new generic rule. *)
let C3_CLEANUP_ENDPOINT_CORE_TAC =
 SUBGOAL_THEN `(MAYCHANGE [RIP;RSP;R13;RSI;RDI] ,, MAYCHANGE SOME_FLAGS ,, MAYCHANGE [memory :> bytes(word_sub(stackpointer:int64)(word 48),48)] ,, MAYCHANGE [events]) (returned:x86state) u7` ASSUME_TAC THENL
 [MP_TAC(SPEC `stackpointer:int64`C3_CLEANUP_CONCRETE_FRAME_INCLUDED) THEN
 REWRITE_TAC[subsumed] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];ALL_TAC] THEN
 MP_TAC(ISPECL[`lib_file:num->byte`;`stackpointer:int64`;`p:int64`;`q:int64`;`n:num`;
 `m:int64->byte`;`rp:num->bool`;`wp:num->bool`;`xp:num->bool`;`ordinary:num->bool`;
 `initial:x86state`;`a:abi_omitted_state`;`entry:x86state`;`returned:x86state`]C3_FIRST_RETURN_SAVED_PREFIX) THEN
 ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
 SUBGOAL_THEN `!addr:int64. ~c3_scratch stackpointer(val addr) ==> read memory(u7:x86state)addr=m addr` ASSUME_TAC THENL
 [X_GEN_TAC `addr:int64` THEN DISCH_TAC THEN
 SUBGOAL_THEN `read memory(u7:x86state)addr=read memory(returned:x86state)addr` MP_TAC THENL
 [MATCH_MP_TAC(ISPECL[`stackpointer:int64`;`addr:int64`;`returned:x86state`;`u7:x86state`]C3_CLEANUP_FRAME_BYTE) THEN ASM_REWRITE_TAC[];
 DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
 MP_TAC(REWRITE_RULE[c3_saved_prefix](ASSUME `c3_saved_prefix stackpointer p q n m (initial:x86state)(returned:x86state)`)) THEN MESON_TAC[]];ALL_TAC] THEN
 SUBGOAL_THEN `!addr. fb_immutable addr ==> ~c3_scratch stackpointer addr` ASSUME_TAC THENL
 [MATCH_MP_TAC(ISPECL[`stackpointer:int64`;`wp:num->bool`;`ordinary:num->bool`]C3_PREFIX_LIBRARY_SCRATCH_DISJOINT) THEN ASM_REWRITE_TAC[] THEN
 X_GEN_TAC `addr:num` THEN DISCH_TAC THEN
 MP_TAC(MATCH_MP(SPEC `addr:num`(ASSUME `!addr. lw_image_domain addr ==> rp addr /\ ordinary addr /\ (xp addr <=> lw_execute addr) /\ (wp addr <=> lw_image_write addr)`))(ASSUME `lw_image_domain(addr:num)`)) THEN MESON_TAC[];ALL_TAC] THEN
 SUBGOAL_THEN `fb_full_image lib_file(read memory(u7:x86state))(read memory u7)(read memory u7)` ASSUME_TAC THENL
 [MATCH_MP_TAC(ISPECL[`lib_file:num->byte`;`lib_rw:int64->byte`;`lib_padding:int64->byte`;`stackpointer:int64`;`m:int64->byte`;`u7:x86state`]C3_PREFIX_IMAGE_REBIND) THEN ASM_REWRITE_TAC[];ALL_TAC] THEN
 SUBGOAL_THEN `!i. i<n ==> read memory(u7:x86state)(word_add p(word i))=m(word_add p(word i))` ASSUME_TAC THENL
 [MATCH_MP_TAC(ISPECL[`\a:num. rp a /\ ordinary a`;`p:int64`;`n:num`;`stackpointer:int64`;`m:int64->byte`;`u7:x86state`]C3_PREFIX_INPUT_MEMORY) THEN ASM_REWRITE_TAC[];ALL_TAC] THEN
 SUBGOAL_THEN `!i. i<n ==> read memory(u7:x86state)(word_add q(word i))=m(word_add q(word i))` ASSUME_TAC THENL
 [MATCH_MP_TAC(ISPECL[`\a:num. rp a /\ ordinary a`;`q:int64`;`n:num`;`stackpointer:int64`;`m:int64->byte`;`u7:x86state`]C3_PREFIX_INPUT_MEMORY) THEN ASM_REWRITE_TAC[];ALL_TAC] THEN
 (let saved=CONJUNCT1(CONJUNCT2(REWRITE_RULE[c3_crypto_ready](ASSUME
 `c3_crypto_ready lib_file stackpointer p q n m rp wp xp ordinary (initial:x86state) a (entry:x86state)`))) in
 let cs=CONJUNCTS(REWRITE_RULE[c3_saved_prefix]saved) in
 let eq=MATCH_MP(ISPECL[`m:int64->byte`;`read memory(entry:x86state)`;`p:int64`;`q:int64`;`n:num`]C3_INITIAL_LOGICAL_SNAPSHOT_EQ)(CONJ(el 8 cs)(el 9 cs)) in
 SUBGOAL_THEN `read R13(u7:x86state)=(if c3_equal m p q n then word 1 else word 0)` ASSUME_TAC THENL
 [REWRITE_TAC[ASSUME `read R13(u7:x86state)=word_join (word 0:int32)
 (if val(word_zx(if !i. i<n ==> read memory(entry:x86state)(word_add p(word i))=read memory entry(word_add q(word i)) then word 0:int64 else word 1):int32)=0 then word 1:int32 else word 0)`;
 GSYM c3_equal;eq] THEN COND_CASES_TAC THEN CONV_TAC WORD_REDUCE_CONV THEN REWRITE_TAC[];ALL_TAC]) THEN
 (let working=MATCH_MP(ISPECL[`lib_file:num->byte`;`stackpointer:int64`;`p:int64`;`q:int64`;`n:num`;
 `m:int64->byte`;`rp:num->bool`;`wp:num->bool`;`xp:num->bool`;`ordinary:num->bool`;
 `initial:x86state`;`a:abi_omitted_state`;`entry:x86state`;`returned:x86state`]C3_FIRST_RETURN_WORKING_STATE)
 (CONJ(ASSUME `c3_crypto_ready lib_file stackpointer p q n m rp wp xp ordinary (initial:x86state) a (entry:x86state)`)
 (ASSUME `bp_assurance_call_post 0x10241840 (word_sub(stackpointer:int64)(word 48))(word 0x23001138)p q n(read events(entry:x86state))(read memory entry)entry(returned:x86state)`)) in
 let ac=MATCH_MP(ISPECL[`stackpointer:int64`;`returned:x86state`;`u7:x86state`]C3_CLEANUP_FRAME_AC)
 (ASSUME `(MAYCHANGE [RIP;RSP;R13;RSI;RDI] ,, MAYCHANGE SOME_FLAGS ,, MAYCHANGE [memory :> bytes(word_sub(stackpointer:int64)(word 48),48)] ,, MAYCHANGE [events]) (returned:x86state) u7`) in
 ASSUME_TAC(REWRITE_RULE[GSYM ac](last(CONJUNCTS working)))) THEN
 MP_TAC(MATCH_MP(SPEC `stackpointer:int64`C3_STACK_ALIGNMENT)(CONJ(ASSUME `48<=val(stackpointer:int64)`)(ASSUME `val(stackpointer:int64) MOD 16=8`))) THEN STRIP_TAC;;
e C3_CLEANUP_ENDPOINT_CORE_TAC;;
print_endline "C3_CLEANUP_ENDPOINT_CORE_V1_RETURN";;
print_endline(string_of_term(snd(top_goal())));;
