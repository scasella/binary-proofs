(* Fixed three-phase C3 frame composition; no generic sequencing automation. *)
let C3_CLEANUP_ENDPOINT_TOTAL_FRAME_TAC =
 SUBGOAL_THEN `(c3_frame stackpointer p q n m ,, MAYCHANGE[RBX;RBP;R12;R13]) (initial:x86state)u7` ASSUME_TAC THENL
 [MATCH_MP_TAC(REWRITE_RULE[subsumed](ISPECL[`stackpointer:int64`;`p:int64`;`q:int64`;`n:num`;`m:int64->byte`]C3_CLEANUP_TOTAL_FRAME_INCLUDED)) THEN
 GEN_REWRITE_TAC (RATOR_CONV o RATOR_CONV)[seq] THEN BETA_TAC THEN EXISTS_TAC `entry:x86state` THEN CONJ_TAC THENL
 [ACCEPT_TAC(last(CONJUNCTS(REWRITE_RULE[c3_crypto_ready](ASSUME `c3_crypto_ready lib_file stackpointer p q n m rp wp xp ordinary(initial:x86state)a(entry:x86state)`))));
 GEN_REWRITE_TAC (RATOR_CONV o RATOR_CONV)[seq] THEN BETA_TAC THEN EXISTS_TAC `returned:x86state` THEN CONJ_TAC THENL
 [ACCEPT_TAC(last(CONJUNCTS(REWRITE_RULE[bp_assurance_call_post](ASSUME `bp_assurance_call_post 0x10241840(word_sub(stackpointer:int64)(word 48))(word 0x23001138)p q n(read events(entry:x86state))(read memory entry)entry(returned:x86state)`))));
 ACCEPT_TAC(ASSUME `(MAYCHANGE[RIP;RSP;R13;RSI;RDI] ,, MAYCHANGE SOME_FLAGS ,, MAYCHANGE[memory :> bytes(word_sub(stackpointer:int64)(word 48),48)] ,, MAYCHANGE[events])(returned:x86state)(u7:x86state)`)] ];ALL_TAC];;
e C3_CLEANUP_ENDPOINT_TOTAL_FRAME_TAC;;
print_endline "C3_CLEANUP_TOTAL_FRAME_CONTEXT_V1_RETURN";;
print_endline(string_of_term(snd(top_goal())));;
