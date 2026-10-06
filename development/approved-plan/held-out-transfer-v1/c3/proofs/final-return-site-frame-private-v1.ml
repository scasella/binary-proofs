(* Exact first fixed-component preservation stages on private goal. *)
let c3fr_frame13_literal =
 `!stackpointer p q:int64 n m u v:x86state.
 (c3_frame stackpointer p q n m ,, MAYCHANGE[RBX;RBP;R12])u v ==> read R13 v=read R13 u`;;
let _,c3fr_frame13_prefix,_ =
 (REPEAT GEN_TAC THEN REWRITE_TAC[c3_frame] THEN DISCH_TAC)([],c3fr_frame13_literal);;
print_endline "C3_FINAL_RETURN_FRAME13_PREFIX";;List.iter print_goal c3fr_frame13_prefix;;
let _,c3fr_frame13_match,_ =
 (MATCH_MP_TAC(ISPECL[`R13:(x86state,int64)component`;
 `[RIP;RSP;RAX;RDI;RSI;RDX;R10;R11;RBX;RBP;R12]:((x86state,int64)component)list`;
 `SOME_FLAGS:((x86state,bool)component)list`;
 `[memory :> bytes(p,n);memory :> bytes(word_sub stackpointer(word 48),48)]`;
 `[events]:((x86state,uarch_event list)component)list`;`u:x86state`;`v:x86state`]
 R1_SECRET_FOUR_FRAME_PRESERVATION) THEN REPEAT CONJ_TAC)(List.hd c3fr_frame13_prefix);;
print_endline "C3_FINAL_RETURN_FRAME13_AFTER_MATCH";;List.iter print_goal c3fr_frame13_match;;
let _,c3fr_frame13_monotone,_ = MONOTONE_MAYCHANGE_TAC(List.nth c3fr_frame13_match 4);;
print_endline "C3_FINAL_RETURN_FRAME13_AFTER_MONOTONE";;List.iter print_goal c3fr_frame13_monotone;;
print_endline "C3_FINAL_RETURN_FRAME13_PRIVATE_COMPLETE";;
