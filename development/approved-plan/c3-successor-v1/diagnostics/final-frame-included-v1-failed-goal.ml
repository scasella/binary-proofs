let c3_successor_final_included_literal =
 `!stackpointer p q:int64 n m.
   (c3_frame stackpointer p q n m ,, MAYCHANGE[RBX;RBP;R12;R13] ,,
    MAYCHANGE[RIP] ,, MAYCHANGE[ZF] ,, MAYCHANGE[SF] ,, MAYCHANGE[PF] ,,
    MAYCHANGE[CF] ,, MAYCHANGE[OF] ,, MAYCHANGE[AF] ,, MAYCHANGE[RAX] ,,
    MAYCHANGE[RSP]) subsumed
   (c3_frame stackpointer p q n m ,, MAYCHANGE[RBX;RBP;R12;R13])`;;
let _,c3_successor_final_included_v1_failed_input,_ =
 (REPEAT GEN_TAC THEN REWRITE_TAC[c3_frame]) ([],c3_successor_final_included_literal);;
print_endline "C3_SUCCESSOR_FINAL_FRAME_INCLUDED_V1_EXACT_FAIL_INPUT";;
List.iter print_goal c3_successor_final_included_v1_failed_input;;
