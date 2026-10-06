(* Fixed C3 suffix accumulated relation, supplied as local frame data. *)
let C3_FINAL_RETURN_EXPANDED_FRAME_INCLUDED = prove
 (`!stackpointer p q:int64 n m.
   (c3_frame stackpointer p q n m ,, MAYCHANGE[RBX;RBP;R12;R13] ,,
    MAYCHANGE[RIP] ,, MAYCHANGE[ZF] ,, MAYCHANGE[SF] ,, MAYCHANGE[PF] ,,
    MAYCHANGE[CF] ,, MAYCHANGE[OF] ,, MAYCHANGE[AF] ,, MAYCHANGE[RAX] ,,
    MAYCHANGE[RSP]) subsumed
   (c3_frame stackpointer p q n m ,, MAYCHANGE[RBX;RBP;R12;R13])`,
 REPEAT GEN_TAC THEN REWRITE_TAC[c3_frame] THEN SUBSUMED_MAYCHANGE_TAC);;
print_endline "C3_SUCCESSOR_FINAL_LITERAL_FRAME_INCLUDED_CHECKED";;
