(* Concrete C3 accumulated prefix/first-call/cleanup7 frame inclusion.
 Named obligation: cleanup endpoint retains complete caller MID frame.
 Existing SUBSUMED_MAYCHANGE_TAC only; no new automation or generic export. *)
let C3_CLEANUP_TOTAL_FRAME_INCLUDED = prove
 (`!stackpointer p q:int64 n m:int64->byte.
 (c3_prefix_frame stackpointer ,,
  (MAYCHANGE[RIP;RSP;RAX;RDI;RSI;RDX;R10;R11] ,,
   MAYCHANGE SOME_FLAGS ,, MAYCHANGE[events]) ,,
  (MAYCHANGE[RIP;RSP;R13;RSI;RDI] ,, MAYCHANGE SOME_FLAGS ,,
   MAYCHANGE[memory :> bytes(word_sub stackpointer(word 48),48)] ,,
   MAYCHANGE[events])) subsumed
 (c3_frame stackpointer p q n m ,, MAYCHANGE[RBX;RBP;R12;R13])`,
 REPEAT GEN_TAC THEN REWRITE_TAC[c3_prefix_frame;c3_frame;SOME_FLAGS] THEN
 SUBSUMED_MAYCHANGE_TAC);;
print_endline "C3_CLEANUP_TOTAL_FRAME_INCLUDED_V1_DEVELOPMENT_CHECKED";;
