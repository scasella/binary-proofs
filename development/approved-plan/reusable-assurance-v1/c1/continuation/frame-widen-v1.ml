(* Generic frame-subsumption tactic reused from the accepted caller's finite-frame adapter. *)
let rec C1_CONT_FRAME_WIDEN_TAC gl =
 let left,_ = dest_binary "subsumed" (snd gl) in
 if is_binary ",," left then
  (MATCH_MP_TAC SUBSUMED_FOR_SEQ THEN CONJ_TAC THENL
   [MAYCHANGE_IDEMPOT_TAC;
    CONJ_TAC THENL [C1_CONT_FRAME_WIDEN_TAC;C1_CONT_FRAME_WIDEN_TAC]]) gl
 else SUBSUMED_MAYCHANGE_TAC gl;;
