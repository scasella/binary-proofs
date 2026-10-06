(* Private application of the failed, existing fixed C3 memory-word tactic. No theorem/global-goal change. *)
let (_,c3w_memory_private_goals_v1,_) =
 (REPEAT GEN_TAC THEN REWRITE_TAC[c3w_memory] THEN
  CONV_TAC(DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV) THEN REWRITE_TAC[]) ([],`!lib_file client_file payload.
    read (bytes64 (word 0x300008))
      (c3w_memory lib_file client_file payload)=word 0x400000 /\
    read (bytes64 (word 0x23003fd0))
      (c3w_memory lib_file client_file payload)=word 0x10241840 /\
    read (bytes64 (word 0x23003fd8))
      (c3w_memory lib_file client_file payload)=word 0x102417d0`);;
List.iter print_goal c3w_memory_private_goals_v1;;
print_endline "C3W_MEMORY_PRIVATE_DIAGNOSTIC_V1_COMPLETE";;
