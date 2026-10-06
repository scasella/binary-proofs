(* Fixed C3 three-slot read repair. Requires checked memory-v2 first three facts.
   Uses the existing READ_OVER_WRITE_TAC directly; no new generic law/tactic. *)
let C3W_MEMORY_WORDS = prove
 (`!lib_file client_file payload.
    read (bytes64 (word 0x300008))
      (c3w_memory lib_file client_file payload)=word 0x400000 /\
    read (bytes64 (word 0x23003fd0))
      (c3w_memory lib_file client_file payload)=word 0x10241840 /\
    read (bytes64 (word 0x23003fd8))
      (c3w_memory lib_file client_file payload)=word 0x102417d0`,
  REPEAT GEN_TAC THEN REWRITE_TAC[c3w_memory] THEN
  REPEAT CONJ_TAC THEN READ_OVER_WRITE_TAC);;

print_endline "C3W_MEMBERSHIP_MEMORY_WORDS_V3_COMPLETE";;
