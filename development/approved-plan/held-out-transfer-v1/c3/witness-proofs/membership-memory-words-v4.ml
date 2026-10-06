(* Only the actual C3 return/GOT slot pairs; no variable-slot law or new tactic. *)
let C3W_FIXED_SLOT_ORTHOGONAL = prove
 (`orthogonal_components
      (bytes64(word 0x23003fd0):((int64->byte),int64)component)
      (bytes64(word 0x300008)) /\
   orthogonal_components
      (bytes64(word 0x23003fd8):((int64->byte),int64)component)
      (bytes64(word 0x300008)) /\
   orthogonal_components
      (bytes64(word 0x23003fd8):((int64->byte),int64)component)
      (bytes64(word 0x23003fd0))`,
  REPEAT CONJ_TAC THEN REWRITE_TAC[bytes64] THEN
  MATCH_MP_TAC ORTHOGONAL_COMPONENTS_COMPOSE_LEFT THEN
  REWRITE_TAC[ORTHOGONAL_COMPONENTS_BYTES; VAL_WORD; DIMINDEX_64] THEN
  MATCH_MP_TAC NONOVERLAPPING_MODULO_SIMPLE THEN CONV_TAC NUM_REDUCE_CONV);;

let C3W_MEMORY_WORDS = prove
 (`!lib_file client_file payload.
    read (bytes64 (word 0x300008))
      (c3w_memory lib_file client_file payload)=word 0x400000 /\
    read (bytes64 (word 0x23003fd0))
      (c3w_memory lib_file client_file payload)=word 0x10241840 /\
    read (bytes64 (word 0x23003fd8))
      (c3w_memory lib_file client_file payload)=word 0x102417d0`,
  REPEAT GEN_TAC THEN REWRITE_TAC[c3w_memory] THEN
  SIMP_TAC[READ_WRITE_ORTHOGONAL_COMPONENTS; C3W_FIXED_SLOT_ORTHOGONAL;
           READ_WRITE_SAME_RULE `bytes64(word 0x300008):((int64->byte),int64)component`;
           READ_WRITE_SAME_RULE `bytes64(word 0x23003fd0):((int64->byte),int64)component`;
           READ_WRITE_SAME_RULE `bytes64(word 0x23003fd8):((int64->byte),int64)component`]);;

print_endline "C3W_MEMBERSHIP_MEMORY_WORDS_V4_COMPLETE";;
