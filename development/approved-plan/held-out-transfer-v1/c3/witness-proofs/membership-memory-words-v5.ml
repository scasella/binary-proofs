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
           READ_WRITE_VALID_COMPONENT; VALID_COMPONENT_BYTES64]);;

print_endline "C3W_MEMBERSHIP_MEMORY_WORDS_V5_COMPLETE";;
