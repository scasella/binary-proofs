(* Isolated actual C3 initial-word-slot support; no generic law/automation or execution proof. *)
let C3W_FIXED_WORD_WRITES = prove
 (`!(m:int64->byte).
    write (bytes64 (word 0x300008)) (word 0x400000) m =
      write (bytes(word 0x300008,8)) 0x400000 m /\
    write (bytes64 (word 0x23003fd0)) (word 0x10241840) m =
      write (bytes(word 0x23003fd0,8)) 0x10241840 m /\
    write (bytes64 (word 0x23003fd8)) (word 0x102417d0) m =
      write (bytes(word 0x23003fd8,8)) 0x102417d0 m`,
  REWRITE_TAC[bytes64; WRITE_COMPONENT_COMPOSE; asword; through; write;
              VAL_WORD; DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV);;

let C3W_FIXED_OUTSIDE_DISTANCE = prove
 (`!(addr:int64).
    (~assurance_region (word 0x300008) 8 (val addr)
       ==> ~(val(word_sub addr (word 0x300008))<8)) /\
    (~assurance_region (word 0x23003fd0) 8 (val addr)
       ==> ~(val(word_sub addr (word 0x23003fd0))<8)) /\
    (~assurance_region (word 0x23003fd8) 8 (val addr)
       ==> ~(val(word_sub addr (word 0x23003fd8))<8))`,
  REWRITE_TAC[assurance_region; VAL_WORD_SUB_CASES; VAL_WORD; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REPEAT GEN_TAC THEN
  REPEAT CONJ_TAC THEN REPEAT COND_CASES_TAC THEN ASM_ARITH_TAC);;

let C3W_MEMORY_OUTSIDE = prove
 (`!lib_file client_file payload (addr:int64).
    ~assurance_region (word 0x300008) 8 (val addr) /\
    ~assurance_region (word 0x23003fd0) 8 (val addr) /\
    ~assurance_region (word 0x23003fd8) 8 (val addr)
    ==> c3w_memory lib_file client_file payload addr =
        c3w_seed lib_file client_file payload addr`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[c3w_memory; C3W_FIXED_WORD_WRITES] THEN
  CONV_TAC(BINOP_CONV(REWR_CONV(GSYM READ_ELEMENT))) THEN
  ASM_SIMP_TAC[READ_ELEMENT_WRITE_BYTES; C3W_FIXED_OUTSIDE_DISTANCE] THEN
  REWRITE_TAC[READ_ELEMENT]);;

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

print_endline "C3W_MEMBERSHIP_MEMORY_V3_COMPLETE";;
