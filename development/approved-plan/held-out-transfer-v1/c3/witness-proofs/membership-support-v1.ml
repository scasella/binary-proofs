(* Permitted C3 caller-specific membership support; no caller execution proof.
   Each memory-write fact uses only the three actual frozen initial slots.
   No general address/width/state composition law or new tactic is introduced. *)

let C3W_STATE_PROJECTIONS = prove
 (`!lib_file client_file payload p q n.
    read RIP (c3w_state lib_file client_file payload p q n)=word 0x23001120 /\
    read RSP (c3w_state lib_file client_file payload p q n)=word 0x300008 /\
    C_ARGUMENTS [p;q;word n] (c3w_state lib_file client_file payload p q n) /\
    read memory (c3w_state lib_file client_file payload p q n)=
      c3w_memory lib_file client_file payload /\
    read DF (c3w_state lib_file client_file payload p q n)=F /\
    ~bit 18(read rflags(c3w_state lib_file client_file payload p q n)) /\
    e5_normal_flags(c3w_state lib_file client_file payload p q n)`,
  REWRITE_TAC[c3w_state; C_ARGUMENTS; RSP; RDI; RSI; RDX; DF;
              e5_normal_flags; READ_COMPONENT_COMPOSE; READ_ELEMENT;
              READ_BITELEMENT; x86state_COMPONENTS] THEN
  CONV_TAC(DEPTH_CONV WORD_REDUCE_CONV) THEN REWRITE_TAC[]);;

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
  CONV_TAC NUM_REDUCE_CONV THEN REPEAT STRIP_TAC THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let C3W_MEMORY_OUTSIDE = prove
 (`!lib_file client_file payload (addr:int64).
    ~assurance_region (word 0x300008) 8 (val addr) /\
    ~assurance_region (word 0x23003fd0) 8 (val addr) /\
    ~assurance_region (word 0x23003fd8) 8 (val addr)
    ==> c3w_memory lib_file client_file payload addr =
        c3w_seed lib_file client_file payload addr`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[c3w_memory; C3W_FIXED_WORD_WRITES] THEN
  ONCE_REWRITE_TAC[GSYM READ_ELEMENT] THEN
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
  CONV_TAC(DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV) THEN REWRITE_TAC[]);;

print_endline "C3W_MEMBERSHIP_SUPPORT_V1_COMPLETE";;
