(* Concrete state projections, fixed congruences reduced with standard CONG/NUM only. *)
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
  SIMP_TAC[c3w_state; C_ARGUMENTS; RSP; RDI; RSI; RDX; DF;
           e5_normal_flags; READ_COMPONENT_COMPOSE; READ_ELEMENT;
           READ_BITELEMENT; x86state_COMPONENTS; WORD_EQ;
           DIMINDEX_4; DIMINDEX_64; BIT_WORD] THEN
  REWRITE_TAC[CONG] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]);;
print_endline "C3W_MEMBERSHIP_STATE_V3_COMPLETE";;
