let C3W_EIGHT_LAYOUTS = prove
 (`c3w_layout (word 0) (word 0) 0 /\
   c3w_layout (word 0x50000000) (word 0x60000000) 1 /\
   c3w_layout (word 0x50000003) (word 0x60000005) 17 /\
   c3w_layout (word 0x50000003) (word 0x50000003) 16 /\
   c3w_layout (word 0x50000003) (word 0x50000004) 17 /\
   c3w_layout (word 0x50000004) (word 0x50000003) 17 /\
   c3w_layout (word 0x50000fff) (word 0x60000fff) 15 /\
   c3w_layout (word 0x7fffffffffff) (word 0xffff800000000000) 1`,
  REWRITE_TAC[c3w_layout; assurance_span_ok; c3w_external;
              assurance_canonical48; VAL_WORD; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REPEAT STRIP_TAC THEN ASM_ARITH_TAC);;

print_endline "C3W_MEMBERSHIP_EIGHT_LAYOUTS_V1_COMPLETE";;
