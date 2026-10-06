(* C3 concrete witness permission/layout facts. Existing rules only. *)

let C3W_INITIAL_ABI = prove
 (`assurance_canonical48(val(read ABI_FS_BASE fb_initial_abi))`,
  REWRITE_TAC[fb_initial_abi; abi_omitted_state_COMPONENTS;
              assurance_canonical48; VAL_WORD; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let C3W_IMAGE_PERMISSIONS = prove
 (`(!addr. lw_image_domain addr ==> c3w_read addr /\ c3w_ordinary addr /\
      (c3w_execute addr <=> lw_execute addr) /\
      (c3w_write addr <=> lw_image_write addr)) /\
    (!addr. c3_image_domain addr ==> c3w_read addr /\ c3w_ordinary addr /\
      (c3w_execute addr <=> c3_image_execute addr) /\
      (c3w_write addr <=> c3_image_write addr))`,
  REWRITE_TAC[c3w_read; c3w_ordinary; c3w_execute; c3w_write;
              assurance_canonical48; lw_execute; lw_image_execute;
              lw_image_domain; lw_image_write; c3_image_domain;
              c3_image_execute; c3_image_write] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REPEAT STRIP_TAC THEN
  REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let C3W_FIXED_SPANS = prove
 (`assurance_span_ok (\a. c3w_read a /\ c3w_ordinary a) (0x300008-48) 48 /\
    assurance_span_ok (\a. c3w_write a /\ c3w_ordinary a) (0x300008-48) 48 /\
    assurance_span_ok (\a. c3w_read a /\ c3w_ordinary a) 0x300008 8 /\
    assurance_span_ok (\a. c3w_read a /\ c3w_ordinary a) 0x23003fd0 8 /\
    assurance_span_ok (\a. c3w_read a /\ c3w_ordinary a) 0x23003fd8 8 /\
    assurance_span_ok (\a. c3w_execute a /\ c3w_ordinary a) 0x23001120 89 /\
    assurance_span_ok (\a. c3w_execute a /\ c3w_ordinary a) 0x23001030 6 /\
    assurance_span_ok (\a. c3w_execute a /\ c3w_ordinary a) 0x23001040 6 /\
    assurance_span_ok (\a. c3w_execute a /\ c3w_ordinary a) 0x10241840 95 /\
    assurance_span_ok (\a. c3w_execute a /\ c3w_ordinary a) 0x102417d0 97`,
  REWRITE_TAC[assurance_span_ok; c3w_read; c3w_ordinary; c3w_execute;
              c3w_write; assurance_canonical48; lw_execute; lw_image_execute;
              lw_image_domain; lw_image_write; c3_image_domain;
              c3_image_execute; c3_image_write] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REPEAT STRIP_TAC THEN
  REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let C3W_LAYOUT_SPANS = prove
 (`!p q n. c3w_layout p q n
    ==> assurance_span_ok (\a. c3w_read a /\ c3w_ordinary a) (val p) n /\
        assurance_span_ok (\a. c3w_read a /\ c3w_ordinary a) (val q) n /\
        assurance_span_ok (\a. c3w_write a /\ c3w_ordinary a) (val p) n`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC (SPECL [`c3w_external`;`\a. c3w_read a /\ c3w_ordinary a`;
                        `val(p:int64)`;`n:num`] R1_SECRET_SPAN_MONO);
    MATCH_MP_TAC (SPECL [`c3w_external`;`\a. c3w_read a /\ c3w_ordinary a`;
                        `val(q:int64)`;`n:num`] R1_SECRET_SPAN_MONO);
    MATCH_MP_TAC (SPECL [`c3w_external`;`\a. c3w_write a /\ c3w_ordinary a`;
                        `val(p:int64)`;`n:num`] R1_SECRET_SPAN_MONO)] THEN
  ASM_MESON_TAC[c3w_layout; C3W_EXTERNAL_PERMISSIONS]);;

let C3W_LAYOUT_PROTECTION = prove
 (`!p q n. c3w_layout p q n
    ==> (!addr. ~(assurance_region p n addr /\ c3_scratch(word 0x300008) addr)) /\
        (!addr. ~(assurance_region q n addr /\ c3_scratch(word 0x300008) addr)) /\
        (!addr. ~(assurance_region p n addr /\ assurance_region(word 0x300008) 8 addr)) /\
        (!addr. assurance_region p n addr ==>
          ~(assurance_region(word 0x23001120) 89 addr \/
            assurance_region(word 0x23001030) 6 addr \/
            assurance_region(word 0x23001040) 6 addr \/
            assurance_region(word 0x23003fd0) 8 addr \/
            assurance_region(word 0x23003fd8) 8 addr \/
            assurance_region(word 0x10241840) 95 addr \/
            assurance_region(word 0x102417d0) 97 addr))`,
  REWRITE_TAC[c3_scratch; assurance_region; VAL_WORD_SUB_CASES;
              VAL_WORD; DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `c3w_external addr` ASSUME_TAC THENL
   [ASM_MESON_TAC[C3W_LAYOUT_EXTERNAL_REGIONS; assurance_region];
    UNDISCH_TAC `c3w_external addr` THEN
    REWRITE_TAC[c3w_external] THEN ASM_ARITH_TAC]);;

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

print_endline "C3W_MEMBERSHIP_PERMISSIONS_V1_COMPLETE";;
