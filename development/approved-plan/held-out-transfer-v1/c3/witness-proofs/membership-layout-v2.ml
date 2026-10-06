(* Concrete C3 membership image/layout facts. Requires membership-support.
   No new general memory/normalization/automation law and no execution import. *)

let C3W_IMMUTABLE_SLOT_SEPARATION = prove
 (`!(addr:int64).
    fb_immutable(val addr) \/ c3_immutable(val addr)
    ==> ~assurance_region (word 0x300008) 8 (val addr) /\
        ~assurance_region (word 0x23003fd0) 8 (val addr) /\
        ~assurance_region (word 0x23003fd8) 8 (val addr)`,
  REWRITE_TAC[fb_immutable; c3_immutable; assurance_region;
              VAL_WORD; DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT STRIP_TAC THEN ASM_ARITH_TAC);;

let C3W_IMMUTABLE_IMAGES_SEPARATE = prove
 (`!(addr:int64). c3_immutable(val addr) ==> ~fb_immutable(val addr)`,
  REWRITE_TAC[c3_immutable; fb_immutable] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REPEAT STRIP_TAC THEN ASM_ARITH_TAC);;

let C3W_MEMORY_IMMUTABLE = prove
 (`!lib_file client_file payload (addr:int64).
    (fb_immutable(val addr)
       ==> c3w_memory lib_file client_file payload addr=
           lib_file(val addr-0x10000000)) /\
    (c3_immutable(val addr)
       ==> c3w_memory lib_file client_file payload addr=
           client_file(val addr-0x23000000))`,
  REPEAT GEN_TAC THEN CONJ_TAC THEN DISCH_TAC THEN
  ASM_SIMP_TAC[C3W_MEMORY_OUTSIDE; C3W_IMMUTABLE_SLOT_SEPARATION;
               C3W_IMMUTABLE_IMAGES_SEPARATE; c3w_seed]);;

let C3W_MEMORY_IMAGES = prove
 (`!lib_file client_file payload.
    fb_full_image lib_file (c3w_memory lib_file client_file payload)
      (c3w_memory lib_file client_file payload)
      (c3w_memory lib_file client_file payload) /\
    c3_full_image client_file (c3w_memory lib_file client_file payload)
      (c3w_memory lib_file client_file payload)
      (c3w_memory lib_file client_file payload)`,
  REWRITE_TAC[fb_full_image; c3_full_image;
              fb_reference_image; c3_reference_image] THEN
  REPEAT STRIP_TAC THEN REPEAT COND_CASES_TAC THEN
  ASM_SIMP_TAC[C3W_MEMORY_IMMUTABLE]);;

let C3W_EXTERNAL_SLOT_SEPARATION = prove
 (`!(addr:int64). c3w_external(val addr)
    ==> ~fb_immutable(val addr) /\ ~c3_immutable(val addr) /\
        ~assurance_region (word 0x300008) 8 (val addr) /\
        ~assurance_region (word 0x23003fd0) 8 (val addr) /\
        ~assurance_region (word 0x23003fd8) 8 (val addr)`,
  REWRITE_TAC[c3w_external; fb_immutable; c3_immutable; assurance_region;
              VAL_WORD; DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT STRIP_TAC THEN ASM_ARITH_TAC);;

let C3W_EXTERNAL_PERMISSIONS = prove
 (`!addr. c3w_external addr
    ==> c3w_read addr /\ c3w_write addr /\ c3w_ordinary addr`,
  REWRITE_TAC[c3w_external; c3w_read; c3w_write; c3w_ordinary;
              lw_image_domain; lw_image_write; c3_image_domain; c3_image_write] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REPEAT STRIP_TAC THEN
  REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let C3W_LAYOUT_EXTERNAL_REGIONS = prove
 (`!p q n addr. c3w_layout p q n /\
    (assurance_region p n addr \/ assurance_region q n addr)
    ==> c3w_external addr`,
  REWRITE_TAC[c3w_layout] THEN
  MESON_TAC[HT_SPAN_POINT]);;

let C3W_LAYOUT_POINT = prove
 (`!p q n i. c3w_layout p q n /\ i<n
    ==> c3w_external(val(word_add p (word i))) /\
        c3w_external(val(word_add q (word i)))`,
  REWRITE_TAC[c3w_layout] THEN
  MESON_TAC[HT_SPAN_POINT; HT_SPAN_WORD_ADD_REGION]);;

let C3W_BUFFER_VALUES = prove
 (`!lib_file client_file payload p q n. c3w_layout p q n
    ==> (!i. i<n ==> c3w_memory lib_file client_file payload
          (word_add p (word i))=payload(word_add p (word i))) /\
        (!i. i<n ==> c3w_memory lib_file client_file payload
          (word_add q (word i))=payload(word_add q (word i)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`p:int64`;`q:int64`;`n:num`;`i:num`] C3W_LAYOUT_POINT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[C3W_MEMORY_OUTSIDE; C3W_EXTERNAL_SLOT_SEPARATION;
               c3w_seed]);;

print_endline "C3W_MEMBERSHIP_BUFFER_VALUES_V2_COMPLETE";;
