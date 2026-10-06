(* Only tactical grouping repair: apply the existing two-way subgoal block to each of 10 branches. *)
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
  (SUBGOAL_THEN `c3w_external addr` ASSUME_TAC THENL
   [ASM_MESON_TAC[C3W_LAYOUT_EXTERNAL_REGIONS; assurance_region];
    UNDISCH_TAC `c3w_external addr` THEN
    REWRITE_TAC[c3w_external] THEN ASM_ARITH_TAC]));;

print_endline "C3W_MEMBERSHIP_PROTECTION_V2_COMPLETE";;
