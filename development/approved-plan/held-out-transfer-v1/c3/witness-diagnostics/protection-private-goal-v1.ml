(* Private exact protection tactic prefix: print generated goal count and terms.
   No theorem binding, no global goalstack mutation, no new proof procedure. *)
let (_,c3w_protection_private_goals_v1,_) =
 (REWRITE_TAC[c3_scratch; assurance_region; VAL_WORD_SUB_CASES;
              VAL_WORD; DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT STRIP_TAC) ([],`!p q n. c3w_layout p q n
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
            assurance_region(word 0x102417d0) 97 addr))`);;
Printf.printf "C3W_PROTECTION_PREFIX_GOALS=%d\n" (List.length c3w_protection_private_goals_v1);;
List.iter print_goal c3w_protection_private_goals_v1;;
print_endline "C3W_PROTECTION_PRIVATE_DIAGNOSTIC_V1_COMPLETE";;
