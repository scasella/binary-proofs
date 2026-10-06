(* Diagnostic replay of the literal failed v1 fixed caller-code geometry.
   Stops before ARITH_RULE to retain the exact residual and all free types. *)
g `!j. j<89 ==> assurance_region(word 0x23001120:int64)89
    (val(word_add(word 0x23001120)(word j)))`;;
e(GEN_TAC THEN DISCH_TAC THEN
 SUBGOAL_THEN `j<18446744073709551616 /\ 587206944+j<18446744073709551616`
   STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC;ALL_TAC] THEN
 REWRITE_TAC[assurance_region;VAL_WORD_ADD;VAL_WORD;DIMINDEX_64] THEN
 CONV_TAC NUM_REDUCE_CONV THEN ASM_SIMP_TAC[MOD_LT]);;
print_endline "C3_TRANSPORT_CALLER_CODE_BYTE_GEOMETRY_V1_EXACT_RESIDUAL_BEGIN";;
print_goal(top_realgoal());;
List.iter (fun v -> print_endline(string_of_term v ^ " : " ^ string_of_type(type_of v)))
 (frees(snd(top_goal())));;
print_endline "C3_TRANSPORT_CALLER_CODE_BYTE_GEOMETRY_V1_EXACT_RESIDUAL_END";;
