(* Preserve exact residual of the executed old RSP_VALUE tactic. *)
let _,c3_successor_final_old_rsp_value_goals,_ =
 (REPEAT STRIP_TAC THEN ASM_SIMP_TAC[VAL_WORD_ADD;VAL_WORD;DIMINDEX_64;MOD_LT] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_SIMP_TAC[MOD_LT])
 ([],`!stackpointer:int64. val stackpointer+8<2 EXP 64
 ==> val(word_add stackpointer(word 8))=val stackpointer+8`);;
print_endline "C3_SUCCESSOR_FINAL_OLD_RSP_VALUE_ACTUAL_RESIDUALS";;
List.iter print_goal c3_successor_final_old_rsp_value_goals;;
print_endline "C3_SUCCESSOR_FINAL_OLD_RSP_VALUE_RESIDUALS_RETAINED";;
