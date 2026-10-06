(* Exact failed local RSPvalue tactic on a private goal. *)
let c3fr_rsp_value_literal =
 `!stackpointer:int64. val stackpointer+8<2 EXP 64
 ==> val(word_add stackpointer(word 8))=val stackpointer+8`;;
let _,c3fr_rsp_value_goals,_ =
 (REPEAT STRIP_TAC THEN ASM_SIMP_TAC[VAL_WORD_ADD;VAL_WORD;DIMINDEX_64;MOD_LT] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_SIMP_TAC[MOD_LT])([],c3fr_rsp_value_literal);;
print_endline "C3_FINAL_RETURN_RSP_VALUE_PRIVATE_RESIDUAL";;
List.iter print_goal c3fr_rsp_value_goals;;
print_endline "C3_FINAL_RETURN_RSP_VALUE_PRIVATE_COMPLETE";;
