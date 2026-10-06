(* Closed concrete C3 tail offsets, supplied as data to frozen normalization. *)
let C3_FINAL_RETURN_OFFSET40 = WORD_RULE
 `!stackpointer:int64. word_add(word_sub stackpointer(word 40))(word 8)=word_sub stackpointer(word 32)`;;
let C3_FINAL_RETURN_OFFSET32 = WORD_RULE
 `!stackpointer:int64. word_add(word_sub stackpointer(word 32))(word 8)=word_sub stackpointer(word 24)`;;
let C3_FINAL_RETURN_OFFSET24 = WORD_RULE
 `!stackpointer:int64. word_add(word_sub stackpointer(word 24))(word 8)=word_sub stackpointer(word 16)`;;
let C3_FINAL_RETURN_OFFSET16 = WORD_RULE
 `!stackpointer:int64. word_add(word_sub stackpointer(word 16))(word 8)=word_sub stackpointer(word 8)`;;
let C3_FINAL_RETURN_OFFSET8 = WORD_RULE
 `!stackpointer:int64. word_add(word_sub stackpointer(word 8))(word 8)=stackpointer`;;
let C3_FINAL_RETURN_RSP_VALUE = prove
 (`!stackpointer:int64. val stackpointer+8<2 EXP 64
 ==> val(word_add stackpointer(word 8))=val stackpointer+8`,
 REPEAT STRIP_TAC THEN ASM_SIMP_TAC[VAL_WORD_ADD;VAL_WORD;DIMINDEX_64;MOD_LT] THEN
 CONV_TAC NUM_REDUCE_CONV THEN ASM_SIMP_TAC[MOD_LT]);;
print_endline "C3_FINAL_RETURN_CLOSED_OFFSETS_CHECKED_NOT_ACCEPTANCE";;
