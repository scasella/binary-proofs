let c1_tail_return_rsp_value_statement =
 `!stackpointer:int64. val stackpointer+8<2 EXP 64
    ==> val(word_add stackpointer(word 8))=val stackpointer+8`;;
