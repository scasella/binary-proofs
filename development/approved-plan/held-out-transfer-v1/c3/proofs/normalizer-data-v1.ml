(* Allowed per-caller normalization data: closed one-pointer concrete48-byte site identities. No new normalization algorithm. *)
let C3_STACK_OFFSET_8 = WORD_RULE `!stackpointer:int64. word_sub stackpointer(word 8)=word_add(word_sub stackpointer(word 48))(word 40)`;;
let C3_STACK_OFFSET_16 = WORD_RULE `!stackpointer:int64. word_sub stackpointer(word 16)=word_add(word_sub stackpointer(word 48))(word 32)`;;
let C3_STACK_OFFSET_24 = WORD_RULE `!stackpointer:int64. word_sub stackpointer(word 24)=word_add(word_sub stackpointer(word 48))(word 24)`;;
let C3_STACK_OFFSET_32 = WORD_RULE `!stackpointer:int64. word_sub stackpointer(word 32)=word_add(word_sub stackpointer(word 48))(word 16)`;;
let C3_STACK_OFFSET_40 = WORD_RULE `!stackpointer:int64. word_sub stackpointer(word 40)=word_add(word_sub stackpointer(word 48))(word 8)`;;
