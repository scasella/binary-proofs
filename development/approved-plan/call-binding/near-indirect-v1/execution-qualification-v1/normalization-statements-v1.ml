(* Extra generic normalizer targets frozen before proof search. *)
let r1_absolute_operation_eta_statement =
 `!target. x86_JMP_ABSOLUTE target =
   (\s. (events := CONS(EventJump(read RIP s,target))(read events s) ,,
         RIP := target) s)`;;
let r1_word_val_address_statement =
 `!a b. (word(val(word a:int64)+b):int64)=word(a+b)`;;
