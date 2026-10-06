print_thm x86_JMP_ABSOLUTE;;
List.iter (fun th->if can(find_term(fun t->is_const t && fst(dest_const t)="x86_JMP_ABSOLUTE"))(concl th) then print_thm th) X86_OPERATION_CLAUSES;;
print_endline "R1_ABSOLUTE_OPERATION_DEBUG1";;
let R1_CRYPTO_STEP_CONV_DEBUG =
 X86_CONV (snd R1_CRYPTO_PLT_PREFIX_EXEC)
 [ASSUME `bytes_loaded s0 (word pc) r1_crypto_plt_prefix`;
  ASSUME `read RIP s0=word pc`]
 `x86 s0 s1`;;
print_thm R1_CRYPTO_STEP_CONV_DEBUG;;
let R1_CRYPTO_STEP_CONV_DEBUG2=REWRITE_RULE[x86_JMP_ABSOLUTE]
 R1_CRYPTO_STEP_CONV_DEBUG;;
print_thm R1_CRYPTO_STEP_CONV_DEBUG2;;
print_endline "R1_ABSOLUTE_OPERATION_DEBUG1_RETURNED";;
