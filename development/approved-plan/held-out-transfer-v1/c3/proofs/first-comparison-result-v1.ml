(* Concrete C3 first comparison result, using only the public postcondition
   and the initial logical snapshot carried by c3_crypto_ready.
   Named obligation: R13 stores the first comparison against initial inputs.
   No supplier instruction semantics, new generic rule, or new public premise. *)
let C3_FIRST_COMPARISON_RESULT = prove
 (`!lib_file stackpointer p q n m rp wp xp ordinary initial a entry returned.
 c3_crypto_ready lib_file stackpointer p q n m rp wp xp ordinary initial a entry /\
 bp_assurance_call_post 0x10241840 (word_sub stackpointer(word 48)) (word 0x23001138) p q n
 (read events entry) (read memory entry) entry returned
 ==> read RAX returned = (if c3_equal m p q n then word 0 else word 1)`,
 REPEAT GEN_TAC THEN STRIP_TAC THEN
 SUBGOAL_THEN `c3_equal (read memory(entry:x86state)) p q n <=> c3_equal m p q n` ASSUME_TAC THENL
 [MATCH_MP_TAC C3_INITIAL_LOGICAL_SNAPSHOT_EQ THEN
  UNDISCH_TAC `c3_crypto_ready lib_file stackpointer p q n m rp wp xp ordinary initial a entry` THEN
  REWRITE_TAC[c3_crypto_ready;c3_saved_prefix] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[];
  UNDISCH_TAC `bp_assurance_call_post 0x10241840 (word_sub(stackpointer:int64)(word 48)) (word 0x23001138) p q n
   (read events(entry:x86state)) (read memory entry) entry returned` THEN
  REWRITE_TAC[bp_assurance_call_post;GSYM c3_equal] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[]]);;
print_endline "C3_FIRST_COMPARISON_RESULT_V1_DEVELOPMENT_CHECKED";;
