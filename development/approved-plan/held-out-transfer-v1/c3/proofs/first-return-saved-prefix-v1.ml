(* Concrete C3 saved-prefix transport through the first public comparison.
   Named obligation: derive the actual cleanup entry from original caller
   state, initial input snapshot, saved stack slots, and public return/frame.
   This is a caller predicate implication, not a reusable memory law. *)
let C3_FIRST_RETURN_SAVED_PREFIX = prove
 (`!lib_file stackpointer p q n m rp wp xp ordinary initial a entry returned.
 c3_crypto_ready lib_file stackpointer p q n m rp wp xp ordinary initial a entry /\
 bp_assurance_call_post 0x10241840 (word_sub stackpointer(word 48)) (word 0x23001138) p q n
 (read events entry) (read memory entry) entry returned
 ==> c3_saved_prefix stackpointer p q n m initial returned`,
 REPEAT GEN_TAC THEN STRIP_TAC THEN
 MP_TAC(ISPECL[`lib_file:num->byte`;`stackpointer:int64`;`p:int64`;`q:int64`;
   `n:num`;`m:int64->byte`;`rp:num->bool`;`wp:num->bool`;`xp:num->bool`;
   `ordinary:num->bool`;`initial:x86state`;`a:abi_omitted_state`;
   `entry:x86state`;`returned:x86state`]C3_FIRST_RETURN_WORKING_STATE) THEN
 ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
 UNDISCH_TAC `c3_crypto_ready lib_file stackpointer p q n m rp wp xp ordinary initial a entry` THEN
 REWRITE_TAC[c3_crypto_ready;c3_saved_prefix] THEN STRIP_TAC THEN
 UNDISCH_TAC `bp_assurance_call_post 0x10241840 (word_sub(stackpointer:int64)(word 48)) (word 0x23001138) p q n
   (read events(entry:x86state)) (read memory entry) entry returned` THEN
 REWRITE_TAC[bp_assurance_call_post] THEN STRIP_TAC THEN
 RULE_ASSUM_TAC(REWRITE_RULE[c3_loaded_code;c3_got;bytes_loaded;READ_COMPONENT_COMPOSE]) THEN
 REWRITE_TAC[c3_saved_prefix;c3_loaded_code;c3_got;bytes_loaded;READ_COMPONENT_COMPOSE] THEN
 ASM_REWRITE_TAC[]);;
print_endline "C3_FIRST_RETURN_SAVED_PREFIX_V1_DEVELOPMENT_CHECKED";;
