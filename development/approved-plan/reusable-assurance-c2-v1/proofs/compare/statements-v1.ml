(* Named O2/O3 obligations frozen before the corresponding proof recipe. *)
let c2_crypto_segment_application_statement =
 `!lib_file stackpointer p q:int64 n m rp wp xp ordinary initial a entry:x86state.
    c2_crypto_ready lib_file stackpointer p q n m rp wp xp ordinary initial a entry
    ==> assurance_checked_run (bp_assurance_call_steps n)
      (bp_assurance_call_post 0x10241840 (word_sub stackpointer (word 32))
        (word 0x22001132) p q n (read events entry) (read memory entry) entry)
      (c2_segment_policy stackpointer p q n m rp wp xp ordinary) entry`;;
let c2_crypto_completed_run_statement =
 `!lib_file stackpointer p q:int64 n m rp wp xp ordinary initial a entry:x86state.
    c2_crypto_ready lib_file stackpointer p q n m rp wp xp ordinary initial a entry
    ==> assurance_checked_run (bp_assurance_call_steps n)
      (c2_crypto_completed lib_file stackpointer p q n m rp wp xp ordinary initial a)
      (c2_segment_policy stackpointer p q n m rp wp xp ordinary) entry`;;
let c2_compare_memory_code_got_transport_statement =
 `!s t:x86state. read memory t=read memory s
    ==> (c2_loaded_code t <=> c2_loaded_code s) /\ (c2_got t <=> c2_got s)`;;
let c2_compare_memory_slot_transport_statement =
 `!s t:x86state pointer:int64. read memory t=read memory s
    ==> read (memory :> bytes64 pointer) t=read (memory :> bytes64 pointer) s`;;
let c2_crypto_result_transport_statement =
 `!lib_file stackpointer p q:int64 n m rp wp xp ordinary initial a entry returned:x86state.
    c2_crypto_ready lib_file stackpointer p q n m rp wp xp ordinary initial a entry /\
    bp_assurance_call_post 0x10241840 (word_sub stackpointer (word 32))
      (word 0x22001132) p q n (read events entry) (read memory entry) entry returned
    ==> read RAX returned=(if c2_equal m p q n then word 0 else word 1)`;;
let c2_crypto_return_stack_statement =
 `!stackpointer:int64 returned:x86state. 32<=val stackpointer /\
    val(read RSP returned)=val(word_sub stackpointer (word 32))+8
    ==> read RSP returned=word_sub stackpointer (word 24)`;;
let c2_compare_initial_facts_statement =
 `!lib_file stackpointer p q:int64 n m rp wp xp ordinary initial a returned:x86state.
    32<=val stackpointer /\
    c2_crypto_completed lib_file stackpointer p q n m rp wp xp ordinary initial a returned
    ==> read RIP returned=word 0x22001132 /\
        read RSP returned=word_sub stackpointer (word 24) /\
        read RAX returned=(if c2_equal m p q n then word 0 else word 1) /\
        read RBX returned=p /\ read RBP returned=word n /\ read R12 returned=word 0 /\
        read (memory :> bytes64 (word_sub stackpointer (word 8))) returned=read R12 initial /\
        read (memory :> bytes64 (word_sub stackpointer (word 16))) returned=read RBP initial /\
        read (memory :> bytes64 (word_sub stackpointer (word 24))) returned=read RBX initial /\
        (!addr. ~c2_scratch stackpointer (val addr) ==> read memory returned addr=m addr) /\
        (!i. i<n ==> read memory returned (word_add p (word i))=m(word_add p (word i))) /\
        (!i. i<n ==> read memory returned (word_add q (word i))=m(word_add q (word i))) /\
        c2_loaded_code returned /\ c2_got returned`;;
