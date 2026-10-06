(* Immutable literal targets frozen before proof source. *)
let c1_completion_memory_slot_transport_statement =
 `!s t:x86state stackpointer:int64.
    read memory t=read memory s
    ==> read (memory :> bytes64 stackpointer) t=
        read (memory :> bytes64 stackpointer) s`;;
let c1_completion_memory_code_got_transport_statement =
 `!s t:x86state. read memory t=read memory s
    ==> (c1_loaded_code t <=> c1_loaded_code s) /\ (c1_got t <=> c1_got s)`;;
let c1_prefix_frame_included_statement =
 `!stackpointer:int64. c1_prefix_frame stackpointer subsumed c1_frame stackpointer`;;
let c1_crypto_public_frame_included_statement =
 `!stackpointer:int64. c1_crypto_public_frame subsumed c1_frame stackpointer`;;
let c1_frame_idempotent_statement =
 `!stackpointer:int64. c1_frame stackpointer ,, c1_frame stackpointer =
    c1_frame stackpointer`;;
let c1_crypto_frame_compose_statement =
 `!stackpointer:int64 initial entry returned:x86state.
    c1_prefix_frame stackpointer initial entry /\ c1_crypto_public_frame entry returned
    ==> c1_frame stackpointer initial returned`;;
let c1_frame_saved_preserved_statement =
 `!stackpointer:int64 s t:x86state. c1_frame stackpointer s t
    ==> read RBX t=read RBX s /\ read RBP t=read RBP s /\
        read R12 t=read R12 s /\ read R13 t=read R13 s /\
        read R14 t=read R14 s /\ read R15 t=read R15 s /\
        read DF t=read DF s /\ bit 18(read rflags t)=bit 18(read rflags s)`;;
let c1_crypto_result_transport_statement =
 `!stackpointer p q:int64 n m initial entry returned:x86state
    lib_file rp xp ordinary a.
    c1_crypto_ready lib_file stackpointer p q n m rp xp ordinary initial a entry /\
    bp_assurance_call_post 0x10241840 (word_sub stackpointer (word 16))
      (word 0x21001119) p q n (read events entry) (read memory entry) entry returned
    ==> read RAX returned=
        (if (!i. i<n ==> m(word_add p (word i))=m(word_add q (word i)))
         then word 0 else word 1)`;;
let c1_crypto_result_01_statement =
 `!b result:int64. result=(if b then word 0 else word 1)
    ==> (result=word 0 \/ result=word 1) /\ (result=word 0 <=> b)`;;
let c1_crypto_return_stack_statement =
 `!stackpointer:int64 returned:x86state.
    16<=val stackpointer /\
    val(read RSP returned)=val(word_sub stackpointer (word 16))+8
    ==> read RSP returned=word_sub stackpointer (word 8)`;;
let c1_incoming_read_span_statement =
 `!rp ordinary stackpointer p q:int64 n.
    assurance_span_ok (\addr. rp addr /\ ordinary addr) (val stackpointer) 8
    ==> assurance_span_ok (c1_allowed_read rp ordinary stackpointer p q n)
          (val stackpointer) 8`;;
let c1_crypto_completed_facts_statement =
 `!lib_file stackpointer p q:int64 n m rp xp ordinary initial a returned:x86state.
    c1_crypto_completed lib_file stackpointer p q n m rp xp ordinary initial a returned
    ==> read RIP returned=word 0x21001119 /\
        val(read RSP returned)=val(word_sub stackpointer (word 16))+8 /\
        read RAX returned=
          (if (!i. i<n ==> m(word_add p (word i))=m(word_add q (word i)))
           then word 0 else word 1) /\
        (!addr. ~c1_call_slot stackpointer (val addr)
                ==> read memory returned addr=m addr) /\
        (!i. i<n ==> read memory returned (word_add p (word i))=
                     m(word_add p (word i))) /\
        (!i. i<n ==> read memory returned (word_add q (word i))=
                     m(word_add q (word i))) /\
        read (memory :> bytes64 stackpointer) returned=
          read (memory :> bytes64 stackpointer) initial /\
        c1_loaded_code returned /\ c1_got returned /\
        c1_frame stackpointer initial returned /\
        read RBX returned=read RBX initial /\ read RBP returned=read RBP initial /\
        read R12 returned=read R12 initial /\ read R13 returned=read R13 initial /\
        read R14 returned=read R14 initial /\ read R15 returned=read R15 initial /\
        read DF returned=read DF initial /\
        bit 18(read rflags returned)=bit 18(read rflags initial)`;;
let c1_crypto_completed_run_statement =
 `!lib_file stackpointer p q:int64 n m rp wp xp ordinary initial a entry:x86state.
    c1_crypto_ready lib_file stackpointer p q n m rp xp ordinary initial a entry
    ==> assurance_checked_run (bp_assurance_call_steps n)
      (c1_crypto_completed lib_file stackpointer p q n m rp xp ordinary initial a)
      (c1_segment_policy stackpointer p q n rp wp xp ordinary) entry`;;
let c1_crypto_completed_access_statement =
 `!lib_file lib_rw lib_padding client_file client_rw client_padding
    stackpointer ra p q:int64 n m rp wp xp ordinary initial a returned:x86state.
    c1_pre lib_file lib_rw lib_padding client_file client_rw client_padding
      stackpointer ra p q n m rp wp xp ordinary (initial,a) /\
    c1_crypto_completed lib_file stackpointer p q n m rp xp ordinary initial a returned
    ==> read RIP returned=word 0x21001119 /\
        read RSP returned=word_sub stackpointer (word 8) /\
        (read RAX returned=word 0 \/ read RAX returned=word 1) /\
        (read RAX returned=word 0 <=>
          (!i. i<n ==> m(word_add p (word i))=m(word_add q (word i)))) /\
        bytes_loaded returned (word 0x21001110) c1_crypto_caller_mc /\
        read (memory :> bytes64 stackpointer) returned=ra /\
        16<=val stackpointer /\ val stackpointer+8<2 EXP 64 /\
        assurance_span_ok (c1_allowed_read rp ordinary stackpointer p q n)
          (val stackpointer) 8 /\
        assurance_span_ok (c1_allowed_fetch xp ordinary) 0x21001110 22 /\
        (!addr. ~c1_call_slot stackpointer (val addr)
                ==> read memory returned addr=m addr) /\
        (!i. i<n ==> read memory returned (word_add p (word i))=
                     m(word_add p (word i))) /\
        (!i. i<n ==> read memory returned (word_add q (word i))=
                     m(word_add q (word i))) /\
        c1_loaded_code returned /\ c1_got returned /\
        c1_frame stackpointer initial returned /\
        read RBX returned=read RBX initial /\ read RBP returned=read RBP initial /\
        read R12 returned=read R12 initial /\ read R13 returned=read R13 initial /\
        read R14 returned=read R14 initial /\ read R15 returned=read R15 initial /\
        read DF returned=F /\ ~bit 18(read rflags returned)`;;
