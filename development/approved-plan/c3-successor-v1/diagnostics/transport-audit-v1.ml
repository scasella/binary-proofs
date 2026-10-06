(* Exact local development receipt only. This does not assert C3 acceptance. *)
let c3_transport_saved_bindings_expected_v1 = `!lib_file lib_rw lib_padding client_file client_rw client_padding
 stackpointer ra p q n m rp wp xp ordinary initial a entry returned.
 c3_pre lib_file lib_rw lib_padding client_file client_rw client_padding
   stackpointer ra p q n m rp wp xp ordinary(initial,a) /\
 c3_saved_prefix stackpointer p q n m initial entry /\
 bp_e2_cleanse_call_post 0x102417d0(word_sub stackpointer(word 48))
   (word 0x2300114c)p n(read memory entry)entry returned
 ==> read(memory :> bytes64(word_sub stackpointer(word 8)))returned=read R13 initial /\
     read(memory :> bytes64(word_sub stackpointer(word 16)))returned=read R12 initial /\
     read(memory :> bytes64(word_sub stackpointer(word 24)))returned=read RBP initial /\
     read(memory :> bytes64(word_sub stackpointer(word 32)))returned=read RBX initial /\
     read(memory :> bytes64 stackpointer)returned=ra /\
     c3_loaded_code returned /\ c3_got returned`;;
if not(aconv(concl C3_CLEANSE_SAVED_BINDINGS)c3_transport_saved_bindings_expected_v1)
 then failwith "C3_TRANSPORT_SAVED_BINDINGS_LITERAL_MISMATCH";;
if hyp C3_CLEANSE_SAVED_BINDINGS <> []
 then failwith "C3_TRANSPORT_SAVED_BINDINGS_OPEN_HYPOTHESES";;
if frees(concl C3_CLEANSE_SAVED_BINDINGS) <> []
 then failwith "C3_TRANSPORT_SAVED_BINDINGS_FREE_VARIABLES";;
if axioms() <> reuse_c3_foundation_axioms
 then failwith "C3_TRANSPORT_FOUNDATION_AXIOMS_CHANGED";;
print_endline "C3_TRANSPORT_SAVED_BINDINGS_EXACT_CLOSED_LITERAL_BEGIN";;
print_thm C3_CLEANSE_SAVED_BINDINGS;;
print_endline "C3_TRANSPORT_SAVED_BINDINGS_EXACT_CLOSED_LITERAL_END";;
print_endline "C3_TRANSPORT_SAVED_BINDINGS_LOCAL_DEVELOPMENT_AUDIT_PASS_NOT_C3_ACCEPTANCE";;
