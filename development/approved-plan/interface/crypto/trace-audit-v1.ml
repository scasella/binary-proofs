let crypto_public_trace_audit path =
 let th=BP_E2_CRYPTO_PUBLIC_TRACE in
 let expected=parse_term "!file_bytes initial_rw1 padding1 initial_rw2 padding2 stackpointer ra p q n\n       m1 m2 rp xp ordinary s1 a1 s2 a2 trace1 trace2 t1 t2.\n    bp_e2_crypto_public_pre file_bytes initial_rw1 padding1 stackpointer ra\n      p q n m1 rp xp ordinary (s1,a1) /\\\n    bp_e2_crypto_public_pre file_bytes initial_rw2 padding2 stackpointer ra\n      p q n m2 rp xp ordinary (s2,a2) /\\\n    crypto_first_ret_execution trace1 s1 t1 /\\\n    crypto_first_ret_execution trace2 s2 t2\n    ==> trace1=crypto_public_call 0x10241840 p q n stackpointer ra /\\\n        trace2=crypto_public_call 0x10241840 p q n stackpointer ra /\\\n        trace1=trace2 /\\\n        read RIP t1=ra /\\ read RSP t1=word_add stackpointer (word 8) /\\\n        read RIP t2=ra /\\ read RSP t2=word_add stackpointer (word 8)" in
 if hyp th<>[] || not(aconv(concl th) expected) || axioms()<>assurance_initial_axioms
 then failwith "public trace live-object audit failed";
 let oc=open_out path in
 output_string oc ("{\"expanded_definition_count\":0,\"theorems\":[{\"name\":\"BP_E2_CRYPTO_PUBLIC_TRACE\",\"hypothesis_count\":0,\"new_axioms\":0,\"conclusion_matches_expected\":true,\"statement\":"^Printf.sprintf "%S"(string_of_term(concl th))^"}]}\n");
 close_out oc;;
