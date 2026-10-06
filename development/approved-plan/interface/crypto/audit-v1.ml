(* Expected terms copied from the pre-search V1 contract, not proof outputs. *)
let crypto_public_audit path =
 let ds = [
  "bp_e2_crypto_public_pre",parse_term "bp_e2_crypto_public_pre file_bytes initial_rw padding stackpointer ra p q n\n                         m rp xp ordinary (s:x86state,a:abi_omitted_state) <=>\n    fb_file_code file_bytes /\\ fb_full_image file_bytes initial_rw padding m /\\\n    bp_e2_crypto_pre 0x10241840 stackpointer ra p q n m rp xp ordinary s /\\\n    (!addr. lw_image_domain addr\n       ==> rp addr /\\ ordinary addr /\\ (xp addr <=> lw_execute addr)) /\\\n    assurance_canonical48 (val(read ABI_FS_BASE a))",bp_e2_crypto_public_pre;
  "bp_e2_crypto_public_post",parse_term "bp_e2_crypto_public_post file_bytes initial_rw padding stackpointer ra p q n\n                          e m s a (t:x86state#abi_omitted_state) <=>\n    bp_assurance_call_post 0x10241840 stackpointer ra p q n e m s (FST t) /\\\n    fb_full_image file_bytes initial_rw padding (read memory (FST t)) /\\\n    SND t = a /\\ abi_required_controls_preserved a (SND t)",bp_e2_crypto_public_post;
 ] in
 List.iter(fun(name,expected,th)->
  if hyp th<>[] || not(aconv (snd(strip_forall(concl th))) expected)
  then failwith(name^": expanded definition mismatch")) ds;
 let targets = [
  "BP_E2_CRYPTO_PUBLIC_POLICY",parse_term "!file_bytes initial_rw padding stackpointer ra p q n m rp xp ordinary s a.\n    bp_e2_crypto_public_pre file_bytes initial_rw padding stackpointer ra p q n\n      m rp xp ordinary (s,a)\n    ==> assurance_checked_run (bp_assurance_call_steps n)\n      (bp_assurance_call_post 0x10241840 stackpointer ra p q n\n         (read events s) m s)\n      (assurance_zero_scalar_step\n        (bp_e2_crypto_allowed_read rp ordinary p q n stackpointer)\n        bp_e2_crypto_allowed_write\n        (bp_e2_crypto_allowed_fetch xp ordinary 0x10241840)) s",BP_E2_CRYPTO_PUBLIC_POLICY;
  "BP_E2_CRYPTO_PUBLIC_INTERFACE",parse_term "!file_bytes initial_rw padding stackpointer ra p q n m rp xp ordinary s a.\n    bp_e2_crypto_public_pre file_bytes initial_rw padding stackpointer ra p q n\n      m rp xp ordinary (s,a)\n    ==> eventually_n abi_scalar_extended_step (bp_assurance_call_steps n)\n      (bp_e2_crypto_public_post file_bytes initial_rw padding\n        stackpointer ra p q n (read events s) m s a) (s,a)",BP_E2_CRYPTO_PUBLIC_INTERFACE;
  "BP_E2_CRYPTO_PUBLIC_WITNESS_BRIDGE",parse_term "!file_bytes initial_rw padding image p q n different.\n    fb_pre file_bytes initial_rw padding image p q n different\n    ==> bp_e2_crypto_public_pre file_bytes initial_rw padding\n      (word 0x300008) (word 0x400000) p q n\n      (lw_memory image p q n different) (fb_read p q n) lw_execute\n      (fb_ordinary p q n) (fb_machine image p q n different)",BP_E2_CRYPTO_PUBLIC_WITNESS_BRIDGE;
 ] in
 let rows=List.map(fun(name,expected,th)->
  if hyp th<>[] then failwith(name^": theorem hypotheses");
  if not(aconv(concl th) expected) then failwith(name^": exact expected conclusion mismatch");
  if axioms()<>assurance_initial_axioms then failwith(name^": added foundation axioms");
  "{\"name\":"^Printf.sprintf "%S" name^","^
  "\"statement\":"^Printf.sprintf "%S"(string_of_term(concl th))^","^
  "\"hypothesis_count\":0,\"new_axioms\":0,\"conclusion_matches_expected\":true}") targets in
 let oc=open_out path in
 output_string oc ("{\"expanded_definition_count\":2,\"theorems\":["^String.concat "," rows^"]}\n");
 close_out oc;;
