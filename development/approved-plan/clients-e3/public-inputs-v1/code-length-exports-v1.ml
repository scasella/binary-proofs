(* Public code-binding algebra only. No callee EXEC_RULE, instruction step,
   implementation proof or correctness assumption appears in this source.
   Checked in the same namespace as the opaque supplier's code definitions. *)
let bp_public_crypto_memcmp_code_length_statement =
 `LENGTH crypto_memcmp_mc = 95`;;
let bp_public_openssl_cleanse_code_length_statement =
 `LENGTH openssl_cleanse_mc = 97`;;
let BP_PUBLIC_CRYPTO_MEMCMP_CODE_LENGTH = prove
 (bp_public_crypto_memcmp_code_length_statement,
  REWRITE_TAC [crypto_memcmp_mc; LENGTH] THEN CONV_TAC NUM_REDUCE_CONV);;
let BP_PUBLIC_OPENSSL_CLEANSE_CODE_LENGTH = prove
 (bp_public_openssl_cleanse_code_length_statement,
  REWRITE_TAC [openssl_cleanse_mc; LENGTH] THEN CONV_TAC NUM_REDUCE_CONV);;
