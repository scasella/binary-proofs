(* Reconstruct the production decoder/executor rule from the exact source bytes.
   This is a conversion result, not a new semantic assumption. *)
needs "/work/proofs/qualification/openssl_bytes.ml";;
let CRYPTO_MEMCMP_EXEC = X86_MK_EXEC_RULE crypto_memcmp_mc;;
