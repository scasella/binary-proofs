(* Conservative automation adapter. Every array entry is a derived kernel
   rewrite of the same decode theorem. No HOL definition/model is modified. *)
let R1_NORMALIZE_EXEC_RULE (length_th,decode_array) =
 let normalize th=REWRITE_RULE
   ([r1_near_operand64;r1_near_register] @ GPR_thms) th in
 length_th, Array.map (function None->None | Some th->Some(normalize th)) decode_array;;
let R1_CRYPTO_PLT_PREFIX_RAW_EXEC = X86_MK_EXEC_RULE r1_crypto_plt_prefix;;
let R1_CLEANSE_PLT_PREFIX_RAW_EXEC = X86_MK_EXEC_RULE r1_cleanse_plt_prefix;;
let R1_MEMCMP_PLT_PREFIX_RAW_EXEC = X86_MK_EXEC_RULE r1_memcmp_plt_prefix;;
let R1_CRYPTO_PLT_PREFIX_EXEC = R1_NORMALIZE_EXEC_RULE R1_CRYPTO_PLT_PREFIX_RAW_EXEC;;
let R1_CLEANSE_PLT_PREFIX_EXEC = R1_NORMALIZE_EXEC_RULE R1_CLEANSE_PLT_PREFIX_RAW_EXEC;;
let R1_MEMCMP_PLT_PREFIX_EXEC = R1_NORMALIZE_EXEC_RULE R1_MEMCMP_PLT_PREFIX_RAW_EXEC;;
let R1_EXEC_DECODE_AT_ZERO (_,array) =
 match array.(0) with Some th->th | None->failwith "missing entry decode";;
let R1_CRYPTO_PLT_EXECUTION_DECODE = prove
 (r1_crypto_plt_decode_statement,
  MATCH_ACCEPT_TAC(R1_EXEC_DECODE_AT_ZERO R1_CRYPTO_PLT_PREFIX_EXEC));;
let R1_CLEANSE_PLT_EXECUTION_DECODE = prove
 (r1_cleanse_plt_decode_statement,
  MATCH_ACCEPT_TAC(R1_EXEC_DECODE_AT_ZERO R1_CLEANSE_PLT_PREFIX_EXEC));;
let R1_MEMCMP_PLT_EXECUTION_DECODE = prove
 (r1_memcmp_plt_decode_statement,
  MATCH_ACCEPT_TAC(R1_EXEC_DECODE_AT_ZERO R1_MEMCMP_PLT_PREFIX_EXEC));;
