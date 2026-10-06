(* Exact successful generic prefix of retained proof-attempt1.ml. *)
let BP_REUSE_DECODED_STEP = prove
 (bp_reuse_decoded_step_statement,
  REPEAT STRIP_TAC THEN REWRITE_TAC[FUN_EQ_THM; x86] THEN
  ASM_MESON_TAC[x86_decode_unique; PAIR_EQ]);;
