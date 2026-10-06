(* Restricted feasibility slices. These do not establish full-domain O1,
   physical instruction correspondence, a permission invariant over all
   intermediate states, or the missing x87/MXCSR ABI obligation. *)
needs "/work/proofs/qualification/openssl_bytes.ml";;
let ASSURANCE_CRYPTO_EXEC = X86_MK_EXEC_RULE crypto_memcmp_mc;;

let ASSURANCE_CRYPTO_ZERO_REACHES_RET_READY = prove
 (`!pc sp ra p q e.
    ensures x86
      (\s. bytes_loaded s (word pc) crypto_memcmp_mc /\
           read RIP s = word pc /\ read RSP s = sp /\
           read (memory :> bytes64 sp) s = ra /\
           C_ARGUMENTS [p;q;word 0] s /\ read events s = e)
      (\s. read RIP s = word(pc+93) /\ read RSP s = sp /\
           read RAX s = word 0 /\
           bytes_loaded s (word pc) crypto_memcmp_mc /\
           read (memory :> bytes64 sp) s = ra /\
           x86_decode s (read RIP s) (2,RET) /\
           read events s = APPEND
             [EventJump(word(pc+16),word(pc+93))] e)
      (MAYCHANGE [RIP;RAX;R10] ,, MAYCHANGE SOME_FLAGS ,,
       MAYCHANGE [events])`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS; fst ASSURANCE_CRYPTO_EXEC] THEN
  X86_SIM_TAC ASSURANCE_CRYPTO_EXEC (1--5) THEN
  ASM_REWRITE_TAC[APPEND] THEN
  MATCH_MP_TAC(Option.get (snd ASSURANCE_CRYPTO_EXEC).(93)) THEN
  ASM_REWRITE_TAC[]);;

let ASSURANCE_CRYPTO_16_REACHES_RET_READY = prove
 (`!pc sp ra p q a0 a1 b0 b1 e.
    ensures x86
      (\s. bytes_loaded s (word pc) crypto_memcmp_mc /\
           read RIP s = word pc /\ read RSP s = sp /\
           read (memory :> bytes64 sp) s = ra /\
           C_ARGUMENTS [p;q;word 16] s /\
           read (memory :> bytes64 p) s = a0 /\
           read (memory :> bytes64 (word_add p (word 8))) s = a1 /\
           read (memory :> bytes64 q) s = b0 /\
           read (memory :> bytes64 (word_add q (word 8))) s = b1 /\
           read events s = e)
      (\s. read RIP s = word(pc+50) /\ read RSP s = sp /\
           read RAX s = (if a0 = b0 /\ a1 = b1 then word 0 else word 1) /\
           bytes_loaded s (word pc) crypto_memcmp_mc /\
           read (memory :> bytes64 sp) s = ra /\
           x86_decode s (read RIP s) (2,RET) /\
           read events s = APPEND
             [EventLoad(word_add q (word 8),8);EventLoad(q,8);
              EventLoad(word_add p (word 8),8);EventLoad(p,8);
              EventJump(word(pc+22),word(pc+22));
              EventJump(word(pc+16),word(pc+16))] e)
      (MAYCHANGE [RIP;RAX;RDX;R10;R11] ,, MAYCHANGE SOME_FLAGS ,,
       MAYCHANGE [events])`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS; fst ASSURANCE_CRYPTO_EXEC] THEN
  X86_SIM_TAC ASSURANCE_CRYPTO_EXEC (1--14) THEN
  ASM_REWRITE_TAC[APPEND; VAL_EQ_0; WORD_OR_EQ_0; WORD_XOR_EQ_0] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(Option.get (snd ASSURANCE_CRYPTO_EXEC).(50)) THEN
  ASM_REWRITE_TAC[]);;
