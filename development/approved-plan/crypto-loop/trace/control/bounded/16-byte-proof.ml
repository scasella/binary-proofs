needs "/work/proofs/qualification/qualification.ml";;
needs "/work/development/approved-plan/crypto-loop/trace/control/bounded/restricted-proof.ml";;
needs "/work/development/approved-plan/byte-contract/proof_attempt2.ml";;
needs "/work/development/approved-plan/crypto-loop/trace/control/bounded/16-byte-statement.ml";;
let CRYPTO_BOUNDED_16_BYTES_RETURN =
 let th = SPECL
  [`pc:num`; `stackpointer:int64`; `returnaddress:int64`; `p:int64`; `q:int64`;
   `read (bytes64 p) m:int64`;
   `read (bytes64(word_add p (word 8))) m:int64`;
   `read (bytes64 q) m:int64`;
   `read (bytes64(word_add q (word 8))) m:int64`; `e:((64)address_uarch_event)list`]
  CRYPTO_BOUNDED_16_RETURN in
 let th = REWRITE_RULE[BP_WORDPAIR_BYTE16] th in
 let pre = List.nth (snd(strip_comb(rand(concl th)))) 1 in
 prove(crypto_bounded_16_bytes_statement,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC ENSURES_N_PRECONDITION_THM THEN EXISTS_TAC pre THEN
  CONJ_TAC THENL
   [SIMP_TAC[READ_COMPONENT_COMPOSE];
    MATCH_MP_TAC th THEN ASM_REWRITE_TAC[]]);;

print_endline "CRYPTO_BOUNDED_16_BYTES_COMPLETE";;
