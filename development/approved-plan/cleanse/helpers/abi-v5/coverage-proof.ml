(* Conversion from unchanged production bytes through the actual pinned decoder. *)
let ASSURANCE_CLEANSE_EXEC_V5 = X86_MK_EXEC_RULE openssl_cleanse_mc;;
let ABI_CLEANSE_REGISTERED_DECODE_QUALIFIED = prove
 (abi_cleanse_registered_decode_qualified_statement,
  REPEAT GEN_TAC THEN REWRITE_TAC[MEM] THEN STRIP_TAC THENL
   (map (fun offset ->
     let decode_ths = snd ASSURANCE_CLEANSE_EXEC_V5 in
     let dt = Option.get decode_ths.(offset) in
     let _,conseq = dest_imp(snd(strip_forall(concl dt))) in
     let len,inst = dest_pair(rand conseq) in
     MATCH_MP_TAC(ISPECL [len; inst; `s:x86state`]
       ABI_CLEANSE_DECODED_SCALAR_UNIQUE) THEN
     CONJ_TAC THENL
      [ASM_REWRITE_TAC[ADD_CLAUSES] THEN
       MATCH_MP_TAC(REWRITE_RULE[ADD_CLAUSES] dt) THEN ASM_REWRITE_TAC[];
       MATCH_MP_TAC(ISPECL [mk_numeral(num offset); len; inst]
         ABI_CLEANSE_REGISTERED_SITE_IS_SCALAR) THEN
       REWRITE_TAC[abi_cleanse_site]])
    [0;4;7;11;13;17;19;21;25;29;31;48;55;57;59;63;67;69;72;76;83;87;89;93;95]));;
