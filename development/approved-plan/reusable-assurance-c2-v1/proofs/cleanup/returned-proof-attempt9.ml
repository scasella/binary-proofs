(* O4/O5 selected transport source; the unchanged three frame-algebra proofs
   are loaded from frame-algebra-proof-attempt1.ml first. Prior attempts preserved. *)
let C2_CLEANSE_RETURN_PROTECTION_TAC =
 (* Instantiations of the same permission-to-separation rule; exact C2 image. *)
 MAP_EVERY (fun (base,len,readonly) ->
  let ptr=parse_term ("word "^base^":int64") and width=parse_term len in
  let separation=list_mk_comb(`nonoverlapping:int64#num->int64#num->bool`,
   [mk_pair(`p:int64`,`n:num`);mk_pair(ptr,width)]) in
  SUBGOAL_THEN separation ASSUME_TAC THENL
   [MATCH_MP_TAC (SPECL [`wp:num->bool`;`ordinary:num->bool`;`p:int64`;`n:num`;ptr;width]
     C2_WRITABLE_READONLY_NONOVERLAPPING) THEN
    REWRITE_TAC[VAL_WORD;DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[readonly];ALL_TAC])
 ["0x22001120","59",C2_CALLER_READONLY_REGION;
  "0x22001030","6",C2_CRYPTO_PLT_READONLY_REGION;
  "0x22001040","6",C2_CLEANSE_PLT_READONLY_REGION;
  "0x10241840","95",C2_CRYPTO_READONLY_REGION;
  "0x102417d0","97",C2_CLEANSE_READONLY_REGION;
  "0x22003fd0","8",C2_CRYPTO_GOT_READONLY_REGION;
  "0x22003fd8","8",C2_CLEANSE_GOT_READONLY_REGION];;
let C2_CLEANSE_RETURN_SLOT_TAC k =
 let slot=if k=0 then `stackpointer:int64` else
  mk_binop `word_sub:int64->int64->int64` `stackpointer:int64`
   (mk_comb(`word:num->int64`,mk_small_numeral k)) in
 let separation=list_mk_comb(`nonoverlapping:int64#num->int64#num->bool`,
  [mk_pair(slot,`8`);mk_pair(`p:int64`,`n:num`)]) in
 SUBGOAL_THEN separation ASSUME_TAC THENL
  [MATCH_MP_TAC C2_REGION_NONOVERLAPPING THEN
   ASM_SIMP_TAC[VAL_WORD_SUB_CASES;VAL_WORD;DIMINDEX_64] THEN
   CONV_TAC NUM_REDUCE_CONV THEN
   REPEAT CONJ_TAC THENL
    [ASM_ARITH_TAC;
     UNDISCH_TAC `assurance_span_ok (\addr:num. wp addr /\ ordinary addr) (val(p:int64)) n` THEN
     REWRITE_TAC[assurance_span_ok] THEN CONV_TAC NUM_REDUCE_CONV THEN MESON_TAC[];
     REWRITE_TAC[assurance_region] THEN
     ASM_SIMP_TAC[VAL_WORD_SUB_CASES;VAL_WORD;DIMINDEX_64] THEN
     CONV_TAC NUM_REDUCE_CONV THEN REPEAT STRIP_TAC THEN
     (if k=0 then
       (fun gl ->
        let separated=REWRITE_RULE[assurance_region]
         (SPEC `addr:num` (ASSUME
          `!addr:num. ~(assurance_region (p:int64) n addr /\
                        assurance_region (stackpointer:int64) 8 addr)`)) in
        let contradiction=MATCH_MP
         (TAUT `~((A /\ B) /\ (C /\ D)) ==> A ==> B ==> C ==> D ==> F`) separated in
        let contradiction=MP (MP (MP (MP contradiction
         (ASSUME `val(p:int64)<=addr`))
         (ASSUME `addr<val(p:int64)+n`))
         (ASSUME `val(stackpointer:int64)<=addr`))
         (ASSUME `addr<val(stackpointer:int64)+8`) in
        ACCEPT_TAC contradiction gl)
      else
       SUBGOAL_THEN `c2_scratch stackpointer addr` ASSUME_TAC THENL
        [ASM_SIMP_TAC[c2_scratch;assurance_region;C2_STACK_SUB32_VALUE] THEN ASM_ARITH_TAC;
         (fun gl ->
          let separated=REWRITE_RULE[assurance_region]
           (SPEC `addr:num` (ASSUME
            `!addr:num. ~(assurance_region (p:int64) n addr /\
                          c2_scratch (stackpointer:int64) addr)`)) in
          let contradiction=MATCH_MP
           (TAUT `~((A /\ B) /\ C) ==> A ==> B ==> C ==> F`) separated in
          let contradiction=MP (MP (MP contradiction
           (ASSUME `val(p:int64)<=addr`))
           (ASSUME `addr<val(p:int64)+n`))
           (ASSUME `c2_scratch (stackpointer:int64) addr`) in
          ACCEPT_TAC contradiction gl)])];ALL_TAC] THEN
 MP_TAC (ISPECL [`p:int64`;slot;`n:num`;`entry:x86state`;`returned:x86state`]
  C2_CLEANSE_FRAME_SLOT) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC;;
let C2_CLEANSE_RETURNED_FACTS = prove
 (c2_cleanse_returned_facts_statement,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC
   `c2_cleanse_completed lib_file (stackpointer:int64) p q n m rp wp xp ordinary
     (initial:x86state) a (returned:x86state)` THEN
  REWRITE_TAC[c2_cleanse_completed] THEN
  DISCH_THEN(X_CHOOSE_THEN `entry:x86state` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC
   `c2_cleanse_ready lib_file (stackpointer:int64) p q n m rp wp xp ordinary
     (initial:x86state) a (entry:x86state)` THEN
  REWRITE_TAC[c2_cleanse_ready;c2_saved_prefix] THEN STRIP_TAC THEN
  UNDISCH_TAC
   `bp_e2_cleanse_call_post 0x102417d0 (word_sub (stackpointer:int64) (word 32))
      (word 0x22001153) p n (read memory (entry:x86state)) entry (returned:x86state)` THEN
  REWRITE_TAC[bp_e2_cleanse_call_post] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`p:int64`;`n:num`;`entry:x86state`;`returned:x86state`]
   C2_CLEANSE_FRAME_PRESERVED) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`stackpointer:int64`;`initial:x86state`;`entry:x86state`]
   C2_BEFORE_CLEANUP_UNTOUCHED) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC
   `c2_pre lib_file lib_rw lib_padding client_file client_rw client_padding
     (stackpointer:int64) ra p q n m rp wp xp ordinary (initial:x86state,a)` THEN
  REWRITE_TAC[c2_pre] THEN STRIP_TAC THEN
  SUBGOAL_THEN `read RSP (returned:x86state)=word_sub stackpointer (word 24)`
   ASSUME_TAC THENL
   [MATCH_MP_TAC C2_CRYPTO_RETURN_STACK THEN ASM_REWRITE_TAC[];ALL_TAC] THEN
  MAP_EVERY C2_CLEANSE_RETURN_SLOT_TAC [8;16;24;0] THEN
  C2_CLEANSE_RETURN_PROTECTION_TAC THEN
  SUBGOAL_THEN `c2_loaded_code (returned:x86state)` ASSUME_TAC THENL
   [UNDISCH_TAC `c2_loaded_code (entry:x86state)` THEN
    REWRITE_TAC[c2_loaded_code] THEN STRIP_TAC THEN
    REWRITE_TAC[c2_loaded_code] THEN REPEAT CONJ_TAC THEN
    (fun gl ->
     let _,args=strip_comb(snd gl) in
     if length args<>3 then failwith "C2 cleanup code target is not bytes_loaded";
     (MATCH_MP_TAC (ISPECL [`p:int64`;el 1 args;`n:num`;el 2 args;
       `entry:x86state`;`returned:x86state`] C2_CLEANSE_FRAME_CODE) THEN
      ASM_REWRITE_TAC[c2_caller_mc;c2_crypto_plt_prefix;c2_cleanse_plt_prefix;
       crypto_memcmp_mc;openssl_cleanse_mc;LENGTH;NONOVERLAPPING_SYM] THEN
      CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[]) gl);ALL_TAC] THEN
  SUBGOAL_THEN `c2_got (returned:x86state)` ASSUME_TAC THENL
   [UNDISCH_TAC `c2_got (entry:x86state)` THEN REWRITE_TAC[c2_got] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`p:int64`;`word 0x22003fd0:int64`;`n:num`;`entry:x86state`;`returned:x86state`]
      C2_CLEANSE_FRAME_SLOT) THEN
    MP_TAC(ISPECL [`p:int64`;`word 0x22003fd8:int64`;`n:num`;`entry:x86state`;`returned:x86state`]
      C2_CLEANSE_FRAME_SLOT) THEN
    ASM_REWRITE_TAC[NONOVERLAPPING_SYM] THEN REWRITE_TAC[c2_got] THEN MESON_TAC[];ALL_TAC] THEN
  SUBGOAL_THEN `c2_accumulated_frame stackpointer p q n m (initial:x86state) returned`
   ASSUME_TAC THENL
   [GEN_REWRITE_TAC (RATOR_CONV o RATOR_CONV)
      [GSYM(ISPECL [`stackpointer:int64`;`p:int64`;`q:int64`;`n:num`;`m:int64->byte`]
       C2_ACCUMULATED_FRAME_IDEMPOTENT)] THEN
    REWRITE_TAC[seq] THEN EXISTS_TAC `entry:x86state` THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`stackpointer:int64`;`p:int64`;`q:int64`;`n:num`;`m:int64->byte`]
       C2_BEFORE_CLEANUP_ACCUMULATED_INCLUDED) THEN
      REWRITE_TAC[subsumed] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`stackpointer:int64`;`p:int64`;`q:int64`;`n:num`;`m:int64->byte`]
       C2_CLEANSE_FRAME_ACCUMULATED) THEN
      ASM_REWRITE_TAC[subsumed] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
  (ASM_MESON_TAC[] ORELSE
   (fun gl -> print_endline "C2_CLEANSE_RETURNED_FACTS_RESIDUAL";
    print_goal gl;FAIL_TAC "C2 cleanup public return transport residual" gl)));;
