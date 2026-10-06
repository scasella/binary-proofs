(* Reuses the original decoder/executor conversion and state-update machinery.
   Each original successor is retained before its policy obligation is proved. *)
let CLEANSE_ACCESS_LOCAL_STEP_TAC decode_ths offset original_step update (asl,w) =
  let _,goal_args=strip_comb w in
  let fetchperm=List.nth goal_args 3 in
  let dt=Option.get decode_ths.(offset) in
  let _,conseq=dest_imp(snd(strip_forall(concl dt))) in
  let len,inst=dest_pair(rand conseq) in
  let _,args=strip_comb(concl original_step) in let source=hd args in
  let d0=if offset=19 || offset=57 then `[EventStore(read RDI source,1)]`
    else if offset=69 then `[EventStore(read RDI source,8)]`
    else if offset=11 then
      `[EventJump(word(pc+13),if ~read CF source then word(pc+48) else word(pc+13))]`
    else if offset=17 then
      `[EventJump(word(pc+19),if read ZF source then word(pc+31) else word(pc+19))]`
    else if offset=29 then
      `[EventJump(word(pc+31),if ~read ZF source then word(pc+19) else word(pc+31))]`
    else if offset=55 then
      `[EventJump(word(pc+57),if read ZF source then word(pc+69) else word(pc+57))]`
    else if offset=67 then `[EventJump(word(pc+69),word(pc+48))]`
    else if offset=87 then
      `[EventJump(word(pc+89),if ~read ZF source then word(pc+69) else word(pc+89))]`
    else if offset=93 then
      `[EventJump(word(pc+95),if ~read ZF source then word(pc+19) else word(pc+95))]`
    else if offset=31 then
      `[EventJump(word(pc+33),ra);EventLoad(stackpointer:int64,8)]`
    else if offset=95 then
      `[EventJump(word(pc+97),ra);EventLoad(stackpointer:int64,8)]`
    else `[]:uarch_event list` in
  let d=vsubst [source,`source:x86state`] d0 in
  (REWRITE_TAC[cleanse_access_covered_step] THEN CONJ_TAC THENL
   [REWRITE_TAC[assurance_zero_step] THEN CONJ_TAC THENL
     [REWRITE_TAC[assurance_step_policy] THEN MAP_EVERY EXISTS_TAC [len;inst;d] THEN
      REPEAT CONJ_TAC THENL
       [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(REWRITE_RULE[ADD_CLAUSES] dt) THEN ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[CLEANSE_ACCESS_CODE_OFFSET_VALUE;
          CLEANSE_ACCESS_CODE_BASE_VALUE;ARITH_RULE(mk_binary "<" (mk_numeral(num offset),`97`))] THEN
        MP_TAC(ISPECL [fetchperm;`pc:num`;`97`;mk_numeral(num offset);len]
          ASSURANCE_SPAN_SUBRANGE) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ARITH_TAC;REWRITE_TAC[ADD_CLAUSES]];
        SUBST1_TAC(SYM update) THEN ASM_REWRITE_TAC[APPEND] THEN
        CONV_TAC(TOP_DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV) THEN
        ASM_REWRITE_TAC[APPEND;WORD_ADD_0;GSYM WORD_ADD_ASSOC;GSYM WORD_ADD];
        (fun g->print_endline("CLEANSE_ACCESS_EVENT "^string_of_int offset);ALL_TAC g) THEN
        REWRITE_TAC[ALL;assurance_event_policy] THEN ASM_REWRITE_TAC[]];
      (fun g->print_endline("CLEANSE_ACCESS_RETCOUNT "^string_of_int offset);ALL_TAC g) THEN
      if offset<>31 && offset<>95 then
        MATCH_MP_TAC(TAUT `~p ==> (p ==> q)`) THEN
        (fun (asl,w) -> ACCEPT_TAC(ARITH_RULE w) (asl,w)) else
        REPEAT STRIP_TAC THEN MATCH_MP_TAC ASSURANCE_RET_FROM_DECODE_AND_STEP THEN
        CONJ_TAC THENL
         [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC dt THEN ASM_REWRITE_TAC[];
          ACCEPT_TAC original_step]];
    (fun g->print_endline("CLEANSE_ACCESS_COVERAGE "^string_of_int offset);ALL_TAC g) THEN
    MAP_EVERY EXISTS_TAC [mk_numeral(num offset);len;inst] THEN
    ASM_REWRITE_TAC[abi_cleanse_site] THEN
    MATCH_MP_TAC(REWRITE_RULE[ADD_CLAUSES] dt) THEN ASM_REWRITE_TAC[]]) (asl,w);;
let CLEANSE_ACCESS_BASIC_STEP_TAC offset decode_ths sname (asl,w) =
  let _,args=strip_comb w in let stepn=hd args in
  let predecessor=mk_binary "-" (stepn,`1:num`) in
  let n_th=ARITH_RULE(mk_eq(stepn,mk_binary "+" (`1:num`,predecessor))) in
  let sv=last args and sv'=mk_var(sname,`:x86state`) in
  let eth=X86_CONV decode_ths (map snd asl) (mk_comb(mk_comb(`x86`,sv),sv')) in
  (GEN_REWRITE_TAC (RATOR_CONV o RATOR_CONV o RATOR_CONV o RAND_CONV) [n_th] THEN
   GEN_REWRITE_TAC I [ASSURANCE_RUN_STEP] THEN CONJ_TAC THENL
    [GEN_REWRITE_TAC BINDER_CONV [eth] THEN CONV_TAC EXISTS_NONTRIVIAL_CONV;
     X_GEN_TAC sv' THEN DISCH_THEN(fun original_step ->
       MP_TAC(EQ_MP eth original_step) THEN REPEAT X86_UNDEFINED_CHOOSE_TAC THEN
       DISCH_THEN(fun update -> CONJ_TAC THENL
        [CLEANSE_ACCESS_LOCAL_STEP_TAC decode_ths offset original_step update;MP_TAC update]))]) (asl,w);;
let CLEANSE_ACCESS_STEP_TAC offset (length_th,decode_ths) sname =
  CLEANSE_ACCESS_BASIC_STEP_TAC offset decode_ths sname THEN
  (fun g->print_endline("CLEANSE_ACCESS_UPDATE "^string_of_int offset);ALL_TAC g) THEN
  NONSELFMODIFYING_STATE_UPDATE_TAC (MATCH_MP bytes_loaded_update length_th) THEN
  ASSUMPTION_STATE_UPDATE_TAC THEN DISCH_THEN(fun update ->
   let reads=STATE_UPDATE_NEW_RULE update in
   if reads=[] then ALL_TAC else MP_TAC(end_itlist CONJ reads) THEN
   ASSEMBLER_SIMPLIFY_TAC THEN STRIP_TAC) THEN
  (fun g->print_endline("CLEANSE_ACCESS_STEP_FINISHED "^string_of_int offset);ALL_TAC g);;
