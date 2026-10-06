(* New C2 entrymembership attempt. Frozen beforehand; no execution or target-correctness premise. *)
let C2W_WRITE64_OUTSIDE = prove
 (c2w_write64_outside_statement,
  REPEAT GEN_TAC THEN REWRITE_TAC[assurance_region] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(val(word_sub (addr:int64) loc)<8)` ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD_SUB_CASES;DIMINDEX_64] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `addr:int64` VAL_BOUND) THEN
    REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC;
    GEN_REWRITE_TAC LAND_CONV [GSYM READ_ELEMENT] THEN
    REWRITE_TAC[bytes64;WRITE_COMPONENT_COMPOSE;asword;through;write] THEN
    ASM_REWRITE_TAC[READ_ELEMENT_WRITE_BYTES;READ_ELEMENT]]);;

let c2w_fixed_write_outside = map
 (fun tm -> REWRITE_RULE[]
   (CONV_RULE (ONCE_DEPTH_CONV NUM_REDUCE_CONV)
    (REWRITE_RULE[VAL_WORD;DIMINDEX_64] (ISPEC tm C2W_WRITE64_OUTSIDE))))
 [`word 0x300008:int64`;`word 0x22003fd0:int64`;`word 0x22003fd8:int64`];;
let C2W_MEMORY_OUTSIDE = prove
 (c2w_memory_outside_statement,
  REPEAT STRIP_TAC THEN REWRITE_TAC[c2w_memory] THEN
  ASM_SIMP_TAC c2w_fixed_write_outside);;
let C2W_MEMORY_WORDS =
 let slots=[`word 0x300008:int64`;`word 0x22003fd0:int64`;`word 0x22003fd8:int64`] in
 let components=map(fun loc -> mk_comb
  (`bytes64:int64->((int64->byte),int64)component`,loc)) slots in
 let crosses=flat(map(fun c -> map(fun d ->
  MATCH_MP READ_WRITE_ORTHOGONAL_COMPONENTS
   (prove(list_mk_icomb "orthogonal_components" [c;d],
    REWRITE_TAC[bytes64] THEN
    MATCH_MP_TAC ORTHOGONAL_COMPONENTS_COMPOSE_LEFT THEN
    REWRITE_TAC[ORTHOGONAL_COMPONENTS_BYTES;VAL_WORD;DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    MATCH_MP_TAC NONOVERLAPPING_MODULO_SIMPLE THEN CONV_TAC NUM_REDUCE_CONV)))
   (filter(fun d -> not(aconv c d)) components)) components) in
 let same=map(fun loc -> REWRITE_RULE[strongly_valid_component]
  (ISPEC loc STRONGLY_VALID_COMPONENT_BYTES64)) slots in
 prove(c2w_memory_words_statement,
  REPEAT GEN_TAC THEN REWRITE_TAC[c2w_memory] THEN SIMP_TAC(crosses@same));;
let C2W_STATE_PROJECTIONS = prove
 (c2w_state_projections_statement,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[c2w_state;C_ARGUMENTS;RSP;RDI;RSI;RDX;DF;
    e5_normal_flags;READ_COMPONENT_COMPOSE;READ_ELEMENT;READ_BITELEMENT;x86state_COMPONENTS;BIT_WORD;BIT_WORD_0;
    WORD_EQ;CONG;VAL_WORD;DIMINDEX_4;DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV);;
let C2W_INITIAL_ABI = prove
 (c2w_initial_abi_statement,
  REWRITE_TAC[fb_initial_abi;abi_omitted_state_COMPONENTS;
    assurance_canonical48;VAL_WORD;DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV);;
let C2W_BYTES_LOADED_READS = prove
 (c2w_bytes_loaded_reads_statement,
  GEN_TAC THEN GEN_REWRITE_TAC I [SWAP_FORALL_THM] THEN
  LIST_INDUCT_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[bytes_loaded;READ_COMPONENT_COMPOSE]) THEN
  REWRITE_TAC[LENGTH;bytes_loaded;READ_COMPONENT_COMPOSE;
    bytelist_clauses;CONS_11] THEN
  X_GEN_TAC `pc:int64` THEN DISCH_TAC THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `0`) THEN
    REWRITE_TAC[LT_0;WORD_ADD_0;EL;HD];
    FIRST_X_ASSUM(MATCH_MP_TAC o SPEC `word_add (pc:int64) (word 1)`) THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `SUC i`) THEN
    ASM_REWRITE_TAC[LT_SUC;EL;TL;GSYM WORD_ADD_ASSOC;GSYM WORD_ADD;
      ARITH_RULE `1+i=SUC i`]]);;
