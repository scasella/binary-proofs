(* Unchanged frozen targets. Specialize layout and loaded-code facts before
   rewriting; no conditional broad-context simplification or final MESON. *)
let CW_PRE = prove
 (cw_pre_statement,
  REPEAT STRIP_TAC THEN
  (fun (asl,w as goal) ->
    let lib = ASSUME `fb_file_code (lib_file:num->byte)` in
    let client = ASSUME `c1_file_code (client_file:num->byte)` in
    let layout = ASSUME `cw_layout (p:int64) q n k different` in
    let parameters = [`p:int64`;`q:int64`;`n:num`;`k:num`;`different:bool`] in
    let perms = MATCH_MP (SPECL parameters CW_LAYOUT_PERMISSIONS) layout in
    let code = MATCH_MP
      (SPECL ([`lib_file:num->byte`;`client_file:num->byte`] @ parameters)
        CW_LOADED_CODE) (CONJ lib client) in
    let bound = CONJUNCT1 (REWRITE_RULE[cw_layout] layout) in
    (REWRITE_TAC[c1_pre;c1_got;READ_COMPONENT_COMPOSE;
      CW_STATE_PROJECTIONS;CW_MEMORY_IMAGES;CW_MEMORY_WORDS;
      CW_INITIAL_ABI;CW_IMAGE_PERMISSIONS;perms;code;bound;lib;client] THEN
     REWRITE_TAC[VAL_WORD;DIMINDEX_64;WORD_EQ;CONG;assurance_canonical48] THEN
     CONV_TAC NUM_REDUCE_CONV THEN
     REWRITE_TAC[CONV_RULE (ONCE_DEPTH_CONV NUM_REDUCE_CONV) CW_FIXED_SPANS] THEN
     REWRITE_TAC[assurance_region;c1_call_slot;VAL_WORD_SUB_CASES;
       VAL_WORD;DIMINDEX_64] THEN
     CONV_TAC NUM_REDUCE_CONV THEN
     ARITH_TAC) goal));;
let CW_GENERIC_WITNESS = prove
 (cw_generic_witness_statement,
  REPEAT STRIP_TAC THEN REWRITE_TAC[c1_entry_witness] THEN
  MAP_EVERY EXISTS_TAC
   [`cw_memory lib_file client_file (p:int64) k different`;
    `cw_memory lib_file client_file (p:int64) k different`;
    `cw_memory lib_file client_file (p:int64) k different`;
    `cw_memory lib_file client_file (p:int64) k different`;
    `cw_memory lib_file client_file (p:int64) k different`;
    `cw_read`;`cw_write`;`cw_execute`;`cw_ordinary`;
    `cw_state lib_file client_file (p:int64) (q:int64) n k different`;
    `fb_initial_abi`] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(SPECL
     [`lib_file:num->byte`;`client_file:num->byte`;`p:int64`;`q:int64`;
      `n:num`;`k:num`;`different:bool`] CW_PRE) THEN ASM_REWRITE_TAC[];
    MP_TAC(SPECL
     [`lib_file:num->byte`;`client_file:num->byte`;`p:int64`;`q:int64`;
      `n:num`;`k:num`;`different:bool`] CW_BUFFER_VALUES) THEN
    ASM_REWRITE_TAC[cw_read] THEN MESON_TAC[]]);;
let C1_ADMISSIBLE_ENTRY_WITNESSES = prove
 (c1_admissible_entry_witnesses_statement,
  REPEAT STRIP_TAC THEN MP_TAC CW_SEVEN_LAYOUTS THEN STRIP_TAC THEN
  REPEAT CONJ_TAC THEN MATCH_MP_TAC CW_GENERIC_WITNESS THEN ASM_REWRITE_TAC[]);;
