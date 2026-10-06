(* New C2 entrymembership attempt. Frozen beforehand; no execution or target-correctness premise. *)
(* Unchanged frozen targets. Specialize layout and loaded-code facts before
   rewriting; no conditional broad-context simplification or final MESON. *)
let C2W_PRE = prove
 (c2w_pre_statement,
  REPEAT STRIP_TAC THEN
  (fun (asl,w as goal) ->
    let lib = ASSUME `fb_file_code (lib_file:num->byte)` in
    let client = ASSUME `c2_file_code (client_file:num->byte)` in
    let cleanse = ASSUME `clw_file_code (lib_file:num->byte)` in
    let layout = ASSUME `c2w_layout (p:int64) q n k different` in
    let parameters = [`p:int64`;`q:int64`;`n:num`;`k:num`;`different:bool`] in
    let perms = MATCH_MP (SPECL parameters C2W_LAYOUT_PERMISSIONS) layout in
    let code = MATCH_MP
      (SPECL ([`lib_file:num->byte`;`client_file:num->byte`] @ parameters)
        C2W_LOADED_CODE) (CONJ lib (CONJ cleanse client)) in
    let bound = CONJUNCT1 (REWRITE_RULE[c2w_layout] layout) in
    (REWRITE_TAC[c2_pre;c2_got;READ_COMPONENT_COMPOSE;
      C2W_STATE_PROJECTIONS;C2W_MEMORY_IMAGES;C2W_MEMORY_WORDS;
      C2W_INITIAL_ABI;C2W_IMAGE_PERMISSIONS;perms;code;bound;lib;cleanse;client] THEN
     REWRITE_TAC[VAL_WORD;DIMINDEX_64;WORD_EQ;CONG;assurance_canonical48] THEN
     CONV_TAC NUM_REDUCE_CONV THEN
     REWRITE_TAC[CONV_RULE (ONCE_DEPTH_CONV NUM_REDUCE_CONV) C2W_FIXED_SPANS] THEN
     REWRITE_TAC[assurance_region;c2_scratch;VAL_WORD_SUB_CASES;
       VAL_WORD;DIMINDEX_64] THEN
     CONV_TAC NUM_REDUCE_CONV THEN
     ARITH_TAC) goal));;
let C2W_GENERIC_WITNESS = prove
 (c2w_generic_witness_statement,
  REPEAT STRIP_TAC THEN REWRITE_TAC[c2_entry_witness] THEN
  MAP_EVERY EXISTS_TAC
   [`c2w_memory lib_file client_file (p:int64) k different`;
    `c2w_memory lib_file client_file (p:int64) k different`;
    `c2w_memory lib_file client_file (p:int64) k different`;
    `c2w_memory lib_file client_file (p:int64) k different`;
    `c2w_memory lib_file client_file (p:int64) k different`;
    `c2w_read`;`c2w_write`;`c2w_execute`;`c2w_ordinary`;
    `c2w_state lib_file client_file (p:int64) (q:int64) n k different`;
    `fb_initial_abi`] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(SPECL
     [`lib_file:num->byte`;`client_file:num->byte`;`p:int64`;`q:int64`;
      `n:num`;`k:num`;`different:bool`] C2W_PRE) THEN ASM_REWRITE_TAC[];
    MP_TAC(SPECL
     [`lib_file:num->byte`;`client_file:num->byte`;`p:int64`;`q:int64`;
      `n:num`;`k:num`;`different:bool`] C2W_BUFFER_VALUES) THEN
    ASM_REWRITE_TAC[c2w_read] THEN MESON_TAC[]]);;
let C2_ADMISSIBLE_ENTRY_WITNESSES = prove
 (c2_admissible_entry_witnesses_statement,
  REPEAT STRIP_TAC THEN MP_TAC C2W_EIGHT_LAYOUTS THEN STRIP_TAC THEN
  REPEAT CONJ_TAC THEN MATCH_MP_TAC C2W_GENERIC_WITNESS THEN ASM_REWRITE_TAC[]);;
