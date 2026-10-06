(* New recipes over previously frozen literal target terms. *)
let CLW_REFERENCE_SATISFIES = prove
 (clw_reference_satisfies_statement, MATCH_ACCEPT_TAC FB_REFERENCE_SATISFIES);;
let CLW_INITIAL_IMAGE_BINDING = prove
 (clw_initial_image_binding_statement,
  REWRITE_TAC[clw_memory;clw_layout] THEN MATCH_ACCEPT_TAC FB_IMAGE_PRESERVATION);;
let CLW_VALID_ABI = prove
 (clw_valid_abi_statement, MATCH_ACCEPT_TAC FB_VALID_ABI);;
let CLW_LAYOUT_EMPTY = prove
 (`!p. clw_layout p 0`, REWRITE_TAC[clw_layout;LW_LAYOUT_EMPTY]);;
let CLW_CASE_LAYOUT = prove
 (`clw_layout (word 0x200001) 1 /\
   clw_layout (word 0x200003) 7 /\
   clw_layout (word 0x200000) 24 /\
   clw_layout (word 0x200001) 17 /\
   clw_layout (word 0x200003) 33 /\
   clw_layout (word 0x200fff) 17 /\
   clw_layout (word(2 EXP 47-1)) 1 /\
   clw_layout (word(2 EXP 64-1)) 1 /\
   clw_layout (word(2 EXP 64-8)) 8`,
  REWRITE_TAC[clw_layout;lw_layout;lw_overlay_domain;lw_pagecover;
    lw_image_domain;VAL_WORD;DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REPEAT CONJ_TAC THEN ARITH_TAC);;
let CLW_CODE_VALUE = prove
 (`!i. i<97 ==> val(word(0x102417d0+i):int64) = 0x102417d0+i`,
  REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC);;

let CLW_CODE_IN_IMAGE = prove
 (`!i. i<97 ==> lw_image_domain (0x102417d0+i)`,
  REWRITE_TAC[lw_image_domain] THEN ARITH_TAC);;

let CLW_CODE_BYTE = prove
 (`!image p n high_first i.
    clw_reference_code image /\ clw_layout p n /\ i<97
    ==> clw_memory image p n high_first (word(0x102417d0+i)) =
        EL i openssl_cleanse_mc`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
    `clw_memory image p n high_first (word(0x102417d0+i)) =
     image(word(0x102417d0+i))` SUBST1_TAC THENL
   [ASM_MESON_TAC[clw_memory; clw_layout; LW_PRESERVES_IMAGE; CLW_CODE_VALUE; CLW_CODE_IN_IMAGE];
    ASM_MESON_TAC[clw_reference_code]]);;

let CLW_CODE_CORRESPONDENCE = prove
 (clw_code_correspondence_statement,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[clw_reference_code] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `file_bytes(0x2417d0+i) = EL i openssl_cleanse_mc`
    ASSUME_TAC THENL
   [MP_TAC(SPEC `i:num` (REWRITE_RULE[clw_file_code]
      (ASSUME `clw_file_code (file_bytes:num->byte)`))) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `fb_immutable (0x102417d0+i)` ASSUME_TAC THENL
   [REWRITE_TAC[fb_immutable] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC `word(0x102417d0+i):int64` (REWRITE_RULE[fb_full_image]
    (ASSUME `fb_full_image file_bytes initial_rw padding (image:int64->byte)`))) THEN
  ASM_SIMP_TAC[CLW_CODE_VALUE; CLW_CODE_IN_IMAGE; fb_reference_image;
    ARITH_RULE `(0x102417d0+(i:num))-0x10000000 = 0x2417d0+i`]);;
let clw_code_byte_numeral_ths = List.init 97 (fun i ->
  CONV_RULE (NUM_REDUCE_CONV THENC WORD_REDUCE_CONV)
    (SPECL [`image:int64->byte`; `p:int64`; `n:num`;
            `high_first:bool`; mk_numeral(num i)] CLW_CODE_BYTE));;

let CLW_CODE_LOADED = prove
 (`!image p n high_first.
    clw_reference_code image /\ clw_layout p n
    ==> bytes_loaded (clw_state image p n high_first)
          (word 0x102417d0) openssl_cleanse_mc`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[bytes_loaded; clw_state; READ_COMPONENT_COMPOSE;
              x86state_COMPONENTS; openssl_cleanse_mc; LENGTH] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC(LAND_CONV LW_READ_BYTELIST_EXPAND_CONV) THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  ASM_SIMP_TAC clw_code_byte_numeral_ths THEN
  REWRITE_TAC[openssl_cleanse_mc] THEN
  CONV_TAC(DEPTH_CONV EL_CONV) THEN REWRITE_TAC[]);;

let CLW_RETURN_SLOT = prove
 (`!image p n high_first. read(bytes64(word 0x300008))
    (clw_memory image p n high_first)=(word 0x400000:int64)`,
  REWRITE_TAC[clw_memory;LW_RETURN_SLOT]);;
let CLW_MACHINE_MEMORY = prove
 (`!image p n high_first. read memory(clw_state image p n high_first)=
    clw_memory image p n high_first`,
  REWRITE_TAC[clw_state;x86state_COMPONENTS]);;
let CLW_TLS_ENVIRONMENT = prove
 (`!p n a. fb_tls_page a ==> clw_read p n a /\ clw_ordinary p n a`,
  REWRITE_TAC[clw_read;clw_ordinary;FB_TLS_ENVIRONMENT]);;
let CLW_IMAGE_PERMISSIONS = prove
 (`!p n a. clw_layout p n /\ lw_image_domain a ==>
    clw_read p n a /\ clw_ordinary p n a /\
    (lw_execute a <=> lw_image_execute a) /\
    (clw_write p n a <=> lw_image_write a)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~lw_pagecover p n a` ASSUME_TAC THENL
   [ASM_MESON_TAC[clw_layout;lw_layout;lw_overlay_domain];ALL_TAC] THEN
  REWRITE_TAC[clw_read;clw_ordinary;clw_write;fb_read;fb_ordinary;
    lw_read;lw_ordinary;lw_image_read;lw_execute] THEN
  ASM_REWRITE_TAC[]);;
let CLW_FULL_PRE_LIFT = prove
 (clw_full_pre_lift_statement,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[clw_full_pre;clw_machine;FST;SND;CLW_MACHINE_MEMORY;
    GSYM clw_scalar_pre] THEN
  ASM_SIMP_TAC[CLW_VALID_ABI;CLW_TLS_ENVIRONMENT] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CLW_INITIAL_IMAGE_BINDING THEN ASM_REWRITE_TAC[];
    GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC CLW_IMAGE_PERMISSIONS THEN
    ASM_REWRITE_TAC[]]);;
