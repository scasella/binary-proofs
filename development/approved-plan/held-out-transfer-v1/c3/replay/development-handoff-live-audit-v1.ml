let fresh_initial_axioms=reuse_c3_foundation_axioms;;
(* Adapted from normal-entry-e5-v1/live-audit-v3.ml.
   Expected strings come from frozen C3 targets, pre-proof witness requirements,
   and versioned auxiliary definition identity anchors. Auxiliary anchors can
   postdate first helper construction; the attempt ledger records chronology.
   GEN_ALL below is the kernel closure of primitive recursive equations. *)
let c3_fresh_typealpha tm =
 let tvs=sort (fun a b->compare a b<0) (type_vars_in_term tm) in
 inst(map(fun(i,t)->mk_vartype("C3Audit"^string_of_int i),t)
      (map2(fun i t->i,t)(0--(length tvs-1))tvs))tm;;
let c3_fresh_close tm=list_mk_forall(frees tm,tm);;
let c3_fresh_json text =
 let b=Buffer.create 256 in Buffer.add_char b '"';
 String.iter (fun c->match c with
  | '"' -> Buffer.add_string b "\\\""
  | '\\' -> Buffer.add_string b "\\\\"
  | '\n' -> Buffer.add_string b "\\n"
  | '\r' -> Buffer.add_string b "\\r"
  | '\t' -> Buffer.add_string b "\\t"
  | _ -> if Char.code c<32 then Buffer.add_string b (Printf.sprintf "\\u%04x" (Char.code c)) else Buffer.add_char b c) text;
 Buffer.add_char b '"'; Buffer.contents b;;
let c3_fresh_rf_checked_run_closed=GEN_ALL e5_rf_checked_run;;
let c3_fresh_definition_rules=[
("c3_allowed_fetch",c3_allowed_fetch);
("c3_allowed_read",c3_allowed_read);
("c3_allowed_write",c3_allowed_write);
("c3_caller_mc",c3_caller_mc);
("c3_cleanse_plt_prefix",c3_cleanse_plt_prefix);
("c3_cleansed_memory",c3_cleansed_memory);
("c3_crypto_plt_prefix",c3_crypto_plt_prefix);
("c3_crypto_ready",c3_crypto_ready);
("c3_entry_witness",c3_entry_witness);
("c3_equal",c3_equal);
("c3_file_code",c3_file_code);
("c3_frame",c3_frame);
("c3_full_image",c3_full_image);
("c3_got",c3_got);
("c3_image_domain",c3_image_domain);
("c3_image_execute",c3_image_execute);
("c3_image_write",c3_image_write);
("c3_immutable",c3_immutable);
("c3_initialized_rw",c3_initialized_rw);
("c3_loaded_code",c3_loaded_code);
("c3_pre",c3_pre);
("c3_prefix_frame",c3_prefix_frame);
("c3_public_post",c3_public_post);
("c3_reference_image",c3_reference_image);
("c3_result",c3_result);
("c3_saved_prefix",c3_saved_prefix);
("c3_scalar_post",c3_scalar_post);
("c3_scratch",c3_scratch);
("c3_segment_policy",c3_segment_policy);
("c3_step_policy",c3_step_policy);
("c3_steps",c3_steps);
("c3w_execute",c3w_execute);
("c3w_external",c3w_external);
("c3w_layout",c3w_layout);
("c3w_memory",c3w_memory);
("c3w_ordinary",c3w_ordinary);
("c3w_read",c3w_read);
("c3w_seed",c3w_seed);
("c3w_state",c3w_state);
("c3w_write",c3w_write);
("e5_normal_flags",e5_normal_flags);
("e5_rf_clear",e5_rf_clear);
("e5_rf_retired_step",e5_rf_retired_step);
("e5_rf_retired_extended_step",e5_rf_retired_extended_step);
("e5_normal_step_policy",e5_normal_step_policy);
("e5_normal_environment",e5_normal_environment);
("e5_rf_checked_run",c3_fresh_rf_checked_run_closed)
];;
let c3_fresh_rows=[
("object","C3_HANDOFF","!lib_file lib_rw lib_padding client_file client_rw client_padding\n    stackpointer ra p q n m rp wp xp ordinary s a.\n    c3_pre lib_file lib_rw lib_padding client_file client_rw client_padding\n      stackpointer ra p q n m rp wp xp ordinary (s,a)\n    ==> assurance_checked_run 10\n      (c3_crypto_ready lib_file stackpointer p q n m rp wp xp ordinary s a)\n      (c3_segment_policy stackpointer p q n m rp wp xp ordinary) s","4e802c082b33c68ee21f3390813b9c72a145fa483fa24e630da0ba15c2408ff7","raw_closed_aconv",C3_HANDOFF);
("definition","c3_allowed_fetch","c3_allowed_fetch xp ordinary a <=>\n    xp a /\\ ordinary a /\\\n    (assurance_region (word 0x23001120) 89 a \\/\n     assurance_region (word 0x23001030) 6 a \\/\n     assurance_region (word 0x23001040) 6 a \\/\n     assurance_region (word 0x10241840) 95 a \\/\n     assurance_region (word 0x102417d0) 97 a)","3ca7cea3373313a60e5fea73f595e82e82dcb152ef5da917b2ed1adcd1de4be9","SPEC_ALL_closed_type_variable_alpha_only",c3_allowed_fetch);
("definition","c3_allowed_read","c3_allowed_read rp ordinary stackpointer p q n a <=>\n    rp a /\\ ordinary a /\\\n    (assurance_region p n a \\/ assurance_region q n a \\/\n     c3_scratch stackpointer a \\/\n     assurance_region stackpointer 8 a \\/\n     assurance_region (word 0x23003fd0) 8 a \\/\n     assurance_region (word 0x23003fd8) 8 a)","aa0cc2d2d1fdf2cd67947f8a56ca0f0d78d5952e2ca49a40802784cd26e4282f","SPEC_ALL_closed_type_variable_alpha_only",c3_allowed_read);
("definition","c3_allowed_write","c3_allowed_write wp ordinary stackpointer (p:int64) (q:int64) n (m:int64->byte) a <=>\n    wp a /\\ ordinary a /\\\n    ((assurance_region p n a) \\/\n     c3_scratch stackpointer a)","202c5f0543cdfed1152ca2b2608005d681ff0cd2a95028b109d9bb4b9d52f6ed","SPEC_ALL_closed_type_variable_alpha_only",c3_allowed_write);
("definition","c3_caller_mc","c3_caller_mc:byte list =\n   [word 0x41;word 0x55;word 0x41;word 0x54;word 0x55;word 0x53;word 0x48;word 0x83;word 0xec;word 0x08;word 0x48;word 0x89;word 0xfb;word 0x49;word 0x89;word 0xf4;word 0x48;word 0x89;word 0xd5;word 0xe8;word 0xf8;word 0xfe;word 0xff;word 0xff;word 0x45;word 0x31;word 0xed;word 0x85;word 0xc0;word 0x41;word 0x0f;word 0x94;word 0xc5;word 0x48;word 0x89;word 0xee;word 0x48;word 0x89;word 0xdf;word 0xe8;word 0xf4;word 0xfe;word 0xff;word 0xff;word 0x48;word 0x89;word 0xea;word 0x4c;word 0x89;word 0xe6;word 0x48;word 0x89;word 0xdf;word 0xe8;word 0xd6;word 0xfe;word 0xff;word 0xff;word 0x45;word 0x85;word 0xed;word 0x74;word 0x0a;word 0x85;word 0xc0;word 0x0f;word 0x94;word 0xc0;word 0x0f;word 0xb6;word 0xc0;word 0xeb;word 0x05;word 0xb8;word 0x02;word 0x00;word 0x00;word 0x00;word 0x48;word 0x83;word 0xc4;word 0x08;word 0x5b;word 0x5d;word 0x41;word 0x5c;word 0x41;word 0x5d;word 0xc3]","adcbe1c0afd69a40f4ba8c34fa1a771d5ab124d33b8d9a2a9c03f6b282fe868e","SPEC_ALL_closed_type_variable_alpha_only",c3_caller_mc);
("definition","c3_cleanse_plt_prefix","c3_cleanse_plt_prefix:byte list =\n   [word 0xff;word 0x25;word 0x92;word 0x2f;word 0x00;word 0x00]","d5ebde5dd6cb7eb8884358f3d2e0fa97538dc420c371de694b5c17948c0d17eb","SPEC_ALL_closed_type_variable_alpha_only",c3_cleanse_plt_prefix);
("definition","c3_cleansed_memory","c3_cleansed_memory (m:int64->byte) (p:int64) n (addr:int64) =\n    if assurance_region p n (val addr) then word 0 else m addr","f649f4c4ec2597ca2cdf7b5f19737e125125042c65cc7fe6f479e2be2296a159","SPEC_ALL_closed_type_variable_alpha_only",c3_cleansed_memory);
("definition","c3_crypto_plt_prefix","c3_crypto_plt_prefix:byte list =\n   [word 0xff;word 0x25;word 0x9a;word 0x2f;word 0x00;word 0x00]","293f7ef4d4148f4e8af36b4ea637cde35222224e56e380bd7cdf2b271f4cb0ee","SPEC_ALL_closed_type_variable_alpha_only",c3_crypto_plt_prefix);
("definition","c3_crypto_ready","c3_crypto_ready lib_file stackpointer p q n m rp (wp:num->bool) xp\n    ordinary (s:x86state) a (t:x86state) <=>\n    bp_e2_crypto_public_pre lib_file (read memory t) (read memory t)\n      (word_sub stackpointer (word 48)) (word 0x23001138) p q n\n      (read memory t) rp xp ordinary (t,a) /\\\n    c3_saved_prefix stackpointer p q n m s t /\\\n    read R13 t=read R13 s /\\ c3_prefix_frame stackpointer s t","11dd4fdceafeadc25082367507f34771dffa47573e289ffe8a52f505efbd60e7","SPEC_ALL_closed_type_variable_alpha_only",c3_crypto_ready);
("definition","c3_entry_witness","c3_entry_witness lib_file client_file payload p q n <=>\n    ?lib_rw lib_padding client_rw client_padding m rp wp xp ordinary s a.\n      c3_pre lib_file lib_rw lib_padding client_file client_rw client_padding\n        (word 0x300008) (word 0x400000) p q n m rp wp xp ordinary (s,a) /\\\n      (!i. i<n ==> m(word_add p (word i))=payload(word_add p (word i))) /\\\n      (!i. i<n ==> m(word_add q (word i))=payload(word_add q (word i))) /\\\n      (p=word 0 /\\ q=word 0 /\\ n=0 ==> ~rp 0)","664950d829f36389ef1dcdc0f69398ca62305c7efce198598e1f2608c32c9df8","SPEC_ALL_closed_type_variable_alpha_only",c3_entry_witness);
("definition","c3_equal","c3_equal (m:int64->byte) (p:int64) (q:int64) n <=>\n    !i. i<n ==> m(word_add p (word i))=m(word_add q (word i))","addc10d1386c7661d2dea23195435d46179fa63648d1de1ed5305d1fbfd9a309","SPEC_ALL_closed_type_variable_alpha_only",c3_equal);
("definition","c3_file_code","c3_file_code (file_bytes:num->byte) <=>\n    (!i. i<89 ==> file_bytes(0x1120+i)=EL i c3_caller_mc) /\\\n    (!i. i<6 ==> file_bytes(0x1030+i)=EL i c3_crypto_plt_prefix) /\\\n    (!i. i<6 ==> file_bytes(0x1040+i)=EL i c3_cleanse_plt_prefix)","6e06e4e9c4843436ab4c6bd56bf132ed90086bda456bdbd50e3dc4adce75fd9d","SPEC_ALL_closed_type_variable_alpha_only",c3_file_code);
("definition","c3_frame","c3_frame stackpointer (p:int64) (q:int64) n (m:int64->byte) =\n    MAYCHANGE [RIP;RSP;RAX;RDI;RSI;RDX;R10;R11] ,,\n    MAYCHANGE SOME_FLAGS ,,\n    MAYCHANGE [memory :> bytes(p,n);\n               memory :> bytes(word_sub stackpointer (word 48),48)] ,,\n    MAYCHANGE [events]","6ce44709bee9774976a7f38cca4b27f1f2af28759e2f2b46e16b2e0680a074de","SPEC_ALL_closed_type_variable_alpha_only",c3_frame);
("definition","c3_full_image","c3_full_image file_bytes initial_rw padding (m:int64->byte) <=>\n    !a. c3_image_domain (val a)\n        ==> m a = c3_reference_image file_bytes initial_rw padding a","41074f3f16e5d24bd8bf1de6cacfd6deac7c6c3faaedbd5a777219f83e54243d","SPEC_ALL_closed_type_variable_alpha_only",c3_full_image);
("definition","c3_got","c3_got (s:x86state) <=>\n    read (memory :> bytes64 (word 0x23003fd0)) s=word 0x10241840 /\\\n    read (memory :> bytes64 (word 0x23003fd8)) s=word 0x102417d0","bcdf583d2aad039d04225b04bb4d9758cb94ef48c6c8a1824874e5e535e9cfb1","SPEC_ALL_closed_type_variable_alpha_only",c3_got);
("definition","c3_image_domain","c3_image_domain a <=> 0x23000000 <= a /\\ a < 0x23005000","5b2863325a38f314fe00c1d6fbb207aa8724b7e1b0e2be7a91ca1313e17ea69b","SPEC_ALL_closed_type_variable_alpha_only",c3_image_domain);
("definition","c3_image_execute","c3_image_execute a <=> 0x23001000 <= a /\\ a < 0x23002000","820d794ad7656f3d8497db488c36fa154b88223397e93b6e97b9894e091b5d34","SPEC_ALL_closed_type_variable_alpha_only",c3_image_execute);
("definition","c3_image_write","c3_image_write a <=> 0x23004000 <= a /\\ a < 0x23005000","922669a259c9fe98209cfb6b5241b404ac86202a7b70fc3aa08e78666e5e8394","SPEC_ALL_closed_type_variable_alpha_only",c3_image_write);
("definition","c3_immutable","c3_immutable a <=>\n    (0x23000000 <= a /\\ a < 0x23000510) \\/\n    (0x23001000 <= a /\\ a < 0x23001185) \\/\n    (0x23002000 <= a /\\ a < 0x23002004)","b41f3245fd9c7662c85ec38e1e045d8aa17b1a9080bb67b704ea28f52bc47876","SPEC_ALL_closed_type_variable_alpha_only",c3_immutable);
("definition","c3_initialized_rw","c3_initialized_rw a <=> 0x23003da8 <= a /\\ a < 0x23004010","2360a2e3460d699f7a9c8bdc253a3e76a10c140311810051d943a9203282a5bf","SPEC_ALL_closed_type_variable_alpha_only",c3_initialized_rw);
("definition","c3_loaded_code","c3_loaded_code (s:x86state) <=>\n    bytes_loaded s (word 0x23001120) c3_caller_mc /\\\n    bytes_loaded s (word 0x23001030) c3_crypto_plt_prefix /\\\n    bytes_loaded s (word 0x23001040) c3_cleanse_plt_prefix /\\\n    bytes_loaded s (word 0x10241840) crypto_memcmp_mc /\\\n    bytes_loaded s (word 0x102417d0) openssl_cleanse_mc","8644b7ee351fcc64eb8a00855f39d06bbea78ca00aac289c95b83a5b77f73916","SPEC_ALL_closed_type_variable_alpha_only",c3_loaded_code);
("definition","c3_pre","c3_pre lib_file lib_rw lib_padding client_file client_rw\n    client_padding stackpointer ra p q n m rp wp xp ordinary\n    (s:x86state,a:abi_omitted_state) <=>\n    n<2 EXP 64 /\\ 48<=val(stackpointer:int64) /\\\n    val stackpointer MOD 16=8 /\\ val stackpointer+8<2 EXP 64 /\\\n    assurance_canonical48(val(ra:int64)) /\\ ~(ra=word 0x23001120) /\\\n    read RIP s=word 0x23001120 /\\ read RSP s=stackpointer /\\\n    read (memory :> bytes64 stackpointer) s=ra /\\\n    C_ARGUMENTS [p;q;word n] s /\\ read memory s=m /\\\n    read DF s=F /\\ ~bit 18(read rflags s) /\\ e5_normal_flags s /\\\n    assurance_canonical48(val(read ABI_FS_BASE a)) /\\\n    fb_file_code lib_file /\\ clw_file_code lib_file /\\\n    fb_full_image lib_file lib_rw lib_padding m /\\\n    c3_file_code client_file /\\\n    c3_full_image client_file client_rw client_padding m /\\\n    c3_loaded_code s /\\ c3_got s /\\\n    (!addr. lw_image_domain addr ==>\n       rp addr /\\ ordinary addr /\\ (xp addr <=> lw_execute addr) /\\\n       (wp addr <=> lw_image_write addr)) /\\\n    (!addr. c3_image_domain addr ==>\n       rp addr /\\ ordinary addr /\\\n       (xp addr <=> c3_image_execute addr) /\\\n       (wp addr <=> c3_image_write addr)) /\\\n    assurance_span_ok (\\a. rp a /\\ ordinary a) (val p) n /\\\n    assurance_span_ok (\\a. rp a /\\ ordinary a) (val q) n /\\\n    assurance_span_ok (\\a. wp a /\\ ordinary a) (val p) n /\\\n    assurance_span_ok (\\a. rp a /\\ ordinary a) (val stackpointer-48) 48 /\\\n    assurance_span_ok (\\a. wp a /\\ ordinary a) (val stackpointer-48) 48 /\\\n    assurance_span_ok (\\a. rp a /\\ ordinary a) (val stackpointer) 8 /\\\n    assurance_span_ok (\\a. rp a /\\ ordinary a) 0x23003fd0 8 /\\\n    assurance_span_ok (\\a. rp a /\\ ordinary a) 0x23003fd8 8 /\\\n    assurance_span_ok (\\a. xp a /\\ ordinary a) 0x23001120 89 /\\\n    assurance_span_ok (\\a. xp a /\\ ordinary a) 0x23001030 6 /\\\n    assurance_span_ok (\\a. xp a /\\ ordinary a) 0x23001040 6 /\\\n    assurance_span_ok (\\a. xp a /\\ ordinary a) 0x10241840 95 /\\\n    assurance_span_ok (\\a. xp a /\\ ordinary a) 0x102417d0 97 /\\\n    (!addr. ~(assurance_region p n addr /\\\n               c3_scratch stackpointer addr)) /\\\n    (!addr. ~(assurance_region q n addr /\\\n               c3_scratch stackpointer addr)) /\\\n    (!addr. ~(assurance_region p n addr /\\\n               assurance_region stackpointer 8 addr)) /\\\n    (!addr. assurance_region p n addr ==>\n      ~(assurance_region (word 0x23001120) 89 addr \\/\n        assurance_region (word 0x23001030) 6 addr \\/\n        assurance_region (word 0x23001040) 6 addr \\/\n        assurance_region (word 0x23003fd0) 8 addr \\/\n        assurance_region (word 0x23003fd8) 8 addr \\/\n        assurance_region (word 0x10241840) 95 addr \\/\n        assurance_region (word 0x102417d0) 97 addr))","1e3e4bac8a3f07aac9cbd42fd4eda36916398c22ad169c1ff081026ac93d2d9b","SPEC_ALL_closed_type_variable_alpha_only",c3_pre);
("definition","c3_prefix_frame","c3_prefix_frame stackpointer =\n    MAYCHANGE [RIP;RSP;RBX;RBP;R12] ,, MAYCHANGE SOME_FLAGS ,,\n    MAYCHANGE [memory :> bytes(word_sub stackpointer (word 48),48)] ,,\n    MAYCHANGE [events]","735cb8f82881e86ef5ccfc573a20261bcc982c6d74ce2745079de3add3016c03","SPEC_ALL_closed_type_variable_alpha_only",c3_prefix_frame);
("definition","c3_public_post","c3_public_post stackpointer ra p q n m s a\n    (t:x86state#abi_omitted_state) <=>\n    c3_scalar_post stackpointer ra p q n m s (FST t) /\\\n    SND t=a /\\ abi_required_controls_preserved a (SND t)","ae5725d7fe2f2cdb7c5cd5448e42cc4b366a2958ce22cda1e039bd2d61875369","SPEC_ALL_closed_type_variable_alpha_only",c3_public_post);
("definition","c3_reference_image","c3_reference_image (file_bytes:num->byte)\n     (initial_rw:int64->byte) (padding:int64->byte) (a:int64) =\n    if c3_immutable (val a)\n    then file_bytes (val a - 0x23000000)\n    else if c3_initialized_rw (val a) then initial_rw a\n    else padding a","9662e994b0eef4dac9e2877a0dedcb55d7ed9f671a41ba696e253a3c3fe7f7d2","SPEC_ALL_closed_type_variable_alpha_only",c3_reference_image);
("definition","c3_result","c3_result (m:int64->byte) (p:int64) (q:int64) n =\n    if c3_equal m p q n\n    then if c3_equal (c3_cleansed_memory m p n) p q n then word 1 else word 0\n    else word 2:int64","f835fe1c4e3c46680a2790e89d58a859825ed9c6bfa15be95fe0436d6a4132f6","SPEC_ALL_closed_type_variable_alpha_only",c3_result);
("definition","c3_saved_prefix","c3_saved_prefix stackpointer p q n m (s:x86state) t <=>\n    read RBX t=p /\\ read RBP t=word n /\\ read R12 t=q /\\\n    read (memory :> bytes64 (word_sub stackpointer (word 8))) t=read R13 s /\\\n    read (memory :> bytes64 (word_sub stackpointer (word 16))) t=read R12 s /\\\n    read (memory :> bytes64 (word_sub stackpointer (word 24))) t=read RBP s /\\\n    read (memory :> bytes64 (word_sub stackpointer (word 32))) t=read RBX s /\\\n    (!addr. ~c3_scratch stackpointer (val addr)\n            ==> read memory t addr=m addr) /\\\n    (!i. i<n ==> read memory t (word_add p (word i))=m(word_add p (word i))) /\\\n    (!i. i<n ==> read memory t (word_add q (word i))=m(word_add q (word i))) /\\\n    c3_loaded_code t /\\ c3_got t","14499abc85eddbce5672b6b34d4a71f0162a10bf477cb051d55a41af51ef2400","SPEC_ALL_closed_type_variable_alpha_only",c3_saved_prefix);
("definition","c3_scalar_post","c3_scalar_post stackpointer ra p q n m (s:x86state) t <=>\n    read RIP t=ra /\\ val(read RSP t)=val(stackpointer:int64)+8 /\\\n    read RAX t=c3_result m p q n /\\\n    (!i. i<n ==> read memory t (word_add p (word i))=word 0) /\\\n    (!i. i<n ==> read memory t (word_add q (word i))=\n      c3_cleansed_memory m p n (word_add q (word i))) /\\\n    (!addr. ~(assurance_region p n (val addr) \\/\n               c3_scratch stackpointer (val addr))\n            ==> read memory t addr=m addr) /\\\n    read (memory :> bytes64 stackpointer) t=ra /\\\n    read RBX t=read RBX s /\\ read RBP t=read RBP s /\\\n    read R12 t=read R12 s /\\ read R13 t=read R13 s /\\\n    read R14 t=read R14 s /\\ read R15 t=read R15 s /\\\n    read DF t=F /\\ c3_loaded_code t /\\ c3_got t /\\\n    c3_frame stackpointer p q n m s t","4e31a8851dfb5a8bf17021731008dff27c1169ccde4c1fc4914a9b358e8f28f1","SPEC_ALL_closed_type_variable_alpha_only",c3_scalar_post);
("definition","c3_scratch","c3_scratch (stackpointer:int64) a <=>\n    assurance_region (word_sub stackpointer (word 48)) 48 a","dfb1714636730abac47592e71315aceae753a96c39c9fc388e0492b6aa62c4c9","SPEC_ALL_closed_type_variable_alpha_only",c3_scratch);
("definition","c3_segment_policy","c3_segment_policy stackpointer p q n m rp wp xp ordinary\n    (remaining:num) (source:x86state) (target:x86state) <=>\n    assurance_step_policy\n      (c3_allowed_read rp ordinary stackpointer p q n)\n      (c3_allowed_write wp ordinary stackpointer p q n m)\n      (c3_allowed_fetch xp ordinary) source target /\\\n    abi_all_decodes_caller_scalar source","2af47d167766a42294c90b15afc3e22d03fb8cd60f19f0f6aa50aca7f6243cdf","SPEC_ALL_closed_type_variable_alpha_only",c3_segment_policy);
("definition","c3_step_policy","c3_step_policy stackpointer p q n m rp wp xp ordinary\n    (remaining:num) (source:x86state) (target:x86state) <=>\n    assurance_step_policy\n      (c3_allowed_read rp ordinary stackpointer p q n)\n      (c3_allowed_write wp ordinary stackpointer p q n m)\n      (c3_allowed_fetch xp ordinary) source target /\\\n    (remaining=1 ==> assurance_actual_ret 1 source target) /\\\n    abi_all_decodes_caller_scalar source","eefe0a0c95279c3d61047e844138d94a0b3946d9bdd6ab1888186744e46800da","SPEC_ALL_closed_type_variable_alpha_only",c3_step_policy);
("definition","c3_steps","c3_steps p q n m =\n    (if c3_equal m p q n then 34 else 31) +\n    2 * bp_assurance_call_steps n + cleanse_functional_steps p n","34cfb1f0f66265e0a19889fbe0090490a618c0d28bee5d834b1312b0aae9966e","SPEC_ALL_closed_type_variable_alpha_only",c3_steps);
("definition","c3w_execute","c3w_execute a <=> lw_execute a \\/ c3_image_execute a","7ca2151eee465609b4e2da0337187fee1daeca9798f58b36f778db10b913f6cb","SPEC_ALL_closed_type_variable_alpha_only",c3w_execute);
("definition","c3w_external","c3w_external a <=> 0x50000000 <= a /\\ assurance_canonical48 a","377a35aa9d675c6a26e74608a601c26afe89c7df5f8089ba4a464b150abefec7","SPEC_ALL_closed_type_variable_alpha_only",c3w_external);
("definition","c3w_layout","c3w_layout (p:int64) (q:int64) n <=>\n    n<2 EXP 64 /\\ assurance_span_ok c3w_external (val p) n /\\\n    assurance_span_ok c3w_external (val q) n","d821569b426d99401e46080142287e48740561dead8c41d7b74f3a0c3f07a369","SPEC_ALL_closed_type_variable_alpha_only",c3w_layout);
("definition","c3w_memory","c3w_memory lib_file client_file payload =\n    write (bytes64 (word 0x300008)) (word 0x400000)\n      (write (bytes64 (word 0x23003fd0)) (word 0x10241840)\n        (write (bytes64 (word 0x23003fd8)) (word 0x102417d0)\n          (c3w_seed lib_file client_file payload)))","709b9e0428a7702581714950a953ff7da5eb2b144c8e15d357d3b391d89fd36e","SPEC_ALL_closed_type_variable_alpha_only",c3w_memory);
("definition","c3w_ordinary","c3w_ordinary a <=> assurance_canonical48 a","65f93eebac38d207d25667ff408a9605d0c32dd91e5243f8aa7fe1651afe6d6c","SPEC_ALL_closed_type_variable_alpha_only",c3w_ordinary);
("definition","c3w_read","c3w_read a <=> assurance_canonical48 a /\\ ~(a=0)","dc3daaad6770618694efc09a847cad9644f88b513700f4e52b6408468277f3c9","SPEC_ALL_closed_type_variable_alpha_only",c3w_read);
("definition","c3w_seed","c3w_seed (lib_file:num->byte) (client_file:num->byte)\n    (payload:int64->byte) (addr:int64) =\n    if fb_immutable (val addr) then lib_file(val addr-0x10000000)\n    else if c3_immutable (val addr) then client_file(val addr-0x23000000)\n    else payload addr","9a20422915e816b5177580100f1022aee8199b637ccf44f7f5b53a18e331e003","SPEC_ALL_closed_type_variable_alpha_only",c3w_seed);
("definition","c3w_state","c3w_state lib_file client_file payload p q n =\n    x86state_RECORD (word 0x23001120)\n      (\\j:(4)word. if j=word 7 then p else if j=word 6 then q\n                    else if j=word 2 then word n\n                    else if j=word 4 then word 0x300008 else word 0)\n      (\\j:(5)word. word 0) (\\j:(3)word. word 0) (word 2)\n      (c3w_memory lib_file client_file payload) []","055a3b43f00e3e0d291978f7a399d726a164f1ffb676ab9d3385b53feeb5612d","SPEC_ALL_closed_type_variable_alpha_only",c3w_state);
("definition","c3w_write","c3w_write a <=>\n    if lw_image_domain a then lw_image_write a\n    else if c3_image_domain a then c3_image_write a\n    else assurance_canonical48 a","2aa7048b2cc6e0a6570fc8f2f0f2a0007fa18b35cf569f71950132f71e090127","SPEC_ALL_closed_type_variable_alpha_only",c3w_write);
("definition","e5_normal_flags","e5_normal_flags (s:x86state) <=>\n    ~bit 16 (read rflags s) /\\ ~bit 8 (read rflags s)","7c9549b60e6a9c672402ec022ab0f9fee85dfebc1057d139d281bbdaf8b210de","SPEC_ALL_closed_type_variable_alpha_only",e5_normal_flags);
("definition","e5_rf_clear","e5_rf_clear (s:x86state) = write (rflags :> bitelement 16) F s","fa86e7e7f34ee37f9415323b17fbb2b979693c8bf4161417d7352a642882cfec","SPEC_ALL_closed_type_variable_alpha_only",e5_rf_clear);
("definition","e5_rf_retired_step","e5_rf_retired_step (s:x86state) t <=>\n    ?u. x86 s u /\\ t=e5_rf_clear u","a0be86aab579d9edd5fd1d090e1781bcf82811bb24575b6c76775dde06534640","SPEC_ALL_closed_type_variable_alpha_only",e5_rf_retired_step);
("definition","e5_rf_retired_extended_step","e5_rf_retired_extended_step (s:x86state,a:abi_omitted_state) t <=>\n    ?u b. abi_caller_scalar_extended_step (s,a) (u,b) /\\\n          t=(e5_rf_clear u,b)","85b06f3ac1f6d95cf84e78a288532e170440fe6501a5e4d89acb9d6503e8fc33","SPEC_ALL_closed_type_variable_alpha_only",e5_rf_retired_extended_step);
("definition","e5_normal_step_policy","e5_normal_step_policy (C:num->x86state->x86state->bool) k s t <=>\n    C k s t /\\ e5_normal_flags s /\\ e5_normal_flags t","419a6a73e92f3be3078991ca6e3c633737fcfbf6625ba3ee541f309591052116","SPEC_ALL_closed_type_variable_alpha_only",e5_normal_step_policy);
("definition","e5_normal_environment","e5_normal_environment long_mode cpl (dr7:int64) cet_enabled\n      external_event_delivered debug_agent_modified <=>\n    long_mode /\\ cpl=3 /\\\n    (!i. i<8 ==> ~bit i dr7) /\\ ~cet_enabled /\\\n    ~external_event_delivered /\\ ~debug_agent_modified","58f9a3c744345c969e9060652e727095b41b61139f918265ce4de51fa1b852ab","SPEC_ALL_closed_type_variable_alpha_only",e5_normal_environment);
("definition","e5_rf_checked_run","(e5_rf_checked_run 0 (P:x86state->bool)\n      (C:num->x86state->x86state->bool) s <=> P s) /\\\n  (e5_rf_checked_run (SUC n) P C s <=>\n     (?t. e5_rf_retired_step s t) /\\\n     !t. e5_rf_retired_step s t ==> C (SUC n) s t /\\\n                                      e5_rf_checked_run n P C t)","406f90c895f09f16a7881a3eb0a4489dbe2efc8b5bfd009741ca51637d85f914","SPEC_ALL_closed_type_variable_alpha_only",c3_fresh_rf_checked_run_closed)
];;
let c3_fresh_checked_rows=List.map(fun(kind,name,literal,digest,mode,th)->
 if hyp th<>[] || frees(concl th)<>[] then failwith(name^":hyp/free variables");
 if axioms()<>fresh_initial_axioms || axioms()<>[INFINITY_AX;SELECT_AX;ETA_AX]
 then failwith(name^":axioms changed");
 let expected=parse_term literal in
 let actual=if kind="object" then concl th else concl(SPEC_ALL th) in
 let normalize tm=c3_fresh_close(c3_fresh_typealpha tm) in
 let matches=if kind="object" then aconv actual expected else
   aconv(normalize actual)(normalize expected) in
 if not matches then failwith(name^":original literal mismatch");
 (* Exclude recursive run equations and the definition's own LHS rewrite.
    Every supporting definition is independently anchored by the rows above. *)
 let rules=List.map snd(List.filter(fun(n,_)->n<>name && n<>"e5_rf_checked_run")
   c3_fresh_definition_rules) in
 let expanded=rhs(concl(REWRITE_CONV rules actual)) in
 let expected_expanded=rhs(concl(REWRITE_CONV rules expected)) in
 if not(aconv(normalize expanded)(normalize expected_expanded))
 then failwith(name^":expanded definition mismatch");
 print_endline("C3_FRESH_ACTUAL_OBJECT_CHECKED "^name);
 "{\"kind\":"^c3_fresh_json kind^",\"name\":"^c3_fresh_json name^
 ",\"expected_literal_sha256\":"^c3_fresh_json digest^
 ",\"comparison\":"^c3_fresh_json mode^
 ",\"hypothesis_count\":0,\"free_variable_count\":0,\"new_axioms\":0,\"literal_match\":true,"^
 "\"expanded_match\":true,\"conclusion\":"^c3_fresh_json(string_of_term(concl th))^
 ",\"expanded_conclusion\":"^c3_fresh_json(string_of_term expanded)^"}")c3_fresh_rows;;
if Sys.file_exists "/output/c3-development-target-handoff-v1.json" then failwith "C3_FRESH_OUTPUT_ALREADY_EXISTS";;
let c3_fresh_audit_channel=open_out "/output/c3-development-target-handoff-v1.json";;
output_string c3_fresh_audit_channel
 ("{\"schema\": \"c3-development-partial-live-audit-v1\", \"theorem_count\": 1, \"original_target_count\": 1, \"witness_target_count\": 0, \"nonvacuity_case_count\": 0, \"definition_count\": 47, \"initial_axiom_count\": 3, \"final_axiom_count\": 3, \"axioms_unchanged\": true, \"standard_axioms\": [\"INFINITY_AX\", \"SELECT_AX\", \"ETA_AX\"],\"rows\":["^String.concat "," c3_fresh_checked_rows^"]}\n");;
close_out c3_fresh_audit_channel;;
print_endline "C3_DEVELOPMENT_HANDOFF_AND_ALL_FROZEN_DEFINITIONS_LIVE_AUDIT_PASS_NOT_ACCEPTANCE";;
