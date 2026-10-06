(* Exact frozen C3 saved bindings transport. Every byte component below is
   fixed by the caller obligation; no universal integration lemma or tactic
   is introduced. All full original antecedents and alias domain are retained. *)
let C3_CLEANSE_SAVED_BINDINGS = prove
 (`!lib_file lib_rw lib_padding client_file client_rw client_padding
 stackpointer ra p q n m rp wp xp ordinary initial a entry returned.
 c3_pre lib_file lib_rw lib_padding client_file client_rw client_padding
   stackpointer ra p q n m rp wp xp ordinary(initial,a) /\
 c3_saved_prefix stackpointer p q n m initial entry /\
 bp_e2_cleanse_call_post 0x102417d0(word_sub stackpointer(word 48))
   (word 0x2300114c)p n(read memory entry)entry returned
 ==> read(memory :> bytes64(word_sub stackpointer(word 8)))returned=read R13 initial /\
     read(memory :> bytes64(word_sub stackpointer(word 16)))returned=read R12 initial /\
     read(memory :> bytes64(word_sub stackpointer(word 24)))returned=read RBP initial /\
     read(memory :> bytes64(word_sub stackpointer(word 32)))returned=read RBX initial /\
     read(memory :> bytes64 stackpointer)returned=ra /\
     c3_loaded_code returned /\ c3_got returned`,
 REPEAT GEN_TAC THEN STRIP_TAC THEN
 MP_TAC(ISPECL[`lib_file:num->byte`;`lib_rw:int64->byte`;`lib_padding:int64->byte`;
   `client_file:num->byte`;`client_rw:int64->byte`;`client_padding:int64->byte`;
   `stackpointer:int64`;`ra:int64`;`p:int64`;`q:int64`;`n:num`;`m:int64->byte`;
   `rp:num->bool`;`wp:num->bool`;`xp:num->bool`;`ordinary:num->bool`;
   `initial:x86state`;`a:abi_omitted_state`;`entry:x86state`]
   C3_TRANSPORT_INCOMING_RA_ENTRY) THEN
 ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
 UNDISCH_TAC `c3_pre lib_file lib_rw lib_padding client_file client_rw client_padding
   stackpointer ra p q n m rp wp xp ordinary(initial,a)` THEN
 REWRITE_TAC[c3_pre] THEN STRIP_TAC THEN
 UNDISCH_TAC `c3_saved_prefix stackpointer p q n m (initial:x86state)(entry:x86state)` THEN
 REWRITE_TAC[c3_saved_prefix] THEN STRIP_TAC THEN
 UNDISCH_TAC `bp_e2_cleanse_call_post 0x102417d0(word_sub(stackpointer:int64)(word 48))
   (word 0x2300114c)p n(read memory(entry:x86state))entry returned` THEN
 REWRITE_TAC[bp_e2_cleanse_call_post] THEN STRIP_TAC THEN
 SUBGOAL_THEN
  `read(bytes(word_sub(stackpointer:int64)(word 8),8))(read memory(returned:x86state))=
   read(bytes(word_sub(stackpointer:int64)(word 8),8))(read memory(entry:x86state))` ASSUME_TAC THENL
 [REWRITE_TAC[READ_BYTES_EQ] THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `c3_scratch(stackpointer:int64)(val(word_add(word_sub(stackpointer:int64)(word 8))(word j)))` ASSUME_TAC THENL
  [MP_TAC(ISPEC `stackpointer:int64` C3_TRANSPORT_SAVED_R13_BYTE_GEOMETRY) THEN
   ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `j:num`) THEN ASM_REWRITE_TAC[];ALL_TAC] THEN
  SUBGOAL_THEN `~assurance_region(p:int64)n(val(word_add(word_sub(stackpointer:int64)(word 8))(word j)))`
    ASSUME_TAC THENL
  [DISCH_TAC THEN MP_TAC(SPEC `val(word_add(word_sub(stackpointer:int64)(word 8))(word j))`
    (ASSUME `!addr. ~(assurance_region(p:int64)n addr /\ c3_scratch stackpointer addr)`)) THEN ASM_REWRITE_TAC[];
   MATCH_ACCEPT_TAC(MATCH_MP(SPEC `word_add(word_sub(stackpointer:int64)(word 8))(word j)`
     (ASSUME `!addr:int64. ~assurance_region p n(val addr)
    ==> read memory(returned:x86state)addr=read memory(entry:x86state)addr`))
     (ASSUME `~assurance_region(p:int64)n(val(word_add(word_sub(stackpointer:int64)(word 8))(word j)))`))];
  ALL_TAC] THEN
 SUBGOAL_THEN
  `read(bytes(word_sub(stackpointer:int64)(word 16),8))(read memory(returned:x86state))=
   read(bytes(word_sub(stackpointer:int64)(word 16),8))(read memory(entry:x86state))` ASSUME_TAC THENL
 [REWRITE_TAC[READ_BYTES_EQ] THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `c3_scratch(stackpointer:int64)(val(word_add(word_sub(stackpointer:int64)(word 16))(word j)))` ASSUME_TAC THENL
  [MP_TAC(ISPEC `stackpointer:int64` C3_TRANSPORT_SAVED_R12_BYTE_GEOMETRY) THEN
   ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `j:num`) THEN ASM_REWRITE_TAC[];ALL_TAC] THEN
  SUBGOAL_THEN `~assurance_region(p:int64)n(val(word_add(word_sub(stackpointer:int64)(word 16))(word j)))`
    ASSUME_TAC THENL
  [DISCH_TAC THEN MP_TAC(SPEC `val(word_add(word_sub(stackpointer:int64)(word 16))(word j))`
    (ASSUME `!addr. ~(assurance_region(p:int64)n addr /\ c3_scratch stackpointer addr)`)) THEN ASM_REWRITE_TAC[];
   MATCH_ACCEPT_TAC(MATCH_MP(SPEC `word_add(word_sub(stackpointer:int64)(word 16))(word j)`
     (ASSUME `!addr:int64. ~assurance_region p n(val addr)
    ==> read memory(returned:x86state)addr=read memory(entry:x86state)addr`))
     (ASSUME `~assurance_region(p:int64)n(val(word_add(word_sub(stackpointer:int64)(word 16))(word j)))`))];
  ALL_TAC] THEN
 SUBGOAL_THEN
  `read(bytes(word_sub(stackpointer:int64)(word 24),8))(read memory(returned:x86state))=
   read(bytes(word_sub(stackpointer:int64)(word 24),8))(read memory(entry:x86state))` ASSUME_TAC THENL
 [REWRITE_TAC[READ_BYTES_EQ] THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `c3_scratch(stackpointer:int64)(val(word_add(word_sub(stackpointer:int64)(word 24))(word j)))` ASSUME_TAC THENL
  [MP_TAC(ISPEC `stackpointer:int64` C3_TRANSPORT_SAVED_RBP_BYTE_GEOMETRY) THEN
   ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `j:num`) THEN ASM_REWRITE_TAC[];ALL_TAC] THEN
  SUBGOAL_THEN `~assurance_region(p:int64)n(val(word_add(word_sub(stackpointer:int64)(word 24))(word j)))`
    ASSUME_TAC THENL
  [DISCH_TAC THEN MP_TAC(SPEC `val(word_add(word_sub(stackpointer:int64)(word 24))(word j))`
    (ASSUME `!addr. ~(assurance_region(p:int64)n addr /\ c3_scratch stackpointer addr)`)) THEN ASM_REWRITE_TAC[];
   MATCH_ACCEPT_TAC(MATCH_MP(SPEC `word_add(word_sub(stackpointer:int64)(word 24))(word j)`
     (ASSUME `!addr:int64. ~assurance_region p n(val addr)
    ==> read memory(returned:x86state)addr=read memory(entry:x86state)addr`))
     (ASSUME `~assurance_region(p:int64)n(val(word_add(word_sub(stackpointer:int64)(word 24))(word j)))`))];
  ALL_TAC] THEN
 SUBGOAL_THEN
  `read(bytes(word_sub(stackpointer:int64)(word 32),8))(read memory(returned:x86state))=
   read(bytes(word_sub(stackpointer:int64)(word 32),8))(read memory(entry:x86state))` ASSUME_TAC THENL
 [REWRITE_TAC[READ_BYTES_EQ] THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `c3_scratch(stackpointer:int64)(val(word_add(word_sub(stackpointer:int64)(word 32))(word j)))` ASSUME_TAC THENL
  [MP_TAC(ISPEC `stackpointer:int64` C3_TRANSPORT_SAVED_RBX_BYTE_GEOMETRY) THEN
   ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `j:num`) THEN ASM_REWRITE_TAC[];ALL_TAC] THEN
  SUBGOAL_THEN `~assurance_region(p:int64)n(val(word_add(word_sub(stackpointer:int64)(word 32))(word j)))`
    ASSUME_TAC THENL
  [DISCH_TAC THEN MP_TAC(SPEC `val(word_add(word_sub(stackpointer:int64)(word 32))(word j))`
    (ASSUME `!addr. ~(assurance_region(p:int64)n addr /\ c3_scratch stackpointer addr)`)) THEN ASM_REWRITE_TAC[];
   MATCH_ACCEPT_TAC(MATCH_MP(SPEC `word_add(word_sub(stackpointer:int64)(word 32))(word j)`
     (ASSUME `!addr:int64. ~assurance_region p n(val addr)
    ==> read memory(returned:x86state)addr=read memory(entry:x86state)addr`))
     (ASSUME `~assurance_region(p:int64)n(val(word_add(word_sub(stackpointer:int64)(word 32))(word j)))`))];
  ALL_TAC] THEN
 SUBGOAL_THEN
  `read(bytes(stackpointer:int64,8))(read memory(returned:x86state))=
   read(bytes(stackpointer:int64,8))(read memory(entry:x86state))` ASSUME_TAC THENL
 [REWRITE_TAC[READ_BYTES_EQ] THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `assurance_region(stackpointer:int64)8(val(word_add(stackpointer:int64)(word j)))` ASSUME_TAC THENL
  [MP_TAC(ISPEC `stackpointer:int64` C3_TRANSPORT_INCOMING_RA_BYTE_GEOMETRY) THEN
   ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `j:num`) THEN
   ASM_REWRITE_TAC[] THEN DISCH_THEN(ACCEPT_TAC o CONJUNCT2);ALL_TAC] THEN
  SUBGOAL_THEN `~assurance_region(p:int64)n(val(word_add(stackpointer:int64)(word j)))`
    ASSUME_TAC THENL
  [DISCH_TAC THEN MP_TAC(SPEC `val(word_add(stackpointer:int64)(word j))`
    (ASSUME `!addr. ~(assurance_region(p:int64)n addr /\ assurance_region stackpointer 8 addr)`)) THEN ASM_REWRITE_TAC[];
   MATCH_ACCEPT_TAC(MATCH_MP(SPEC `word_add(stackpointer:int64)(word j)`
     (ASSUME `!addr:int64. ~assurance_region p n(val addr)
    ==> read memory(returned:x86state)addr=read memory(entry:x86state)addr`))
     (ASSUME `~assurance_region(p:int64)n(val(word_add(stackpointer:int64)(word j)))`))];
  ALL_TAC] THEN
 SUBGOAL_THEN
  `read(bytes(word 0x23001120:int64,89))(read memory(returned:x86state))=
   read(bytes(word 0x23001120:int64,89))(read memory(entry:x86state))` ASSUME_TAC THENL
 [REWRITE_TAC[READ_BYTES_EQ] THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `assurance_region(word 0x23001120:int64)89(val(word_add(word 0x23001120:int64)(word j)))` ASSUME_TAC THENL
  [MATCH_MP_TAC C3_TRANSPORT_CALLER_CODE_BYTE_GEOMETRY THEN ASM_REWRITE_TAC[];ALL_TAC] THEN
  SUBGOAL_THEN `~assurance_region(p:int64)n(val(word_add(word 0x23001120:int64)(word j)))`
    ASSUME_TAC THENL
  [DISCH_TAC THEN MP_TAC(SPEC `val(word_add(word 0x23001120:int64)(word j))`
    (ASSUME `!addr. assurance_region(p:int64)n addr ==>
      ~(assurance_region(word 0x23001120)89 addr \/
        assurance_region(word 0x23001030)6 addr \/
        assurance_region(word 0x23001040)6 addr \/
        assurance_region(word 0x23003fd0)8 addr \/
        assurance_region(word 0x23003fd8)8 addr \/
        assurance_region(word 0x10241840)95 addr \/
        assurance_region(word 0x102417d0)97 addr)`)) THEN ASM_REWRITE_TAC[];
   MATCH_ACCEPT_TAC(MATCH_MP(SPEC `word_add(word 0x23001120:int64)(word j)`
     (ASSUME `!addr:int64. ~assurance_region p n(val addr)
    ==> read memory(returned:x86state)addr=read memory(entry:x86state)addr`))
     (ASSUME `~assurance_region(p:int64)n(val(word_add(word 0x23001120:int64)(word j)))`))];
  ALL_TAC] THEN
 SUBGOAL_THEN
  `read(bytes(word 0x23001030:int64,6))(read memory(returned:x86state))=
   read(bytes(word 0x23001030:int64,6))(read memory(entry:x86state))` ASSUME_TAC THENL
 [REWRITE_TAC[READ_BYTES_EQ] THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `assurance_region(word 0x23001030:int64)6(val(word_add(word 0x23001030:int64)(word j)))` ASSUME_TAC THENL
  [MATCH_MP_TAC C3_TRANSPORT_CRYPTO_PLT_BYTE_GEOMETRY THEN ASM_REWRITE_TAC[];ALL_TAC] THEN
  SUBGOAL_THEN `~assurance_region(p:int64)n(val(word_add(word 0x23001030:int64)(word j)))`
    ASSUME_TAC THENL
  [DISCH_TAC THEN MP_TAC(SPEC `val(word_add(word 0x23001030:int64)(word j))`
    (ASSUME `!addr. assurance_region(p:int64)n addr ==>
      ~(assurance_region(word 0x23001120)89 addr \/
        assurance_region(word 0x23001030)6 addr \/
        assurance_region(word 0x23001040)6 addr \/
        assurance_region(word 0x23003fd0)8 addr \/
        assurance_region(word 0x23003fd8)8 addr \/
        assurance_region(word 0x10241840)95 addr \/
        assurance_region(word 0x102417d0)97 addr)`)) THEN ASM_REWRITE_TAC[];
   MATCH_ACCEPT_TAC(MATCH_MP(SPEC `word_add(word 0x23001030:int64)(word j)`
     (ASSUME `!addr:int64. ~assurance_region p n(val addr)
    ==> read memory(returned:x86state)addr=read memory(entry:x86state)addr`))
     (ASSUME `~assurance_region(p:int64)n(val(word_add(word 0x23001030:int64)(word j)))`))];
  ALL_TAC] THEN
 SUBGOAL_THEN
  `read(bytes(word 0x23001040:int64,6))(read memory(returned:x86state))=
   read(bytes(word 0x23001040:int64,6))(read memory(entry:x86state))` ASSUME_TAC THENL
 [REWRITE_TAC[READ_BYTES_EQ] THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `assurance_region(word 0x23001040:int64)6(val(word_add(word 0x23001040:int64)(word j)))` ASSUME_TAC THENL
  [MATCH_MP_TAC C3_TRANSPORT_CLEANSE_PLT_BYTE_GEOMETRY THEN ASM_REWRITE_TAC[];ALL_TAC] THEN
  SUBGOAL_THEN `~assurance_region(p:int64)n(val(word_add(word 0x23001040:int64)(word j)))`
    ASSUME_TAC THENL
  [DISCH_TAC THEN MP_TAC(SPEC `val(word_add(word 0x23001040:int64)(word j))`
    (ASSUME `!addr. assurance_region(p:int64)n addr ==>
      ~(assurance_region(word 0x23001120)89 addr \/
        assurance_region(word 0x23001030)6 addr \/
        assurance_region(word 0x23001040)6 addr \/
        assurance_region(word 0x23003fd0)8 addr \/
        assurance_region(word 0x23003fd8)8 addr \/
        assurance_region(word 0x10241840)95 addr \/
        assurance_region(word 0x102417d0)97 addr)`)) THEN ASM_REWRITE_TAC[];
   MATCH_ACCEPT_TAC(MATCH_MP(SPEC `word_add(word 0x23001040:int64)(word j)`
     (ASSUME `!addr:int64. ~assurance_region p n(val addr)
    ==> read memory(returned:x86state)addr=read memory(entry:x86state)addr`))
     (ASSUME `~assurance_region(p:int64)n(val(word_add(word 0x23001040:int64)(word j)))`))];
  ALL_TAC] THEN
 SUBGOAL_THEN
  `read(bytes(word 0x23003fd0:int64,8))(read memory(returned:x86state))=
   read(bytes(word 0x23003fd0:int64,8))(read memory(entry:x86state))` ASSUME_TAC THENL
 [REWRITE_TAC[READ_BYTES_EQ] THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `assurance_region(word 0x23003fd0:int64)8(val(word_add(word 0x23003fd0:int64)(word j)))` ASSUME_TAC THENL
  [MATCH_MP_TAC C3_TRANSPORT_CRYPTO_GOT_BYTE_GEOMETRY THEN ASM_REWRITE_TAC[];ALL_TAC] THEN
  SUBGOAL_THEN `~assurance_region(p:int64)n(val(word_add(word 0x23003fd0:int64)(word j)))`
    ASSUME_TAC THENL
  [DISCH_TAC THEN MP_TAC(SPEC `val(word_add(word 0x23003fd0:int64)(word j))`
    (ASSUME `!addr. assurance_region(p:int64)n addr ==>
      ~(assurance_region(word 0x23001120)89 addr \/
        assurance_region(word 0x23001030)6 addr \/
        assurance_region(word 0x23001040)6 addr \/
        assurance_region(word 0x23003fd0)8 addr \/
        assurance_region(word 0x23003fd8)8 addr \/
        assurance_region(word 0x10241840)95 addr \/
        assurance_region(word 0x102417d0)97 addr)`)) THEN ASM_REWRITE_TAC[];
   MATCH_ACCEPT_TAC(MATCH_MP(SPEC `word_add(word 0x23003fd0:int64)(word j)`
     (ASSUME `!addr:int64. ~assurance_region p n(val addr)
    ==> read memory(returned:x86state)addr=read memory(entry:x86state)addr`))
     (ASSUME `~assurance_region(p:int64)n(val(word_add(word 0x23003fd0:int64)(word j)))`))];
  ALL_TAC] THEN
 SUBGOAL_THEN
  `read(bytes(word 0x23003fd8:int64,8))(read memory(returned:x86state))=
   read(bytes(word 0x23003fd8:int64,8))(read memory(entry:x86state))` ASSUME_TAC THENL
 [REWRITE_TAC[READ_BYTES_EQ] THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `assurance_region(word 0x23003fd8:int64)8(val(word_add(word 0x23003fd8:int64)(word j)))` ASSUME_TAC THENL
  [MATCH_MP_TAC C3_TRANSPORT_CLEANSE_GOT_BYTE_GEOMETRY THEN ASM_REWRITE_TAC[];ALL_TAC] THEN
  SUBGOAL_THEN `~assurance_region(p:int64)n(val(word_add(word 0x23003fd8:int64)(word j)))`
    ASSUME_TAC THENL
  [DISCH_TAC THEN MP_TAC(SPEC `val(word_add(word 0x23003fd8:int64)(word j))`
    (ASSUME `!addr. assurance_region(p:int64)n addr ==>
      ~(assurance_region(word 0x23001120)89 addr \/
        assurance_region(word 0x23001030)6 addr \/
        assurance_region(word 0x23001040)6 addr \/
        assurance_region(word 0x23003fd0)8 addr \/
        assurance_region(word 0x23003fd8)8 addr \/
        assurance_region(word 0x10241840)95 addr \/
        assurance_region(word 0x102417d0)97 addr)`)) THEN ASM_REWRITE_TAC[];
   MATCH_ACCEPT_TAC(MATCH_MP(SPEC `word_add(word 0x23003fd8:int64)(word j)`
     (ASSUME `!addr:int64. ~assurance_region p n(val addr)
    ==> read memory(returned:x86state)addr=read memory(entry:x86state)addr`))
     (ASSUME `~assurance_region(p:int64)n(val(word_add(word 0x23003fd8:int64)(word j)))`))];
  ALL_TAC] THEN
 SUBGOAL_THEN
  `read(bytes(word 0x10241840:int64,95))(read memory(returned:x86state))=
   read(bytes(word 0x10241840:int64,95))(read memory(entry:x86state))` ASSUME_TAC THENL
 [REWRITE_TAC[READ_BYTES_EQ] THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `assurance_region(word 0x10241840:int64)95(val(word_add(word 0x10241840:int64)(word j)))` ASSUME_TAC THENL
  [MATCH_MP_TAC C3_TRANSPORT_CRYPTO_CODE_BYTE_GEOMETRY THEN ASM_REWRITE_TAC[];ALL_TAC] THEN
  SUBGOAL_THEN `~assurance_region(p:int64)n(val(word_add(word 0x10241840:int64)(word j)))`
    ASSUME_TAC THENL
  [DISCH_TAC THEN MP_TAC(SPEC `val(word_add(word 0x10241840:int64)(word j))`
    (ASSUME `!addr. assurance_region(p:int64)n addr ==>
      ~(assurance_region(word 0x23001120)89 addr \/
        assurance_region(word 0x23001030)6 addr \/
        assurance_region(word 0x23001040)6 addr \/
        assurance_region(word 0x23003fd0)8 addr \/
        assurance_region(word 0x23003fd8)8 addr \/
        assurance_region(word 0x10241840)95 addr \/
        assurance_region(word 0x102417d0)97 addr)`)) THEN ASM_REWRITE_TAC[];
   MATCH_ACCEPT_TAC(MATCH_MP(SPEC `word_add(word 0x10241840:int64)(word j)`
     (ASSUME `!addr:int64. ~assurance_region p n(val addr)
    ==> read memory(returned:x86state)addr=read memory(entry:x86state)addr`))
     (ASSUME `~assurance_region(p:int64)n(val(word_add(word 0x10241840:int64)(word j)))`))];
  ALL_TAC] THEN
 SUBGOAL_THEN
  `read(bytes(word 0x102417d0:int64,97))(read memory(returned:x86state))=
   read(bytes(word 0x102417d0:int64,97))(read memory(entry:x86state))` ASSUME_TAC THENL
 [REWRITE_TAC[READ_BYTES_EQ] THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `assurance_region(word 0x102417d0:int64)97(val(word_add(word 0x102417d0:int64)(word j)))` ASSUME_TAC THENL
  [MATCH_MP_TAC C3_TRANSPORT_CLEANSE_CODE_BYTE_GEOMETRY THEN ASM_REWRITE_TAC[];ALL_TAC] THEN
  SUBGOAL_THEN `~assurance_region(p:int64)n(val(word_add(word 0x102417d0:int64)(word j)))`
    ASSUME_TAC THENL
  [DISCH_TAC THEN MP_TAC(SPEC `val(word_add(word 0x102417d0:int64)(word j))`
    (ASSUME `!addr. assurance_region(p:int64)n addr ==>
      ~(assurance_region(word 0x23001120)89 addr \/
        assurance_region(word 0x23001030)6 addr \/
        assurance_region(word 0x23001040)6 addr \/
        assurance_region(word 0x23003fd0)8 addr \/
        assurance_region(word 0x23003fd8)8 addr \/
        assurance_region(word 0x10241840)95 addr \/
        assurance_region(word 0x102417d0)97 addr)`)) THEN ASM_REWRITE_TAC[];
   MATCH_ACCEPT_TAC(MATCH_MP(SPEC `word_add(word 0x102417d0:int64)(word j)`
     (ASSUME `!addr:int64. ~assurance_region p n(val addr)
    ==> read memory(returned:x86state)addr=read memory(entry:x86state)addr`))
     (ASSUME `~assurance_region(p:int64)n(val(word_add(word 0x102417d0:int64)(word j)))`))];
  ALL_TAC] THEN
 RULE_ASSUM_TAC(REWRITE_RULE[c3_loaded_code;c3_got;bytes_loaded;
   READ_BYTELIST_EQ_BYTES;bytes64;READ_COMPONENT_COMPOSE;
   fst C3_CALLER_RAW_EXEC;fst C3_CRYPTO_PLT_RAW_EXEC;fst C3_CLEANSE_PLT_RAW_EXEC;
   BP_PUBLIC_CRYPTO_MEMCMP_CODE_LENGTH;BP_PUBLIC_OPENSSL_CLEANSE_CODE_LENGTH]) THEN
 REWRITE_TAC[c3_loaded_code;c3_got;bytes_loaded;READ_BYTELIST_EQ_BYTES;
   bytes64;READ_COMPONENT_COMPOSE;
   fst C3_CALLER_RAW_EXEC;fst C3_CRYPTO_PLT_RAW_EXEC;fst C3_CLEANSE_PLT_RAW_EXEC;
   BP_PUBLIC_CRYPTO_MEMCMP_CODE_LENGTH;BP_PUBLIC_OPENSSL_CLEANSE_CODE_LENGTH] THEN
 ASM_REWRITE_TAC[]);;
print_endline "C3_CLEANSE_SAVED_BINDINGS_SUCCESSOR_V1_DEVELOPMENT_CHECKED";;
