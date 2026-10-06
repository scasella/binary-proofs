(* Fixed C3 incoming caller return slot: S, distinct from cleanse's S-48.
   Named obligation: C3_CLEANSE_SAVED_BINDINGS incoming bytes64 S = ra.
   READ_BYTES_EQ is instantiated only at the frozen incoming slot width 8.
   This does not export a general pointwise/component transport theorem. *)
let C3_TRANSPORT_INCOMING_RA_BYTE_GEOMETRY = prove
 (`!stackpointer:int64. 48<=val stackpointer /\
   val stackpointer+8<2 EXP 64
   ==> !j. j<8
       ==> ~c3_scratch stackpointer(val(word_add stackpointer(word j))) /\
           assurance_region stackpointer 8(val(word_add stackpointer(word j)))`,
 REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
 SUBGOAL_THEN `j<2 EXP 64 /\ val(stackpointer:int64)+j<2 EXP 64`
   STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC;ALL_TAC] THEN
 ASM_SIMP_TAC[c3_scratch;assurance_region;C3_STACK_SUB48_VALUE;
   VAL_WORD_ADD;VAL_WORD;DIMINDEX_64;MOD_LT] THEN ASM_ARITH_TAC);;
print_endline "C3_TRANSPORT_INCOMING_RA_BYTE_GEOMETRY_CHECKED";;

let C3_TRANSPORT_INCOMING_RA_ENTRY = prove
 (`!lib_file lib_rw lib_padding client_file client_rw client_padding
 stackpointer ra p q n m rp wp xp ordinary initial a entry.
 c3_pre lib_file lib_rw lib_padding client_file client_rw client_padding
   stackpointer ra p q n m rp wp xp ordinary(initial,a) /\
 c3_saved_prefix stackpointer p q n m initial entry
 ==> read(memory :> bytes64 stackpointer)entry=ra`,
 REPEAT GEN_TAC THEN STRIP_TAC THEN
 UNDISCH_TAC `c3_pre lib_file lib_rw lib_padding client_file client_rw client_padding
   stackpointer ra p q n m rp wp xp ordinary(initial,a)` THEN
 REWRITE_TAC[c3_pre] THEN STRIP_TAC THEN
 UNDISCH_TAC `c3_saved_prefix stackpointer p q n m (initial:x86state)(entry:x86state)` THEN
 REWRITE_TAC[c3_saved_prefix] THEN STRIP_TAC THEN
 SUBGOAL_THEN
  `read(bytes(stackpointer:int64,8))(read memory(entry:x86state))=
   read(bytes(stackpointer,8))(read memory(initial:x86state))` ASSUME_TAC THENL
 [REWRITE_TAC[READ_BYTES_EQ] THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `~c3_scratch(stackpointer:int64)(val(word_add stackpointer(word j)))`
   ASSUME_TAC THENL
  [MP_TAC(ISPEC `stackpointer:int64` C3_TRANSPORT_INCOMING_RA_BYTE_GEOMETRY) THEN
   ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `j:num`) THEN
   ASM_REWRITE_TAC[] THEN DISCH_THEN(ACCEPT_TAC o CONJUNCT1);
   MATCH_ACCEPT_TAC(REWRITE_RULE[GSYM(ASSUME `read memory(initial:x86state)=m`)]
    (MATCH_MP(SPEC `word_add(stackpointer:int64)(word j)`
      (ASSUME `!addr:int64. ~c3_scratch stackpointer(val addr)
          ==> read memory(entry:x86state)addr=m addr`))
      (ASSUME `~c3_scratch(stackpointer:int64)(val(word_add stackpointer(word j)))`)))];
  UNDISCH_TAC `read(memory :> bytes64(stackpointer:int64))(initial:x86state)=ra` THEN
  ASM_REWRITE_TAC[bytes64;READ_COMPONENT_COMPOSE]]);;
print_endline "C3_TRANSPORT_INCOMING_RA_ENTRY_CHECKED";;
