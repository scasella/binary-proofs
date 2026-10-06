(* C3 local final-return obligation. Fixed source, offsets, counts and policy only.
  No supplier body execution and no change to the protected C3 predicates.
  Literal-input provenance: normalized opaque comparison posts and actual saved slots. *)
let c3_final_return_site_statement =
 `!stackpointer ra p q:int64 n m rp wp xp ordinary initial entry:x86state.
 48<=val stackpointer /\ val stackpointer+8<2 EXP 64 /\
 read RIP entry=word 0x2300115a /\ read RSP entry=word_sub stackpointer(word 40) /\
 read R13 entry=(if c3_equal m p q n then word 1 else word 0) /\
 read RAX entry=(if c3_equal(c3_cleansed_memory m p n)p q n then word 0 else word 1) /\
 read(memory :> bytes64(word_sub stackpointer(word 8)))entry=read R13 initial /\
 read(memory :> bytes64(word_sub stackpointer(word 16)))entry=read R12 initial /\
 read(memory :> bytes64(word_sub stackpointer(word 24)))entry=read RBP initial /\
 read(memory :> bytes64(word_sub stackpointer(word 32)))entry=read RBX initial /\
 read(memory :> bytes64 stackpointer)entry=ra /\
 read R14 entry=read R14 initial /\ read R15 entry=read R15 initial /\
 read DF entry=F /\ ~bit 18(read rflags entry) /\
 (!i. i<n ==> read memory entry(word_add p(word i))=word 0) /\
 (!i. i<n ==> read memory entry(word_add q(word i))=
     c3_cleansed_memory m p n(word_add q(word i))) /\
 (!addr. ~(assurance_region p n(val addr) \/ c3_scratch stackpointer(val addr))
     ==> read memory entry addr=m addr) /\
 c3_loaded_code entry /\ c3_got entry /\
 (c3_frame stackpointer p q n m ,, MAYCHANGE[RBX;RBP;R12;R13])initial entry /\
 assurance_span_ok(c3_allowed_read rp ordinary stackpointer p q n)(val stackpointer-48)48 /\
 assurance_span_ok(c3_allowed_read rp ordinary stackpointer p q n)(val stackpointer)8 /\
 assurance_span_ok(c3_allowed_fetch xp ordinary)0x23001120 89
 ==> assurance_checked_run (if c3_equal m p q n then 12 else 9)
       (c3_scalar_post stackpointer ra p q n m initial)
       (c3_step_policy stackpointer p q n m rp wp xp ordinary)entry`;;
(* This wrapper supplies literal C3 data to the frozen algorithms. *)
let C3_FINAL_RETURN_STEP_TAC remaining source target name =
 HT_CHECKED_STEP_TAC
  (HT_FINAL_POLICY_TAC
   (HT_PUBLIC_CODE_POLICY_TAC c3_segment_policy
     `c3_allowed_fetch (xp:num->bool)(ordinary:num->bool)` 89 "pc"
     (snd C3_CALLER_RAW_EXEC) C3_EVENT_SPAN_TAC)
   C3_FINAL_POLICY_BRIDGE remaining source target (snd C3_CALLER_RAW_EXEC))
  C3_CALLER_RAW_EXEC C3_CALLER_SUBTHS name;;
let C3_FINAL_RETURN_SITE_PREFIX_TAC =
 REPEAT GEN_TAC THEN REWRITE_TAC[c3_loaded_code;c3_got] THEN STRIP_TAC THEN
 ABBREV_TAC `pc=0x23001120` THEN
 SUBGOAL_THEN `read RIP(entry:x86state)=word(pc+58)` ASSUME_TAC THENL
 [EXPAND_TAC "pc" THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[];ALL_TAC] THEN
 UNDISCH_TAC `read RIP(entry:x86state)=word 0x2300115a` THEN DISCH_THEN(K ALL_TAC) THEN
 REWRITE_TAC[c3_frame] THEN
 ASM_CASES_TAC `c3_equal (m:int64->byte)(p:int64)(q:int64)n` THEN
 ASM_REWRITE_TAC[] THEN
 ASM_CASES_TAC `c3_equal(c3_cleansed_memory(m:int64->byte)(p:int64)n)p(q:int64)n` THEN
 ASM_REWRITE_TAC[];;
