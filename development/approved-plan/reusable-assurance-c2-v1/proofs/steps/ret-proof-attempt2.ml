(* New C2 proof-level adapters for O5; no generic export is changed. *)
let C2_ORIGINAL_RET =
 let pth = prove
  (`read RIP (s:x86state)=word pc ==> x86_decode s (word pc) (n,instr) ==>
    (x86 s t <=> (RIP := word(pc+n) ,, x86_execute instr) s t)`,
   REPEAT STRIP_TAC THEN REWRITE_TAC[x86] THEN
   ASM_REWRITE_TAC[GSYM WORD_ADD] THEN
   ASM_MESON_TAC[PAIR_EQ;x86_decode_unique]) in
 prove(c2_original_ret_statement,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  let step = MATCH_MP (MATCH_MP pth
    (ASSUME `read RIP (s:x86state)=word pc`))
    (ASSUME `x86_decode s (word pc) (1,RET)`) in
  let step = EQ_MP step (ASSUME `x86 (s:x86state) t`) in
  REWRITE_TAC[assurance_actual_ret] THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    MP_TAC step THEN ASM_REWRITE_TAC[assoc "RET" X86_EXECUTE_CASES;GSYM WORD_ADD;ETA_AX]]);;
let C2_SEGMENT_TO_FINAL_POLICY = prove
 (c2_segment_to_final_policy_statement,
  REWRITE_TAC[c2_segment_policy;c2_step_policy] THEN MESON_TAC[]);;
