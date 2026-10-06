(* Construction revision before any execution. Explicitly split the span's
   bound and quantified clause so REPEAT STRIP does not over-split THENL. *)
let R1_SECRET_SPAN_MONO = prove
 (r1_secret_span_mono_statement,
  REWRITE_TAC[assurance_span_ok] THEN MESON_TAC[]);;
let R1_SECRET_SPAN_SUBSPAN = prove
 (r1_secret_span_subspan_statement,
  REWRITE_TAC[assurance_span_ok] THEN REPEAT GEN_TAC THEN
  STRIP_TAC THEN CONJ_TAC THENL
   [ASM_ARITH_TAC;
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `off+j<n` ASSUME_TAC THENL [ASM_ARITH_TAC;ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `off+j:num`) THEN
    ASM_SIMP_TAC[ARITH_RULE `off+len<=n /\ j<len ==> off+j<n`;
                 ARITH_RULE `(a+off)+j=a+(off+j)`]]);;
let R1_SECRET_SPAN_REGION = prove
 (r1_secret_span_region_statement,
  REWRITE_TAC[assurance_span_ok;assurance_region] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN ASM_ARITH_TAC);;
