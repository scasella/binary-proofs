(* Conservative observed-transition bridge. Development evidence only.
   The relation does not filter any successor of the pinned x86 relation.
   Event deltas are meaningful only after the separate append-prefix property
   has been established; exception semantics can overwrite the events field. *)

let assurance_delta = new_definition
 `assurance_delta (s:x86state) (s':x86state) =
    @d:uarch_event list. read events s' = APPEND d (read events s)`;;

let assurance_observation = new_definition
 `assurance_observation (s:x86state) (len:num) (inst:instruction) (s':x86state) =
    (read RIP s,len,inst,REVERSE(assurance_delta s s'))`;;

let assurance_observed_step = new_definition
 `assurance_observed_step (s:x86state)
      (obs:int64#num#instruction#uarch_event list) (s':x86state) <=>
    ?len inst.
      x86_decode s (read RIP s) (len,inst) /\
      (RIP := word_add (read RIP s) (word len) ,,
       x86_execute inst) s s' /\
      obs = assurance_observation s len inst s'`;;

let ASSURANCE_OBSERVED_PROJECTION = prove
 (`!s obs s'. assurance_observed_step s obs s' ==> x86 s s'`,
  REWRITE_TAC[assurance_observed_step; x86] THEN MESON_TAC[]);;

let ASSURANCE_OBSERVED_BACKLIFT_ALL = prove
 (`!s s'. x86 s s' ==> ?obs. assurance_observed_step s obs s'`,
  REWRITE_TAC[assurance_observed_step; x86] THEN MESON_TAC[]);;

let ASSURANCE_OBSERVED_EQUIVALENCE = prove
 (`!s s'. (?obs. assurance_observed_step s obs s') <=> x86 s s'`,
  MESON_TAC[ASSURANCE_OBSERVED_PROJECTION;
            ASSURANCE_OBSERVED_BACKLIFT_ALL]);;

let ASSURANCE_OBSERVED_PROGRESS = prove
 (`!s. (?s'. x86 s s') <=> ?obs s'. assurance_observed_step s obs s'`,
  MESON_TAC[ASSURANCE_OBSERVED_EQUIVALENCE]);;

let ASSURANCE_OBSERVED_FETCH_CORRESPONDENCE = prove
 (`!s ip len inst es s'.
    assurance_observed_step s (ip,len,inst,es) s'
    ==> ip = read RIP s /\
        x86_decode s ip (len,inst) /\
        (?l. bytes_loaded s ip l /\ LENGTH l = len /\
             decode l = SOME(inst,[]))`,
  REWRITE_TAC[assurance_observed_step; assurance_observation;
              PAIR_EQ; x86_decode] THEN MESON_TAC[]);;

let ASSURANCE_DELTA_EXACT = prove
 (`!s s' d. read events s' = APPEND d (read events s)
             ==> assurance_delta s s' = d`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[assurance_delta] THEN
  MATCH_MP_TAC SELECT_UNIQUE THEN GEN_TAC THEN
  ASM_REWRITE_TAC[APPEND_RCANCEL] THEN MESON_TAC[]);;

let ASSURANCE_OBSERVATION_EVENT_ORDER = prove
 (`!s s' len inst d.
    read events s' = APPEND d (read events s)
    ==> assurance_observation s len inst s' =
        (read RIP s,len,inst,REVERSE d)`,
  SIMP_TAC[assurance_observation; ASSURANCE_DELTA_EXACT]);;

let ASSURANCE_DELTA_CONCATENATION = prove
 (`!s0 s1 s2 d1 d2.
    read events s1 = APPEND d1 (read events s0) /\
    read events s2 = APPEND d2 (read events s1)
    ==> assurance_delta s0 s2 = APPEND d2 d1 /\
        REVERSE(assurance_delta s0 s2) =
          APPEND (REVERSE d1) (REVERSE d2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `assurance_delta s0 s2 = APPEND d2 d1` ASSUME_TAC THENL
   [MATCH_MP_TAC ASSURANCE_DELTA_EXACT THEN
    ASM_REWRITE_TAC[APPEND_ASSOC];
    ASM_REWRITE_TAC[REVERSE_APPEND]]);;

(* Same universal-successor eventuality, without throwing away deadlocks or
   nondeterministic choices. This is a relation equality, not a new prover. *)
let ASSURANCE_EVENTUALLY_CORRESPONDENCE = prove
 (`!P s. eventually (\a b. ?obs. assurance_observed_step a obs b) P s
           <=> eventually x86 P s`,
  REWRITE_TAC[ASSURANCE_OBSERVED_EQUIVALENCE; ETA_AX]);;

let assurance_actual_ret = new_definition
 `assurance_actual_ret len (s:x86state) (s':x86state) <=>
    x86_decode s (read RIP s) (len,RET) /\
    (RIP := word_add (read RIP s) (word len) ,, x86_RET) s s'`;;

let ASSURANCE_EXECUTE_RET = prove
 (`x86_execute RET = x86_RET`,
  REWRITE_TAC[FUN_EQ_THM; x86_execute]);;

let ASSURANCE_ACTUAL_RET_PROJECTION = prove
 (`!len s s'. assurance_actual_ret len s s' ==> x86 s s'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[assurance_actual_ret; x86] THEN
  STRIP_TAC THEN EXISTS_TAC `len:num` THEN EXISTS_TAC `RET` THEN
  ASM_REWRITE_TAC[ASSURANCE_EXECUTE_RET]);;

let ASSURANCE_ACTUAL_RET_EFFECTS = prove
 (`!len s s'. assurance_actual_ret len s s'
    ==> read RSP s' = word_add (read RSP s) (word 8) /\
        read RIP s' = read (memory :> bytes64 (read RSP s)) s /\
        read events s' = APPEND
          [EventJump(word_add (read RIP s) (word len),
                     read (memory :> bytes64 (read RSP s)) s);
           EventLoad(read RSP s,8)] (read events s)`,
  REWRITE_TAC[assurance_actual_ret; SEQ; x86_RET;
              LET_DEF; LET_END_DEF; assign] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[APPEND] THEN
  CONV_TAC(DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV) THEN
  REWRITE_TAC[]);;

let ASSURANCE_ACTUAL_RET_OBSERVATION = prove
 (`!len s s'. assurance_actual_ret len s s'
    ==> assurance_observation s len RET s' =
        (read RIP s,len,RET,
         [EventLoad(read RSP s,8);
          EventJump(word_add (read RIP s) (word len),
                    read (memory :> bytes64 (read RSP s)) s)])`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP ASSURANCE_ACTUAL_RET_EFFECTS) THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP ASSURANCE_DELTA_EXACT) THEN
  ASM_REWRITE_TAC[assurance_observation; REVERSE; APPEND]);;

let ASSURANCE_DECODED_RET_ALL_SUCCESSORS = prove
 (`!len s. x86_decode s (read RIP s) (len,RET)
    ==> !s'. x86 s s' ==> assurance_actual_ret len s s'`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN
  REWRITE_TAC[x86] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num`
    (X_CHOOSE_THEN `inst:instruction` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `(n:num) = (len:num) /\ inst = RET`
    (CONJUNCTS_THEN SUBST_ALL_TAC) THENL
   [MP_TAC(ISPECL [`s:x86state`; `read RIP s`; `(len:num,RET)`;
                   `(n:num,inst:instruction)`] x86_decode_unique) THEN
    ASM_REWRITE_TAC[PAIR_EQ] THEN MESON_TAC[];
    RULE_ASSUM_TAC(REWRITE_RULE[ASSURANCE_EXECUTE_RET]) THEN
    ASM_REWRITE_TAC[assurance_actual_ret]]);;

let ASSURANCE_DECODED_RET_PROGRESS = prove
 (`!len s. x86_decode s (read RIP s) (len,RET)
    ==> ?s'. assurance_actual_ret len s s'`,
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[assurance_actual_ret; SEQ; x86_RET;
                  LET_DEF; LET_END_DEF; assign] THEN
  MESON_TAC[]);;
