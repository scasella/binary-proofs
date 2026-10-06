(* Generic proof automation only. No library byte arrays, callee execution
   rules, target-specific offsets, event interpreter or assumed interfaces.
   Clients supply a kernel-checked execution-rule array and a policy tactic.
   The policy applies to EVERY original x86 successor; progress is separate. *)
let CLIENT_CHECKED_RUN_STEP = prove
 (`!n P C s. assurance_checked_run (1+n) P C s <=>
     (?s'. x86 s s') /\
     !s'. x86 s s' ==> C (1+n) s s' /\
                        assurance_checked_run n P C s'`,
  REWRITE_TAC[ARITH_RULE `1+n = SUC n`; assurance_checked_run]);;

let CLIENT_CHECKED_BASIC_STEP_TAC execute_conv decode_ths sname policy_tac
    (asl,w) =
  let _,args = strip_comb w in
  let stepn = dest_numeral(hd args) in
  if stepn <=/ num 0 then failwith "CLIENT_CHECKED_BASIC_STEP_TAC: positive count required";
  let count = stepn -/ num 1 in
  let n_th = GSYM(NUM_ADD_CONV(mk_binary "+" (`1:num`,mk_numeral count))) in
  let sv = last args and sv' = mk_var(sname,`:x86state`) in
  let eth = execute_conv decode_ths (map snd asl)
      (mk_comb(mk_comb(`x86`,sv),sv')) in
  (GEN_REWRITE_TAC
     (RATOR_CONV o RATOR_CONV o RATOR_CONV o RAND_CONV) [n_th] THEN
   GEN_REWRITE_TAC I [CLIENT_CHECKED_RUN_STEP] THEN CONJ_TAC THENL
    [GEN_REWRITE_TAC BINDER_CONV [eth] THEN
     CONV_TAC EXISTS_NONTRIVIAL_CONV;
     X_GEN_TAC sv' THEN DISCH_THEN(fun original_step ->
       MP_TAC(EQ_MP eth original_step) THEN
       REPEAT X86_UNDEFINED_CHOOSE_TAC THEN
       DISCH_THEN(fun update -> CONJ_TAC THENL
        [policy_tac original_step update;
         MP_TAC update]))]) (asl,w);;
