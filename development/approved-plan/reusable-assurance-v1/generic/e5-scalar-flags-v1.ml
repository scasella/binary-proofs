(* Generic instruction-semantics proof; no target byte identity or successful
   execution state is assumed. Every existing execute successor is covered. *)
let e5_gpr_cases = prove_cases_thm gpr_INDUCT;;
let e5_regsize_cases = prove_cases_thm regsize_INDUCT;;
let rec E5_ENUM_GPRS_TAC gl =
 let asl,w=gl in
 let vs=setify(List.concat(map (frees o concl o snd) asl) @ frees w) in
 try let v=find(fun v->type_of v = `:gpr` || type_of v = `:regsize`) vs in
  ((STRUCT_CASES_THEN SUBST_ALL_TAC)(SPEC v (if type_of v = `:gpr` then e5_gpr_cases else e5_regsize_cases)) THEN
   E5_ENUM_GPRS_TAC) gl
 with Failure _ -> ALL_TAC gl;;
let E5_SUBST_VAR_THM th =
 let l,r=dest_eq(concl th) in
 if is_var l then SUBST_ALL_TAC th
 else if is_var r then SUBST_ALL_TAC(SYM th)
 else failwith "E5 substitute variables only";;
let E5_FLAG_BITS_ORTHOGONAL = prove
 (`!k i. ~(k=i) ==> orthogonal_components
    (rflags :> bitelement k) (rflags :> bitelement i)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC ORTHOGONAL_COMPONENTS_COMPOSE_RIGHT THEN
  CONJ_TAC THENL [CONV_TAC VALID_COMPONENT_CONV;
    MATCH_MP_TAC ORTHOGONAL_COMPONENTS_BITELEMENT THEN ASM_REWRITE_TAC[]]);;
let E5_READ_FLAG_FRAME_TAC =
 let orth=prove(`orthogonal_components c d /\ read c s'=read c s
    ==> read c (write d y s')=read c s`,MESON_TAC[orthogonal_components]) in
 let rec tac gl =
  (REFL_TAC ORELSE (MATCH_MP_TAC orth THEN CONJ_TAC THENL
   [ORTHOGONAL_COMPONENTS_TAC ORELSE
     (MATCH_MP_TAC E5_FLAG_BITS_ORTHOGONAL THEN ASM_REWRITE_TAC[]);
    tac])) gl in
 REWRITE_TAC[CF;PF;AF;ZF;SF;OF] THEN tac;;
let rec E5_SPLIT_HYP_CONDITIONAL_TAC gl =
 let asl,_=gl in
 try
  let _,th=find(fun(_,th)->can(find_term is_cond)(concl th)) asl in
  (UNDISCH_TAC(concl th) THEN COND_CASES_TAC THEN
   ASM_REWRITE_TAC[SEQ;UNDEFINED_VALUE;UNDEFINED_VALUES;ASSIGNS_THM;assign;seq] THEN
   REPEAT STRIP_TAC THEN REPEAT(FIRST_X_ASSUM(E5_SUBST_VAR_THM)) THEN
   E5_SPLIT_HYP_CONDITIONAL_TAC) gl
 with Failure "find" -> ALL_TAC gl;;
let E5_SCALAR_OPERATION_OUTSIDE_FLAGS = prove
 (e5_scalar_operation_outside_flags_statement,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[abi_caller_scalar_instruction;abi_cleanse_scalar_instruction;
    abi_scalar_instruction;abi_integer_operand;abi_integer_writable;
    abi_integer_immediate;abi_integer_memory_width;abi_cmov_operand;
    MEM;DE_MORGAN_THM] THEN
  REPEAT STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(E5_SUBST_VAR_THM)) THEN
  E5_ENUM_GPRS_TAC THEN
  W(fun(asl,w)->
    let th=find(fun(_,th)->let hd,_=strip_comb(concl th) in
      is_const hd && fst(dest_const hd)="x86_execute") asl in
    let original=concl(snd th) in
    fun gl -> try
     (UNDISCH_TAC original THEN
      REWRITE_TAC(map snd X86_EXECUTE_CASES) THEN
      REWRITE_TAC[r1_indirect_operand;add_load_event;add_store_event;SEQ_ID] THEN
      CONV_TAC(ONCE_DEPTH_CONV OPERAND_SIZE_CONV) THEN
      REWRITE_TAC[OPERAND_SIZE_CASES;OPERAND_CLAUSES;OPERAND64;OPERAND32;
       OPERAND16;OPERAND8;GPR64;GPR32_Z;GPR16;GPR8;register_size;regsize] THEN
      REWRITE_TAC (X86_OPERATION_CLAUSES @
       [x86_MOV;x86_XOR;x86_OR;x86_CMP;x86_DEC;x86_NEG;x86_LEA;
        x86_CMOV;x86_SHR;x86_SUB;x86_TEST;x86_ADD;
        x86_MOVZX;x86_SET;x86_PUSH;x86_POP;x86_CALL;x86_RET;x86_ENDBR64]) THEN
      REWRITE_TAC[x86_PUSH;x86_POP;x86_CALL;x86_RET] THEN
      REWRITE_TAC[READ_RVALUE;ASSIGN_ZEROTOP_32;READ_ZEROTOP_32;WRITE_ZEROTOP_32;
       SEQ;UNDEFINED_VALUE;UNDEFINED_VALUES;ASSIGNS_THM;assign;seq;
       LET_DEF;LET_END_DEF;condition_semantics] THEN
      REPEAT(CHANGED_TAC(REWRITE_TAC[x86_JMP_ABSOLUTE;x86_CALL;x86_CALL_ALT;x86_PUSH;x86_PUSH_ALT;
        SEQ;assign;seq;LET_DEF;LET_END_DEF])) THEN
      REPEAT STRIP_TAC THEN
      REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[SEQ;UNDEFINED_VALUE;
        UNDEFINED_VALUES;ASSIGNS_THM;assign;seq]) THEN
      REPEAT STRIP_TAC THEN
      REPEAT(FIRST_X_ASSUM(E5_SUBST_VAR_THM)) THEN
      E5_SPLIT_HYP_CONDITIONAL_TAC THEN
      REWRITE_TAC[GSYM READ_BITELEMENT;GSYM READ_COMPONENT_COMPOSE] THEN
      (E5_READ_FLAG_FRAME_TAC ORELSE
       W(fun(asl,w)->List.iter(fun(_,th)->print_endline("E5_STUCK_ASSUM "^string_of_term(concl th))) asl; print_endline("E5_STUCK_GOAL "^string_of_term w);FAIL_TAC "E5 frame stuck"))) gl
     with Failure e -> print_endline("E5_STUCK_OPCODE "^string_of_term original); failwith e));;
print_endline "E5_GENERIC_SCALAR_OUTSIDE_FLAGS_ALL_SUCCESSORS_KERNEL_PASS";;
