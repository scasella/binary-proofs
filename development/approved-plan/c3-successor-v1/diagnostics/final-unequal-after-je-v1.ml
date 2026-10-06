(* Reconstruct exactly first two fixed unequal instructions, retaining post-JE
   goal before the stalled frozen assumption normalization. *)
let _,c3_successor_final_prefix_cases,_ =
 C3_FINAL_RETURN_SITE_PREFIX_TAC ([],c3_final_return_site_statement);;
let _,c3_successor_final_unequal_after_je,_ =
 (C3_FINAL_RETURN_STEP_TAC `9` `entry:x86state` `fr1:x86state` "fr1" THEN
  HT_STATE_NORMALIZE_TAC[C3_FINAL_RETURN_OFFSET40;C3_FINAL_RETURN_OFFSET32;
   C3_FINAL_RETURN_OFFSET24;C3_FINAL_RETURN_OFFSET16;C3_FINAL_RETURN_OFFSET8] THEN
  C3_FINAL_RETURN_STEP_TAC `8` `fr1:x86state` `fr2:x86state` "fr2")
 (List.nth c3_successor_final_prefix_cases 2);;
print_endline "C3_SUCCESSOR_FINAL_UNEQUAL_AFTER_JE_BEFORE_NORMALIZE_EXACT_GOAL";;
List.iter print_goal c3_successor_final_unequal_after_je;;

let _,c3_successor_final_unequal_after_je_normalized,_ =
 HT_STATE_NORMALIZE_TAC[C3_FINAL_RETURN_OFFSET40;C3_FINAL_RETURN_OFFSET32;
  C3_FINAL_RETURN_OFFSET24;C3_FINAL_RETURN_OFFSET16;C3_FINAL_RETURN_OFFSET8]
 (List.hd c3_successor_final_unequal_after_je);;
let c3_successor_final_decode73,_ =
 HT_SYMBOLIC_DECODE (snd C3_CALLER_RAW_EXEC)
 (map snd (fst(List.hd c3_successor_final_unequal_after_je_normalized))) `fr2:x86state`;;
let c3_successor_final_nd73 =
 REWRITE_RULE ([r1_near_operand64;r1_near_register] @ GPR_thms) c3_successor_final_decode73;;
let _,c3_successor_final_inst73 = dest_pair(last(snd(strip_comb(concl c3_successor_final_nd73))));;
print_endline "C3_SUCCESSOR_FINAL_OFFSET73_EXACT_DECODE";;
print_thm c3_successor_final_nd73;;
let _,c3_successor_final_qualification73_residuals,_ =
 REWRITE_TAC[abi_caller_scalar_instruction;abi_cleanse_scalar_instruction;
   abi_scalar_instruction;abi_integer_operand;abi_integer_writable;abi_cmov_operand]
 ([],mk_comb(`abi_caller_scalar_instruction`,c3_successor_final_inst73));;
print_endline "C3_SUCCESSOR_FINAL_OFFSET73_QUALIFICATION_EXACT_PRE_MESON_RESIDUALS";;
List.iter print_goal c3_successor_final_qualification73_residuals;;
