(* Exact two SUBGOAL_THEN outputs, using an independent raw literal.
   Failed v1 source and checker log remain unchanged. *)
let c3_successor_final_mov2_site_raw_literal =
 `!stackpointer p q:int64 n m rp wp xp ordinary source target:x86state.
  bytes_loaded source (word 0x23001120) c3_caller_mc /\
  read RIP source=word 0x23001169 /\
  assurance_span_ok(c3_allowed_fetch xp ordinary)0x23001120 89 /\
  read events target=read events source
  ==> c3_step_policy stackpointer p q n m rp wp xp ordinary 7 source target`;;
let _,c3_successor_final_mov2_decode_actual_subgoals,_ =
 (REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `x86_decode (source:x86state) (read RIP source)
    (5,MOV (Register(Gpr(word 0)Lower_32)) (Imm32(word 2)))`
   ASSUME_TAC)
 ([],c3_successor_final_mov2_site_raw_literal);;
print_endline "C3_SUCCESSOR_FINAL_MOV2_V1_ACTUAL_DECODE_SUBGOALS";;
print_int(length c3_successor_final_mov2_decode_actual_subgoals);;
List.iter print_goal c3_successor_final_mov2_decode_actual_subgoals;;
print_endline "C3_SUCCESSOR_FINAL_MOV2_V1_ACTUAL_SUBGOALS_RETAINED";;
