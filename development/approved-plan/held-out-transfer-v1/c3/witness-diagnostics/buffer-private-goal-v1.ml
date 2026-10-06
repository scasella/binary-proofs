(* Exact failed fixed C3 witness buffer tactic, applied privately. *)
let (_,c3w_buffer_private_goals_v1,_) =
 (REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[C3W_MEMORY_OUTSIDE; C3W_EXTERNAL_SLOT_SEPARATION;
               C3W_LAYOUT_POINT; c3w_seed]) ([],`!lib_file client_file payload p q n. c3w_layout p q n
    ==> (!i. i<n ==> c3w_memory lib_file client_file payload
          (word_add p (word i))=payload(word_add p (word i))) /\
        (!i. i<n ==> c3w_memory lib_file client_file payload
          (word_add q (word i))=payload(word_add q (word i)))`);;
List.iter print_goal c3w_buffer_private_goals_v1;;
print_endline "C3W_BUFFER_PRIVATE_DIAGNOSTIC_V1_COMPLETE";;
