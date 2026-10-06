(* Explicit application of checked frozen-layout point fact; no new generic law. *)
let C3W_BUFFER_VALUES = prove
 (`!lib_file client_file payload p q n. c3w_layout p q n
    ==> (!i. i<n ==> c3w_memory lib_file client_file payload
          (word_add p (word i))=payload(word_add p (word i))) /\
        (!i. i<n ==> c3w_memory lib_file client_file payload
          (word_add q (word i))=payload(word_add q (word i)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`p:int64`;`q:int64`;`n:num`;`i:num`] C3W_LAYOUT_POINT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[C3W_MEMORY_OUTSIDE; C3W_EXTERNAL_SLOT_SEPARATION;
               c3w_seed]);;

print_endline "C3W_MEMBERSHIP_BUFFER_VALUES_V2_COMPLETE";;
