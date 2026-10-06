(* Original x86 events are newest-first. This schema contains each byte load
   and JNE event, including the final not-taken branch. It does not encode
   nonbranch instructions or instruction fetches. *)
let crypto_trace_prefix = new_recursive_definition num_RECURSION
 `(crypto_trace_prefix pc (p:int64) q n 0 = []) /\
  (crypto_trace_prefix pc p q n (SUC i) =
    APPEND
      [EventJump(word(pc+86),if SUC i=n then word(pc+86) else word(pc+64));
       EventLoad(word_add q (word i),1);EventLoad(word_add p (word i),1)]
      (crypto_trace_prefix pc p q n i))`;;
let crypto_trace_body_prefix = new_definition
 `crypto_trace_body_prefix pc (p:int64) q n i =
    if i=0 then [] else
    APPEND [EventLoad(word_add q (word(i-1)),1);
            EventLoad(word_add p (word(i-1)),1)]
           (crypto_trace_prefix pc p q n (i-1))`;;
let crypto_trace_call = new_definition
 `crypto_trace_call pc (p:int64) q n stackpointer returnaddress =
    if n=0 then
      [EventJump(word(pc+95),returnaddress);EventLoad(stackpointer,8);
       EventJump(word(pc+16),word(pc+93))]
    else if n=16 then
      [EventJump(word(pc+52),returnaddress);EventLoad(stackpointer,8);
       EventLoad(word_add q (word 8),8);EventLoad(q,8);
       EventLoad(word_add p (word 8),8);EventLoad(p,8);
       EventJump(word(pc+22),word(pc+22));
       EventJump(word(pc+16),word(pc+16))]
    else APPEND [EventJump(word(pc+95),returnaddress);EventLoad(stackpointer,8)]
      (APPEND (crypto_trace_prefix pc p q n n)
       [EventJump(word(pc+22),word(pc+64));
        EventJump(word(pc+16),word(pc+16))])`;;
