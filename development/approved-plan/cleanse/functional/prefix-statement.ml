(* Frozen same-state concatenation needed after symbolic execution. *)
let cleanse_functional_prefix_read_statement =
 `!s p i. read(memory :> bytes(p:int64,i))(s:x86state)=0 /\
           read(memory :> bytes8(word_add p (word i)))s=word 0 ==>
           read(memory :> bytes(p,i+1))s=0`;;
