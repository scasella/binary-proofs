(* Exact-count functional/frame/event targets frozen before proof search. *)
let crypto_bounded_iteration_statement =
 `!pc p q k acc a b e.
    0 < k /\ k < 2 EXP 64 ==>
    ensures_n x86
      (\s. bytes_loaded s (word pc) crypto_memcmp_mc /\
           read RIP s = word(pc+64) /\ C_ARGUMENTS [p;q;word k] s /\
           read RAX s = word_zx(acc:byte) /\
           val(read R10 s) < 256 /\
           read (memory :> bytes8 p) s = a /\
           read (memory :> bytes8 q) s = b /\ read events s = e)
      (\s. read RIP s = word(pc+84) /\
           read RDI s = word_add p (word 1) /\
           read RSI s = word_add q (word 1) /\
           read RDX s = word(k-1) /\
           read RAX s = word_zx(word_or acc (word_xor a b)) /\
           val(read R10 s) < 256 /\
           (read ZF s <=> k=1) /\
           read events s = APPEND [EventLoad(q,1);EventLoad(p,1)] e)
      (MAYCHANGE [RIP; RAX; RDI; RSI; RDX; R10] ,,
       MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events]) (\s.6)`;;
(* Independently frozen before search. These statements concern original
   modeled load/store/jump events, not fetch coverage or all-step policy. *)
let crypto_bounded_loop_statement =
 `!pc p q n m e.
    0<n /\ n<2 EXP 64 ==>
    ensures_n x86
      (\s. bytes_loaded s (word pc) crypto_memcmp_mc /\
           read RIP s=word(pc+64) /\ C_ARGUMENTS [p;q;word n] s /\
           read RAX s=word 0 /\ read R10 s=word 0 /\
           read memory s=m /\ read events s=e)
      (\s. read RIP s=word(pc+93) /\
           read RAX s=(if (!j. j<n ==> m(word_add p (word j))=m(word_add q (word j)))
                       then word 0 else word 1) /\
           read events s=APPEND (crypto_trace_prefix pc p q n n) e)
      (MAYCHANGE [RIP;RAX;RDI;RSI;RDX;R10] ,,
       MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events]) (\s.7*n+2)`;;
(* Internal compositional targets, frozen before proof search. *)
let crypto_bounded_generic_core_statement =
 `!pc p q n m e.
    0<n /\ n<2 EXP 64 /\ ~(n=16) ==>
    ensures_n x86
      (\s. bytes_loaded s (word pc) crypto_memcmp_mc /\
           read RIP s = word pc /\ C_ARGUMENTS [p;q;word n] s /\
           read memory s = m /\ read events s=e)
      (\s. read RIP s = word(pc+93) /\
           read RAX s =
             (if (!j. j<n ==> m(word_add p (word j)) = m(word_add q (word j)))
              then word 0 else word 1) /\
           read events s=APPEND (crypto_trace_prefix pc p q n n)
             (APPEND [EventJump(word(pc+22),word(pc+64));
                      EventJump(word(pc+16),word(pc+16))] e))
      (MAYCHANGE [RIP;RAX;RDI;RSI;RDX;R10] ,,
       MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events]) (\s.7*n+9)`;;
let crypto_bounded_generic_return_statement =
 `!pc stackpointer returnaddress p q n m e.
    0<n /\ n<2 EXP 64 /\ ~(n=16) ==>
    ensures_n x86
      (\s. bytes_loaded s (word pc) crypto_memcmp_mc /\
           read RIP s = word pc /\ read RSP s = stackpointer /\
           read (memory :> bytes64 stackpointer) s = returnaddress /\
           C_ARGUMENTS [p;q;word n] s /\ read memory s = m /\ read events s=e)
      (\s. read RIP s = returnaddress /\
           read RSP s = word_add stackpointer (word 8) /\
           read RAX s =
             (if (!j. j<n ==> m(word_add p (word j)) = m(word_add q (word j)))
              then word 0 else word 1) /\
           read events s=APPEND (crypto_trace_call pc p q n stackpointer returnaddress) e)
      (MAYCHANGE [RIP;RSP;RAX;RDI;RSI;RDX;R10;R11] ,,
       MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events]) (\s.7*n+10)`;;
