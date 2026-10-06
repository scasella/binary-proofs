(* Full sixteen-byte equivalence, frozen before its proof search. This bridges
   the production fast path's word loads to the initial logical byte sequence. *)
let bp_read_bytes_at_zero_statement =
 `!m p n. read (bytes(p:int64,n)) m =
          read (bytes(word 0,n)) (\a. m(word_add p a))`;;
let bp_read_bytes_different_eq_statement =
 `!m p q n. read (bytes(p:int64,n)) m = read (bytes(q,n)) m <=>
            !i. i<n ==> m(word_add p (word i)) = m(word_add q (word i))`;;
let bp_prefix_16_split_statement =
 `!P:num->bool. (!i. i<16 ==> P i) <=>
                (!i. i<8 ==> P i) /\ (!i. i<8 ==> P(8+i))`;;
let bp_wordpair_byte16_statement =
 `!m p q.
   (read (bytes64(p:int64)) m = read (bytes64 q) m /\
    read (bytes64(word_add p (word 8))) m =
    read (bytes64(word_add q (word 8))) m) <=>
   (!i. i<16 ==> m(word_add p (word i)) = m(word_add q (word i)))`;;
