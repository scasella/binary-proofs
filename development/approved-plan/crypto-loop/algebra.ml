(* New development lemmas. No original source or statement is changed. *)
let CRYPTO_DEV_ZX_BYTE_EQ_0 = prove
 (`!b:byte. (word_zx b:int64) = word 0 <=> b = word 0`,
  SIMP_TAC[GSYM VAL_EQ; VAL_WORD_ZX; VAL_WORD_0;
           DIMINDEX_8; DIMINDEX_64; ARITH]);;

let CRYPTO_DEV_ACCUMULATE_EQ_0 = prove
 (`!acc a b:byte.
    (word_zx(word_or acc (word_xor a b)):int64) = word 0 <=>
    (word_zx acc:int64) = word 0 /\ a = b`,
  REWRITE_TAC[CRYPTO_DEV_ZX_BYTE_EQ_0; WORD_OR_EQ_0; WORD_XOR_EQ_0]);;

let CRYPTO_DEV_PREFIX_EQ_STEP = prove
 (`!m:int64->byte. !p q i.
    (!j. j < i + 1 ==> m(word_add p (word j)) = m(word_add q (word j))) <=>
    (!j. j < i ==> m(word_add p (word j)) = m(word_add q (word j))) /\
    m(word_add p (word i)) = m(word_add q (word i))`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [MESON_TAC[ARITH_RULE `j<i ==> j<i+1`; ARITH_RULE `i<i+1`];
    STRIP_TAC THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    ASM_CASES_TAC `j:num = i` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]);;
print_endline "CRYPTO_DEV_ALGEBRA_COMPLETE";;
