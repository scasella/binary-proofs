let r1_secret_span_mono_statement =
 `!P Q a n.
    (!addr. P addr ==> Q addr) /\ assurance_span_ok P a n
    ==> assurance_span_ok Q a n`;;
let r1_secret_span_subspan_statement =
 `!P a n off len.
    assurance_span_ok P a n /\ off+len<=n
    ==> assurance_span_ok P (a+off) len`;;
let r1_secret_span_region_statement =
 `!P (p:int64) n.
    assurance_span_ok P (val p) n
    ==> assurance_span_ok (\addr. P addr /\ assurance_region p n addr)
          (val p) n`;;
