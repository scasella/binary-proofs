let ra_checked_run_three_segment_statement =
 `!a b c H A B P C1 C2 C3 C (s:x86state).
    assurance_checked_run a H C1 s /\
    (!t. H t ==> A t) /\
    (!t. A t ==> assurance_checked_run b B C2 t) /\
    (!t. B t ==> assurance_checked_run c P C3 t) /\
    (!k source target. C1 k source target ==> C ((b+c)+k) source target) /\
    (!k source target. C2 k source target ==> C (c+k) source target) /\
    (!k source target. C3 k source target ==> C k source target)
    ==> assurance_checked_run (a+(b+c)) P C s`;;
