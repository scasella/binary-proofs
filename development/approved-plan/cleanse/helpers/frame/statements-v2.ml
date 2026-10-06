(* Pure frozen region/frame targets. Endpoint val p+n=2^64 is permitted.
   No target behavior, permissions or preservation are assumed. *)
needs "/work/development/approved-plan/assurance/policy.ml";;
let cleanse_regions_disjoint_nonoverlapping_statement =
 `!p q n k.
    val(p:int64)+n<=2 EXP 64 /\ val(q:int64)+k<=2 EXP 64 /\
    (!a. ~(assurance_region p n a /\ assurance_region q k a))
    ==> nonoverlapping (p,n) (q,k)`;;
let cleanse_region_word_sub_statement =
 `!p a n.
    n<2 EXP 64 /\ val(p:int64)+n<=2 EXP 64
    ==> (assurance_region p n (val(a:int64)) <=> val(word_sub a p)<n)`;;
let cleanse_memory_write_bytes_outside_statement =
 `!p a n x m.
    n<2 EXP 64 /\ val(p:int64)+n<=2 EXP 64 /\
    ~assurance_region p n (val(a:int64))
    ==> write(bytes(p,n)) x m a = m a`;;
let cleanse_state_write_bytes_outside_statement =
 `!p a n x (s:x86state).
    n<2 EXP 64 /\ val(p:int64)+n<=2 EXP 64 /\
    ~assurance_region p n (val(a:int64))
    ==> read memory (write(memory :> bytes(p,n)) x s) a = read memory s a`;;
