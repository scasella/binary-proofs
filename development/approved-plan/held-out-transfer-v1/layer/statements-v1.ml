(* Candidate preparation: exact address-free accepted C2 fragments; identifier renaming only. *)
let ht_policy_event_mono_statement =
 `!rp0 wp0 rp wp e:uarch_event.
    (!addr. rp0 addr ==> rp addr) /\
    (!addr. wp0 addr ==> wp addr) /\
    assurance_event_policy rp0 wp0 e
    ==> assurance_event_policy rp wp e`;;
let ht_policy_all_mono_statement =
 `!P Q d:uarch_event list.
    (!e. P e ==> Q e) /\ ALL P d ==> ALL Q d`;;
let ht_policy_step_mono_statement =
 `!rp0 wp0 xp0 rp wp xp source target:x86state.
    (!addr. rp0 addr ==> rp addr) /\
    (!addr. wp0 addr ==> wp addr) /\
    (!addr. xp0 addr ==> xp addr) /\
    assurance_step_policy rp0 wp0 xp0 source target
    ==> assurance_step_policy rp wp xp source target`;;
let ht_policy_span_statement = `!P Q (p:int64) n. (!addr. P addr /\ assurance_region p n addr ==> Q addr) /\ assurance_span_ok P (val p) n ==> assurance_span_ok Q (val p) n`;;
let ht_span_point_statement = `!P (p:int64) n addr. assurance_span_ok P (val p) n /\ assurance_region p n addr ==> P addr`;;
let ht_region_nonoverlapping_statement = `!p q n k. val(p:int64)+n <= 2 EXP 64 /\ val(q:int64)+k <= 2 EXP 64 /\ (!addr. ~(assurance_region p n addr /\ assurance_region q k addr)) ==> nonoverlapping(p,n)(q,k)`;;
let ht_span_word_add_region_statement = `!P p:int64 n i. assurance_span_ok P (val p) n /\ i<n ==> assurance_region p n (val(word_add p (word i)))`;;
let ht_region_disjoint_statement = `!p q:int64 n k.
 val p+n<=2 EXP 64 /\ val q+k<=2 EXP 64 /\ nonoverlapping(p,n)(q,k)
 ==> !addr. ~(assurance_region p n addr /\ assurance_region q k addr)`;;
let ht_frame_cancel_component_statement = `!c:(A,B)component R:A->A->bool s t.
 extensionally_valid_component c /\
 (!u v. R u v ==> read c v=read c u) /\
 (R ,, MAYCHANGE [c]) s t /\ read c t=read c s
 ==> R s t`;;
let ht_original_ret_statement =
 `!pc s t:x86state.
   read RIP s=word pc /\ x86_decode s (word pc) (1,RET) /\ x86 s t
   ==> assurance_actual_ret 1 s t`;;

let ht_word_sub_sub_statement = `!pointer:int64. !a b. word_sub (word_sub pointer (word a)) (word b)=word_sub pointer (word(a+b))`;;
