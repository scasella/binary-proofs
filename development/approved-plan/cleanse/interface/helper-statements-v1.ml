(* Exact independent helper goals, frozen before their proof search. *)
let cleanse_interface_count_equal_statement =
 `!p n. cleanse_access_count (p:int64) n=cleanse_functional_steps p n`;;
let cleanse_interface_run_post_statement =
 `!n P Q C (s:x86state).
    assurance_checked_run n P C s /\ eventually_n x86 n Q s
    ==> assurance_checked_run n (\t. P t /\ Q t) C s`;;
let cleanse_interface_run_mono_statement =
 `!n P Q C (s:x86state).
    (!t. P t ==> Q t) /\ assurance_checked_run n P C s
    ==> assurance_checked_run n Q C s`;;
let cleanse_interface_slot_preserved_statement =
 `!stackpointer p n m (t:x86state).
    val(stackpointer:int64)+8<=2 EXP 64 /\
    (!a. ~(assurance_region p n a /\ assurance_region stackpointer 8 a)) /\
    (!a. ~assurance_region p n (val a) ==> read memory t a=m a)
    ==> read (memory :> bytes64 stackpointer) t=read (bytes64 stackpointer) m`;;
