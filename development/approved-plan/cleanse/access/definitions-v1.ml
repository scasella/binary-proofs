(* Exact all-length access lane; human model/specification review PENDING.
   The checked run quantifies over every original x86 successor. *)
let cleanse_access_count = new_definition
 `cleanse_access_count p n =
    if n<15 then 4*n+7 else
    let a=(8-val(p:int64) MOD 8) MOD 8 in
    let k=(n-a) DIV 8 in let r=(n-a) MOD 8 in
    9+6*a+5*k+4*r`;;
let cleanse_access_covered_step = new_definition
 `cleanse_access_covered_step pc rp wp xp remaining (s:x86state) s' <=>
    assurance_zero_step rp wp xp remaining s s' /\
    (?off len inst.
       read RIP s=word(pc+off) /\ abi_cleanse_site off len inst /\
       x86_decode s (read RIP s) (len,inst))`;;
let cleanse_access_return_post = new_definition
 `cleanse_access_return_post pc stackpointer ra (s:x86state) <=>
    read RIP s=ra /\ read RSP s=word_add stackpointer (word 8) /\
    bytes_loaded s (word pc) openssl_cleanse_mc`;;
let cleanse_access_loop_pre = new_definition
 `cleanse_access_loop_pre pc off stackpointer ra p n rp wp xp (s:x86state) <=>
    n<2 EXP 64 /\ pc+97<=2 EXP 64 /\
    assurance_span_ok xp pc 97 /\
    assurance_span_ok rp (val(stackpointer:int64)) 8 /\
    assurance_span_ok wp (val(p:int64)) n /\
    nonoverlapping (word pc,97) (p,n) /\
    nonoverlapping (stackpointer,8) (p,n) /\
    bytes_loaded s (word pc) openssl_cleanse_mc /\
    read RIP s=word(pc+off) /\ read RSP s=stackpointer /\
    read (memory :> bytes64 stackpointer) s=ra /\
    read RDI s=p /\ read RSI s=word n /\ read RAX s=word 0`;;
