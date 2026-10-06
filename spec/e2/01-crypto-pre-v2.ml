(* BP-20260930-E2 candidate: explicit scalar-state entry domain.
   A definition is not a theorem or an assumption of target behavior.
   The missing architectural ABI fields require a qualified extension.
   Human review remains pending. No old E1 result is relabeled E2. *)

let bp_e2_crypto_pre = new_definition
 `bp_e2_crypto_pre pc stackpointer ra p q n m rp xp ordinary (s:x86state) <=>
    n < 2 EXP 64 /\ pc+95 <= 2 EXP 64 /\
    bytes_loaded s (word pc) crypto_memcmp_mc /\
    read RIP s = word pc /\ read RSP s = stackpointer /\
    read (memory :> bytes64 stackpointer) s = ra /\
    C_ARGUMENTS [p;q;word n] s /\ read memory s = m /\
    val(stackpointer:int64) MOD 16 = 8 /\ val stackpointer+8 < 2 EXP 64 /\
    assurance_canonical48 (val(ra:int64)) /\ ~(ra = word pc) /\
    read DF s = F /\ ~bit 18 (read rflags s) /\
    assurance_span_ok (\a. xp a /\ ordinary a) pc 95 /\
    assurance_span_ok (\a. rp a /\ ordinary a) (val stackpointer) 8 /\
    assurance_span_ok (\a. rp a /\ ordinary a) (val(p:int64)) n /\
    assurance_span_ok (\a. rp a /\ ordinary a) (val(q:int64)) n /\
    (!a. ~(assurance_region (word pc) 95 a /\
           assurance_region stackpointer 8 a))`;;

let bp_e2_crypto_allowed_read = new_definition
 `bp_e2_crypto_allowed_read rp ordinary p q n stackpointer a <=>
    rp a /\ ordinary a /\
    (assurance_region p n a \/ assurance_region q n a \/
     assurance_region stackpointer 8 a)`;;

let bp_e2_crypto_allowed_write = new_definition
 `bp_e2_crypto_allowed_write (a:num) <=> F`;;

let bp_e2_crypto_allowed_fetch = new_definition
 `bp_e2_crypto_allowed_fetch xp ordinary pc a <=>
    xp a /\ ordinary a /\ assurance_region (word pc) 95 a`;;

(* No code/data parse is postulated here. Independent final-ELF extraction,
   PT_LOAD/address/relocation correspondence and a declared loaded image bind
   crypto_memcmp_mc and pc to the final library in the acceptance driver. *)
