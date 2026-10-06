(* BP-20260930-E2 candidate unchanged OPENSSL_cleanse whole-routine contract.
   Human specification review PENDING. Main functional proof not constructed.
   Readability is required only for the actual incoming return slot. *)
let bp_e2_cleanse_pre = new_definition
 `bp_e2_cleanse_pre pc stackpointer ra p n m rp wp xp ordinary (s:x86state) <=>
    n<2 EXP 64 /\ pc+97<=2 EXP 64 /\
    bytes_loaded s (word pc) openssl_cleanse_mc /\
    read RIP s=word pc /\ read RSP s=stackpointer /\
    read (memory :> bytes64 stackpointer) s=ra /\
    C_ARGUMENTS [p;word n] s /\ read memory s=m /\
    val(stackpointer:int64) MOD 16=8 /\ val stackpointer+8<2 EXP 64 /\
    assurance_canonical48(val(ra:int64)) /\ ~(ra=word pc) /\
    read DF s=F /\ ~bit 18(read rflags s) /\
    assurance_span_ok (\a. xp a /\ ordinary a) pc 97 /\
    assurance_span_ok (\a. rp a /\ ordinary a) (val stackpointer) 8 /\
    assurance_span_ok (\a. wp a /\ ordinary a) (val(p:int64)) n /\
    (!a. ~(assurance_region p n a /\ assurance_region (word pc) 97 a)) /\
    (!a. ~(assurance_region p n a /\ assurance_region stackpointer 8 a))`;;
let bp_e2_cleanse_allowed_read = new_definition
 `bp_e2_cleanse_allowed_read rp ordinary stackpointer a <=>
    rp a /\ ordinary a /\ assurance_region stackpointer 8 a`;;
let bp_e2_cleanse_allowed_write = new_definition
 `bp_e2_cleanse_allowed_write wp ordinary p n a <=>
    wp a /\ ordinary a /\ assurance_region p n a`;;
let bp_e2_cleanse_allowed_fetch = new_definition
 `bp_e2_cleanse_allowed_fetch xp ordinary pc a <=>
    xp a /\ ordinary a /\ assurance_region (word pc) 97 a`;;
let bp_e2_cleanse_functional_statement =
 `!pc stackpointer ra p n m rp wp xp ordinary.
    ensures x86
     (bp_e2_cleanse_pre pc stackpointer ra p n m rp wp xp ordinary)
     (\s. read RIP s=ra /\ val(read RSP s)=val(stackpointer:int64)+8 /\
          (!i. i<n ==> read memory s (word_add p (word i))=word 0) /\
          (!a. ~(assurance_region p n (val a)) ==> read memory s a=m a))
     (MAYCHANGE [RIP;RSP;RAX;RDI;RSI] ,,
      MAYCHANGE SOME_FLAGS ,, MAYCHANGE [memory :> bytes(p,n)] ,, MAYCHANGE [events])`;;

(* All-count genuine internal byte-loop component, not full O1. No small cap. *)
let cleanse_byte_loop_statement =
 `!pc p n.
    0<n /\ n<2 EXP 64 /\ nonoverlapping (word pc,97) (p,n) ==>
    ensures x86
     (\s. bytes_loaded s (word pc) openssl_cleanse_mc /\
          read RIP s=word(pc+19) /\ read RDI s=p /\
          read RSI s=word n /\ read RAX s=word 0)
     (\s. read RIP s=word(pc+31) /\ read RDI s=word_add p (word n) /\
          read RSI s=word 0 /\ read RAX s=word 0 /\
          read (memory :> bytes(p,n)) s=0)
     (MAYCHANGE [RIP;RDI;RSI] ,, MAYCHANGE SOME_FLAGS ,,
      MAYCHANGE [memory :> bytes(p,n)] ,, MAYCHANGE [events])`;;
