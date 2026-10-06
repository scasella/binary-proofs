(* Literal targets recorded before linkage proof construction.
   No new HOL definitions, ISA relation or axiom. *)
let bp_reuse_decoded_step_statement =
 `!len inst s.
   x86_decode s (read RIP s) (len,inst)
   ==> x86 s =
       (RIP := word_add (read RIP s) (word len) ,, x86_execute inst) s`;;

let bp_reuse_riprel_jump_successor_statement =
 `!pc disp target e m s.
   x86_decode s pc
     (6,JUMP Unconditional (Memop Quadword (Riprel disp))) /\
   read RIP s=pc /\ read memory s=m /\ read events s=e /\
   read (memory :> bytes64 (word_add (word_add pc (word 6)) disp)) s=target
   ==> (?next. x86 s next) /\
       !next. x86 s next ==>
         read RIP next=target /\ read memory next=m /\
         read events next=APPEND
           [EventJump(word_add pc (word 6),target);
            EventLoad(word_add (word_add pc (word 6)) disp,8)] e /\
         (MAYCHANGE [RIP] ,, MAYCHANGE [events]) s next`;;

let bp_reuse_riprel_jump_checked_hop_statement =
 `!pc disp target e m rp xp s.
   x86_decode s pc
     (6,JUMP Unconditional (Memop Quadword (Riprel disp))) /\
   read RIP s=pc /\ read memory s=m /\ read events s=e /\
   read (memory :> bytes64 (word_add (word_add pc (word 6)) disp)) s=target /\
   assurance_span_ok xp (val(pc:int64)) 6 /\
   assurance_span_ok rp (val(word_add (word_add pc (word 6)) disp:int64)) 8
   ==> assurance_checked_run 1
     (\next. read RIP next=target /\ read memory next=m /\
       read events next=APPEND
         [EventJump(word_add pc (word 6),target);
          EventLoad(word_add (word_add pc (word 6)) disp,8)] e /\
       (MAYCHANGE [RIP] ,, MAYCHANGE [events]) s next)
     (\remaining source successor.
       assurance_step_policy rp (\a.F) xp source successor /\
       x86_decode source (read RIP source)
         (6,JUMP Unconditional (Memop Quadword (Riprel disp))) /\
       read RIP successor=target /\ read memory successor=read memory source /\
       (MAYCHANGE [RIP] ,, MAYCHANGE [events]) source successor) s`;;

let bp_reuse_riprel_jump_omitted_statement =
 `!pc disp s a next a'.
   x86_decode s pc
     (6,JUMP Unconditional (Memop Quadword (Riprel disp))) /\
   read RIP s=pc /\
   abi_caller_scalar_extended_step (s,a) (next,a')
   ==> a'=a`;;

(* Exact C1 byte binding is deliberately separate from the generic targets. *)
let bp_c1_plt_decode_statement =
 `!s pc. bytes_loaded s (word pc) c1_crypto_plt_prefix
   ==> x86_decode s (word pc)
     (6,JUMP Unconditional (Memop Quadword (Riprel(word 0x2fa2))))`;;

let bp_c1_plt_checked_hop_statement =
 `!e m rp xp s.
   bytes_loaded s (word 0x21001030) c1_crypto_plt_prefix /\
   read RIP s=word 0x21001030 /\ read memory s=m /\ read events s=e /\
   read (memory :> bytes64 (word 0x21003fd8)) s=word 0x10241840 /\
   assurance_span_ok xp 0x21001030 6 /\
   assurance_span_ok rp 0x21003fd8 8
   ==> assurance_canonical48(val(word 0x10241840:int64)) /\
       assurance_checked_run 1
        (\next. read RIP next=word 0x10241840 /\ read memory next=m /\
          read events next=APPEND
           [EventJump(word 0x21001036,word 0x10241840);
            EventLoad(word 0x21003fd8,8)] e /\
          (MAYCHANGE [RIP] ,, MAYCHANGE [events]) s next)
        (\remaining source successor.
          assurance_step_policy rp (\a.F) xp source successor /\
          x86_decode source (read RIP source)
           (6,JUMP Unconditional (Memop Quadword (Riprel(word 0x2fa2)))) /\
          read RIP successor=word 0x10241840 /\
          read memory successor=read memory source /\
          (MAYCHANGE [RIP] ,, MAYCHANGE [events]) source successor) s`;;
