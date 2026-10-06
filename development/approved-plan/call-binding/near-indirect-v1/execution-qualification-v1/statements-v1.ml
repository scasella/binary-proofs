(* Additional literal qualifications frozen before execution proof search. *)
let r1_crypto_plt_bounded_statement=
 `!pc target e m.
   ensures_n x86
    (\s. bytes_loaded s (word pc) r1_crypto_plt_prefix /\
         read RIP s=word pc /\ read memory s=m /\ read events s=e /\
         read (memory :> bytes64 (word(pc+6+0x2f92))) s=target)
    (\s. read RIP s=target /\ read memory s=m /\
         read events s=APPEND
          [EventJump(word(pc+6),target);EventLoad(word(pc+6+0x2f92),8)] e)
    (MAYCHANGE[RIP] ,, MAYCHANGE[events]) (\s.1)`;;
let r1_crypto_plt_decode_statement=
 `!s pc. bytes_loaded s (word pc) r1_crypto_plt_prefix ==>
  x86_decode s (word pc) (6,JUMP Unconditional (Memop Quadword (Riprel(word 0x2f92))))`;;
let r1_crypto_plt_checked_statement=
 `!pc target e m rp xp s.
  bytes_loaded s (word pc) r1_crypto_plt_prefix /\
  read RIP s=word pc /\ read memory s=m /\ read events s=e /\
  read (memory :> bytes64 (word(pc+6+0x2f92))) s=target /\
  assurance_span_ok xp (val(word pc:int64)) 6 /\
  assurance_span_ok rp (val(word(pc+6+0x2f92):int64)) 8
  ==> assurance_checked_run 1
   (\t. read RIP t=target /\ read memory t=m /\
        read events t=APPEND
          [EventJump(word(pc+6),target);EventLoad(word(pc+6+0x2f92),8)] e)
   (\remaining source successor.
      assurance_step_policy rp (\a.F) xp source successor /\
      x86_decode source (read RIP source)
        (6,JUMP Unconditional (Memop Quadword (Riprel(word 0x2f92)))) /\
      read RIP successor=target) s`;;
let r1_cleanse_plt_bounded_statement=
 `!pc target e m.
   ensures_n x86
    (\s. bytes_loaded s (word pc) r1_cleanse_plt_prefix /\
         read RIP s=word pc /\ read memory s=m /\ read events s=e /\
         read (memory :> bytes64 (word(pc+6+0x2f8a))) s=target)
    (\s. read RIP s=target /\ read memory s=m /\
         read events s=APPEND
          [EventJump(word(pc+6),target);EventLoad(word(pc+6+0x2f8a),8)] e)
    (MAYCHANGE[RIP] ,, MAYCHANGE[events]) (\s.1)`;;
let r1_cleanse_plt_decode_statement=
 `!s pc. bytes_loaded s (word pc) r1_cleanse_plt_prefix ==>
  x86_decode s (word pc) (6,JUMP Unconditional (Memop Quadword (Riprel(word 0x2f8a))))`;;
let r1_cleanse_plt_checked_statement=
 `!pc target e m rp xp s.
  bytes_loaded s (word pc) r1_cleanse_plt_prefix /\
  read RIP s=word pc /\ read memory s=m /\ read events s=e /\
  read (memory :> bytes64 (word(pc+6+0x2f8a))) s=target /\
  assurance_span_ok xp (val(word pc:int64)) 6 /\
  assurance_span_ok rp (val(word(pc+6+0x2f8a):int64)) 8
  ==> assurance_checked_run 1
   (\t. read RIP t=target /\ read memory t=m /\
        read events t=APPEND
          [EventJump(word(pc+6),target);EventLoad(word(pc+6+0x2f8a),8)] e)
   (\remaining source successor.
      assurance_step_policy rp (\a.F) xp source successor /\
      x86_decode source (read RIP source)
        (6,JUMP Unconditional (Memop Quadword (Riprel(word 0x2f8a)))) /\
      read RIP successor=target) s`;;
let r1_memcmp_plt_bounded_statement=
 `!pc target e m.
   ensures_n x86
    (\s. bytes_loaded s (word pc) r1_memcmp_plt_prefix /\
         read RIP s=word pc /\ read memory s=m /\ read events s=e /\
         read (memory :> bytes64 (word(pc+6+0x2f82))) s=target)
    (\s. read RIP s=target /\ read memory s=m /\
         read events s=APPEND
          [EventJump(word(pc+6),target);EventLoad(word(pc+6+0x2f82),8)] e)
    (MAYCHANGE[RIP] ,, MAYCHANGE[events]) (\s.1)`;;
let r1_memcmp_plt_decode_statement=
 `!s pc. bytes_loaded s (word pc) r1_memcmp_plt_prefix ==>
  x86_decode s (word pc) (6,JUMP Unconditional (Memop Quadword (Riprel(word 0x2f82))))`;;
let r1_memcmp_plt_checked_statement=
 `!pc target e m rp xp s.
  bytes_loaded s (word pc) r1_memcmp_plt_prefix /\
  read RIP s=word pc /\ read memory s=m /\ read events s=e /\
  read (memory :> bytes64 (word(pc+6+0x2f82))) s=target /\
  assurance_span_ok xp (val(word pc:int64)) 6 /\
  assurance_span_ok rp (val(word(pc+6+0x2f82):int64)) 8
  ==> assurance_checked_run 1
   (\t. read RIP t=target /\ read memory t=m /\
        read events t=APPEND
          [EventJump(word(pc+6),target);EventLoad(word(pc+6+0x2f82),8)] e)
   (\remaining source successor.
      assurance_step_policy rp (\a.F) xp source successor /\
      x86_decode source (read RIP source)
        (6,JUMP Unconditional (Memop Quadword (Riprel(word 0x2f82)))) /\
      read RIP successor=target) s`;;
