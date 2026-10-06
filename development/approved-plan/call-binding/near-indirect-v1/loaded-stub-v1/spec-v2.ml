(* Conditional final-linked PLT prefix transfer. This is not a callee/client
 * correctness contract. Human review PENDING. Only the successful single
 * architectural transition is considered; next target fetch belongs to the
 * separately checked callee precondition. *)
let r1_crypto_plt_prefix = new_definition
 `r1_crypto_plt_prefix =
   [word 0xff;word 0x25;word 0x92;word 0x2f;word 0;word 0]:byte list`;;
let r1_cleanse_plt_prefix = new_definition
 `r1_cleanse_plt_prefix =
   [word 0xff;word 0x25;word 0x8a;word 0x2f;word 0;word 0]:byte list`;;
let r1_memcmp_plt_prefix = new_definition
 `r1_memcmp_plt_prefix =
   [word 0xff;word 0x25;word 0x82;word 0x2f;word 0;word 0]:byte list`;;

let R1_CRYPTO_PLT_TRANSFER_STATEMENT =
 `!pc target e m.
   ensures x86
    (\s. bytes_loaded s (word pc) r1_crypto_plt_prefix /\
         read RIP s=word pc /\ read memory s=m /\ read events s=e /\
         read (memory :> bytes64 (word(pc+6+0x2f92))) s=target)
    (\s. read RIP s=target /\ read memory s=m /\
         read events s=APPEND
          [EventJump(word(pc+6),target);EventLoad(word(pc+6+0x2f92),8)] e)
    (MAYCHANGE[RIP] ,, MAYCHANGE[events])`;;

let R1_CLEANSE_PLT_TRANSFER_STATEMENT =
 `!pc target e m.
   ensures x86
    (\s. bytes_loaded s (word pc) r1_cleanse_plt_prefix /\
         read RIP s=word pc /\ read memory s=m /\ read events s=e /\
         read (memory :> bytes64 (word(pc+6+0x2f8a))) s=target)
    (\s. read RIP s=target /\ read memory s=m /\
         read events s=APPEND
          [EventJump(word(pc+6),target);EventLoad(word(pc+6+0x2f8a),8)] e)
    (MAYCHANGE[RIP] ,, MAYCHANGE[events])`;;

let R1_MEMCMP_PLT_TRANSFER_STATEMENT =
 `!pc target e m.
   ensures x86
    (\s. bytes_loaded s (word pc) r1_memcmp_plt_prefix /\
         read RIP s=word pc /\ read memory s=m /\ read events s=e /\
         read (memory :> bytes64 (word(pc+6+0x2f82))) s=target)
    (\s. read RIP s=target /\ read memory s=m /\
         read events s=APPEND
          [EventJump(word(pc+6),target);EventLoad(word(pc+6+0x2f82),8)] e)
    (MAYCHANGE[RIP] ,, MAYCHANGE[events])`;;
