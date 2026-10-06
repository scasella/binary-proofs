(* A code-slice reference-map existence construction only. It does not bind
   unrelated loaded-image bytes or assume any target behavior. *)
let lw_reference_overlay = new_definition
 `lw_reference_overlay (background:int64->byte) (a:int64) =
    if 0x10241840 <= val a /\ val a < 0x10241840+95
    then EL (val a-0x10241840) crypto_memcmp_mc
    else background a`;;
