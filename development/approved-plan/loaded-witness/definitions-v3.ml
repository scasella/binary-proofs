(* BP-E2 loaded-image-compatible conditional witness family V1.
   No loader, image existence, target behavior or permission axiom is added.
   image is a quantified reference map. Its independent actual-image binding is
   an explicit remaining obligation, not supplied by these definitions. *)

let lw_image_domain = new_definition
 `lw_image_domain a <=> 0x10000000 <= a /\ a < 0x1048a000`;;

let lw_image_read = new_definition
 `lw_image_read a <=> lw_image_domain a`;;

let lw_image_execute = new_definition
 `lw_image_execute a <=> 0x100c5000 <= a /\ a < 0x10344000`;;

let lw_image_write = new_definition
 `lw_image_write a <=> 0x10484000 <= a /\ a < 0x1048a000`;;

(* Every domain is a union of 4096-byte pages. Empty input intervals give no
   pages, independent of pointer bits. Endpoint 2^64 is allowed mathematically
   for a buffer's final byte; final stack endpoint has the stricter E2 bound. *)
let lw_pagecover = new_definition
 `lw_pagecover (p:int64) n a <=>
    ~(n = 0) /\ 4096 * (val p DIV 4096) <= a /\
    a < 4096 * ((val p + n - 1) DIV 4096 + 1)`;;

let lw_overlay_domain = new_definition
 `lw_overlay_domain p q n a <=>
    (0x300000 <= a /\ a < 0x301000) \/
    lw_pagecover p n a \/ lw_pagecover q n a`;;

let lw_layout = new_definition
 `lw_layout p q n <=>
    !a. ~(lw_image_domain a /\ lw_overlay_domain p q n a)`;;

let lw_reference_code = new_definition
 `lw_reference_code (image:int64->byte) <=>
    !i. i < 95 ==> image(word(0x10241840+i)) = EL i crypto_memcmp_mc`;;

let lw_memory = new_definition
 `lw_memory (image:int64->byte) p q n different (a:int64) =
    if 0x300008 <= val a /\ val a < 0x300010
    then word (0x400000 DIV (256 EXP (val a-0x300008)))
    else if lw_overlay_domain p q n (val a)
         then if different /\ a = q then word 255 else word 128
         else image a`;;

let lw_state = new_definition
 `lw_state (image:int64->byte) (p:int64) (q:int64) n different =
    x86state_RECORD (word 0x10241840)
      (\r:(4)word. if r=word 7 then p
                  else if r=word 6 then q
                  else if r=word 2 then word n
                  else if r=word 4 then word 0x300008
                  else word 0)
      (\z:(5)word. word 0) (\k:(3)word. word 0) (word 2)
      (lw_memory image p q n different) []`;;

let lw_read = new_definition
 `lw_read p q n a <=> lw_image_read a \/ lw_overlay_domain p q n a`;;

let lw_execute = new_definition
 `lw_execute a <=> lw_image_execute a`;;

let lw_ordinary = new_definition
 `lw_ordinary p q n a <=> lw_image_domain a \/ lw_overlay_domain p q n a`;;

(* The same existing scalar E2 Pre, at the corrected actual-image placement.
   No functional equality, termination, trace or ABI preservation is assumed. *)
let lw_pre = new_definition
 `lw_pre image p q n different <=>
    bp_e2_crypto_pre 0x10241840 (word 0x300008) (word 0x400000)
      p q n (lw_memory image p q n different) (lw_read p q n) lw_execute
      (lw_ordinary p q n) (lw_state image p q n different)`;;
