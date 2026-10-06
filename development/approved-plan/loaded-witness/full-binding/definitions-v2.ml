(* BP-E2 full-image nonvacuity binding V2. Definitions only; freeze before
   proof search. file_bytes is the entire acquired final ELF byte map, whose
   interpretation is checked by an explicitly trusted acquisition boundary.
   The first three originally nonwritable PT_LOAD intervals are immutable.
   The fourth PT_LOAD's entire memory interval is public post-init state,
   INCLUDING its subsequently RELRO pages and initialized BSS. Page padding
   is explicit stable public background. No target behavior is assumed. *)

let fb_immutable = new_definition
 `fb_immutable a <=>
    (0x10000000 <= a /\ a < 0x100c4bd0) \/
    (0x100c5000 <= a /\ a < 0x103434c9) \/
    (0x10344000 <= a /\ a < 0x10421a40)`;;

let fb_initialized_rw = new_definition
 `fb_initialized_rw a <=> 0x10422e50 <= a /\ a < 0x104895b0`;;

let fb_reference_image = new_definition
 `fb_reference_image (file_bytes:num->byte) (initial_rw:int64->byte)
                     (padding:int64->byte) (a:int64) =
    if fb_immutable (val a) then file_bytes (val a-0x10000000)
    else if fb_initialized_rw (val a) then initial_rw a
    else padding a`;;

(* One coherent reference image fixes EVERY byte of EVERY mapped PT_LOAD
   page, not just code or logical segment extents. The conditional clauses
   above expose the precise exception to raw-file agreement. *)
let fb_full_image = new_definition
 `fb_full_image file_bytes initial_rw padding (image:int64->byte) <=>
    !a. lw_image_domain (val(a:int64))
        ==> image a = fb_reference_image file_bytes initial_rw padding a`;;

let fb_file_code = new_definition
 `fb_file_code (file_bytes:num->byte) <=>
    !i. i<95 ==> file_bytes(0x241840+i) = EL i crypto_memcmp_mc`;;

let fb_tls_page = new_definition
 `fb_tls_page a <=> 0x500000 <= a /\ a < 0x501000`;;

let fb_read = new_definition
 `fb_read p q n a <=> lw_read p q n a \/ fb_tls_page a`;;

let fb_ordinary = new_definition
 `fb_ordinary p q n a <=> lw_ordinary p q n a \/ fb_tls_page a`;;

(* This literal record has empty x87 tags, a reset control word, zero x87
   status/opcode/pointers/data, reset MXCSR, zero FS selector with canonical
   FS base at a declared ordinary mapped TLS page, and zero GS state.
   Fourteen field order is exactly state-v4.ml. *)
let fb_initial_abi = new_definition
 `fb_initial_abi = abi_omitted_state_RECORD
    (word 0x37f) (word 0) (word 0xffff) (word 0)
    (word 0) (word 0) (word 0) (word 0)
    (\r:(3)word. word 0) (word 0x1f80)
    (word 0) (word 0x500000) (word 0) (word 0)`;;

(* Expanded initial-state clauses are frozen and audited independently of
   the constructor. These are initial data, never a preservation premise. *)
let fb_abi_initial_fields = new_definition
 `fb_abi_initial_fields (a:abi_omitted_state) <=>
    read ABI_X87_CW a = word 0x37f /\
    read ABI_X87_SW a = word 0 /\
    read ABI_X87_TAG a = word 0xffff /\
    read ABI_X87_FOP a = word 0 /\
    read ABI_X87_IP a = word 0 /\
    read ABI_X87_CS a = word 0 /\
    read ABI_X87_DP a = word 0 /\
    read ABI_X87_DS a = word 0 /\
    (!r:(3)word. read ABI_X87_REGS a r = word 0) /\
    read ABI_MXCSR a = word 0x1f80 /\
    read ABI_FS_SELECTOR a = word 0 /\
    read ABI_FS_BASE a = word 0x500000 /\
    read ABI_GS_SELECTOR a = word 0 /\
    read ABI_GS_BASE a = word 0`;;

let fb_machine = new_definition
 `fb_machine image p q n different =
    (lw_state image p q n different,fb_initial_abi)`;;

(* The same scalar Pre used by all four all-length endpoints is instantiated
   with coherent page permissions extended by TLS. Its complete pair is
   supplied, not an assumed valid_state or preservation fact. *)
let fb_pre = new_definition
 `fb_pre file_bytes initial_rw padding image p q n different <=>
    fb_full_image file_bytes initial_rw padding
      (read memory (FST(fb_machine image p q n different))) /\
    bp_e2_crypto_pre 0x10241840 (word 0x300008) (word 0x400000)
      p q n (lw_memory image p q n different) (fb_read p q n) lw_execute
      (fb_ordinary p q n) (FST(fb_machine image p q n different)) /\
    fb_abi_initial_fields (SND(fb_machine image p q n different)) /\
    (!a. fb_tls_page a ==> fb_read p q n a /\ fb_ordinary p q n a) /\
    assurance_canonical48 (val(read ABI_FS_BASE
      (SND(fb_machine image p q n different))))`;;
