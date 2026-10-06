(* Explicit admissible-entry states, arbitrary external payload and layouts. No transition premise. *)
let c3w_external = new_definition
 `c3w_external a <=> 0x50000000 <= a /\ assurance_canonical48 a`;;
let c3w_layout = new_definition
 `c3w_layout (p:int64) (q:int64) n <=>
    n<2 EXP 64 /\ assurance_span_ok c3w_external (val p) n /\
    assurance_span_ok c3w_external (val q) n`;;
let c3w_seed = new_definition
 `c3w_seed (lib_file:num->byte) (client_file:num->byte)
    (payload:int64->byte) (addr:int64) =
    if fb_immutable (val addr) then lib_file(val addr-0x10000000)
    else if c3_immutable (val addr) then client_file(val addr-0x23000000)
    else payload addr`;;
let c3w_memory = new_definition
 `c3w_memory lib_file client_file payload =
    write (bytes64 (word 0x300008)) (word 0x400000)
      (write (bytes64 (word 0x23003fd0)) (word 0x10241840)
        (write (bytes64 (word 0x23003fd8)) (word 0x102417d0)
          (c3w_seed lib_file client_file payload)))`;;
let c3w_state = new_definition
 `c3w_state lib_file client_file payload p q n =
    x86state_RECORD (word 0x23001120)
      (\j:(4)word. if j=word 7 then p else if j=word 6 then q
                    else if j=word 2 then word n
                    else if j=word 4 then word 0x300008 else word 0)
      (\j:(5)word. word 0) (\j:(3)word. word 0) (word 2)
      (c3w_memory lib_file client_file payload) []`;;
let c3w_read = new_definition
 `c3w_read a <=> assurance_canonical48 a /\ ~(a=0)`;;
let c3w_write = new_definition
 `c3w_write a <=>
    if lw_image_domain a then lw_image_write a
    else if c3_image_domain a then c3_image_write a
    else assurance_canonical48 a`;;
let c3w_execute = new_definition
 `c3w_execute a <=> lw_execute a \/ c3_image_execute a`;;
let c3w_ordinary = new_definition
 `c3w_ordinary a <=> assurance_canonical48 a`;;
let c3_entry_witness = new_definition
 `c3_entry_witness lib_file client_file payload p q n <=>
    ?lib_rw lib_padding client_rw client_padding m rp wp xp ordinary s a.
      c3_pre lib_file lib_rw lib_padding client_file client_rw client_padding
        (word 0x300008) (word 0x400000) p q n m rp wp xp ordinary (s,a) /\
      (!i. i<n ==> m(word_add p (word i))=payload(word_add p (word i))) /\
      (!i. i<n ==> m(word_add q (word i))=payload(word_add q (word i))) /\
      (p=word 0 /\ q=word 0 /\ n=0 ==> ~rp 0)`;;
