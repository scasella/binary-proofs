(* Explicit initial states and memory only. No transition or correctness premise. *)
let cw_external = new_definition
 `cw_external a <=> 0x50000000 <= a /\ assurance_canonical48 a`;;
let cw_layout = new_definition
 `cw_layout (p:int64) (q:int64) n k different <=>
    n<2 EXP 64 /\ assurance_span_ok cw_external (val p) n /\
    assurance_span_ok cw_external (val q) n /\
    (different ==> k<n /\
      !i. i<n ==> ~(word_add q (word i)=word_add p (word k)))`;;
let cw_seed = new_definition
 `cw_seed (lib_file:num->byte) (client_file:num->byte)
    (p:int64) k different (addr:int64) =
    if fb_immutable (val addr) then lib_file(val addr-0x10000000)
    else if c1_immutable (val addr) then client_file(val addr-0x21000000)
    else if different /\ addr=word_add p (word k) then word 255 else word 128`;;
let cw_memory = new_definition
 `cw_memory lib_file client_file p k different =
    write (bytes64 (word 0x300008)) (word 0x400000)
      (write (bytes64 (word 0x21003fd8)) (word 0x10241840)
        (cw_seed lib_file client_file p k different))`;;
let cw_state = new_definition
 `cw_state lib_file client_file p q n k different =
    x86state_RECORD (word 0x21001110)
      (\j:(4)word. if j=word 7 then p else if j=word 6 then q
                    else if j=word 2 then word n
                    else if j=word 4 then word 0x300008 else word 0)
      (\j:(5)word. word 0) (\j:(3)word. word 0) (word 2)
      (cw_memory lib_file client_file p k different) []`;;
let cw_read = new_definition
 `cw_read a <=> assurance_canonical48 a /\ ~(a=0)`;;
let cw_write = new_definition
 `cw_write a <=>
    if lw_image_domain a then lw_image_write a
    else if c1_image_domain a then c1_image_write a
    else assurance_canonical48 a`;;
let cw_execute = new_definition
 `cw_execute a <=> lw_execute a \/ c1_image_execute a`;;
let cw_ordinary = new_definition
 `cw_ordinary a <=> assurance_canonical48 a`;;
let c1_entry_witness = new_definition
 `c1_entry_witness lib_file client_file p q n k different <=>
    ?lib_rw lib_padding client_rw client_padding m rp wp xp ordinary s a.
      c1_pre lib_file lib_rw lib_padding client_file client_rw client_padding
        (word 0x300008) (word 0x400000) p q n m rp wp xp ordinary (s,a) /\
      (!i. i<n ==> m(word_add p (word i))=
        (if different /\ i=k then word 255 else word 128)) /\
      (!i. i<n ==> m(word_add q (word i))=word 128) /\
      (p=word 0 /\ q=word 0 /\ n=0 ==> ~rp 0)`;;
