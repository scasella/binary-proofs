(* Explicit initial states and memory only. No transition or correctness premise. *)
let c2w_external = new_definition
 `c2w_external a <=> 0x50000000 <= a /\ assurance_canonical48 a`;;
let c2w_layout = new_definition
 `c2w_layout (p:int64) (q:int64) n k different <=>
    n<2 EXP 64 /\ assurance_span_ok c2w_external (val p) n /\
    assurance_span_ok c2w_external (val q) n /\
    (different ==> k<n /\
      !i. i<n ==> ~(word_add q (word i)=word_add p (word k)))`;;
let c2w_seed = new_definition
 `c2w_seed (lib_file:num->byte) (client_file:num->byte)
    (p:int64) k different (addr:int64) =
    if fb_immutable (val addr) then lib_file(val addr-0x10000000)
    else if c2_immutable (val addr) then client_file(val addr-0x22000000)
    else if different /\ addr=word_add p (word k) then word 255 else word 128`;;
let c2w_memory = new_definition
 `c2w_memory lib_file client_file p k different =
    write (bytes64 (word 0x300008)) (word 0x400000)
      (write (bytes64 (word 0x22003fd0)) (word 0x10241840)
        (write (bytes64 (word 0x22003fd8)) (word 0x102417d0)
          (c2w_seed lib_file client_file p k different)))`;;
let c2w_state = new_definition
 `c2w_state lib_file client_file p q n k different =
    x86state_RECORD (word 0x22001120)
      (\j:(4)word. if j=word 7 then p else if j=word 6 then q
                    else if j=word 2 then word n
                    else if j=word 4 then word 0x300008 else word 0)
      (\j:(5)word. word 0) (\j:(3)word. word 0) (word 2)
      (c2w_memory lib_file client_file p k different) []`;;
let c2w_read = new_definition
 `c2w_read a <=> assurance_canonical48 a /\ ~(a=0)`;;
let c2w_write = new_definition
 `c2w_write a <=>
    if lw_image_domain a then lw_image_write a
    else if c2_image_domain a then c2_image_write a
    else assurance_canonical48 a`;;
let c2w_execute = new_definition
 `c2w_execute a <=> lw_execute a \/ c2_image_execute a`;;
let c2w_ordinary = new_definition
 `c2w_ordinary a <=> assurance_canonical48 a`;;
let c2_entry_witness = new_definition
 `c2_entry_witness lib_file client_file p q n k different <=>
    ?lib_rw lib_padding client_rw client_padding m rp wp xp ordinary s a.
      c2_pre lib_file lib_rw lib_padding client_file client_rw client_padding
        (word 0x300008) (word 0x400000) p q n m rp wp xp ordinary (s,a) /\
      (!i. i<n ==> m(word_add p (word i))=
        (if different /\ i=k then word 255 else word 128)) /\
      (!i. i<n ==> m(word_add q (word i))=word 128) /\
      (p=word 0 /\ q=word 0 /\ n=0 ==> ~rp 0)`;;
