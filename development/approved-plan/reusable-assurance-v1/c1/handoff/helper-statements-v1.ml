(* Exact C1 helper obligations. Frozen before their proof source. *)
let c1_stack_sub16_value_statement =
 `!stackpointer:int64. 16<=val stackpointer
    ==> val(word_sub stackpointer (word 16):int64)=val stackpointer-16`;;
let c1_stack_alignment_statement =
 `!stackpointer:int64. 16<=val stackpointer /\ val stackpointer MOD 16=8
    ==> val(word_sub stackpointer (word 16):int64) MOD 16=8`;;
let c1_span_point_statement =
 `!P p:int64 n addr. assurance_span_ok P (val p) n /\
    assurance_region p n addr ==> P addr`;;
let c1_span_word_add_region_statement =
 `!P p:int64 n i. assurance_span_ok P (val p) n /\ i<n
    ==> assurance_region p n (val(word_add p (word i)))`;;
let c1_region_nonoverlapping_statement =
 `!p q:int64 n k. val p+n<=2 EXP 64 /\ val q+k<=2 EXP 64 /\
    (!addr. ~(assurance_region p n addr /\ assurance_region q k addr))
    ==> nonoverlapping(p,n)(q,k)`;;
let c1_nonoverlapping_region_disjoint_statement =
 `!p q:int64 n k. val p+n<=2 EXP 64 /\ val q+k<=2 EXP 64 /\
    nonoverlapping(p,n)(q,k)
    ==> !addr. ~(assurance_region p n addr /\ assurance_region q k addr)`;;
let c1_writable_readonly_nonoverlapping_statement =
 `!wp ordinary (p:int64) n (q:int64) k.
    assurance_span_ok (\addr. wp addr /\ ordinary addr) (val p) n /\
    val q+k<=2 EXP 64 /\
    (!addr. assurance_region q k addr ==> ~wp addr)
    ==> nonoverlapping(p,n)(q,k)`;;
let c1_library_rebind_statement =
 `!file_bytes initial_rw padding m current.
    fb_full_image file_bytes initial_rw padding m /\
    (!a:int64. fb_immutable(val a) ==> current a=m a)
    ==> fb_full_image file_bytes current current current`;;
let c1_library_immutable_readonly_statement =
 `!addr. fb_immutable addr ==> lw_image_domain addr /\ ~lw_image_write addr`;;
let c1_caller_readonly_region_statement =
 `!addr. assurance_region (word 0x21001110) 22 addr
    ==> c1_image_domain addr /\ ~c1_image_write addr`;;
let c1_plt_readonly_region_statement =
 `!addr. assurance_region (word 0x21001030) 6 addr
    ==> c1_image_domain addr /\ ~c1_image_write addr`;;
let c1_got_readonly_region_statement =
 `!addr. assurance_region (word 0x21003fd8) 8 addr
    ==> c1_image_domain addr /\ ~c1_image_write addr`;;
let c1_crypto_readonly_region_statement =
 `!addr. assurance_region (word 0x10241840) 95 addr
    ==> lw_image_domain addr /\ ~lw_image_write addr`;;
let c1_slot_read_span_statement =
 `!stackpointer p q n rp ordinary.
    16<=val(stackpointer:int64) /\
    assurance_span_ok (\addr. rp addr /\ ordinary addr) (val stackpointer-16) 8
    ==> assurance_span_ok (c1_allowed_read rp ordinary stackpointer p q n)
          (val stackpointer-16) 8`;;
let c1_slot_write_span_statement =
 `!stackpointer wp ordinary.
    16<=val(stackpointer:int64) /\
    assurance_span_ok (\addr. wp addr /\ ordinary addr) (val stackpointer-16) 8
    ==> assurance_span_ok (c1_allowed_write wp ordinary stackpointer)
          (val stackpointer-16) 8`;;
let c1_caller_fetch_span_statement =
 `!xp ordinary. assurance_span_ok (\addr. xp addr /\ ordinary addr) 0x21001110 22
    ==> assurance_span_ok (c1_allowed_fetch xp ordinary) 0x21001110 22`;;
let c1_plt_fetch_span_statement =
 `!xp ordinary. assurance_span_ok (\addr. xp addr /\ ordinary addr) 0x21001030 6
    ==> assurance_span_ok (c1_allowed_fetch xp ordinary) 0x21001030 6`;;
let c1_got_read_span_statement =
 `!rp ordinary stackpointer p q n.
    assurance_span_ok (\addr. rp addr /\ ordinary addr) 0x21003fd8 8
    ==> assurance_span_ok (c1_allowed_read rp ordinary stackpointer p q n)
          0x21003fd8 8`;;
let c1_library_slot_disjoint_statement =
 `!stackpointer:int64 wp ordinary.
    16<=val stackpointer /\
    assurance_span_ok (\addr. wp addr /\ ordinary addr) (val stackpointer-16) 8 /\
    (!addr. lw_image_domain addr ==> (wp addr <=> lw_image_write addr))
    ==> !addr. fb_immutable addr ==> ~c1_call_slot stackpointer addr`;;
let c1_slot_byte_nonoverlapping_statement =
 `!stackpointer addr:int64. 16<=val stackpointer /\
    ~c1_call_slot stackpointer (val addr)
    ==> nonoverlapping(addr,1)(word_sub stackpointer (word 16),8)`;;
let c1_prefix_frame_byte_statement =
 `!stackpointer addr:int64 s t:x86state.
    16<=val stackpointer /\ ~c1_call_slot stackpointer (val addr) /\
    c1_prefix_frame stackpointer s t
    ==> read memory t addr=read memory s addr`;;
let c1_prefix_frame_incoming_slot_statement =
 `!stackpointer:int64 s t:x86state.
    16<=val stackpointer /\ val stackpointer+8<2 EXP 64 /\
    c1_prefix_frame stackpointer s t
    ==> read (memory :> bytes64 stackpointer) t=
        read (memory :> bytes64 stackpointer) s`;;
let c1_unchanged_buffer_statement =
 `!P p:int64 n stackpointer:int64 m t:x86state.
    assurance_span_ok P (val p) n /\
    (!addr. ~(assurance_region p n addr /\ c1_call_slot stackpointer addr)) /\
    (!addr. ~c1_call_slot stackpointer (val addr) ==> read memory t addr=m addr)
    ==> !i. i<n ==> read memory t (word_add p (word i))=m(word_add p (word i))`;;
