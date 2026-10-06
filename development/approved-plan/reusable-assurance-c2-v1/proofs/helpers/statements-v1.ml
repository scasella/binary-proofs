(* New C2-specific helper goals tied to named prefix/branch/return obligations. *)
let c2_policy_span_statement = `!P Q (p:int64) n. (!addr. P addr /\ assurance_region p n addr ==> Q addr) /\ assurance_span_ok P (val p) n ==> assurance_span_ok Q (val p) n`;;
let c2_span_point_statement = `!P (p:int64) n addr. assurance_span_ok P (val p) n /\ assurance_region p n addr ==> P addr`;;
let c2_region_nonoverlapping_statement = `!p q n k. val(p:int64)+n <= 2 EXP 64 /\ val(q:int64)+k <= 2 EXP 64 /\ (!addr. ~(assurance_region p n addr /\ assurance_region q k addr)) ==> nonoverlapping(p,n)(q,k)`;;
let c2_scratch_read_span_statement = `!stackpointer p q n rp ordinary. 32<=val(stackpointer:int64) /\ assurance_span_ok (\addr. rp addr /\ ordinary addr) (val stackpointer-32) 32 ==> assurance_span_ok (c2_allowed_read rp ordinary stackpointer p q n) (val stackpointer-32) 32`;;
let c2_scratch_write_span_statement = `!stackpointer p q n m wp ordinary. 32<=val(stackpointer:int64) /\ assurance_span_ok (\addr. wp addr /\ ordinary addr) (val stackpointer-32) 32 ==> assurance_span_ok (c2_allowed_write wp ordinary stackpointer p q n m) (val stackpointer-32) 32`;;
let c2_caller_fetch_span_statement = `!xp ordinary. assurance_span_ok (\addr. xp addr /\ ordinary addr) 0x22001120 59 ==> assurance_span_ok (c2_allowed_fetch xp ordinary) 0x22001120 59`;;
let c2_crypto_plt_fetch_span_statement = `!xp ordinary. assurance_span_ok (\addr. xp addr /\ ordinary addr) 0x22001030 6 ==> assurance_span_ok (c2_allowed_fetch xp ordinary) 0x22001030 6`;;
let c2_cleanse_plt_fetch_span_statement = `!xp ordinary. assurance_span_ok (\addr. xp addr /\ ordinary addr) 0x22001040 6 ==> assurance_span_ok (c2_allowed_fetch xp ordinary) 0x22001040 6`;;
let c2_writable_readonly_nonoverlapping_statement = `!wp ordinary (p:int64) n (q:int64) k. assurance_span_ok (\addr. wp addr /\ ordinary addr) (val p) n /\ val q+k<=2 EXP 64 /\ (!addr. assurance_region q k addr ==> ~wp addr) ==> nonoverlapping(p,n)(q,k)`;;
let c2_caller_readonly_region_statement = `!addr. assurance_region (word 0x22001120) 59 addr ==> c2_image_domain addr /\ ~c2_image_write addr`;;
let c2_crypto_plt_readonly_region_statement = `!addr. assurance_region (word 0x22001030) 6 addr ==> c2_image_domain addr /\ ~c2_image_write addr`;;
let c2_cleanse_plt_readonly_region_statement = `!addr. assurance_region (word 0x22001040) 6 addr ==> c2_image_domain addr /\ ~c2_image_write addr`;;
let c2_crypto_readonly_region_statement = `!addr. assurance_region (word 0x10241840) 95 addr ==> lw_image_domain addr /\ ~lw_image_write addr`;;
let c2_cleanse_readonly_region_statement = `!addr. assurance_region (word 0x102417d0) 97 addr ==> lw_image_domain addr /\ ~lw_image_write addr`;;
let c2_crypto_got_readonly_region_statement = `!addr. assurance_region (word 0x22003fd0) 8 addr ==> c2_image_domain addr /\ ~c2_image_write addr`;;
let c2_cleanse_got_readonly_region_statement = `!addr. assurance_region (word 0x22003fd8) 8 addr ==> c2_image_domain addr /\ ~c2_image_write addr`;;
let c2_crypto_got_read_span_statement = `!rp ordinary stackpointer p q n. assurance_span_ok (\addr. rp addr /\ ordinary addr) 0x22003fd0 8 ==> assurance_span_ok (c2_allowed_read rp ordinary stackpointer p q n) 0x22003fd0 8`;;
let c2_cleanse_got_read_span_statement = `!rp ordinary stackpointer p q n. assurance_span_ok (\addr. rp addr /\ ordinary addr) 0x22003fd8 8 ==> assurance_span_ok (c2_allowed_read rp ordinary stackpointer p q n) 0x22003fd8 8`;;
let c2_incoming_read_span_statement = `!rp ordinary (stackpointer:int64) p q n. assurance_span_ok (\addr. rp addr /\ ordinary addr) (val stackpointer) 8 ==> assurance_span_ok (c2_allowed_read rp ordinary stackpointer p q n) (val stackpointer) 8`;;
let c2_library_immutable_readonly_statement = `!addr. fb_immutable addr ==> lw_image_domain addr /\ ~lw_image_write addr`;;
let c2_immutable_readonly_statement = `!addr. c2_immutable addr ==> c2_image_domain addr /\ ~c2_image_write addr`;;
let c2_span_word_add_region_statement = `!P p:int64 n i. assurance_span_ok P (val p) n /\ i<n ==> assurance_region p n (val(word_add p (word i)))`;;
let c2_library_scratch_disjoint_statement = `!stackpointer:int64 wp ordinary.
 32<=val stackpointer /\
 assurance_span_ok (\addr. wp addr /\ ordinary addr) (val stackpointer-32) 32 /\
 (!addr. lw_image_domain addr ==> (wp addr <=> lw_image_write addr))
 ==> !addr. fb_immutable addr ==> ~c2_scratch stackpointer addr`;;
let c2_unchanged_buffer_statement = `!P p:int64 n stackpointer:int64 m t:x86state.
 assurance_span_ok P (val p) n /\
 (!addr. ~(assurance_region p n addr /\ c2_scratch stackpointer addr)) /\
 (!addr. ~c2_scratch stackpointer (val addr) ==> read memory t addr=m addr)
 ==> !i. i<n ==> read memory t (word_add p (word i))=m(word_add p (word i))`;;
let c2_nonoverlapping_region_disjoint_statement = `!p q:int64 n k.
 val p+n<=2 EXP 64 /\ val q+k<=2 EXP 64 /\ nonoverlapping(p,n)(q,k)
 ==> !addr. ~(assurance_region p n addr /\ assurance_region q k addr)`;;
let c2_scratch_slot_region_statement = `!stackpointer:int64 addr.
 assurance_region (word_sub stackpointer (word 32)) 8 addr ==> c2_scratch stackpointer addr`;;
let c2_stack_alignment_statement = `!stackpointer:int64.
    32<=val stackpointer /\ val stackpointer MOD 16=8
    ==> val(word_sub stackpointer (word 32):int64)=val stackpointer-32 /\
        val(word_sub stackpointer (word 32):int64) MOD 16=8`;;
let c2_stack_segment_span_statement = `!P (stackpointer:int64) k width. 32<=val stackpointer /\ k<=32 /\ width<=k /\ assurance_span_ok P (val stackpointer-32) 32 ==> assurance_span_ok P (val(word_sub stackpointer (word k))) width`;;
let c2_scratch_byte_nonoverlapping_statement = `!stackpointer addr:int64. 32<=val stackpointer /\
 ~c2_scratch stackpointer (val addr)
 ==> nonoverlapping(addr,1)(word_sub stackpointer (word 32),32)`;;
let c2_prefix_frame_byte_statement = `!stackpointer addr:int64 s t:x86state.
 32<=val stackpointer /\ ~c2_scratch stackpointer (val addr) /\
 c2_prefix_frame stackpointer s t
 ==> read memory t addr = read memory s addr`;;
let c2_library_rebind_statement = `!file_bytes initial_rw padding m m'.
    fb_full_image file_bytes initial_rw padding m /\
    (!addr. fb_immutable (val addr) ==> m' addr=m addr)
    ==> fb_full_image file_bytes m' m' m'`;;
