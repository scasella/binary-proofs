# Literal caller contracts and access/frame predicates

Human review: **PENDING**. This view copies frozen statements and definitions without changing them. It is documentation, not a new acceptance input. `contracts-and-rules-v1.json` retains the exact accepted live conclusions and expanded terms, with source digests. The original sources and complete gates remain controlling.

## C1

Controlling frozen sources: `development/approved-plan/reusable-assurance-v1/c1/contract/statements-v1.ml` and `development/approved-plan/reusable-assurance-v1/c1/contract/definitions-v1.ml`.

### c1_checked_statement

```text
!lib_file lib_rw lib_padding client_file client_rw client_padding
    stackpointer ra p q n m rp wp xp ordinary s a.
    c1_pre lib_file lib_rw lib_padding client_file client_rw client_padding
      stackpointer ra p q n m rp wp xp ordinary (s,a)
    ==> assurance_checked_run (c1_steps n)
      (c1_scalar_post stackpointer ra p q n m s)
      (c1_step_policy stackpointer p q n rp wp xp ordinary) s
```

### c1_interface_statement

```text
!lib_file lib_rw lib_padding client_file client_rw client_padding
    stackpointer ra p q n m rp wp xp ordinary s a.
    c1_pre lib_file lib_rw lib_padding client_file client_rw client_padding
      stackpointer ra p q n m rp wp xp ordinary (s,a)
    ==> eventually_n abi_caller_scalar_extended_step (c1_steps n)
      (c1_public_post stackpointer ra p q n m s a) (s,a)
```

### c1_normal_checked_statement

```text
!lib_file lib_rw lib_padding client_file client_rw client_padding
    stackpointer ra p q n m rp wp xp ordinary s a.
    c1_pre lib_file lib_rw lib_padding client_file client_rw client_padding
      stackpointer ra p q n m rp wp xp ordinary (s,a)
    ==> assurance_checked_run (c1_steps n)
      (\t. c1_scalar_post stackpointer ra p q n m s t /\ e5_normal_flags t)
      (e5_normal_step_policy
        (c1_step_policy stackpointer p q n rp wp xp ordinary)) s
```

### c1_rf_normal_checked_statement

```text
!lib_file lib_rw lib_padding client_file client_rw client_padding
    stackpointer ra p q n m rp wp xp ordinary s a.
    c1_pre lib_file lib_rw lib_padding client_file client_rw client_padding
      stackpointer ra p q n m rp wp xp ordinary (s,a)
    ==> e5_rf_checked_run (c1_steps n)
      (\t. c1_scalar_post stackpointer ra p q n m s t /\ e5_normal_flags t)
      (e5_normal_step_policy
        (c1_step_policy stackpointer p q n rp wp xp ordinary)) s
```

### c1_normal_interface_statement

```text
!lib_file lib_rw lib_padding client_file client_rw client_padding
    stackpointer ra p q n m rp wp xp ordinary s a.
    c1_pre lib_file lib_rw lib_padding client_file client_rw client_padding
      stackpointer ra p q n m rp wp xp ordinary (s,a)
    ==> eventually_n e5_rf_retired_extended_step (c1_steps n)
      (\t. c1_public_post stackpointer ra p q n m s a t /\
           e5_normal_flags(FST t)) (s,a)
```

### c1_handoff_statement

```text
!lib_file lib_rw lib_padding client_file client_rw client_padding
    stackpointer ra p q n m rp wp xp ordinary s a.
    c1_pre lib_file lib_rw lib_padding client_file client_rw client_padding
      stackpointer ra p q n m rp wp xp ordinary (s,a)
    ==> assurance_checked_run 3
      (c1_crypto_ready lib_file stackpointer p q n m rp xp ordinary s a)
      (c1_segment_policy stackpointer p q n rp wp xp ordinary) s
```

### c1_count_statement

```text
!n. c1_steps n = 8 +
    (if n=0 then 6 else if n=16 then 15 else 7*n+10)
```

### c1_pre

```text
c1_pre lib_file lib_rw lib_padding client_file client_rw client_padding
    stackpointer ra p q n m rp wp xp ordinary
    (s:x86state,a:abi_omitted_state) <=>
    n<2 EXP 64 /\ 16<=val(stackpointer:int64) /\
    val stackpointer MOD 16=8 /\ val stackpointer+8<2 EXP 64 /\
    assurance_canonical48(val(ra:int64)) /\ ~(ra=word 0x21001110) /\
    read RIP s=word 0x21001110 /\ read RSP s=stackpointer /\
    read (memory :> bytes64 stackpointer) s=ra /\
    C_ARGUMENTS [p;q;word n] s /\ read memory s=m /\
    read DF s=F /\ ~bit 18(read rflags s) /\ e5_normal_flags s /\
    assurance_canonical48(val(read ABI_FS_BASE a)) /\
    fb_file_code lib_file /\ fb_full_image lib_file lib_rw lib_padding m /\
    c1_file_code client_file /\
    c1_full_image client_file client_rw client_padding m /\
    c1_loaded_code s /\ c1_got s /\
    (!addr. lw_image_domain addr ==>
       rp addr /\ ordinary addr /\ (xp addr <=> lw_execute addr) /\
       (wp addr <=> lw_image_write addr)) /\
    (!addr. c1_image_domain addr ==>
       rp addr /\ ordinary addr /\ (xp addr <=> c1_image_execute addr) /\
       (wp addr <=> c1_image_write addr)) /\
    assurance_span_ok (\a. rp a /\ ordinary a) (val p) n /\
    assurance_span_ok (\a. rp a /\ ordinary a) (val q) n /\
    assurance_span_ok (\a. rp a /\ ordinary a) (val stackpointer-16) 8 /\
    assurance_span_ok (\a. wp a /\ ordinary a) (val stackpointer-16) 8 /\
    assurance_span_ok (\a. rp a /\ ordinary a) (val stackpointer) 8 /\
    assurance_span_ok (\a. rp a /\ ordinary a) 0x21003fd8 8 /\
    assurance_span_ok (\a. xp a /\ ordinary a) 0x21001110 22 /\
    assurance_span_ok (\a. xp a /\ ordinary a) 0x21001030 6 /\
    assurance_span_ok (\a. xp a /\ ordinary a) 0x10241840 95 /\
    (!addr. ~(assurance_region p n addr /\ c1_call_slot stackpointer addr)) /\
    (!addr. ~(assurance_region q n addr /\ c1_call_slot stackpointer addr)) /\
    (!addr. ~(assurance_region stackpointer 8 addr /\
              c1_call_slot stackpointer addr))
```

### c1_allowed_read

```text
c1_allowed_read rp ordinary stackpointer p q n a <=>
    rp a /\ ordinary a /\
    (assurance_region p n a \/ assurance_region q n a \/
     c1_call_slot stackpointer a \/ assurance_region stackpointer 8 a \/
     assurance_region (word 0x21003fd8) 8 a)
```

### c1_allowed_write

```text
c1_allowed_write wp ordinary stackpointer a <=>
    wp a /\ ordinary a /\ c1_call_slot stackpointer a
```

### c1_allowed_fetch

```text
c1_allowed_fetch xp ordinary a <=>
    xp a /\ ordinary a /\
    (assurance_region (word 0x21001110) 22 a \/
     assurance_region (word 0x21001030) 6 a \/
     assurance_region (word 0x10241840) 95 a)
```

### c1_frame

```text
c1_frame stackpointer =
    MAYCHANGE [RIP;RSP;RAX;RDI;RSI;RDX;R10;R11] ,,
    MAYCHANGE SOME_FLAGS ,,
    MAYCHANGE [memory :> bytes(word_sub stackpointer (word 16),8)] ,,
    MAYCHANGE [events]
```

### c1_scalar_post

```text
c1_scalar_post stackpointer ra p q n m (s:x86state) t <=>
    read RIP t=ra /\ val(read RSP t)=val(stackpointer:int64)+8 /\
    read RAX t=(if (!i. i<n ==> m(word_add p (word i))=
                                  m(word_add q (word i)))
                then word 1 else word 0) /\
    (!addr. ~c1_call_slot stackpointer (val addr)
            ==> read memory t addr=m addr) /\
    read (memory :> bytes64 stackpointer) t=ra /\
    read RBX t=read RBX s /\ read RBP t=read RBP s /\
    read R12 t=read R12 s /\ read R13 t=read R13 s /\
    read R14 t=read R14 s /\ read R15 t=read R15 s /\
    read DF t=F /\ c1_loaded_code t /\ c1_got t /\
    c1_frame stackpointer s t
```

### c1_public_post

```text
c1_public_post stackpointer ra p q n m s a
    (t:x86state#abi_omitted_state) <=>
    c1_scalar_post stackpointer ra p q n m s (FST t) /\
    SND t=a /\ abi_required_controls_preserved a (SND t)
```

### c1_step_policy

```text
c1_step_policy stackpointer p q n rp wp xp ordinary
    remaining source target <=>
    c1_segment_policy stackpointer p q n rp wp xp ordinary
      remaining source target /\
    (remaining=1 ==> assurance_actual_ret 1 source target)
```

### c1_got

```text
c1_got (s:x86state) <=>
    read (memory :> bytes64 (word 0x21003fd8)) s=word 0x10241840
```

### c1_call_slot

```text
c1_call_slot (stackpointer:int64) a <=>
    assurance_region (word_sub stackpointer (word 16)) 8 a
```

### c1_crypto_ready

```text
c1_crypto_ready lib_file stackpointer p q n m rp xp ordinary
    (s:x86state) a (t:x86state) <=>
    bp_e2_crypto_public_pre lib_file (read memory t) (read memory t)
      (word_sub stackpointer (word 16)) (word 0x21001119) p q n
      (read memory t) rp xp ordinary (t,a) /\
    (!addr. ~c1_call_slot stackpointer (val addr)
            ==> read memory t addr=m addr) /\
    (!i. i<n ==> read memory t (word_add p (word i))=m(word_add p (word i))) /\
    (!i. i<n ==> read memory t (word_add q (word i))=m(word_add q (word i))) /\
    read (memory :> bytes64 stackpointer) t=
      read (memory :> bytes64 stackpointer) s /\
    c1_loaded_code t /\ c1_got t /\ c1_prefix_frame stackpointer s t
```

## C2

Controlling frozen sources: `development/approved-plan/reusable-assurance-c2-v1/spec/statements-v1.ml` and `development/approved-plan/reusable-assurance-c2-v1/spec/definitions-v1.ml`.

### c2_checked_statement

```text
!lib_file lib_rw lib_padding client_file client_rw client_padding
    stackpointer ra p q n m rp wp xp ordinary s a.
    c2_pre lib_file lib_rw lib_padding client_file client_rw client_padding
      stackpointer ra p q n m rp wp xp ordinary (s,a)
    ==> assurance_checked_run (c2_steps p q n m)
      (c2_scalar_post stackpointer ra p q n m s)
      (c2_step_policy stackpointer p q n m rp wp xp ordinary) s
```

### c2_interface_statement

```text
!lib_file lib_rw lib_padding client_file client_rw client_padding
    stackpointer ra p q n m rp wp xp ordinary s a.
    c2_pre lib_file lib_rw lib_padding client_file client_rw client_padding
      stackpointer ra p q n m rp wp xp ordinary (s,a)
    ==> eventually_n abi_caller_scalar_extended_step (c2_steps p q n m)
      (c2_public_post stackpointer ra p q n m s a) (s,a)
```

### c2_normal_checked_statement

```text
!lib_file lib_rw lib_padding client_file client_rw client_padding
    stackpointer ra p q n m rp wp xp ordinary s a.
    c2_pre lib_file lib_rw lib_padding client_file client_rw client_padding
      stackpointer ra p q n m rp wp xp ordinary (s,a)
    ==> assurance_checked_run (c2_steps p q n m)
      (\t. c2_scalar_post stackpointer ra p q n m s t /\ e5_normal_flags t)
      (e5_normal_step_policy
        (c2_step_policy stackpointer p q n m rp wp xp ordinary)) s
```

### c2_rf_normal_checked_statement

```text
!lib_file lib_rw lib_padding client_file client_rw client_padding
    stackpointer ra p q n m rp wp xp ordinary s a.
    c2_pre lib_file lib_rw lib_padding client_file client_rw client_padding
      stackpointer ra p q n m rp wp xp ordinary (s,a)
    ==> e5_rf_checked_run (c2_steps p q n m)
      (\t. c2_scalar_post stackpointer ra p q n m s t /\ e5_normal_flags t)
      (e5_normal_step_policy
        (c2_step_policy stackpointer p q n m rp wp xp ordinary)) s
```

### c2_normal_interface_statement

```text
!lib_file lib_rw lib_padding client_file client_rw client_padding
    stackpointer ra p q n m rp wp xp ordinary s a.
    c2_pre lib_file lib_rw lib_padding client_file client_rw client_padding
      stackpointer ra p q n m rp wp xp ordinary (s,a)
    ==> eventually_n e5_rf_retired_extended_step (c2_steps p q n m)
      (\t. c2_public_post stackpointer ra p q n m s a t /\
           e5_normal_flags(FST t)) (s,a)
```

### c2_handoff_statement

```text
!lib_file lib_rw lib_padding client_file client_rw client_padding
    stackpointer ra p q n m rp wp xp ordinary s a.
    c2_pre lib_file lib_rw lib_padding client_file client_rw client_padding
      stackpointer ra p q n m rp wp xp ordinary (s,a)
    ==> assurance_checked_run 8
      (c2_crypto_ready lib_file stackpointer p q n m rp wp xp ordinary s a)
      (c2_segment_policy stackpointer p q n m rp wp xp ordinary) s
```

### c2_count_statement

```text
!p q n m. c2_steps p q n m =
    if c2_equal m p q n
    then 20 + (if n=0 then 6 else if n=16 then 15 else 7*n+10)
            + cleanse_functional_steps p n
    else 16 + (if n=0 then 6 else if n=16 then 15 else 7*n+10)
```

### c2_pre

```text
c2_pre lib_file lib_rw lib_padding client_file client_rw
    client_padding stackpointer ra p q n m rp wp xp ordinary
    (s:x86state,a:abi_omitted_state) <=>
    n<2 EXP 64 /\ 32<=val(stackpointer:int64) /\
    val stackpointer MOD 16=8 /\ val stackpointer+8<2 EXP 64 /\
    assurance_canonical48(val(ra:int64)) /\ ~(ra=word 0x22001120) /\
    read RIP s=word 0x22001120 /\ read RSP s=stackpointer /\
    read (memory :> bytes64 stackpointer) s=ra /\
    C_ARGUMENTS [p;q;word n] s /\ read memory s=m /\
    read DF s=F /\ ~bit 18(read rflags s) /\ e5_normal_flags s /\
    assurance_canonical48(val(read ABI_FS_BASE a)) /\
    fb_file_code lib_file /\ clw_file_code lib_file /\
    fb_full_image lib_file lib_rw lib_padding m /\
    c2_file_code client_file /\
    c2_full_image client_file client_rw client_padding m /\
    c2_loaded_code s /\ c2_got s /\
    (!addr. lw_image_domain addr ==>
       rp addr /\ ordinary addr /\ (xp addr <=> lw_execute addr) /\
       (wp addr <=> lw_image_write addr)) /\
    (!addr. c2_image_domain addr ==>
       rp addr /\ ordinary addr /\
       (xp addr <=> c2_image_execute addr) /\
       (wp addr <=> c2_image_write addr)) /\
    assurance_span_ok (\a. rp a /\ ordinary a) (val p) n /\
    assurance_span_ok (\a. rp a /\ ordinary a) (val q) n /\
    assurance_span_ok (\a. wp a /\ ordinary a) (val p) n /\
    assurance_span_ok (\a. rp a /\ ordinary a) (val stackpointer-32) 32 /\
    assurance_span_ok (\a. wp a /\ ordinary a) (val stackpointer-32) 32 /\
    assurance_span_ok (\a. rp a /\ ordinary a) (val stackpointer) 8 /\
    assurance_span_ok (\a. rp a /\ ordinary a) 0x22003fd0 8 /\
    assurance_span_ok (\a. rp a /\ ordinary a) 0x22003fd8 8 /\
    assurance_span_ok (\a. xp a /\ ordinary a) 0x22001120 59 /\
    assurance_span_ok (\a. xp a /\ ordinary a) 0x22001030 6 /\
    assurance_span_ok (\a. xp a /\ ordinary a) 0x22001040 6 /\
    assurance_span_ok (\a. xp a /\ ordinary a) 0x10241840 95 /\
    assurance_span_ok (\a. xp a /\ ordinary a) 0x102417d0 97 /\
    (!addr. ~(assurance_region p n addr /\
               c2_scratch stackpointer addr)) /\
    (!addr. ~(assurance_region q n addr /\
               c2_scratch stackpointer addr)) /\
    (!addr. ~(assurance_region p n addr /\
               assurance_region stackpointer 8 addr))
```

### c2_allowed_read

```text
c2_allowed_read rp ordinary stackpointer p q n a <=>
    rp a /\ ordinary a /\
    (assurance_region p n a \/ assurance_region q n a \/
     c2_scratch stackpointer a \/
     assurance_region stackpointer 8 a \/
     assurance_region (word 0x22003fd0) 8 a \/
     assurance_region (word 0x22003fd8) 8 a)
```

### c2_allowed_write

```text
c2_allowed_write wp ordinary stackpointer p q n m a <=>
    wp a /\ ordinary a /\
    ((c2_equal m p q n /\ assurance_region p n a) \/
     c2_scratch stackpointer a)
```

### c2_allowed_fetch

```text
c2_allowed_fetch xp ordinary a <=>
    xp a /\ ordinary a /\
    (assurance_region (word 0x22001120) 59 a \/
     assurance_region (word 0x22001030) 6 a \/
     assurance_region (word 0x22001040) 6 a \/
     assurance_region (word 0x10241840) 95 a \/
     assurance_region (word 0x102417d0) 97 a)
```

### c2_frame

```text
c2_frame stackpointer p q n m =
    MAYCHANGE [RIP;RSP;RAX;RDI;RSI;RDX;R10;R11] ,,
    MAYCHANGE SOME_FLAGS ,,
    MAYCHANGE [memory :> bytes(p,if c2_equal m p q n then n else 0);
               memory :> bytes(word_sub stackpointer (word 32),32)] ,,
    MAYCHANGE [events]
```

### c2_scalar_post

```text
c2_scalar_post stackpointer ra p q n m (s:x86state) t <=>
    read RIP t=ra /\ val(read RSP t)=val(stackpointer:int64)+8 /\
    read RAX t=(if c2_equal m p q n then word 1 else word 0) /\
    (c2_equal m p q n
       ==> !i. i<n ==> read memory t (word_add p (word i))=word 0) /\
    (!addr. ~((c2_equal m p q n /\ assurance_region p n (val addr)) \/
               c2_scratch stackpointer (val addr))
            ==> read memory t addr=m addr) /\
    read (memory :> bytes64 stackpointer) t=ra /\
    read RBX t=read RBX s /\ read RBP t=read RBP s /\
    read R12 t=read R12 s /\ read R13 t=read R13 s /\
    read R14 t=read R14 s /\ read R15 t=read R15 s /\
    read DF t=F /\ c2_loaded_code t /\ c2_got t /\
    c2_frame stackpointer p q n m s t
```

### c2_public_post

```text
c2_public_post stackpointer ra p q n m s a
    (t:x86state#abi_omitted_state) <=>
    c2_scalar_post stackpointer ra p q n m s (FST t) /\
    SND t=a /\ abi_required_controls_preserved a (SND t)
```

### c2_step_policy

```text
c2_step_policy stackpointer p q n m rp wp xp ordinary
    (remaining:num) (source:x86state) (target:x86state) <=>
    assurance_step_policy
      (c2_allowed_read rp ordinary stackpointer p q n)
      (c2_allowed_write wp ordinary stackpointer p q n m)
      (c2_allowed_fetch xp ordinary) source target /\
    (remaining=1 ==> assurance_actual_ret 1 source target) /\
    abi_all_decodes_caller_scalar source
```

### c2_got

```text
c2_got (s:x86state) <=>
    read (memory :> bytes64 (word 0x22003fd0)) s=word 0x10241840 /\
    read (memory :> bytes64 (word 0x22003fd8)) s=word 0x102417d0
```

### c2_scratch

```text
c2_scratch (stackpointer:int64) a <=>
    assurance_region (word_sub stackpointer (word 32)) 32 a
```

### c2_equal

```text
c2_equal (m:int64->byte) (p:int64) (q:int64) n <=>
    !i. i<n ==> m(word_add p (word i))=m(word_add q (word i))
```

## C3

Controlling frozen sources: `development/approved-plan/held-out-transfer-v1/c3/contract/statements-v1.ml` and `development/approved-plan/held-out-transfer-v1/c3/contract/definitions-v2.ml`.

### c3_checked_statement

```text
!lib_file lib_rw lib_padding client_file client_rw client_padding
    stackpointer ra p q n m rp wp xp ordinary s a.
    c3_pre lib_file lib_rw lib_padding client_file client_rw client_padding
      stackpointer ra p q n m rp wp xp ordinary (s,a)
    ==> assurance_checked_run (c3_steps p q n m)
      (c3_scalar_post stackpointer ra p q n m s)
      (c3_step_policy stackpointer p q n m rp wp xp ordinary) s
```

### c3_interface_statement

```text
!lib_file lib_rw lib_padding client_file client_rw client_padding
    stackpointer ra p q n m rp wp xp ordinary s a.
    c3_pre lib_file lib_rw lib_padding client_file client_rw client_padding
      stackpointer ra p q n m rp wp xp ordinary (s,a)
    ==> eventually_n abi_caller_scalar_extended_step (c3_steps p q n m)
      (c3_public_post stackpointer ra p q n m s a) (s,a)
```

### c3_normal_checked_statement

```text
!lib_file lib_rw lib_padding client_file client_rw client_padding
    stackpointer ra p q n m rp wp xp ordinary s a.
    c3_pre lib_file lib_rw lib_padding client_file client_rw client_padding
      stackpointer ra p q n m rp wp xp ordinary (s,a)
    ==> assurance_checked_run (c3_steps p q n m)
      (\t. c3_scalar_post stackpointer ra p q n m s t /\ e5_normal_flags t)
      (e5_normal_step_policy
        (c3_step_policy stackpointer p q n m rp wp xp ordinary)) s
```

### c3_rf_normal_checked_statement

```text
!lib_file lib_rw lib_padding client_file client_rw client_padding
    stackpointer ra p q n m rp wp xp ordinary s a.
    c3_pre lib_file lib_rw lib_padding client_file client_rw client_padding
      stackpointer ra p q n m rp wp xp ordinary (s,a)
    ==> e5_rf_checked_run (c3_steps p q n m)
      (\t. c3_scalar_post stackpointer ra p q n m s t /\ e5_normal_flags t)
      (e5_normal_step_policy
        (c3_step_policy stackpointer p q n m rp wp xp ordinary)) s
```

### c3_normal_interface_statement

```text
!lib_file lib_rw lib_padding client_file client_rw client_padding
    stackpointer ra p q n m rp wp xp ordinary s a.
    c3_pre lib_file lib_rw lib_padding client_file client_rw client_padding
      stackpointer ra p q n m rp wp xp ordinary (s,a)
    ==> eventually_n e5_rf_retired_extended_step (c3_steps p q n m)
      (\t. c3_public_post stackpointer ra p q n m s a t /\
           e5_normal_flags(FST t)) (s,a)
```

### c3_handoff_statement

```text
!lib_file lib_rw lib_padding client_file client_rw client_padding
    stackpointer ra p q n m rp wp xp ordinary s a.
    c3_pre lib_file lib_rw lib_padding client_file client_rw client_padding
      stackpointer ra p q n m rp wp xp ordinary (s,a)
    ==> assurance_checked_run 10
      (c3_crypto_ready lib_file stackpointer p q n m rp wp xp ordinary s a)
      (c3_segment_policy stackpointer p q n m rp wp xp ordinary) s
```

### c3_count_statement

```text
!p q n m. c3_steps p q n m =
    (if c3_equal m p q n then 34 else 31) +
    2 * (if n=0 then 6 else if n=16 then 15 else 7*n+10) +
    cleanse_functional_steps p n
```

### c3_pre

```text
c3_pre lib_file lib_rw lib_padding client_file client_rw
    client_padding stackpointer ra p q n m rp wp xp ordinary
    (s:x86state,a:abi_omitted_state) <=>
    n<2 EXP 64 /\ 48<=val(stackpointer:int64) /\
    val stackpointer MOD 16=8 /\ val stackpointer+8<2 EXP 64 /\
    assurance_canonical48(val(ra:int64)) /\ ~(ra=word 0x23001120) /\
    read RIP s=word 0x23001120 /\ read RSP s=stackpointer /\
    read (memory :> bytes64 stackpointer) s=ra /\
    C_ARGUMENTS [p;q;word n] s /\ read memory s=m /\
    read DF s=F /\ ~bit 18(read rflags s) /\ e5_normal_flags s /\
    assurance_canonical48(val(read ABI_FS_BASE a)) /\
    fb_file_code lib_file /\ clw_file_code lib_file /\
    fb_full_image lib_file lib_rw lib_padding m /\
    c3_file_code client_file /\
    c3_full_image client_file client_rw client_padding m /\
    c3_loaded_code s /\ c3_got s /\
    (!addr. lw_image_domain addr ==>
       rp addr /\ ordinary addr /\ (xp addr <=> lw_execute addr) /\
       (wp addr <=> lw_image_write addr)) /\
    (!addr. c3_image_domain addr ==>
       rp addr /\ ordinary addr /\
       (xp addr <=> c3_image_execute addr) /\
       (wp addr <=> c3_image_write addr)) /\
    assurance_span_ok (\a. rp a /\ ordinary a) (val p) n /\
    assurance_span_ok (\a. rp a /\ ordinary a) (val q) n /\
    assurance_span_ok (\a. wp a /\ ordinary a) (val p) n /\
    assurance_span_ok (\a. rp a /\ ordinary a) (val stackpointer-48) 48 /\
    assurance_span_ok (\a. wp a /\ ordinary a) (val stackpointer-48) 48 /\
    assurance_span_ok (\a. rp a /\ ordinary a) (val stackpointer) 8 /\
    assurance_span_ok (\a. rp a /\ ordinary a) 0x23003fd0 8 /\
    assurance_span_ok (\a. rp a /\ ordinary a) 0x23003fd8 8 /\
    assurance_span_ok (\a. xp a /\ ordinary a) 0x23001120 89 /\
    assurance_span_ok (\a. xp a /\ ordinary a) 0x23001030 6 /\
    assurance_span_ok (\a. xp a /\ ordinary a) 0x23001040 6 /\
    assurance_span_ok (\a. xp a /\ ordinary a) 0x10241840 95 /\
    assurance_span_ok (\a. xp a /\ ordinary a) 0x102417d0 97 /\
    (!addr. ~(assurance_region p n addr /\
               c3_scratch stackpointer addr)) /\
    (!addr. ~(assurance_region q n addr /\
               c3_scratch stackpointer addr)) /\
    (!addr. ~(assurance_region p n addr /\
               assurance_region stackpointer 8 addr)) /\
    (!addr. assurance_region p n addr ==>
      ~(assurance_region (word 0x23001120) 89 addr \/
        assurance_region (word 0x23001030) 6 addr \/
        assurance_region (word 0x23001040) 6 addr \/
        assurance_region (word 0x23003fd0) 8 addr \/
        assurance_region (word 0x23003fd8) 8 addr \/
        assurance_region (word 0x10241840) 95 addr \/
        assurance_region (word 0x102417d0) 97 addr))
```

### c3_allowed_read

```text
c3_allowed_read rp ordinary stackpointer p q n a <=>
    rp a /\ ordinary a /\
    (assurance_region p n a \/ assurance_region q n a \/
     c3_scratch stackpointer a \/
     assurance_region stackpointer 8 a \/
     assurance_region (word 0x23003fd0) 8 a \/
     assurance_region (word 0x23003fd8) 8 a)
```

### c3_allowed_write

```text
c3_allowed_write wp ordinary stackpointer (p:int64) (q:int64) n (m:int64->byte) a <=>
    wp a /\ ordinary a /\
    ((assurance_region p n a) \/
     c3_scratch stackpointer a)
```

### c3_allowed_fetch

```text
c3_allowed_fetch xp ordinary a <=>
    xp a /\ ordinary a /\
    (assurance_region (word 0x23001120) 89 a \/
     assurance_region (word 0x23001030) 6 a \/
     assurance_region (word 0x23001040) 6 a \/
     assurance_region (word 0x10241840) 95 a \/
     assurance_region (word 0x102417d0) 97 a)
```

### c3_frame

```text
c3_frame stackpointer (p:int64) (q:int64) n (m:int64->byte) =
    MAYCHANGE [RIP;RSP;RAX;RDI;RSI;RDX;R10;R11] ,,
    MAYCHANGE SOME_FLAGS ,,
    MAYCHANGE [memory :> bytes(p,n);
               memory :> bytes(word_sub stackpointer (word 48),48)] ,,
    MAYCHANGE [events]
```

### c3_scalar_post

```text
c3_scalar_post stackpointer ra p q n m (s:x86state) t <=>
    read RIP t=ra /\ val(read RSP t)=val(stackpointer:int64)+8 /\
    read RAX t=c3_result m p q n /\
    (!i. i<n ==> read memory t (word_add p (word i))=word 0) /\
    (!i. i<n ==> read memory t (word_add q (word i))=
      c3_cleansed_memory m p n (word_add q (word i))) /\
    (!addr. ~(assurance_region p n (val addr) \/
               c3_scratch stackpointer (val addr))
            ==> read memory t addr=m addr) /\
    read (memory :> bytes64 stackpointer) t=ra /\
    read RBX t=read RBX s /\ read RBP t=read RBP s /\
    read R12 t=read R12 s /\ read R13 t=read R13 s /\
    read R14 t=read R14 s /\ read R15 t=read R15 s /\
    read DF t=F /\ c3_loaded_code t /\ c3_got t /\
    c3_frame stackpointer p q n m s t
```

### c3_public_post

```text
c3_public_post stackpointer ra p q n m s a
    (t:x86state#abi_omitted_state) <=>
    c3_scalar_post stackpointer ra p q n m s (FST t) /\
    SND t=a /\ abi_required_controls_preserved a (SND t)
```

### c3_step_policy

```text
c3_step_policy stackpointer p q n m rp wp xp ordinary
    (remaining:num) (source:x86state) (target:x86state) <=>
    assurance_step_policy
      (c3_allowed_read rp ordinary stackpointer p q n)
      (c3_allowed_write wp ordinary stackpointer p q n m)
      (c3_allowed_fetch xp ordinary) source target /\
    (remaining=1 ==> assurance_actual_ret 1 source target) /\
    abi_all_decodes_caller_scalar source
```

### c3_got

```text
c3_got (s:x86state) <=>
    read (memory :> bytes64 (word 0x23003fd0)) s=word 0x10241840 /\
    read (memory :> bytes64 (word 0x23003fd8)) s=word 0x102417d0
```

### c3_scratch

```text
c3_scratch (stackpointer:int64) a <=>
    assurance_region (word_sub stackpointer (word 48)) 48 a
```

### c3_equal

```text
c3_equal (m:int64->byte) (p:int64) (q:int64) n <=>
    !i. i<n ==> m(word_add p (word i))=m(word_add q (word i))
```

### c3_cleansed_memory

```text
c3_cleansed_memory (m:int64->byte) (p:int64) n (addr:int64) =
    if assurance_region p n (val addr) then word 0 else m addr
```

### c3_result

```text
c3_result (m:int64->byte) (p:int64) (q:int64) n =
    if c3_equal m p q n
    then if c3_equal (c3_cleansed_memory m p n) p q n then word 1 else word 0
    else word 2:int64
```

### c3_crypto_ready

```text
c3_crypto_ready lib_file stackpointer p q n m rp (wp:num->bool) xp
    ordinary (s:x86state) a (t:x86state) <=>
    bp_e2_crypto_public_pre lib_file (read memory t) (read memory t)
      (word_sub stackpointer (word 48)) (word 0x23001138) p q n
      (read memory t) rp xp ordinary (t,a) /\
    c3_saved_prefix stackpointer p q n m s t /\
    read R13 t=read R13 s /\ c3_prefix_frame stackpointer s t
```

