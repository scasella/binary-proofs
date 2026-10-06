let c3s_suffix_q = `\entry:x86state.  48<=val stackpointer /\ val stackpointer+8<2 EXP 64 /\
 read RIP entry=word 0x2300115a /\ read RSP entry=word_sub stackpointer(word 40) /\
 read R13 entry=(if c3_equal m p q n then word 1 else word 0) /\
 read RAX entry=(if c3_equal(c3_cleansed_memory m p n)p q n then word 0 else word 1) /\
 read(memory :> bytes64(word_sub stackpointer(word 8)))entry=read R13 initial /\
 read(memory :> bytes64(word_sub stackpointer(word 16)))entry=read R12 initial /\
 read(memory :> bytes64(word_sub stackpointer(word 24)))entry=read RBP initial /\
 read(memory :> bytes64(word_sub stackpointer(word 32)))entry=read RBX initial /\
 read(memory :> bytes64 stackpointer)entry=ra /\
 read R14 entry=read R14 initial /\ read R15 entry=read R15 initial /\
 read DF entry=F /\ ~bit 18(read rflags entry) /\
 (!i. i<n ==> read memory entry(word_add p(word i))=word 0) /\
 (!i. i<n ==> read memory entry(word_add q(word i))=
     c3_cleansed_memory m p n(word_add q(word i))) /\
 (!addr. ~(assurance_region p n(val addr) \/ c3_scratch stackpointer(val addr))
     ==> read memory entry addr=m addr) /\
 c3_loaded_code entry /\ c3_got entry /\
 (c3_frame stackpointer p q n m ,, MAYCHANGE[RBX;RBP;R12;R13])initial entry /\
 assurance_span_ok(c3_allowed_read rp ordinary stackpointer p q n)(val stackpointer-48)48 /\
 assurance_span_ok(c3_allowed_read rp ordinary stackpointer p q n)(val stackpointer)8 /\
 assurance_span_ok(c3_allowed_fetch xp ordinary)0x23001120 89`;;
