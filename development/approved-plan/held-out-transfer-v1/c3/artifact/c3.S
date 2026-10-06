/* Independent C3 selection: assembler-authored SysV AMD64 caller.
 * GCC assembles and links this source; no C-language refinement is claimed.
 * Three calls: compare initial bytes, clear p unconditionally, compare current bytes.
 * Return 2 for initial mismatch; otherwise return current equality (1 or 0).
 */
.text
.p2align 4
.globl c3_compare_clear_compare
.type c3_compare_clear_compare,@function
c3_compare_clear_compare:
    push %r13
    push %r12
    push %rbp
    push %rbx
    sub $8,%rsp
    mov %rdi,%rbx
    mov %rsi,%r12
    mov %rdx,%rbp
    call CRYPTO_memcmp@PLT
    xor %r13d,%r13d
    test %eax,%eax
    sete %r13b
    mov %rbp,%rsi
    mov %rbx,%rdi
    call OPENSSL_cleanse@PLT
    mov %rbp,%rdx
    mov %r12,%rsi
    mov %rbx,%rdi
    call CRYPTO_memcmp@PLT
    test %r13d,%r13d
    je .Linitial_mismatch
    test %eax,%eax
    sete %al
    movzbl %al,%eax
    jmp .Lrestore
.Linitial_mismatch:
    mov $2,%eax
.Lrestore:
    add $8,%rsp
    pop %rbx
    pop %rbp
    pop %r12
    pop %r13
    ret
.size c3_compare_clear_compare,.-c3_compare_clear_compare
.section .note.GNU-stack,"",@progbits
