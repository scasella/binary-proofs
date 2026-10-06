(* Target qualification registry only; not the semantics extension. *)
let abi_crypto_site = new_definition
 `abi_crypto_site off len inst <=>
    (off = 0 /\ len = 4 /\ inst = ENDBR64) \/
    (off = 4 /\ len = 3 /\ inst = XOR (% rax) (% rax)) \/
    (off = 7 /\ len = 3 /\ inst = XOR (% r10) (% r10)) \/
    (off = 10 /\ len = 4 /\ inst = CMP (% rdx) (Imm8 (word 0))) \/
    (off = 14 /\ len = 2 /\ inst = JUMP Condition_Z (Imm8 (word 77))) \/
    (off = 16 /\ len = 4 /\ inst = CMP (% rdx) (Imm8 (word 16))) \/
    (off = 20 /\ len = 2 /\ inst = JUMP Condition_NZ (Imm8 (word 42))) \/
    (off = 22 /\ len = 3 /\ inst = MOV (% r10) (Memop Quadword (%% (rdi,0)))) \/
    (off = 25 /\ len = 4 /\ inst = MOV (% r11) (Memop Quadword (%% (rdi,8)))) \/
    (off = 29 /\ len = 7 /\ inst = MOV (% rdx) (Imm32 (word 1))) \/
    (off = 36 /\ len = 3 /\ inst = XOR (% r10) (Memop Quadword (%% (rsi,0)))) \/
    (off = 39 /\ len = 4 /\ inst = XOR (% r11) (Memop Quadword (%% (rsi,8)))) \/
    (off = 43 /\ len = 3 /\ inst = OR (% r10) (% r11)) \/
    (off = 46 /\ len = 4 /\ inst = CMOV Condition_NZ (% rax) (% rdx)) \/
    (off = 50 /\ len = 2 /\ inst = RET) \/
    (off = 64 /\ len = 3 /\ inst = MOV (% r10b) (Memop Byte (%% (rdi,0)))) \/
    (off = 67 /\ len = 4 /\ inst = LEA (% rdi) (%% (rdi,1))) \/
    (off = 71 /\ len = 3 /\ inst = XOR (% r10b) (Memop Byte (%% (rsi,0)))) \/
    (off = 74 /\ len = 4 /\ inst = LEA (% rsi) (%% (rsi,1))) \/
    (off = 78 /\ len = 3 /\ inst = OR (% al) (% r10b)) \/
    (off = 81 /\ len = 3 /\ inst = DEC (% rdx)) \/
    (off = 84 /\ len = 2 /\ inst = JUMP Condition_NZ (Imm8 (word 234))) \/
    (off = 86 /\ len = 3 /\ inst = NEG (% rax)) \/
    (off = 89 /\ len = 4 /\ inst = SHR (% rax) (Imm8 (word 63))) \/
    (off = 93 /\ len = 2 /\ inst = RET)`;;

