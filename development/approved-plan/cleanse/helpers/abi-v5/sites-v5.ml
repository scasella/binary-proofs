(* Exact frozen production decode constructors; padding +33/+44 excluded.
   Registry membership alone does not establish reachability. *)
let abi_cleanse_site = new_definition
 `abi_cleanse_site off len inst <=>
    (off = 0 /\ len = 4 /\ inst = ENDBR64) \/
    (off = 4 /\ len = 3 /\ inst = XOR (% rax) (% rax)) \/
    (off = 7 /\ len = 4 /\ inst = CMP (% rsi) (Imm8 (word 15))) \/
    (off = 11 /\ len = 2 /\ inst = JUMP Condition_NB (Imm8 (word 35))) \/
    (off = 13 /\ len = 4 /\ inst = CMP (% rsi) (Imm8 (word 0))) \/
    (off = 17 /\ len = 2 /\ inst = JUMP Condition_Z (Imm8 (word 12))) \/
    (off = 19 /\ len = 2 /\ inst = MOV (Memop Byte (%% (rdi,0))) (% al)) \/
    (off = 21 /\ len = 4 /\ inst = SUB (% rsi) (Imm8 (word 1))) \/
    (off = 25 /\ len = 4 /\ inst = LEA (% rdi) (%% (rdi,1))) \/
    (off = 29 /\ len = 2 /\ inst = JUMP Condition_NZ (Imm8 (word 244))) \/
    (off = 31 /\ len = 2 /\ inst = RET) \/
    (off = 48 /\ len = 7 /\ inst = TEST (% rdi) (Imm32 (word 7))) \/
    (off = 55 /\ len = 2 /\ inst = JUMP Condition_Z (Imm8 (word 12))) \/
    (off = 57 /\ len = 2 /\ inst = MOV (Memop Byte (%% (rdi,0))) (% al)) \/
    (off = 59 /\ len = 4 /\ inst = LEA (% rsi) (%% (rsi,18446744073709551615))) \/
    (off = 63 /\ len = 4 /\ inst = LEA (% rdi) (%% (rdi,1))) \/
    (off = 67 /\ len = 2 /\ inst = JUMP Unconditional (Imm8 (word 235))) \/
    (off = 69 /\ len = 3 /\ inst = MOV (Memop Quadword (%% (rdi,0))) (% rax)) \/
    (off = 72 /\ len = 4 /\ inst = LEA (% rsi) (%% (rsi,18446744073709551608))) \/
    (off = 76 /\ len = 7 /\ inst = TEST (% rsi) (Imm32 (word 4294967288))) \/
    (off = 83 /\ len = 4 /\ inst = LEA (% rdi) (%% (rdi,8))) \/
    (off = 87 /\ len = 2 /\ inst = JUMP Condition_NZ (Imm8 (word 236))) \/
    (off = 89 /\ len = 4 /\ inst = CMP (% rsi) (Imm8 (word 0))) \/
    (off = 93 /\ len = 2 /\ inst = JUMP Condition_NZ (Imm8 (word 180))) \/
    (off = 95 /\ len = 2 /\ inst = RET)`;;
