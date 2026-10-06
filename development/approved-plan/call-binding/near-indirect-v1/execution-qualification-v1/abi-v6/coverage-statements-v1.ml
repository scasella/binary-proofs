(* Exact independent byte-to-qualified-decode targets frozen before proof search. *)
let abi_caller_decode_0_0_statement =
 `!pc s. bytes_loaded s (word pc) r1_secret_caller_mc ==> x86_decode s (word(pc+0)) (2,PUSH (Register(Gpr (word 12) Full_64)))`;;
let abi_caller_decode_0_2_statement =
 `!pc s. bytes_loaded s (word pc) r1_secret_caller_mc ==> x86_decode s (word(pc+2)) (1,PUSH (Register(Gpr (word 5) Full_64)))`;;
let abi_caller_decode_0_3_statement =
 `!pc s. bytes_loaded s (word pc) r1_secret_caller_mc ==> x86_decode s (word(pc+3)) (3,MOV (Register(Gpr (word 5) Full_64)) (Register(Gpr (word 2) Full_64)))`;;
let abi_caller_decode_0_6_statement =
 `!pc s. bytes_loaded s (word pc) r1_secret_caller_mc ==> x86_decode s (word(pc+6)) (1,PUSH (Register(Gpr (word 3) Full_64)))`;;
let abi_caller_decode_0_7_statement =
 `!pc s. bytes_loaded s (word pc) r1_secret_caller_mc ==> x86_decode s (word(pc+7)) (3,MOV (Register(Gpr (word 3) Full_64)) (Register(Gpr (word 7) Full_64)))`;;
let abi_caller_decode_0_10_statement =
 `!pc s. bytes_loaded s (word pc) r1_secret_caller_mc ==> x86_decode s (word(pc+10)) (5,CALL (Imm32(word 0xfffffed1)))`;;
let abi_caller_decode_0_15_statement =
 `!pc s. bytes_loaded s (word pc) r1_secret_caller_mc ==> x86_decode s (word(pc+15)) (3,MOV (Register(Gpr (word 6) Full_64)) (Register(Gpr (word 5) Full_64)))`;;
let abi_caller_decode_0_18_statement =
 `!pc s. bytes_loaded s (word pc) r1_secret_caller_mc ==> x86_decode s (word(pc+18)) (3,MOV (Register(Gpr (word 7) Full_64)) (Register(Gpr (word 3) Full_64)))`;;
let abi_caller_decode_0_21_statement =
 `!pc s. bytes_loaded s (word pc) r1_secret_caller_mc ==> x86_decode s (word(pc+21)) (3,MOV (Register(Gpr (word 12) Lower_32)) (Register(Gpr (word 0) Lower_32)))`;;
let abi_caller_decode_0_24_statement =
 `!pc s. bytes_loaded s (word pc) r1_secret_caller_mc ==> x86_decode s (word(pc+24)) (5,CALL (Imm32(word 0xfffffed3)))`;;
let abi_caller_decode_0_29_statement =
 `!pc s. bytes_loaded s (word pc) r1_secret_caller_mc ==> x86_decode s (word(pc+29)) (2,XOR (Register(Gpr (word 0) Lower_32)) (Register(Gpr (word 0) Lower_32)))`;;
let abi_caller_decode_0_31_statement =
 `!pc s. bytes_loaded s (word pc) r1_secret_caller_mc ==> x86_decode s (word(pc+31)) (3,TEST (Register(Gpr (word 12) Lower_32)) (Register(Gpr (word 12) Lower_32)))`;;
let abi_caller_decode_0_34_statement =
 `!pc s. bytes_loaded s (word pc) r1_secret_caller_mc ==> x86_decode s (word(pc+34)) (1,POP (Register(Gpr (word 3) Full_64)))`;;
let abi_caller_decode_0_35_statement =
 `!pc s. bytes_loaded s (word pc) r1_secret_caller_mc ==> x86_decode s (word(pc+35)) (3,SET Condition_Z (Register(Gpr (word 0) Lower_8)))`;;
let abi_caller_decode_0_38_statement =
 `!pc s. bytes_loaded s (word pc) r1_secret_caller_mc ==> x86_decode s (word(pc+38)) (1,POP (Register(Gpr (word 5) Full_64)))`;;
let abi_caller_decode_0_39_statement =
 `!pc s. bytes_loaded s (word pc) r1_secret_caller_mc ==> x86_decode s (word(pc+39)) (2,POP (Register(Gpr (word 12) Full_64)))`;;
let abi_caller_decode_0_41_statement =
 `!pc s. bytes_loaded s (word pc) r1_secret_caller_mc ==> x86_decode s (word(pc+41)) (1,RET)`;;
let abi_caller_decode_1_0_statement =
 `!pc s. bytes_loaded s (word pc) r1_public_caller_mc ==> x86_decode s (word(pc+0)) (4,SUB (Register(Gpr (word 4) Full_64)) (Imm8(word 8)))`;;
let abi_caller_decode_1_4_statement =
 `!pc s. bytes_loaded s (word pc) r1_public_caller_mc ==> x86_decode s (word(pc+4)) (5,CALL(Imm32(word 0xffffff17)))`;;
let abi_caller_decode_1_9_statement =
 `!pc s. bytes_loaded s (word pc) r1_public_caller_mc ==> x86_decode s (word(pc+9)) (2,TEST (Register(Gpr (word 0) Lower_32)) (Register(Gpr (word 0) Lower_32)))`;;
let abi_caller_decode_1_11_statement =
 `!pc s. bytes_loaded s (word pc) r1_public_caller_mc ==> x86_decode s (word(pc+11)) (3,SET Condition_Z (Register(Gpr (word 0) Lower_8)))`;;
let abi_caller_decode_1_14_statement =
 `!pc s. bytes_loaded s (word pc) r1_public_caller_mc ==> x86_decode s (word(pc+14)) (4,ADD (Register(Gpr (word 4) Full_64)) (Imm8(word 8)))`;;
let abi_caller_decode_1_18_statement =
 `!pc s. bytes_loaded s (word pc) r1_public_caller_mc ==> x86_decode s (word(pc+18)) (3,MOVZX (Register(Gpr (word 0) Lower_32)) (Register(Gpr (word 0) Lower_8)))`;;
let abi_caller_decode_1_21_statement =
 `!pc s. bytes_loaded s (word pc) r1_public_caller_mc ==> x86_decode s (word(pc+21)) (1,RET)`;;
let abi_caller_decode_2_0_statement =
 `!pc s. bytes_loaded s (word pc) r1_crypto_plt_prefix ==> x86_decode s (word(pc+0)) (6,JUMP Unconditional (Memop Quadword (Riprel(word 0x2f92))))`;;
let abi_caller_decode_3_0_statement =
 `!pc s. bytes_loaded s (word pc) r1_cleanse_plt_prefix ==> x86_decode s (word(pc+0)) (6,JUMP Unconditional (Memop Quadword (Riprel(word 0x2f8a))))`;;
let abi_caller_decode_4_0_statement =
 `!pc s. bytes_loaded s (word pc) r1_memcmp_plt_prefix ==> x86_decode s (word(pc+0)) (6,JUMP Unconditional (Memop Quadword (Riprel(word 0x2f82))))`;;
let abi_caller_site_scalar_statement =
 `!family off len inst. abi_caller_site family off len inst ==> abi_caller_scalar_instruction inst`;;
let abi_caller_coverage_statement =
 `!pc s code family off len inst. abi_caller_code family code /\ bytes_loaded s (word pc) code /\ abi_caller_site family off len inst /\ read RIP s=word(pc+off) ==> x86_decode s (read RIP s) (len,inst) /\ abi_all_decodes_caller_scalar s`;;
