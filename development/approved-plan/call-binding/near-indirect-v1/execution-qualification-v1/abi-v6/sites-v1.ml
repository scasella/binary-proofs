let abi_caller_site = new_definition
 `abi_caller_site family off len inst <=>
   (family=0 /\ off=0 /\ len=2 /\ inst=PUSH (Register(Gpr (word 12) Full_64))) \/
   (family=0 /\ off=2 /\ len=1 /\ inst=PUSH (Register(Gpr (word 5) Full_64))) \/
   (family=0 /\ off=3 /\ len=3 /\ inst=MOV (Register(Gpr (word 5) Full_64)) (Register(Gpr (word 2) Full_64))) \/
   (family=0 /\ off=6 /\ len=1 /\ inst=PUSH (Register(Gpr (word 3) Full_64))) \/
   (family=0 /\ off=7 /\ len=3 /\ inst=MOV (Register(Gpr (word 3) Full_64)) (Register(Gpr (word 7) Full_64))) \/
   (family=0 /\ off=10 /\ len=5 /\ inst=CALL (Imm32(word 0xfffffed1))) \/
   (family=0 /\ off=15 /\ len=3 /\ inst=MOV (Register(Gpr (word 6) Full_64)) (Register(Gpr (word 5) Full_64))) \/
   (family=0 /\ off=18 /\ len=3 /\ inst=MOV (Register(Gpr (word 7) Full_64)) (Register(Gpr (word 3) Full_64))) \/
   (family=0 /\ off=21 /\ len=3 /\ inst=MOV (Register(Gpr (word 12) Lower_32)) (Register(Gpr (word 0) Lower_32))) \/
   (family=0 /\ off=24 /\ len=5 /\ inst=CALL (Imm32(word 0xfffffed3))) \/
   (family=0 /\ off=29 /\ len=2 /\ inst=XOR (Register(Gpr (word 0) Lower_32)) (Register(Gpr (word 0) Lower_32))) \/
   (family=0 /\ off=31 /\ len=3 /\ inst=TEST (Register(Gpr (word 12) Lower_32)) (Register(Gpr (word 12) Lower_32))) \/
   (family=0 /\ off=34 /\ len=1 /\ inst=POP (Register(Gpr (word 3) Full_64))) \/
   (family=0 /\ off=35 /\ len=3 /\ inst=SET Condition_Z (Register(Gpr (word 0) Lower_8))) \/
   (family=0 /\ off=38 /\ len=1 /\ inst=POP (Register(Gpr (word 5) Full_64))) \/
   (family=0 /\ off=39 /\ len=2 /\ inst=POP (Register(Gpr (word 12) Full_64))) \/
   (family=0 /\ off=41 /\ len=1 /\ inst=RET) \/
   (family=1 /\ off=0 /\ len=4 /\ inst=SUB (Register(Gpr (word 4) Full_64)) (Imm8(word 8))) \/
   (family=1 /\ off=4 /\ len=5 /\ inst=CALL(Imm32(word 0xffffff17))) \/
   (family=1 /\ off=9 /\ len=2 /\ inst=TEST (Register(Gpr (word 0) Lower_32)) (Register(Gpr (word 0) Lower_32))) \/
   (family=1 /\ off=11 /\ len=3 /\ inst=SET Condition_Z (Register(Gpr (word 0) Lower_8))) \/
   (family=1 /\ off=14 /\ len=4 /\ inst=ADD (Register(Gpr (word 4) Full_64)) (Imm8(word 8))) \/
   (family=1 /\ off=18 /\ len=3 /\ inst=MOVZX (Register(Gpr (word 0) Lower_32)) (Register(Gpr (word 0) Lower_8))) \/
   (family=1 /\ off=21 /\ len=1 /\ inst=RET) \/
   (family=2 /\ off=0 /\ len=6 /\ inst=JUMP Unconditional (Memop Quadword (Riprel(word 0x2f92)))) \/
   (family=3 /\ off=0 /\ len=6 /\ inst=JUMP Unconditional (Memop Quadword (Riprel(word 0x2f8a)))) \/
   (family=4 /\ off=0 /\ len=6 /\ inst=JUMP Unconditional (Memop Quadword (Riprel(word 0x2f82))))`;;
