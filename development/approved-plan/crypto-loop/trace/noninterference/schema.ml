(* Public fixed-code schema, chronological order. Decode entries are literal
   instruction terms from the production instruction sites; later theorems
   must establish each against the actual loaded decoder. No loaded value,
   result bit, or accumulator is present in an observation. *)
let crypto_public_decode = new_definition
 `crypto_public_decode off =
    if off=0 then (4,ENDBR64)
    else if off=4 then (3,XOR (% rax) (% rax))
    else if off=7 then (3,XOR (% r10) (% r10))
    else if off=10 then (4,CMP (% rdx) (Imm8 (word 0)))
    else if off=14 then (2,JUMP Condition_Z (Imm8 (word 77)))
    else if off=16 then (4,CMP (% rdx) (Imm8 (word 16)))
    else if off=20 then (2,JUMP Condition_NZ (Imm8 (word 42)))
    else if off=22 then (3,MOV (% r10) (Memop Quadword (%% (rdi,0))))
    else if off=25 then (4,MOV (% r11) (Memop Quadword (%% (rdi,8))))
    else if off=29 then (7,MOV (% rdx) (Imm32 (word 1)))
    else if off=36 then (3,XOR (% r10) (Memop Quadword (%% (rsi,0))))
    else if off=39 then (4,XOR (% r11) (Memop Quadword (%% (rsi,8))))
    else if off=43 then (3,OR (% r10) (% r11))
    else if off=46 then (4,CMOV Condition_NZ (% rax) (% rdx))
    else if off=50 then (2,RET)
    else if off=64 then (3,MOV (% r10b) (Memop Byte (%% (rdi,0))))
    else if off=67 then (4,LEA (% rdi) (%% (rdi,1)))
    else if off=71 then (3,XOR (% r10b) (Memop Byte (%% (rsi,0))))
    else if off=74 then (4,LEA (% rsi) (%% (rsi,1)))
    else if off=78 then (3,OR (% al) (% r10b))
    else if off=81 then (3,DEC (% rdx))
    else if off=84 then (2,JUMP Condition_NZ (Imm8 (word 234)))
    else if off=86 then (3,NEG (% rax))
    else if off=89 then (4,SHR (% rax) (Imm8 (word 63)))
    else if off=93 then (2,RET)
    else (0,RET)`;;
let crypto_public_observation = new_definition
 `crypto_public_observation pc off (es:uarch_event list) =
    (word(pc+off):int64,FST(crypto_public_decode off),SND(crypto_public_decode off),es)`;;
let crypto_public_entry5 = new_definition
 `crypto_public_entry5 pc n =
   [crypto_public_observation pc 0 [];
    crypto_public_observation pc 4 [];
    crypto_public_observation pc 7 [];
    crypto_public_observation pc 10 [];
    crypto_public_observation pc 14
      [EventJump(word(pc+16),if n=0 then word(pc+93) else word(pc+16))]]`;;
let crypto_public_entry7 = new_definition
 `crypto_public_entry7 pc n = APPEND (crypto_public_entry5 pc n)
   [crypto_public_observation pc 16 [];
    crypto_public_observation pc 20
      [EventJump(word(pc+22),if n=16 then word(pc+22) else word(pc+64))]]`;;
let crypto_public_body7 = new_definition
 `crypto_public_body7 pc (p:int64) q count =
   [crypto_public_observation pc 64 [EventLoad(p,1)];
    crypto_public_observation pc 67 [];
    crypto_public_observation pc 71 [EventLoad(q,1)];
    crypto_public_observation pc 74 [];
    crypto_public_observation pc 78 [];
    crypto_public_observation pc 81 [];
    crypto_public_observation pc 84
      [EventJump(word(pc+86),if count=1 then word(pc+86) else word(pc+64))]]`;;
let crypto_public_exit = new_definition
 `crypto_public_exit pc (stackpointer:int64) returnaddress =
   [crypto_public_observation pc 86 [];
    crypto_public_observation pc 89 [];
    crypto_public_observation pc 93
      [EventLoad(stackpointer,8);EventJump(word(pc+95),returnaddress)]]`;;
let crypto_public_loop = new_recursive_definition num_RECURSION
 `(crypto_public_loop pc (p:int64) q 0 stackpointer returnaddress =
     crypto_public_exit pc stackpointer returnaddress) /\
  (crypto_public_loop pc p q (SUC n) stackpointer returnaddress =
     APPEND (crypto_public_body7 pc p q (SUC n))
       (crypto_public_loop pc (word_add p (word 1)) (word_add q (word 1)) n
         stackpointer returnaddress))`;;
let crypto_public_call = new_definition
 `crypto_public_call pc (p:int64) q n stackpointer returnaddress =
   if n=0 then APPEND (crypto_public_entry5 pc 0)
    [crypto_public_observation pc 93
      [EventLoad(stackpointer,8);EventJump(word(pc+95),returnaddress)]]
   else if n=16 then APPEND (crypto_public_entry7 pc 16)
    [crypto_public_observation pc 22 [EventLoad(p,8)];
     crypto_public_observation pc 25 [EventLoad(word_add p (word 8),8)];
     crypto_public_observation pc 29 [];
     crypto_public_observation pc 36 [EventLoad(q,8)];
     crypto_public_observation pc 39 [EventLoad(word_add q (word 8),8)];
     crypto_public_observation pc 43 [];
     crypto_public_observation pc 46 [];
     crypto_public_observation pc 50
      [EventLoad(stackpointer,8);EventJump(word(pc+52),returnaddress)]]
   else APPEND (crypto_public_entry7 pc n)
     (crypto_public_loop pc p q n stackpointer returnaddress)`;;
