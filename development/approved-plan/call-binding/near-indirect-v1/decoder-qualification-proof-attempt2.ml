(* Frozen expectations predate these finite decoder proofs. *)
let R1_NEAR_PLT_CRYPTO_MEMCMP = prove
 (`decode [word 0xff;word 0x25;word 0x92;word 0x2f;word 0x0;word 0x0] = SOME(JMP(Memop Quadword (Riprel(word 0x2f92))),[])`,
  CONV_TAC(LAND_CONV DECODE_CONV) THEN
  REWRITE_TAC(JNE :: r1_near_register :: r1_near_operand64 :: GPR_thms));;

let R1_NEAR_PLT_OPENSSL_CLEANSE = prove
 (`decode [word 0xff;word 0x25;word 0x8a;word 0x2f;word 0x0;word 0x0] = SOME(JMP(Memop Quadword (Riprel(word 0x2f8a))),[])`,
  CONV_TAC(LAND_CONV DECODE_CONV) THEN
  REWRITE_TAC(JNE :: r1_near_register :: r1_near_operand64 :: GPR_thms));;

let R1_NEAR_PLT_MEMCMP = prove
 (`decode [word 0xff;word 0x25;word 0x82;word 0x2f;word 0x0;word 0x0] = SOME(JMP(Memop Quadword (Riprel(word 0x2f82))),[])`,
  CONV_TAC(LAND_CONV DECODE_CONV) THEN
  REWRITE_TAC(JNE :: r1_near_register :: r1_near_operand64 :: GPR_thms));;

let R1_NEAR_DECODE_NONE_RIP_JMP = prove
 (`decode [word 0xff;word 0x25;word 0x92;word 0x2f;word 0x0;word 0x0] = SOME(JMP(Memop Quadword (Riprel(word 0x2f92))),[])`,
  CONV_TAC(LAND_CONV DECODE_CONV) THEN
  REWRITE_TAC(JNE :: r1_near_register :: r1_near_operand64 :: GPR_thms));;

let R1_NEAR_DECODE_NONE_RIP_CALL = prove
 (`decode [word 0xff;word 0x15;word 0x92;word 0x2f;word 0x0;word 0x0] = SOME(CALL(Memop Quadword (Riprel(word 0x2f92))),[])`,
  CONV_TAC(LAND_CONV DECODE_CONV) THEN
  REWRITE_TAC(JNE :: r1_near_register :: r1_near_operand64 :: GPR_thms));;

let R1_NEAR_DECODE_NONE_REGISTER_JMP = prove
 (`decode [word 0xff;word 0xe0] = SOME(JMP(Register rax),[])`,
  CONV_TAC(LAND_CONV DECODE_CONV) THEN
  REWRITE_TAC(JNE :: r1_near_register :: r1_near_operand64 :: GPR_thms));;

let R1_NEAR_DECODE_NONE_REGISTER_CALL = prove
 (`decode [word 0xff;word 0xd0] = SOME(CALL(Register rax),[])`,
  CONV_TAC(LAND_CONV DECODE_CONV) THEN
  REWRITE_TAC(JNE :: r1_near_register :: r1_near_operand64 :: GPR_thms));;

let R1_NEAR_DECODE_NONE_RSP_CALL_TOP = prove
 (`decode [word 0xff;word 0x14;word 0x24] = SOME(CALL(Memop Quadword (%%(rsp,0))),[])`,
  CONV_TAC(LAND_CONV DECODE_CONV) THEN
  REWRITE_TAC(JNE :: r1_near_register :: r1_near_operand64 :: GPR_thms));;

let R1_NEAR_DECODE_NONE_RSP_CALL_ALIAS = prove
 (`decode [word 0xff;word 0x54;word 0x24;word 0xf8] = SOME(CALL(Memop Quadword (%%(rsp,18446744073709551608))),[])`,
  CONV_TAC(LAND_CONV DECODE_CONV) THEN
  REWRITE_TAC(JNE :: r1_near_register :: r1_near_operand64 :: GPR_thms));;

let R1_NEAR_DECODE_NONE_RSP_JMP_NEXT = prove
 (`decode [word 0xff;word 0x64;word 0x24;word 0x8] = SOME(JMP(Memop Quadword (%%(rsp,8))),[])`,
  CONV_TAC(LAND_CONV DECODE_CONV) THEN
  REWRITE_TAC(JNE :: r1_near_register :: r1_near_operand64 :: GPR_thms));;

let R1_NEAR_DECODE_REX0_RIP_JMP = prove
 (`decode [word 0x40;word 0xff;word 0x25;word 0x92;word 0x2f;word 0x0;word 0x0] = SOME(JMP(Memop Quadword (Riprel(word 0x2f92))),[])`,
  CONV_TAC(LAND_CONV DECODE_CONV) THEN
  REWRITE_TAC(JNE :: r1_near_register :: r1_near_operand64 :: GPR_thms));;

let R1_NEAR_DECODE_REX0_RIP_CALL = prove
 (`decode [word 0x40;word 0xff;word 0x15;word 0x92;word 0x2f;word 0x0;word 0x0] = SOME(CALL(Memop Quadword (Riprel(word 0x2f92))),[])`,
  CONV_TAC(LAND_CONV DECODE_CONV) THEN
  REWRITE_TAC(JNE :: r1_near_register :: r1_near_operand64 :: GPR_thms));;

let R1_NEAR_DECODE_REX0_REGISTER_JMP = prove
 (`decode [word 0x40;word 0xff;word 0xe0] = SOME(JMP(Register rax),[])`,
  CONV_TAC(LAND_CONV DECODE_CONV) THEN
  REWRITE_TAC(JNE :: r1_near_register :: r1_near_operand64 :: GPR_thms));;

let R1_NEAR_DECODE_REX0_REGISTER_CALL = prove
 (`decode [word 0x40;word 0xff;word 0xd0] = SOME(CALL(Register rax),[])`,
  CONV_TAC(LAND_CONV DECODE_CONV) THEN
  REWRITE_TAC(JNE :: r1_near_register :: r1_near_operand64 :: GPR_thms));;

let R1_NEAR_DECODE_REX0_RSP_CALL_TOP = prove
 (`decode [word 0x40;word 0xff;word 0x14;word 0x24] = SOME(CALL(Memop Quadword (%%(rsp,0))),[])`,
  CONV_TAC(LAND_CONV DECODE_CONV) THEN
  REWRITE_TAC(JNE :: r1_near_register :: r1_near_operand64 :: GPR_thms));;

let R1_NEAR_DECODE_REX0_RSP_CALL_ALIAS = prove
 (`decode [word 0x40;word 0xff;word 0x54;word 0x24;word 0xf8] = SOME(CALL(Memop Quadword (%%(rsp,18446744073709551608))),[])`,
  CONV_TAC(LAND_CONV DECODE_CONV) THEN
  REWRITE_TAC(JNE :: r1_near_register :: r1_near_operand64 :: GPR_thms));;

let R1_NEAR_DECODE_REX0_RSP_JMP_NEXT = prove
 (`decode [word 0x40;word 0xff;word 0x64;word 0x24;word 0x8] = SOME(JMP(Memop Quadword (%%(rsp,8))),[])`,
  CONV_TAC(LAND_CONV DECODE_CONV) THEN
  REWRITE_TAC(JNE :: r1_near_register :: r1_near_operand64 :: GPR_thms));;

let R1_NEAR_DECODE_REXW_RIP_JMP = prove
 (`decode [word 0x48;word 0xff;word 0x25;word 0x92;word 0x2f;word 0x0;word 0x0] = SOME(JMP(Memop Quadword (Riprel(word 0x2f92))),[])`,
  CONV_TAC(LAND_CONV DECODE_CONV) THEN
  REWRITE_TAC(JNE :: r1_near_register :: r1_near_operand64 :: GPR_thms));;

let R1_NEAR_DECODE_REXW_RIP_CALL = prove
 (`decode [word 0x48;word 0xff;word 0x15;word 0x92;word 0x2f;word 0x0;word 0x0] = SOME(CALL(Memop Quadword (Riprel(word 0x2f92))),[])`,
  CONV_TAC(LAND_CONV DECODE_CONV) THEN
  REWRITE_TAC(JNE :: r1_near_register :: r1_near_operand64 :: GPR_thms));;

let R1_NEAR_DECODE_REXW_REGISTER_JMP = prove
 (`decode [word 0x48;word 0xff;word 0xe0] = SOME(JMP(Register rax),[])`,
  CONV_TAC(LAND_CONV DECODE_CONV) THEN
  REWRITE_TAC(JNE :: r1_near_register :: r1_near_operand64 :: GPR_thms));;

let R1_NEAR_DECODE_REXW_REGISTER_CALL = prove
 (`decode [word 0x48;word 0xff;word 0xd0] = SOME(CALL(Register rax),[])`,
  CONV_TAC(LAND_CONV DECODE_CONV) THEN
  REWRITE_TAC(JNE :: r1_near_register :: r1_near_operand64 :: GPR_thms));;

let R1_NEAR_DECODE_REXW_RSP_CALL_TOP = prove
 (`decode [word 0x48;word 0xff;word 0x14;word 0x24] = SOME(CALL(Memop Quadword (%%(rsp,0))),[])`,
  CONV_TAC(LAND_CONV DECODE_CONV) THEN
  REWRITE_TAC(JNE :: r1_near_register :: r1_near_operand64 :: GPR_thms));;

let R1_NEAR_DECODE_REXW_RSP_CALL_ALIAS = prove
 (`decode [word 0x48;word 0xff;word 0x54;word 0x24;word 0xf8] = SOME(CALL(Memop Quadword (%%(rsp,18446744073709551608))),[])`,
  CONV_TAC(LAND_CONV DECODE_CONV) THEN
  REWRITE_TAC(JNE :: r1_near_register :: r1_near_operand64 :: GPR_thms));;

let R1_NEAR_DECODE_REXW_RSP_JMP_NEXT = prove
 (`decode [word 0x48;word 0xff;word 0x64;word 0x24;word 0x8] = SOME(JMP(Memop Quadword (%%(rsp,8))),[])`,
  CONV_TAC(LAND_CONV DECODE_CONV) THEN
  REWRITE_TAC(JNE :: r1_near_register :: r1_near_operand64 :: GPR_thms));;

let R1_NEAR_DECODE_OSZ_RIP_JMP = prove
 (`decode [word 0x66;word 0xff;word 0x25;word 0x92;word 0x2f;word 0x0;word 0x0] = SOME(JMP(Memop Quadword (Riprel(word 0x2f92))),[])`,
  CONV_TAC(LAND_CONV DECODE_CONV) THEN
  REWRITE_TAC(JNE :: r1_near_register :: r1_near_operand64 :: GPR_thms));;

let R1_NEAR_DECODE_OSZ_RIP_CALL = prove
 (`decode [word 0x66;word 0xff;word 0x15;word 0x92;word 0x2f;word 0x0;word 0x0] = SOME(CALL(Memop Quadword (Riprel(word 0x2f92))),[])`,
  CONV_TAC(LAND_CONV DECODE_CONV) THEN
  REWRITE_TAC(JNE :: r1_near_register :: r1_near_operand64 :: GPR_thms));;

let R1_NEAR_DECODE_OSZ_REGISTER_JMP = prove
 (`decode [word 0x66;word 0xff;word 0xe0] = SOME(JMP(Register rax),[])`,
  CONV_TAC(LAND_CONV DECODE_CONV) THEN
  REWRITE_TAC(JNE :: r1_near_register :: r1_near_operand64 :: GPR_thms));;

let R1_NEAR_DECODE_OSZ_REGISTER_CALL = prove
 (`decode [word 0x66;word 0xff;word 0xd0] = SOME(CALL(Register rax),[])`,
  CONV_TAC(LAND_CONV DECODE_CONV) THEN
  REWRITE_TAC(JNE :: r1_near_register :: r1_near_operand64 :: GPR_thms));;

let R1_NEAR_DECODE_OSZ_RSP_CALL_TOP = prove
 (`decode [word 0x66;word 0xff;word 0x14;word 0x24] = SOME(CALL(Memop Quadword (%%(rsp,0))),[])`,
  CONV_TAC(LAND_CONV DECODE_CONV) THEN
  REWRITE_TAC(JNE :: r1_near_register :: r1_near_operand64 :: GPR_thms));;

let R1_NEAR_DECODE_OSZ_RSP_CALL_ALIAS = prove
 (`decode [word 0x66;word 0xff;word 0x54;word 0x24;word 0xf8] = SOME(CALL(Memop Quadword (%%(rsp,18446744073709551608))),[])`,
  CONV_TAC(LAND_CONV DECODE_CONV) THEN
  REWRITE_TAC(JNE :: r1_near_register :: r1_near_operand64 :: GPR_thms));;

let R1_NEAR_DECODE_OSZ_RSP_JMP_NEXT = prove
 (`decode [word 0x66;word 0xff;word 0x64;word 0x24;word 0x8] = SOME(JMP(Memop Quadword (%%(rsp,8))),[])`,
  CONV_TAC(LAND_CONV DECODE_CONV) THEN
  REWRITE_TAC(JNE :: r1_near_register :: r1_near_operand64 :: GPR_thms));;

let R1_NEAR_DECODE_OSZ_REX0_RIP_JMP = prove
 (`decode [word 0x66;word 0x40;word 0xff;word 0x25;word 0x92;word 0x2f;word 0x0;word 0x0] = SOME(JMP(Memop Quadword (Riprel(word 0x2f92))),[])`,
  CONV_TAC(LAND_CONV DECODE_CONV) THEN
  REWRITE_TAC(JNE :: r1_near_register :: r1_near_operand64 :: GPR_thms));;

let R1_NEAR_DECODE_OSZ_REX0_RIP_CALL = prove
 (`decode [word 0x66;word 0x40;word 0xff;word 0x15;word 0x92;word 0x2f;word 0x0;word 0x0] = SOME(CALL(Memop Quadword (Riprel(word 0x2f92))),[])`,
  CONV_TAC(LAND_CONV DECODE_CONV) THEN
  REWRITE_TAC(JNE :: r1_near_register :: r1_near_operand64 :: GPR_thms));;

let R1_NEAR_DECODE_OSZ_REX0_REGISTER_JMP = prove
 (`decode [word 0x66;word 0x40;word 0xff;word 0xe0] = SOME(JMP(Register rax),[])`,
  CONV_TAC(LAND_CONV DECODE_CONV) THEN
  REWRITE_TAC(JNE :: r1_near_register :: r1_near_operand64 :: GPR_thms));;

let R1_NEAR_DECODE_OSZ_REX0_REGISTER_CALL = prove
 (`decode [word 0x66;word 0x40;word 0xff;word 0xd0] = SOME(CALL(Register rax),[])`,
  CONV_TAC(LAND_CONV DECODE_CONV) THEN
  REWRITE_TAC(JNE :: r1_near_register :: r1_near_operand64 :: GPR_thms));;

let R1_NEAR_DECODE_OSZ_REX0_RSP_CALL_TOP = prove
 (`decode [word 0x66;word 0x40;word 0xff;word 0x14;word 0x24] = SOME(CALL(Memop Quadword (%%(rsp,0))),[])`,
  CONV_TAC(LAND_CONV DECODE_CONV) THEN
  REWRITE_TAC(JNE :: r1_near_register :: r1_near_operand64 :: GPR_thms));;

let R1_NEAR_DECODE_OSZ_REX0_RSP_CALL_ALIAS = prove
 (`decode [word 0x66;word 0x40;word 0xff;word 0x54;word 0x24;word 0xf8] = SOME(CALL(Memop Quadword (%%(rsp,18446744073709551608))),[])`,
  CONV_TAC(LAND_CONV DECODE_CONV) THEN
  REWRITE_TAC(JNE :: r1_near_register :: r1_near_operand64 :: GPR_thms));;

let R1_NEAR_DECODE_OSZ_REX0_RSP_JMP_NEXT = prove
 (`decode [word 0x66;word 0x40;word 0xff;word 0x64;word 0x24;word 0x8] = SOME(JMP(Memop Quadword (%%(rsp,8))),[])`,
  CONV_TAC(LAND_CONV DECODE_CONV) THEN
  REWRITE_TAC(JNE :: r1_near_register :: r1_near_operand64 :: GPR_thms));;

let R1_NEAR_DECODE_OSZ_REXW_RIP_JMP = prove
 (`decode [word 0x66;word 0x48;word 0xff;word 0x25;word 0x92;word 0x2f;word 0x0;word 0x0] = SOME(JMP(Memop Quadword (Riprel(word 0x2f92))),[])`,
  CONV_TAC(LAND_CONV DECODE_CONV) THEN
  REWRITE_TAC(JNE :: r1_near_register :: r1_near_operand64 :: GPR_thms));;

let R1_NEAR_DECODE_OSZ_REXW_RIP_CALL = prove
 (`decode [word 0x66;word 0x48;word 0xff;word 0x15;word 0x92;word 0x2f;word 0x0;word 0x0] = SOME(CALL(Memop Quadword (Riprel(word 0x2f92))),[])`,
  CONV_TAC(LAND_CONV DECODE_CONV) THEN
  REWRITE_TAC(JNE :: r1_near_register :: r1_near_operand64 :: GPR_thms));;

let R1_NEAR_DECODE_OSZ_REXW_REGISTER_JMP = prove
 (`decode [word 0x66;word 0x48;word 0xff;word 0xe0] = SOME(JMP(Register rax),[])`,
  CONV_TAC(LAND_CONV DECODE_CONV) THEN
  REWRITE_TAC(JNE :: r1_near_register :: r1_near_operand64 :: GPR_thms));;

let R1_NEAR_DECODE_OSZ_REXW_REGISTER_CALL = prove
 (`decode [word 0x66;word 0x48;word 0xff;word 0xd0] = SOME(CALL(Register rax),[])`,
  CONV_TAC(LAND_CONV DECODE_CONV) THEN
  REWRITE_TAC(JNE :: r1_near_register :: r1_near_operand64 :: GPR_thms));;

let R1_NEAR_DECODE_OSZ_REXW_RSP_CALL_TOP = prove
 (`decode [word 0x66;word 0x48;word 0xff;word 0x14;word 0x24] = SOME(CALL(Memop Quadword (%%(rsp,0))),[])`,
  CONV_TAC(LAND_CONV DECODE_CONV) THEN
  REWRITE_TAC(JNE :: r1_near_register :: r1_near_operand64 :: GPR_thms));;

let R1_NEAR_DECODE_OSZ_REXW_RSP_CALL_ALIAS = prove
 (`decode [word 0x66;word 0x48;word 0xff;word 0x54;word 0x24;word 0xf8] = SOME(CALL(Memop Quadword (%%(rsp,18446744073709551608))),[])`,
  CONV_TAC(LAND_CONV DECODE_CONV) THEN
  REWRITE_TAC(JNE :: r1_near_register :: r1_near_operand64 :: GPR_thms));;

let R1_NEAR_DECODE_OSZ_REXW_RSP_JMP_NEXT = prove
 (`decode [word 0x66;word 0x48;word 0xff;word 0x64;word 0x24;word 0x8] = SOME(JMP(Memop Quadword (%%(rsp,8))),[])`,
  CONV_TAC(LAND_CONV DECODE_CONV) THEN
  REWRITE_TAC(JNE :: r1_near_register :: r1_near_operand64 :: GPR_thms));;

let R1_RELATIVE_DECODE_CALL = prove
 (`decode [word 0xe8;word 0x1;word 0x0;word 0x0;word 0x0] = SOME(CALL(Imm32(word 1)),[])`,
  CONV_TAC(LAND_CONV DECODE_CONV) THEN
  REWRITE_TAC(JNE :: r1_near_register :: r1_near_operand64 :: GPR_thms));;

let R1_RELATIVE_DECODE_JMP = prove
 (`decode [word 0xe9;word 0x1;word 0x0;word 0x0;word 0x0] = SOME(JMP(Imm32(word 1)),[])`,
  CONV_TAC(LAND_CONV DECODE_CONV) THEN
  REWRITE_TAC(JNE :: r1_near_register :: r1_near_operand64 :: GPR_thms));;

let R1_RELATIVE_DECODE_JNZ = prove
 (`decode [word 0x75;word 0x1] = SOME(JUMP Condition_NZ (Imm8(word 1)),[])`,
  CONV_TAC(LAND_CONV DECODE_CONV) THEN
  REWRITE_TAC(JNE :: r1_near_register :: r1_near_operand64 :: GPR_thms));;

let R1_PREVIOUS_REP_RET_DECODE = prove
 (`decode [word 0xf3;word 0xc3] = SOME(RET,[])`,
  CONV_TAC(LAND_CONV DECODE_CONV) THEN
  REWRITE_TAC(JNE :: r1_near_register :: r1_near_operand64 :: GPR_thms));;

