(* SCALAR_ABI_EXTENSION_V2. Generic documented scalar instruction effects,
   independent of target identity, pc, memory contents or library bytes.
   Load state-v2.ml first. No unsupported instruction is assigned a no-op.
   Original decode/execute always supplies every modeled-state successor. *)

let abi_integer_memory_width = new_definition
 `abi_integer_memory_width w <=>
    w = Byte \/ w = Word \/ w = Doubleword \/ w = Quadword`;;

let abi_integer_writable = new_definition
 `abi_integer_writable op <=>
    (?r. op = Register r) \/
    (?w addr. op = Memop w addr /\ abi_integer_memory_width w)`;;

let abi_integer_immediate = new_definition
 `abi_integer_immediate op <=>
    (?v. op = Imm8 v) \/ (?v. op = Imm16 v) \/
    (?v. op = Imm32 v) \/ (?v. op = Imm64 v)`;;

let abi_integer_operand = new_definition
 `abi_integer_operand op <=>
    abi_integer_writable op \/ abi_integer_immediate op`;;

let abi_cmov_operand = new_definition
 `abi_cmov_operand op <=>
    (?r size. op = Register(Gpr r size) /\
              (size = Full_64 \/ size = Lower_32 \/ size = Lower_16)) \/
    (?w addr. op = Memop w addr /\
              (w = Word \/ w = Doubleword \/ w = Quadword))`;;

let abi_scalar_instruction = new_definition
 `abi_scalar_instruction inst <=>
    inst = ENDBR64 \/ inst = RET \/
    (?dst src. inst = MOV dst src /\ abi_integer_writable dst /\ abi_integer_operand src) \/
    (?dst src. inst = XOR dst src /\ abi_integer_writable dst /\ abi_integer_operand src) \/
    (?dst src. inst = OR dst src /\ abi_integer_writable dst /\ abi_integer_operand src) \/
    (?dst src. inst = CMP dst src /\ abi_integer_writable dst /\ abi_integer_operand src) \/
    (?dst. inst = DEC dst /\ abi_integer_writable dst) \/
    (?dst. inst = NEG dst /\ abi_integer_writable dst) \/
    (?r addr. inst = LEA (Register r) addr) \/
    (?cond r size src. inst = CMOV cond (Register(Gpr r size)) src /\
       (size = Full_64 \/ size = Lower_32 \/ size = Lower_16) /\ abi_cmov_operand src) \/
    (?cond disp. inst = JUMP cond (Imm8 disp)) \/
    (?cond disp. inst = JUMP cond (Imm32 disp)) \/
    (?dst count. inst = SHR dst count /\ abi_integer_writable dst /\
       ((?v. count = Imm8 v) \/ count = Register(Gpr (word 1) Lower_8)))`;;

(* The semantic clause for documented classes is equality of every omitted
   field. The original scalar transition is retained exactly. For all other
   decoded instructions, omitted-state successors are unconstrained. Formal
   projection/backlift proves relation conservativity, not physical fidelity. *)
let abi_scalar_extended_step = new_definition
 `abi_scalar_extended_step (s:x86state,a:abi_omitted_state) (s',a') <=>
    ?len inst.
      x86_decode s (read RIP s) (len,inst) /\
      (RIP := word_add (read RIP s) (word len) ,, x86_execute inst) s s' /\
      (abi_scalar_instruction inst ==> a' = a)`;;

let abi_all_decodes_scalar = new_definition
 `abi_all_decodes_scalar (s:x86state) <=>
    !len inst. x86_decode s (read RIP s) (len,inst)
               ==> abi_scalar_instruction inst`;;
