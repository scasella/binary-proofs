(* ABI_SCALAR_EXTENSION_V6 candidate. Same fourteen-field V4 record.
   Generic normal-effect clause only; ISA fidelity is an explicit trust boundary.
   No bytes, code location, target identity, permissions or successful-step
   filter occurs in these semantic definitions. V4/V5/E2 are unchanged. *)
let abi_caller_scalar_instruction = new_definition
 `abi_caller_scalar_instruction inst <=>
    abi_cleanse_scalar_instruction inst \/
    (?r imm. inst = ADD (Register(Gpr r Full_64)) (Imm8 imm)) \/
    (?r q. inst = TEST (Register(Gpr r Lower_32)) (Register(Gpr q Lower_32))) \/
    (?r q. inst = MOVZX (Register(Gpr r Lower_32)) (Register(Gpr q Lower_8))) \/
    (?cc r. inst = SET cc (Register(Gpr r Lower_8))) \/
    (?r. inst = PUSH (Register(Gpr r Full_64))) \/
    (?r. inst = POP (Register(Gpr r Full_64))) \/
    (?disp. inst = CALL (Imm32 disp)) \/
    (?r. inst = CALL (Register(Gpr r Full_64))) \/
    (?addr. inst = CALL (Memop Quadword addr)) \/
    (?r. inst = JUMP Unconditional (Register(Gpr r Full_64))) \/
    (?addr. inst = JUMP Unconditional (Memop Quadword addr))`;;
let abi_caller_scalar_extended_step = new_definition
 `abi_caller_scalar_extended_step (s:x86state,a:abi_omitted_state) (s',a') <=>
   ?len inst.
    x86_decode s (read RIP s) (len,inst) /    (RIP := word_add (read RIP s) (word len) ,, x86_execute inst) s s' /    (abi_caller_scalar_instruction inst ==> a'=a)`;;
let abi_all_decodes_caller_scalar = new_definition
 `abi_all_decodes_caller_scalar (s:x86state) <=>
   !len inst. x86_decode s (read RIP s) (len,inst) ==> abi_caller_scalar_instruction inst`;;
