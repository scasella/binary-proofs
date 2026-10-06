(* SCALAR_ABI_EXTENSION_V5 candidate. Requires frozen fourteen-field V4 state
   and generic V4 definitions. Only generic GPR64 immediate SUB/TEST forms are
   added. No target identity or access policy appears in this semantic clause.
   The added-state equality effect is an explicit ISA modeling trust boundary;
   projection/backlift do not prove physical fidelity. V4 files are preserved. *)
let abi_cleanse_scalar_instruction = new_definition
 `abi_cleanse_scalar_instruction inst <=>
    abi_scalar_instruction inst \/
    (?r imm. inst = SUB (Register(Gpr r Full_64)) (Imm8 imm)) \/
    (?r imm. inst = TEST (Register(Gpr r Full_64)) (Imm32 imm))`;;
let abi_cleanse_scalar_extended_step = new_definition
 `abi_cleanse_scalar_extended_step (s:x86state,a:abi_omitted_state) (s',a') <=>
    ?len inst.
      x86_decode s (read RIP s) (len,inst) /\
      (RIP := word_add (read RIP s) (word len) ,, x86_execute inst) s s' /\
      (abi_cleanse_scalar_instruction inst ==> a' = a)`;;
let abi_all_decodes_cleanse_scalar = new_definition
 `abi_all_decodes_cleanse_scalar (s:x86state) <=>
    !len inst. x86_decode s (read RIP s) (len,inst)
               ==> abi_cleanse_scalar_instruction inst`;;
