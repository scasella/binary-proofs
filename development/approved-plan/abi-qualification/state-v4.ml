(* SCALAR_ABI_EXTENSION_V4. Omitted fields; SIMD/mask/rflags remain in x86state. *)
let abi_omitted_state_INDUCT,abi_omitted_state_RECURSION,
    abi_omitted_state_COMPONENTS = define_auto_record_type
 "abi_omitted_state =
   { ABI_X87_CW : (16)word;
     ABI_X87_SW : (16)word;
     ABI_X87_TAG : (16)word;
     ABI_X87_FOP : (11)word;
     ABI_X87_IP : (64)word;
     ABI_X87_CS : (16)word;
     ABI_X87_DP : (64)word;
     ABI_X87_DS : (16)word;
     ABI_X87_REGS : (3)word -> (80)word;
     ABI_MXCSR : (32)word;
     ABI_FS_SELECTOR : (16)word;
     ABI_FS_BASE : (64)word;
     ABI_GS_SELECTOR : (16)word;
     ABI_GS_BASE : (64)word
   }";;

(* ABI-required x87/MXCSR controls plus FS thread-pointer state.
   MXCSR status bits 0..5 are caller-saved.
   DAZ bit 6 is included when supported; reserved values are not made into
   physically realizable states by this mathematical definition. *)
let abi_required_controls_preserved = new_definition
 `abi_required_controls_preserved (a:abi_omitted_state) a' <=>
    read ABI_X87_CW a' = read ABI_X87_CW a /\
    word_and (read ABI_MXCSR a') (word 0xffc0) =
    word_and (read ABI_MXCSR a) (word 0xffc0) /\
    read ABI_FS_SELECTOR a' = read ABI_FS_SELECTOR a /\
    read ABI_FS_BASE a' = read ABI_FS_BASE a`;;

