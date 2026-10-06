let ABI_CALLER_REGISTERED_SITE_IS_SCALAR = prove
 (abi_caller_site_scalar_statement,
  REPEAT GEN_TAC THEN REWRITE_TAC[abi_caller_site] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[abi_caller_scalar_instruction;abi_cleanse_scalar_instruction;
    abi_scalar_instruction;abi_integer_operand;abi_integer_writable;
    abi_integer_immediate;abi_integer_memory_width;abi_cmov_operand] THEN
  MESON_TAC[]);;
