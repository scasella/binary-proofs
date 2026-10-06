(* Structural conservativity and the local rule's logical consequences.
   None establishes physical ISA fidelity or whole-routine ABI preservation. *)

let ABI_CLEANSE_EXTENDED_PROJECTION = prove
 (`!s a s' a'. abi_cleanse_scalar_extended_step (s,a) (s',a') ==> x86 s s'`,
  REWRITE_TAC[abi_cleanse_scalar_extended_step; x86] THEN MESON_TAC[]);;

let ABI_CLEANSE_EXTENDED_BACKLIFT_ALL = prove
 (`!s s' a. x86 s s' ==> abi_cleanse_scalar_extended_step (s,a) (s',a)`,
  REWRITE_TAC[abi_cleanse_scalar_extended_step; x86] THEN MESON_TAC[]);;

let ABI_CLEANSE_EXTENDED_EQUIVALENCE = prove
 (`!s s' a. (?a'. abi_cleanse_scalar_extended_step (s,a) (s',a')) <=> x86 s s'`,
  MESON_TAC[ABI_CLEANSE_EXTENDED_PROJECTION; ABI_CLEANSE_EXTENDED_BACKLIFT_ALL]);;

let ABI_CLEANSE_EXTENDED_PROGRESS = prove
 (`!s a. (?s'. x86 s s') <=> ?s' a'. abi_cleanse_scalar_extended_step (s,a) (s',a')`,
  MESON_TAC[ABI_CLEANSE_EXTENDED_EQUIVALENCE]);;

let ABI_CLEANSE_STEP_PRESERVES_OMITTED = prove
 (`!s a s' a'. abi_cleanse_scalar_extended_step (s,a) (s',a') /\
                abi_all_decodes_cleanse_scalar s ==> a' = a`,
  REWRITE_TAC[abi_cleanse_scalar_extended_step; abi_all_decodes_cleanse_scalar] THEN MESON_TAC[]);;

let ABI_CLEANSE_EQUAL_IMPLIES_REQUIRED_CONTROLS = prove
 (`!a a'. a' = a ==> abi_required_controls_preserved a a'`,
  SIMP_TAC[abi_required_controls_preserved]);;


let ABI_CLEANSE_EXTENDED_REFINES_V4 = prove
 (abi_cleanse_refines_v4_statement,
  REWRITE_TAC[abi_cleanse_scalar_extended_step; abi_scalar_extended_step;
    abi_cleanse_scalar_instruction] THEN MESON_TAC[]);;
let ABI_CLEANSE_REGISTERED_SITE_IS_SCALAR = prove
 (abi_cleanse_site_scalar_statement,
  REPEAT GEN_TAC THEN REWRITE_TAC[abi_cleanse_site] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[abi_cleanse_scalar_instruction; abi_scalar_instruction;
    abi_integer_operand; abi_integer_writable; abi_integer_immediate;
    abi_integer_memory_width; abi_cmov_operand; rax; rdi; rsi; al] THEN
  MESON_TAC[]);;
let ABI_CLEANSE_DECODED_SCALAR_UNIQUE = prove
 (abi_cleanse_decoded_scalar_unique_statement,
  REWRITE_TAC[abi_all_decodes_cleanse_scalar] THEN
  MESON_TAC[x86_decode_unique; PAIR_EQ]);;
