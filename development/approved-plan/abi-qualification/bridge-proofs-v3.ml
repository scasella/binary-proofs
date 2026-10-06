(* Structural conservativity and the local rule's logical consequences.
   None establishes physical ISA fidelity or whole-routine ABI preservation. *)

let ABI_SCALAR_EXTENDED_PROJECTION = prove
 (`!s a s' a'. abi_scalar_extended_step (s,a) (s',a') ==> x86 s s'`,
  REWRITE_TAC[abi_scalar_extended_step; x86] THEN MESON_TAC[]);;

let ABI_SCALAR_EXTENDED_BACKLIFT_ALL = prove
 (`!s s' a. x86 s s' ==> abi_scalar_extended_step (s,a) (s',a)`,
  REWRITE_TAC[abi_scalar_extended_step; x86] THEN MESON_TAC[]);;

let ABI_SCALAR_EXTENDED_EQUIVALENCE = prove
 (`!s s' a. (?a'. abi_scalar_extended_step (s,a) (s',a')) <=> x86 s s'`,
  MESON_TAC[ABI_SCALAR_EXTENDED_PROJECTION; ABI_SCALAR_EXTENDED_BACKLIFT_ALL]);;

let ABI_SCALAR_EXTENDED_PROGRESS = prove
 (`!s a. (?s'. x86 s s') <=> ?s' a'. abi_scalar_extended_step (s,a) (s',a')`,
  MESON_TAC[ABI_SCALAR_EXTENDED_EQUIVALENCE]);;

let ABI_SCALAR_STEP_PRESERVES_OMITTED = prove
 (`!s a s' a'. abi_scalar_extended_step (s,a) (s',a') /\
                abi_all_decodes_scalar s ==> a' = a`,
  REWRITE_TAC[abi_scalar_extended_step; abi_all_decodes_scalar] THEN MESON_TAC[]);;

let ABI_SCALAR_EQUAL_IMPLIES_REQUIRED_CONTROLS = prove
 (`!a a'. a' = a ==> abi_required_controls_preserved a a'`,
  SIMP_TAC[abi_required_controls_preserved]);;

(* Separate target registry refinement: actual byte-to-constructor decode
   proofs and intermediate control-flow coverage are additional obligations. *)
let ABI_CRYPTO_REGISTERED_SITE_IS_SCALAR = prove
 (`!off len inst. abi_crypto_site off len inst ==> abi_scalar_instruction inst`,
  REPEAT GEN_TAC THEN REWRITE_TAC[abi_crypto_site] THEN
  STRIP_TAC THEN
  ASM_REWRITE_TAC[abi_scalar_instruction;
              abi_integer_operand; abi_integer_writable; abi_integer_immediate;
              abi_integer_memory_width; abi_cmov_operand;
              rax; rdx; r10; r11; rdi; rsi; r10b; al] THEN MESON_TAC[]);;
