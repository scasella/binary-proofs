(* Structural conservativity and the local rule's logical consequences.
   None establishes physical ISA fidelity or whole-routine ABI preservation. *)

let ABI_CALLER_EXTENDED_PROJECTION = prove
 (`!s a s' a'. abi_caller_scalar_extended_step (s,a) (s',a') ==> x86 s s'`,
  REWRITE_TAC[abi_caller_scalar_extended_step; x86] THEN MESON_TAC[]);;

let ABI_CALLER_EXTENDED_BACKLIFT_ALL = prove
 (`!s s' a. x86 s s' ==> abi_caller_scalar_extended_step (s,a) (s',a)`,
  REWRITE_TAC[abi_caller_scalar_extended_step; x86] THEN MESON_TAC[]);;

let ABI_CALLER_EXTENDED_EQUIVALENCE = prove
 (`!s s' a. (?a'. abi_caller_scalar_extended_step (s,a) (s',a')) <=> x86 s s'`,
  MESON_TAC[ABI_CALLER_EXTENDED_PROJECTION; ABI_CALLER_EXTENDED_BACKLIFT_ALL]);;

let ABI_CALLER_EXTENDED_PROGRESS = prove
 (`!s a. (?s'. x86 s s') <=> ?s' a'. abi_caller_scalar_extended_step (s,a) (s',a')`,
  MESON_TAC[ABI_CALLER_EXTENDED_EQUIVALENCE]);;

let ABI_CALLER_STEP_PRESERVES_OMITTED = prove
 (`!s a s' a'. abi_caller_scalar_extended_step (s,a) (s',a') /\
                abi_all_decodes_caller_scalar s ==> a' = a`,
  REWRITE_TAC[abi_caller_scalar_extended_step; abi_all_decodes_caller_scalar] THEN MESON_TAC[]);;

let ABI_CALLER_EQUAL_IMPLIES_REQUIRED_CONTROLS = prove
 (`!a a'. a' = a ==> abi_required_controls_preserved a a'`,
  SIMP_TAC[abi_required_controls_preserved]);;


let ABI_CALLER_EXTENDED_REFINES_V5 = prove
 (abi_caller_refines_v5_statement,
  REWRITE_TAC[abi_caller_scalar_extended_step; abi_cleanse_scalar_extended_step;
    abi_caller_scalar_instruction] THEN MESON_TAC[]);;
let ABI_CALLER_DECODED_SCALAR_UNIQUE = prove
 (abi_caller_decoded_scalar_unique_statement,
  REWRITE_TAC[abi_all_decodes_caller_scalar] THEN
  MESON_TAC[x86_decode_unique; PAIR_EQ]);;
