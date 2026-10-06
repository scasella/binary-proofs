needs "/work/development/approved-plan/cleanse/interface/statement-loader-v1.ml";;
let BP_E2_CLEANSE_PUBLIC_WITNESS_BRIDGE = prove
 (bp_e2_cleanse_public_witness_bridge_statement,
  SUBGOAL_THEN
   `!image p n high_first. read memory(clw_state image p n high_first)=
      clw_memory image p n high_first` ASSUME_TAC THENL
   [REWRITE_TAC[clw_state;x86state_COMPONENTS];ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[clw_full_pre;bp_e2_cleanse_public_pre;clw_machine;FST;SND] THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[lw_execute] THEN MESON_TAC[]);;
print_endline "CLEANSE_INTERFACE_WITNESS_ATTEMPT1_COMPLETE";;
