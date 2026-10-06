(* Literal witness targets; all payloads arbitrary, overlap uses one consistent memory function. *)
let c3w_pre_statement =
 `!lib_file client_file payload p q n.
    fb_file_code lib_file /\ clw_file_code lib_file /\ c3_file_code client_file /\ c3w_layout p q n
    ==> c3_pre lib_file (c3w_memory lib_file client_file payload)
      (c3w_memory lib_file client_file payload) client_file
      (c3w_memory lib_file client_file payload)
      (c3w_memory lib_file client_file payload)
      (word 0x300008) (word 0x400000) p q n
      (c3w_memory lib_file client_file payload)
      c3w_read c3w_write c3w_execute c3w_ordinary
      (c3w_state lib_file client_file payload p q n,fb_initial_abi)`;;
let c3w_generic_witness_statement =
 `!lib_file client_file payload p q n.
    fb_file_code lib_file /\ clw_file_code lib_file /\ c3_file_code client_file /\ c3w_layout p q n
    ==> c3_entry_witness lib_file client_file payload p q n`;;
let c3_admissible_entry_witnesses_statement =
 `!lib_file client_file payload.
    fb_file_code lib_file /\ clw_file_code lib_file /\ c3_file_code client_file ==>
    c3_entry_witness lib_file client_file payload (word 0) (word 0) 0 /\
    c3_entry_witness lib_file client_file payload
      (word 0x50000000) (word 0x60000000) 1 /\
    c3_entry_witness lib_file client_file payload
      (word 0x50000003) (word 0x60000005) 17 /\
    c3_entry_witness lib_file client_file payload
      (word 0x50000003) (word 0x50000003) 16 /\
    c3_entry_witness lib_file client_file payload
      (word 0x50000003) (word 0x50000004) 17 /\
    c3_entry_witness lib_file client_file payload
      (word 0x50000004) (word 0x50000003) 17 /\
    c3_entry_witness lib_file client_file payload
      (word 0x50000fff) (word 0x60000fff) 15 /\
    c3_entry_witness lib_file client_file payload
      (word 0x7fffffffffff) (word 0xffff800000000000) 1`;;
