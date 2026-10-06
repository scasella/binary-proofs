(* O3 endpoint: initial snapshot and an actual comparison/header result.
   This predicate is a derived postcondition, not an initial-state premise. *)
let c2_header_completed = new_definition
 `c2_header_completed lib_file stackpointer p q n m rp wp xp ordinary
    (initial:x86state) a (t:x86state) <=>
    ?returned:x86state.
      c2_crypto_completed lib_file stackpointer p q n m rp wp xp ordinary
        initial a returned /\ c2_branch_header_post p q n m returned t`;;
