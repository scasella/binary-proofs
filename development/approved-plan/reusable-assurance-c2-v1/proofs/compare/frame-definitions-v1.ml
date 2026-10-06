(* O3/O5 intermediate frame effects to be derived; not caller premises. *)
let c2_crypto_public_frame = new_definition
 `c2_crypto_public_frame =
    MAYCHANGE [RIP;RSP;RAX;RDI;RSI;RDX;R10;R11] ,,
    MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events]`;;
let c2_before_cleanup_frame = new_definition
 `c2_before_cleanup_frame stackpointer =
    MAYCHANGE [RIP;RSP;RAX;RDI;RSI;RDX;R10;R11;RBX;RBP;R12] ,,
    MAYCHANGE SOME_FLAGS ,,
    MAYCHANGE [memory :> bytes(word_sub stackpointer (word 32),32)] ,,
    MAYCHANGE [events]`;;
let c2_accumulated_frame = new_definition
 `c2_accumulated_frame stackpointer p q n m =
    MAYCHANGE [RIP;RSP;RAX;RDI;RSI;RDX;R10;R11;RBX;RBP;R12] ,,
    MAYCHANGE SOME_FLAGS ,,
    MAYCHANGE [memory :> bytes(p,if c2_equal m p q n then n else 0);
               memory :> bytes(word_sub stackpointer (word 32),32)] ,,
    MAYCHANGE [events]`;;
