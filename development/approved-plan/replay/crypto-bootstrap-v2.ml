use_file_raise_failure := true;;
let replay_entry f = try f() with e -> prerr_endline(Printexc.to_string e); exit 1;;
replay_entry(fun () -> loadt "/work/development/approved-plan/replay/crypto-input-v2.ml");;
