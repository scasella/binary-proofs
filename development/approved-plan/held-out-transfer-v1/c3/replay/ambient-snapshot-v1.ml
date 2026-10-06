(* Observation only: read global simplifier tables; do not change them. *)
let c3_development_ambient_json text =
 let b=Buffer.create 256 in Buffer.add_char b '"';
 String.iter (fun c->match c with
  | '"' -> Buffer.add_string b "\\\""
  | '\\' -> Buffer.add_string b "\\\\"
  | '\n' -> Buffer.add_string b "\\n"
  | '\r' -> Buffer.add_string b "\\r"
  | '\t' -> Buffer.add_string b "\\t"
  | _ -> if Char.code c<32 then Buffer.add_string b (Printf.sprintf "\\u%04x" (Char.code c)) else Buffer.add_char b c) text;
 Buffer.add_char b '"'; Buffer.contents b;;
let rec c3_development_ambient_constants tm =
 if is_const tm then [fst(dest_const tm)]
 else if is_comb tm then union (c3_development_ambient_constants(rator tm))
                              (c3_development_ambient_constants(rand tm))
 else if is_abs tm then c3_development_ambient_constants(snd(dest_abs tm))
 else [];;
let c3_development_ambient_snapshot label path =
 let json=c3_development_ambient_json in
 let array xs="["^String.concat "," xs^"]" in
 let theorem th="{\"conclusion\":"^json(string_of_term(concl th))^
   ",\"hypotheses\":"^array(map(fun tm->json(string_of_term tm))(hyp th))^
   ",\"free_variable_count\":"^string_of_int(length(frees(concl th)))^
   ",\"constants\":"^array(map json(c3_development_ambient_constants(concl th)))^"}" in
 let rewrites=basic_rewrites() and congruences=basic_congs() and conversions=basic_convs() in
 let row (name,(pattern,_))="{\"name\":"^json name^
   ",\"pattern\":"^json(string_of_term pattern)^
   ",\"constants\":"^array(map json(c3_development_ambient_constants pattern))^"}" in
 let stream=open_out path in
 output_string stream ("{\"schema\":\"c3-ambient-automation-snapshot-v1\",\"label\":"^json label^
   ",\"basic_rewrites\":"^array(map theorem rewrites)^
   ",\"basic_congruences\":"^array(map theorem congruences)^
   ",\"basic_conversions\":"^array(map row conversions)^
   ",\"axioms\":"^array(map theorem(axioms()))^
   ",\"conversion_closure_dependencies_observable\":false,"^
   "\"tactic_closure_dependencies_observable\":false,"^
   "\"formal_dependency_isolation\":false}\n");
 close_out stream;
 print_endline("C3_AMBIENT_SNAPSHOT_WRITTEN "^label^" "^path);;
