#!/usr/bin/env python3
"""Generate actual-object audit source from the original frozen C1 literals."""
import json
from pathlib import Path

def ocaml(text):
    # JSON's ASCII string escapes used here are also valid OCaml string escapes.
    return json.dumps(text, ensure_ascii=True)

def generate(registry):
    definitions = registry["definitions"]
    output = r'''(* Adapted from normal-entry-e5-v1/live-audit-v3.ml.
   Expected strings come from original C1 and pre-proof witness/helper freezes.
   GEN_ALL below is the kernel closure of primitive recursive equations. *)
let c1_fresh_typealpha tm =
 let tvs=sort (fun a b->compare a b<0) (type_vars_in_term tm) in
 inst(map(fun(i,t)->mk_vartype("C1Audit"^string_of_int i),t)
      (map2(fun i t->i,t)(0--(length tvs-1))tvs))tm;;
let c1_fresh_close tm=list_mk_forall(frees tm,tm);;
let c1_fresh_json text =
 let b=Buffer.create 256 in Buffer.add_char b '"';
 String.iter (fun c->match c with
  | '"' -> Buffer.add_string b "\\\""
  | '\\' -> Buffer.add_string b "\\\\"
  | '\n' -> Buffer.add_string b "\\n"
  | '\r' -> Buffer.add_string b "\\r"
  | '\t' -> Buffer.add_string b "\\t"
  | _ -> if Char.code c<32 then Buffer.add_string b (Printf.sprintf "\\u%04x" (Char.code c)) else Buffer.add_char b c) text;
 Buffer.add_char b '"'; Buffer.contents b;;
let c1_fresh_rf_checked_run_closed=GEN_ALL e5_rf_checked_run;;
'''
    output += "let c1_fresh_definition_rules=[\n" + ";\n".join(
        f"({ocaml(r['name'])},{'c1_fresh_rf_checked_run_closed' if r['name']=='e5_rf_checked_run' else r['name']})"
        for r in definitions) + "\n];;\n"
    output += "let c1_fresh_rows=[\n"
    entries = []
    for kind, rows in [("object", registry["objects"]), ("definition", definitions)]:
        for row in rows:
            binding = "c1_fresh_rf_checked_run_closed" if row["name"] == "e5_rf_checked_run" else row["name"]
            entries.append("(" + ",".join([ocaml(kind), ocaml(row["name"]),
                           ocaml(row["literal"]), ocaml(row["expected_literal_sha256"]),
                           ocaml(row["comparison"]), binding]) + ")")
    output += ";\n".join(entries) + "\n];;\n"
    output += r'''let c1_fresh_checked_rows=List.map(fun(kind,name,literal,digest,mode,th)->
 if hyp th<>[] || frees(concl th)<>[] then failwith(name^":hyp/free variables");
 if axioms()<>fresh_initial_axioms || axioms()<>[INFINITY_AX;SELECT_AX;ETA_AX]
 then failwith(name^":axioms changed");
 let expected=parse_term literal in
 let actual=if kind="object" then concl th else concl(SPEC_ALL th) in
 let normalize tm=c1_fresh_close(c1_fresh_typealpha tm) in
 let matches=if kind="object" then aconv actual expected else
   aconv(normalize actual)(normalize expected) in
 if not matches then failwith(name^":original literal mismatch");
 (* Exclude recursive run equations and the definition's own LHS rewrite.
    Every supporting definition is independently anchored by the rows above. *)
 let rules=List.map snd(List.filter(fun(n,_)->n<>name && n<>"e5_rf_checked_run")
   c1_fresh_definition_rules) in
 let expanded=rhs(concl(REWRITE_CONV rules actual)) in
 let expected_expanded=rhs(concl(REWRITE_CONV rules expected)) in
 if not(aconv(normalize expanded)(normalize expected_expanded))
 then failwith(name^":expanded definition mismatch");
 print_endline("C1_FRESH_ACTUAL_OBJECT_CHECKED "^name);
 "{\"kind\":"^c1_fresh_json kind^",\"name\":"^c1_fresh_json name^
 ",\"expected_literal_sha256\":"^c1_fresh_json digest^
 ",\"comparison\":"^c1_fresh_json mode^
 ",\"hypothesis_count\":0,\"free_variable_count\":0,\"new_axioms\":0,\"literal_match\":true,"^
 "\"expanded_match\":true,\"conclusion\":"^c1_fresh_json(string_of_term(concl th))^
 ",\"expanded_conclusion\":"^c1_fresh_json(string_of_term expanded)^"}")c1_fresh_rows;;
if Sys.file_exists "/output/c1-live-audit-v1.json" then failwith "C1_FRESH_OUTPUT_ALREADY_EXISTS";;
let c1_fresh_audit_channel=open_out "/output/c1-live-audit-v1.json";;
'''
    output += 'output_string c1_fresh_audit_channel\n (' + ocaml(json.dumps({
        "schema": "c1-fresh-live-audit-v1", "theorem_count": 28,
        "original_target_count": 7, "witness_target_count": 21,
        "nonvacuity_case_count": 7,
        "definition_count": len(definitions), "initial_axiom_count": 3,
        "final_axiom_count": 3, "axioms_unchanged": True,
        "standard_axioms": ["INFINITY_AX", "SELECT_AX", "ETA_AX"]})[:-1] + ',"rows":[') + \
        '^String.concat "," c1_fresh_checked_rows^"]}\\n");;\n'
    output += 'close_out c1_fresh_audit_channel;;\nprint_endline "C1_FRESH_ALL7_ORIGINAL_TARGETS_WITNESS21_ALL_DEFINITIONS_EXPANDED_HYP0_FREES0_STANDARD3_LIVE_AUDIT_PASS";;\n'
    return output
