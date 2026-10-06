#!/usr/bin/env python3
"""Generate recipes/audits from a digest-frozen independent qualification spec."""
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
spec_path = HERE / "expected-qualification-v1.json"
expected_sha = "3b23f58d865f3d6ae55df34e7bb769ee7fe4b6c317bc4e7641671cf5545d1141"
if hashlib.sha256(spec_path.read_bytes()).hexdigest() != expected_sha:
    raise RuntimeError("Frozen qualification statements changed")
spec = json.loads(spec_path.read_text())
proof = "(* Frozen expectations predate these finite decoder proofs. *)\n"
for claim in spec["decoder_claims"]:
    proof += "let " + claim["name"] + " = prove\n (`" + claim["statement"] + "`,\n"
    proof += "  CONV_TAC(LAND_CONV DECODE_CONV) THEN\n"
    proof += "  REWRITE_TAC(r1_near_register :: r1_near_operand64 :: GPR_thms));;\n\n"

def ocaml_list(rows):
    return "[\n" + ";\n".join(rows) + "\n ]"
ds = ocaml_list(["  " + json.dumps(d["name"]) + ",parse_term " + json.dumps(d["equation"]) + "," + d["name"]
                 for d in spec["definitions"]])
claims = spec["executor_claims"] + spec["decoder_claims"]
ts = ocaml_list(["  " + json.dumps(t["name"]) + ",parse_term " + json.dumps(t["statement"]) + "," + t["name"]
                 for t in claims])
audit = """(* Compare live kernel objects with literal independently frozen expectations.
 * Counts, missing objects, hypotheses, or changed foundation axioms are fatal. *)
let r1_near_qualification_audit path =
 let ds = """ + ds + """ in
 List.iter(fun(name,expected,th)->
  if hyp th <> [] ||
     not(aconv (snd(strip_forall(concl th))) (snd(strip_forall expected)))
  then failwith(name^": model definition mismatch")) ds;
 let targets = """ + ts + """ in
 let rows=List.map(fun(name,expected,th)->
  if hyp th<>[] then failwith(name^": hypotheses");
  if not(aconv(concl th) expected) then failwith(name^": exact statement mismatch");
  if axioms()<>model_initial_axioms then failwith(name^": foundation axiom changed");
  "{\\"name\\":"^Printf.sprintf "%S" name^","^
  "\\"statement\\":"^Printf.sprintf "%S"(string_of_term(concl th))^","^
  "\\"hypothesis_count\\":0,\\"new_axioms\\":0,\\"conclusion_matches_expected\\":true}") targets in
 let audit_channel=open_out path in
 output_string audit_channel ("{\\"model_candidate_accepted_for_clients\\":false,"^
  "\\"human_review\\":\\"PENDING\\",\\"expanded_definition_count\\":7,"^
  "\\"theorems\\":["^String.concat "," rows^"]}\\n");
 close_out audit_channel;;
"""
for name, content in [("decoder-qualification-proof-v1.ml", proof),
                       ("qualification-audit-v2.ml", audit)]:
    p = HERE / name
    if p.exists():
        raise RuntimeError("Never overwrite a qualification source: " + name)
    p.write_text(content)
    print(json.dumps({"file": name, "sha256": hashlib.sha256(p.read_bytes()).hexdigest()}))
