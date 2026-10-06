#!/usr/bin/env python3
"""Combine literal frozen expectations; never derive expected terms from theorems."""
from pathlib import Path
import json,re,hashlib
ROOT=Path(__file__).resolve().parents[5]
LANE=Path(__file__).resolve().parent
PARENT=LANE.parent

def readj(p):return json.loads(p.read_text())
def dump(p,x):p.write_text(json.dumps(x,indent=2,sort_keys=True)+'\n')
def defs_from(p):
 return [{'name':m[0],'equation':m[1],'source':str(p.relative_to(ROOT))} for m in re.findall(r'let\s+(\w+)\s*=\s*new_(?:definition|recursive_definition)(?:\s+num_RECURSION)?\s*`([^`]+)`',p.read_text())]
terms=readj(LANE/'expected-statements-v1.json')['theorems'][:]
# These three literal terms were separately frozen before their proof recipes.
for file,name,statement_name in [('normalization-statements-v1.ml','R1_ABSOLUTE_OPERATION_ETA','r1_absolute_operation_eta_statement'),('normalization-statements-v1.ml','R1_WORD_VAL_ADDRESS','r1_word_val_address_statement'),('control-helper-statement-v1.ml','R1_EVENTUALLY_N_ONE','r1_eventually_n_one_statement')]:
 source=(LANE/file).read_text()
 term=re.search(r'let '+statement_name+r'\s*=\s*`([^`]+)`',source).group(1)
 terms.append({'name':name,'statement_name':statement_name,'statement':term})
names=['ABI_CALLER_EXTENDED_PROJECTION','ABI_CALLER_EXTENDED_BACKLIFT_ALL','ABI_CALLER_EXTENDED_EQUIVALENCE','ABI_CALLER_EXTENDED_PROGRESS','ABI_CALLER_EXTENDED_REFINES_V5','ABI_CALLER_STEP_PRESERVES_OMITTED','ABI_CALLER_EQUAL_IMPLIES_REQUIRED_CONTROLS','ABI_CALLER_DECODED_SCALAR_UNIQUE','ABI_CALLER_CHECKED_RUN_LIFT']
for name,t in zip(names,readj(LANE/'abi-v6/expected-statements-v6-attempt2.json')['statements']):terms.append(dict(t,name=name))
terms+=readj(LANE/'abi-v6/expected-coverage-statements-v1.json')['theorems']
assert len(terms)==len({t['name'] for t in terms})==53
# Expanded meanings include immutable candidate ISA plus every new predicate
# in the loaded assurance/ABI layers, code registry and prefixes.
defs=readj(PARENT/'expected-qualification-v1.json')['definitions'][:]
defs+=readj(ROOT/'development/approved-plan/abi-qualification/expected-definitions-v4.json')['definitions']
for file in ['development/approved-plan/cleanse/helpers/abi-v5/extension-v5.ml','development/approved-plan/call-binding/near-indirect-v1/execution-qualification-v1/abi-v6/extension-v6-attempt2.ml','development/approved-plan/call-binding/near-indirect-v1/execution-qualification-v1/abi-v6/code-v1.ml','development/approved-plan/call-binding/near-indirect-v1/execution-qualification-v1/abi-v6/sites-v1.ml','development/approved-plan/call-binding/near-indirect-v1/loaded-stub-v1/spec-v2.ml','development/approved-plan/assurance/correspondence.ml','development/approved-plan/assurance/policy.ml','development/approved-plan/assurance/path.ml']:
 defs+=defs_from(ROOT/file)
assert len(defs)==len({d['name'] for d in defs})
dump(LANE/'expected-audit-v1.json',{'scope':'CANDIDATE_NEAR_INDIRECT_EXECUTION_ABI_QUALIFICATION_ONLY','theorems':terms,'definitions':defs,'human_review':'PENDING','expectation_origin':'Literal pre-search statement registries and fixed source definition equations; no live theorem used to construct expectations.'})
ml='(* Literal comparison of actual kernel objects. Missing objects are fatal. *)\nlet r1_execution_qualification_audit path =\n let ds = [\n'
ml+=';\n'.join('  '+json.dumps(d['name'])+',parse_term '+json.dumps(d['equation'])+','+d['name'] for d in defs)+'\n ] in\n'
ml+=''' List.iter(fun(name,expected,th)->
  if hyp th<>[] then failwith(name^": definition hypotheses");
  if not(aconv(snd(strip_forall(concl th)))(snd(strip_forall expected)))
  then failwith(name^": expanded definition mismatch")) ds;
 let targets = [
'''
ml+=';\n'.join('  '+json.dumps(t['name'])+',parse_term '+json.dumps(t['statement'])+','+t['name'] for t in terms)+'\n ] in\n'
ml+=''' if axioms()<>r1_execution_initial_axioms then failwith "Foundation axioms changed";
 let rows=List.map(fun(name,expected,th)->
  if hyp th<>[] then failwith(name^": hypotheses");
  if not(aconv(concl th)expected) then failwith(name^": exact statement mismatch");
  "{\\"name\\":"^Printf.sprintf "%S" name^","^
  "\\"statement\\":"^Printf.sprintf "%S"(string_of_term(concl th))^","^
  "\\"hypothesis_count\\":0,\\"new_axioms\\":0,\\"conclusion_matches_expected\\":true}")targets in
 let audit_channel=open_out path in
 output_string audit_channel("{\\"R1_pass\\":false,\\"human_review\\":\\"PENDING\\",\\"expanded_definition_count\\":"^
  string_of_int(List.length ds)^",\\"theorems\\":["^String.concat "," rows^"]}\\n");
 close_out audit_channel;;
'''
(LANE/'audit-v1.ml').write_text(ml)
print(len(terms),len(defs))
