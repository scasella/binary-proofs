#!/usr/bin/env python3
"""Freeze the E3 namespace replay; no checker or target execution."""
import datetime as dt, hashlib, json, re
from pathlib import Path
BASE=Path(__file__).resolve().parent
ROOT=BASE.parents[4]
REL=str(BASE.relative_to(ROOT))
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def write(name,obj):
 p=BASE/name
 if p.exists():raise RuntimeError('Refusing to overwrite '+str(p))
 p.write_text(json.dumps(obj,indent=2,sort_keys=True)+'\n' if not isinstance(obj,str) else obj)
# These sources are copied as text only. Expectations never originate in a
# theorem result, saved receipt or log.
crypto=ROOT/'development/approved-plan/replay/crypto-input-v2.ml'
s=crypto.read_text()
lines=[]
for l in s.splitlines():
 if l.startswith(('use_file_raise_failure','let assurance_initial_axioms','let backend_initial_axioms','let component_guard')) or 'component_guard(fun () -> exit 0)' in l:continue
 lines.append(l.replace('-> loadt ','-> needs '))
write('crypto-components-v1.ml','(* Needs-tracked exact predecessor closure under candidate5 only. *)\n'+'\n'.join(lines)+'\n')
execution=ROOT/'development/approved-plan/call-binding/near-indirect-v1/execution-qualification-v1/components-v1.ml'
write('execution-components-v1.ml',execution.read_text().replace('loadt ','needs '))
# Literal model/ABI equations: exact expected source text, including the
# entire changed decoder and x86_execute, not an old model body.
equations=[]
def add(name,comparison,term,origin):equations.append(dict(name=name,comparison=comparison,expected=term,origin=origin))
p='development/approved-plan/cleanse/interface/aggregate-expected-definitions-v1.json'
for d in json.loads((ROOT/p).read_text())['equations']:add(d['name'],d['comparison'],d['expected'],p)
# Root Crypto's independent frozen full audit consists of31+15+12+2+13 equations.
count=0
for p in ['development/approved-plan/replay/audit-assurance-v1.ml','development/approved-plan/interface/crypto/audit-v1.ml']:
 s=(ROOT/p).read_text()
 for m in re.finditer(r'"([A-Za-z0-9_]+)",parse_term\s+("(?:\\.|[^"\\])*")\s*,\s*([A-Za-z0-9_]+)',s):
  name,literal,th=m.groups()
  if not name[0].islower():continue
  if name!=th:raise RuntimeError('Definition binding mismatch')
  add(name,'body',json.loads(literal),p);count+=1
for p,prefix in [('development/approved-plan/replay/audit-loaded-v1.ml','lw'),('development/approved-plan/loaded-witness/full-binding/audit-v2.ml','fb')]:
 s=(ROOT/p).read_text()
 for name,term,th in re.findall(prefix+r'_audit_definition\s+"([A-Za-z0-9_]+)"\s+`([\s\S]*?)`\s+([A-Za-z0-9_]+);;',s):
  if name!=th:raise RuntimeError('Definition binding mismatch')
  add(name,'body',term,p);count+=1
p='development/approved-plan/replay/expected-observation-definitions-v1.json'
for name,term in json.loads((ROOT/p).read_text()).items():add(name,'body',term,p);count+=1
assert count==73,count
for p in ['development/approved-plan/call-binding/near-indirect-v1/expected-qualification-v1.json','development/approved-plan/call-binding/near-indirect-v1/execution-qualification-v1/expected-audit-v2.json']:
 for d in json.loads((ROOT/p).read_text())['definitions']:add(d['name'],'body',d['equation'],p)
assert len(equations)==218,len(equations)
unique=sorted({d['name'] for d in equations})
write('expected-definitions-v1.json',{'expectation_origin':'Independent predecessor literals plus candidate5 complete changed model and V6 literals, frozen before replay','equations':equations,'all_equation_check_count':len(equations),'unique_definition_count':len(unique),'unique_names':unique})
write('definition-claims-v1.ml','let e3_callee_definition_claims = [\n'+''.join('  '+json.dumps(d['name'])+','+json.dumps(d['comparison'])+',parse_term '+json.dumps(d['expected'])+','+d['name']+';\n' for d in equations)+'];;\n')
new=json.loads((BASE/'expected-statements-v1.json').read_text())['theorems']
write('statement-claims-v1.ml','let e3_callee_new_claims = [\n'+''.join('  '+json.dumps(d['name'])+',parse_term '+json.dumps(d['statement'])+','+d['name']+';\n' for d in new)+'];;\n')
write('components-v1.ml',f'''(* Single namespace. Candidate5 overlays are set before HOL loads base.ml. *)
needs "/work/{REL}/crypto-components-v1.ml";;
needs "/work/development/approved-plan/cleanse/interface/aggregate-components-v1.ml";;
needs "/work/development/approved-plan/cleanse/interface/aggregate-audit-v1.ml";;
needs "/work/development/approved-plan/call-binding/near-indirect-v1/qualification-statements-v1.ml";;
needs "/work/development/approved-plan/call-binding/near-indirect-v1/qualification-proof-attempt2.ml";;
needs "/work/development/approved-plan/call-binding/near-indirect-v1/decoder-qualification-proof-attempt2.ml";;
needs "/work/development/approved-plan/call-binding/near-indirect-v1/qualification-audit-v2.ml";;
needs "/work/{REL}/execution-components-v1.ml";;
needs "/work/development/approved-plan/call-binding/near-indirect-v1/execution-qualification-v1/audit-v2.ml";;
needs "/work/{REL}/proof-attempt1.ml";;
''')
write('opaque-callee-loader-v1.ml',f'''(* Same-process theorem entry for the separate client lane. The worker uses
   public contract definitions and these live theorem objects as an interface.
   This loader reconstructs proofs; no saved receipt is a theorem premise.
   Use ONLY in a fresh candidate5-overlaid HOL namespace, with the sealed
   foundation-axiom snapshot. No implementation recipe need be inspected by
   the client worker. The closed source and model literals are checked first. *)
needs "/work/{REL}/components-v1.ml";;
(* Public theorem interface: BP_E3_CRYPTO_PUBLIC_CALLER_POLICY,
   BP_E3_CRYPTO_PUBLIC_CALLER_INTERFACE, BP_E3_CLEANSE_PUBLIC_CALLER_POLICY,
   BP_E3_CLEANSE_PUBLIC_CALLER_INTERFACE. Public E2 Pre/post bindings stay exact.
   All-count first-RET Crypto architectural observation objects are also
   reconstructed in this namespace; Cleanse O2 is not asserted. *)
''')
print(json.dumps({'frozen_expanded_equations':len(equations),'unique_expanded_definitions':len(unique),'new_goals':len(new)}))
