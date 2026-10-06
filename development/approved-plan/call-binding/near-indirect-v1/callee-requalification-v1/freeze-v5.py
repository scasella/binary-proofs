#!/usr/bin/env python3
"""Union immutable predecessor closures and freeze this E3 replay, not a proof."""
import datetime as dt,hashlib,json,re
from pathlib import Path,PurePosixPath
BASE=Path(__file__).resolve().parent;ROOT=BASE.parents[4];REL=str(BASE.relative_to(ROOT))
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def read(n):return json.loads((ROOT/n).read_text())
parents=['development/approved-plan/replay/crypto-seal-v2.json','development/approved-plan/cleanse/interface/aggregate-seal-v1.json','development/approved-plan/call-binding/near-indirect-v1/qualification-seal-v1.json','development/approved-plan/call-binding/near-indirect-v1/execution-qualification-v1/seal-v1.json']
objects=[read(n) for n in parents];pr=objects[0]['preservation_receipt'];ph=objects[0]['preservation_receipt_sha256'];pres=read(pr)
assert sha(ROOT/pr)==ph
files={}
def add(n,h=None):
 p=ROOT/n
 if not p.is_file() or p.is_symlink():raise RuntimeError('Missing source: '+n)
 h=h or sha(p)
 if sha(p)!=h:raise RuntimeError('Frozen predecessor input changed: '+n)
 if n in pres['files']:
  if pres['files'][n]!=h:raise RuntimeError('Preserved-input digest conflict: '+n)
  return
 if n in files and files[n]!=h:raise RuntimeError('Successor digest conflict: '+n)
 files[n]=h
for n,o in zip(parents,objects):
 assert (o['preservation_receipt'],o['preservation_receipt_sha256'])==(pr,ph)
 for f,h in o['files'].items():add(f,h)
 add(n)
for p in BASE.iterdir():
 if p.is_file() and not p.name.startswith('seal-v'):add(str(p.relative_to(ROOT)))
# Resolve and record static needs/loadt recursively, including underlying model
# library loads. Runtime overlay bodies are independently pinned/audited.
seen=set();edges=[]
def visit(n):
 if n in seen:return
 seen.add(n);p=ROOT/n
 if p.suffix!='.ml':return
 s=p.read_text(errors='strict')
 for dep in re.findall(r'\b(?:needs|loadt)\s+"([^"\n]+)"',s):
  if dep.startswith('/work/'):r=dep[6:]
  elif dep.startswith('/'):raise RuntimeError('External checking source: '+dep)
  else:
   choices=[dep,'third_party/s2n-bignum/'+dep,'third_party/hol-light/'+dep]
   r=next((c for c in choices if (ROOT/c).is_file()),None)
   if r is None:raise RuntimeError('Unresolved static dependency: '+dep+' from '+n)
  if '..' in PurePosixPath(r).parts:raise RuntimeError('Unsafe dependency')
  add(r);edges.append({'source':n,'dependency':r});visit(r)
visit(REL+'/fresh-input-v3.ml')
# Candidate bodies mount at the upstream paths before any x86 constant exists.
visit(objects[2]['decoder']);visit(objects[2]['executor'])
crypto,cleanse,model,execution=objects
groups=list(crypto['groups'])
f=read('development/approved-plan/cleanse/functional/seal-v4.json')
a=read('development/approved-plan/cleanse/access/seal-v2.json')
i=read('development/approved-plan/cleanse/interface/expected-statements-v1.json')
interface=re.findall(r'\("([A-Z][A-Z0-9_]+)",\w+,\w+\)',(ROOT/'development/approved-plan/cleanse/interface/audit-v1.ml').read_text())
assert len(interface)==9
# Supplement names are fixed in the independent predecessor aggregate registry.
supp=sorted(set(cleanse['expected_theorems'])-set(f['expected_theorems'])-set(a['expected_theorems'])-set(interface))
groups.extend([
 {'file':'cleanse-functional.json','theorems':f['expected_theorems'],'definition_count':9,'definitions_key':'expanded_definitions'},
 {'file':'cleanse-access.json','theorems':a['expected_theorems'],'definition_count':19,'definitions_key':'expanded_definitions'},
 {'file':'cleanse-interface.json','theorems':interface,'definition_count':39,'definitions_key':'expanded_definitions'},
 {'file':'cleanse-supplement.json','theorems':supp,'definition_count':72,'definitions_key':'expanded_definitions'}])
q=read('development/approved-plan/call-binding/near-indirect-v1/expected-qualification-v1.json')
e=read(execution['expected_terms']);new=read(REL+'/expected-statements-v1.json');defs=read(REL+'/expected-definitions-v1.json')
groups.extend([
 {'file':'model-qualification.json','theorems':[r['name'] for r in q['decoder_claims']+q['executor_claims']],'definition_count':7,'definitions_key':None},
 {'file':'execution-qualification.json','theorems':[r['name'] for r in e['theorems']],'definition_count':41,'definitions_key':None},
 {'file':'e3-interface.json','theorems':[r['name'] for r in new['theorems']],'definition_count':119,'definitions_key':'expanded_definitions'}])
names=sorted({n for g in groups for n in g['theorems']})
assert len(supp)==28
assert len(names)==325,len(names)
assert all(re.fullmatch('[A-Z][A-Z0-9_]*',n) for n in names)
now=dt.datetime.now(dt.timezone.utc)
start=dt.datetime.fromtimestamp((BASE/'statements-v1.ml').stat().st_mtime,dt.timezone.utc)
seal={'scope':'E3_CANDIDATE5_CRYPTO_CLEANSE_CALLEE_REQUALIFICATION','experiment_id':'BP-20260930-E3-CALLEE-REQUALIFICATION-V1','created_at_utc':now.isoformat(),'driver':REL+'/fresh-input-v3.ml','host_driver':REL+'/replay-v1.py','opaque_loader':REL+'/opaque-callee-loader-v3.ml','decoder':model['decoder'],'executor':model['executor'],'checker_image_id':crypto['checker_image_id'],'preservation_receipt':pr,'preservation_receipt_sha256':ph,'files':files,'static_dependencies':edges,'predecessor_seals':[{'path':n,'sha256':sha(ROOT/n)} for n in parents],'groups':groups,'expected_unique_theorems':names,'expected_unique_theorem_count':len(names),'expected_definition_count':119,'expected_definition_names':defs['unique_names'],'all_equation_check_count':218,'new_integration_theorem_count':7,'goals_frozen_before_main_search':True,'old_callee_Pre_and_post_unchanged':True,'proof_uses_saved_result':False,'new_routine_bytes':0,'requalified_previously_completed_unique_bytes':165,'human_review':'PENDING','full_O1_pass':False,'R1_pass':False,'model_candidate_accepted_for_clients':False,'construction_interval':{'start_utc':start.isoformat(),'frozen_at_utc':now.isoformat(),'elapsed_wall_interval_seconds':(now-start).total_seconds(),'active_compute_seconds':None,'includes':'New seven-goal integration construction, source closure/audit/driver staging and first failed trial replay wall interval; old E2 construction excluded', 'failed_trial_checking_seconds':356.93921479201526},'crypto_boundary_programs':['development/approved-plan/loaded-witness/full-binding/acquire-file-map-v2.py','development/approved-plan/loaded-witness/full-binding/crosscheck-image-clauses-v1.py'],'cleanse_boundary_driver':'development/approved-plan/cleanse/interface/replay-v1.py','cleanse_boundary':{k:cleanse[k] for k in ['acquisition_program','image_crosscheck_program','decode_registry','decode_site_source']},'positive_claim':'Fresh reconstruction of unchanged all-length Crypto/Cleanse four-property public packages and same-Pre full-image witnesses in the candidate5 namespace, new public V6 policy/interface objects, and rechecked Crypto first-RET architectural observation noninterference. No caller composition, new165-byte discovery, verified ELF parser/loader, physical ISA fidelity theorem or independent human review.'}
out=BASE/'seal-v3.json'
if out.exists():raise RuntimeError('Refusing to overwrite frozen seal')
out.write_text(json.dumps(seal,indent=2,sort_keys=True)+'\n')
print(json.dumps({'seal':str(out.relative_to(ROOT)),'sha256':sha(out),'files':len(files),'preserved_files':len(pres['files']),'expected_unique_theorems':len(names),'unique_definitions':119,'equation_checks':218,'static_dependencies':len(edges)}))
