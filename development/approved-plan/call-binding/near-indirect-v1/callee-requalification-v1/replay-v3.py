#!/usr/bin/env python3
"""Offline digest-closed E3 requalification of both affected callees.

A saved receipt cannot satisfy any obligation. Preflight is observation only;
accepted routine and trace objects must be reconstructed in the candidate5
namespace, with exact frozen literal model/ABI definition and statement checks.
"""
import argparse, datetime as dt, importlib.util, json, re, shutil, subprocess
import sys, tarfile, time, uuid
from pathlib import Path, PurePosixPath
ROOT=Path(__file__).resolve().parents[5]
sys.path.insert(0,str(ROOT/'scripts'))
from check import integrity,binding,sha

def dump(p,x):
 p.parent.mkdir(parents=True,exist_ok=True)
 p.write_text(json.dumps(x,indent=2,sort_keys=True)+'\n')
def safe(n):
 p=PurePosixPath(n)
 if p.is_absolute() or '..' in p.parts or not p.parts:raise ValueError('Unsafe frozen path: '+n)
 return n
def checked(root,n,h):
 p=root/safe(n)
 if not p.is_file() or p.is_symlink() or sha(p)!=h:raise ValueError('Frozen input mismatch or missing dependency: '+n)
 return p
def module_at(root,n):
 spec=importlib.util.spec_from_file_location('e3_boundary_'+uuid.uuid4().hex,root/safe(n))
 m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m

def boundaries(root,seal):
 # Trusted extraction checks are executed again; never loaded from an old PASS.
 cleanse=module_at(root,seal['cleanse_boundary_driver']).boundary_checks(root,seal['cleanse_boundary'])
 crypto=[]
 for n in seal['crypto_boundary_programs']:
  p=subprocess.run([sys.executable,str(root/n)],cwd=root,capture_output=True,text=True)
  if p.returncode:raise ValueError('Crypto acquisition/image check failed: '+n+' '+p.stderr)
  crypto.append(json.loads(p.stdout))
 if crypto[0]['status']!='PASS_TRUSTED_WHOLE_FILE_MAP_ACQUISITION' or crypto[1]['status']!='PASS_FORMAL_SOURCE_IMAGE_INTERVAL_CROSSCHECK':
  raise ValueError('Unexpected whole-image acquisition scope')
 return {'CRYPTO_memcmp':crypto,'OPENSSL_cleanse':cleanse}

def preflight(args):
 stamp=dt.datetime.now(dt.timezone.utc).strftime('%Y%m%dT%H%M%SZ')
 run=ROOT/'results/development'/('crypto-loop-e3-callees-preflight-'+stamp+'-'+uuid.uuid4().hex[:8])
 ledger={'preflight_only':True,'proof_started':False,'target_routine_executed':False,'callee_chains_requalified':False,'R1_pass':False,'seal':args.seal,'seal_sha256':args.sha256}
 try:
  seal=json.loads(checked(ROOT,args.seal,args.sha256).read_text())
  if seal['scope']!='E3_CANDIDATE5_CRYPTO_CLEANSE_CALLEE_REQUALIFICATION':raise ValueError('Wrong E3 replay scope')
  if checked(ROOT,seal['host_driver'],seal['files'][seal['host_driver']]).resolve()!=Path(__file__).resolve():raise ValueError('Host driver does not match selected seal')
  pres=json.loads(checked(ROOT,seal['preservation_receipt'],seal['preservation_receipt_sha256']).read_text())
  archive=checked(ROOT,pres['archive_path'],pres['archive_sha256'])
  if set(pres['files'])&set(seal['files']):raise ValueError('Candidate would overwrite preserved predecessor sources')
  for n,h in seal['files'].items():checked(ROOT,n,h)
  lock=integrity()
  if lock['checker_image_id']!=seal['checker_image_id']:raise ValueError('Pinned checker mismatch')
  byte_binding=binding()
  image=boundaries(ROOT,seal)
  ledger.update(status='PASS_PREFLIGHT_NOT_PROOF',canonical_E1_integrity=True,artifact_binding=byte_binding,whole_image_checks=image,source_file_count=len(pres['files'])+len(seal['files']),candidate_model_hashes={n:seal['files'][n] for n in (seal['decoder'],seal['executor'])})
  dump(run/'ledger.json',ledger)
  if args.preflight:print(json.dumps({'status':ledger['status'],'ledger':str((run/'ledger.json').relative_to(ROOT)),'preflight_only':True,'proof_started':False,'target_routine_executed':False}),flush=True)
  return seal,pres,archive,ledger,run
 except Exception as e:
  ledger.update(status='FAIL_PREFLIGHT_NOT_PROOF',error=str(e));dump(run/'ledger.json',ledger)
  print(json.dumps({'status':ledger['status'],'error':str(e),'ledger':str((run/'ledger.json').relative_to(ROOT)),'preflight_only':True,'proof_started':False,'target_routine_executed':False}),flush=True)
  raise

def validate_group(a,group,exact_definition_rows):
 if not a:return False
 rows=a.get('theorems',[]);names=[r['name'] for r in rows]
 good=len(names)==len(group['theorems']) and set(names)==set(group['theorems']) and all(r['hypothesis_count']==0 and r['new_axioms']==0 and r['conclusion_matches_expected'] is True for r in rows)
 key=group.get('definitions_key')
 if key:
  defs=a.get(key,[])
  def exact_definition(d):
   status=d.get('equation_matches_expected',d.get('conclusion_matches_expected'))
   ref=exact_definition_rows.get(d.get('name'))
   # Every legacy row must resolve to a separately frozen exact live object.
   # Optional old fields may be absent, but any explicit false/other value
   # or different actual conclusion is rejected. No missing field defaults
   # to a successful proof assertion.
   if not(ref and ref.get('conclusion_matches_expected') is True and
          ref.get('hypothesis_count')==0 and ref.get('new_axioms')==0):return False
   if status is not None and status is not True:return False
   if 'hypothesis_count' in d and d['hypothesis_count']!=0:return False
   if 'new_axioms' in d and d['new_axioms']!=0:return False
   if 'statement' in d and d['statement']!=ref['statement']:return False
   return True
  good=good and len(defs)==group['definition_count'] and all(exact_definition(d) for d in defs)
 else:good=good and a.get('expanded_definition_count')==group['definition_count']
 return good

def replay(args):
 seal,pres,archive,boundary,pre=preflight(args)
 if args.preflight:return 0
 stamp=dt.datetime.now(dt.timezone.utc).strftime('%Y%m%dT%H%M%SZ')
 run=ROOT/'results/development'/('crypto-loop-e3-callees-closed-'+stamp+'-'+uuid.uuid4().hex[:8])
 stage,output=run/'source',run/'checker-output';stage.mkdir(parents=True);output.mkdir()
 seen=set()
 with tarfile.open(archive,'r:gz') as tar:
  for m in tar.getmembers():
   n=safe(m.name)
   if n in seen or n not in pres['files'] or not m.isfile():raise ValueError('Unexpected preserved archive member: '+n)
   seen.add(n);dest=stage/n;dest.parent.mkdir(parents=True,exist_ok=True)
   with tar.extractfile(m) as src,dest.open('xb') as dst:shutil.copyfileobj(src,dst)
   dest.chmod(m.mode&0o777);checked(stage,n,pres['files'][n])
 if seen!=set(pres['files']):raise ValueError('Incomplete predecessor archive')
 sources=dict(pres['files'])
 for n,h in seal['files'].items():
  dest=stage/n;dest.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(ROOT/n,dest);checked(stage,n,h);sources[n]=h
 dump(run/'inputs.json',{'seal_sha256':args.sha256,'files':sources})
 dump(run/'boundary-checks.json',boundaries(stage,seal))
 shutil.copy2(stage/seal['driver'],run/'input.ml')
 command=['docker','run','-i','--rm','--pull','never','--network','none','--memory','2g','--memory-swap','2g','--platform','linux/arm64','-e','HOLLIGHT_DIR=/work/third_party/hol-light','-v',str(stage)+':/work:ro','-v',str(output)+':/output:rw','-v',str(stage/seal['decoder'])+':/work/third_party/s2n-bignum/x86/proofs/decode.ml:ro','-v',str(stage/seal['executor'])+':/work/third_party/s2n-bignum/x86/proofs/x86.ml:ro','-w','/work/third_party/s2n-bignum',seal['checker_image_id'],'/work/third_party/hol-light/ocaml-hol','-init','/work/third_party/hol-light/hol.ml','-safe-string','-I','/work/third_party/hol-light']
 dump(run/'started.json',{'proof_started':True,'target_routine_executed':False,'command':command,'candidate5_only_namespace':True,'readonly_source_with_no_writable_alias':True,'network':'none','preflight_ledger':str((pre/'ledger.json').relative_to(ROOT))})
 print(json.dumps({'run_dir':str(run.relative_to(ROOT)),'stage':'starting_fresh_candidate5_HOL'}),flush=True)
 start=time.monotonic()
 with (run/'input.ml').open('rb') as inp,(run/'replay.log').open('wb') as log:proc=subprocess.run(command,stdin=inp,stdout=log,stderr=subprocess.STDOUT)
 elapsed=time.monotonic()-start
 audits={};groups_ok=True;errors=[]
 for g in seal['groups']:
  p=output/g['file'];audits[g['file']]=json.loads(p.read_text()) if p.exists() else None
 independent=audits.get('e3-interface.json')
 exact_definition_rows={} if not independent else {d['name']:d for d in independent.get('expanded_definitions',[])}
 for g in seal['groups']:
  if not validate_group(audits[g['file']],g,exact_definition_rows):groups_ok=False;errors.append({'file':g['file'],'reason':'Missing or mismatched live exact audit group'})
 rows=[r for a in audits.values() if a for r in a.get('theorems',[])]
 unique={}
 for r in rows:
  if r['name'] in unique and unique[r['name']]['statement']!=r['statement']:groups_ok=False;errors.append({'name':r['name'],'reason':'Inconsistent duplicate live conclusion'})
  unique[r['name']]=r
 own=audits.get('e3-interface.json')
 definitions=[] if not own else own['expanded_definitions']
 defnames=[d['name'] for d in definitions]
 groups_ok=groups_ok and set(unique)==set(seal['expected_unique_theorems']) and len(defnames)==len(set(defnames))==119 and set(defnames)==set(seal['expected_definition_names']) and own is not None and own.get('all_equation_check_count')==218
 unchanged=all((stage/n).is_file() and not (stage/n).is_symlink() and sha(stage/n)==h for n,h in sources.items())
 canonical=True
 try:
  integrity();checked(ROOT,args.seal,args.sha256)
  for n,h in seal['files'].items():checked(ROOT,n,h)
 except Exception:canonical=False
 logtext=re.sub(r'\x1b\[[0-?]*[ -/]*[@-~]','',(run/'replay.log').read_text(errors='replace'))
 passed=bool(proc.returncode==0 and groups_ok and unchanged and canonical and 'E3_CALLEE_FRESH_COMPLETE_CRYPTO_CLEANSE_AND_CRYPTO_FIRST_RET_TRACE' in logtext and not re.search(r'(?m)^\s*(?:#\s*)?(?:Error|Exception):',logtext))
 receipt={'experiment_id':seal['experiment_id'],'status':'PASS_FRESH_E3_AFFECTED_CALLEE_REQUALIFICATION' if passed else 'FAIL_FRESH_E3_AFFECTED_CALLEE_REQUALIFICATION','process_exit':proc.returncode,'elapsed_checking_seconds':elapsed,'construction_interval':seal['construction_interval'],'kernel_audits':audits,'live_unique_theorem_count':len(unique),'expected_unique_theorem_count':len(seal['expected_unique_theorems']),'expanded_definition_count':len(definitions),'all_equation_check_count':218 if own else 0,'failed_audit_obligations':errors,'callee_chains_requalified':passed,'CRYPTO_memcmp_four_property_pass':passed,'OPENSSL_cleanse_four_property_pass':passed,'CRYPTO_memcmp_first_RET_architectural_O2_pass':passed,'OPENSSL_cleanse_O2_pass':False,'public_V6_interfaces_requalified':passed,'same_pre_witnesses':passed,'target_routine_executed':False,'proof_started':True,'R1_pass':False,'core_complete':False,'new_routine_byte_discoveries':0,'requalified_previously_completed_unique_routine_bytes':165 if passed else 0,'library_wide_complete':False,'human_review':'PENDING','model_candidate_accepted_for_callees':passed,'model_candidate_accepted_for_clients':False,'physical_ISA_fidelity':'EXPLICIT_TRUST_BOUNDARY_OF_CANDIDATE5_MODELS_AND_V6_SCALAR_EFFECTS','artifact_binding':boundary['artifact_binding'],'whole_image_checks':boundaries(stage,seal),'initial_cleanse_image_only':True,'readonly_source_with_no_writable_alias':True,'network':'none','source_unchanged':unchanged,'canonical_inputs_unchanged':canonical,'candidate_model_hashes':{n:seal['files'][n] for n in (seal['decoder'],seal['executor'])},'seal_sha256':args.sha256,'source_set_sha256':sha(run/'inputs.json'),'raw_log':str((run/'replay.log').relative_to(ROOT)),'model_identifier':None,'token_usage':None,'billing_cost':None,'unobserved_runtime_metadata_reason':'Not exposed by execution runtime','scope':seal['positive_claim']}
 dump(run/'receipt.json',receipt)
 print(json.dumps({'status':receipt['status'],'run_dir':str(run.relative_to(ROOT))}),flush=True)
 return 0 if passed else 1
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--seal',required=True);p.add_argument('--sha256',required=True);p.add_argument('--preflight',action='store_true')
 try:raise SystemExit(replay(p.parse_args()))
 except Exception as e:raise SystemExit('E3 callee replay rejected: '+str(e))
