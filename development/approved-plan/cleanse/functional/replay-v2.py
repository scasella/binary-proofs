#!/usr/bin/env python3
"""Fresh closed modeled cleanse functional component reconstruction.
Fresh all-count actual callable modeled functional/frame reconstruction. This checker cannot accept full O1 or O2.
"""
import argparse
import datetime as dt
import json
from pathlib import Path, PurePosixPath
import re
import shutil
import subprocess
import sys
import tarfile
import time
import uuid
ROOT = Path(__file__).resolve().parents[4]
sys.path.insert(0, str(ROOT/'scripts'))
from check import integrity, binding, sha

def dump(path,obj): path.write_text(json.dumps(obj,indent=2,sort_keys=True)+'\n')
def safe(name):
 p=PurePosixPath(name)
 if p.is_absolute() or '..' in p.parts or not name:raise RuntimeError('Unsafe input path: '+name)
 return name

def checked(root,name,digest):
 p=root/safe(name)
 if not p.is_file() or p.is_symlink() or sha(p)!=digest:raise RuntimeError('Frozen input mismatch: '+name)
 return p

def replay(args):
 sealpath=checked(ROOT,args.seal,args.sha256);seal=json.loads(sealpath.read_text())
 if seal['scope']!='MODELED_CLEANSE_FUNCTIONAL_COMPONENT_ONLY' or seal['full_O2_pass'] is not False:raise RuntimeError('This checker cannot accept full O2')
 integrity();bound=binding()
 prior=checked(ROOT,seal['preservation_receipt'],seal['preservation_receipt_sha256']);pres=json.loads(prior.read_text())
 archive=checked(ROOT,pres['archive_path'],pres['archive_sha256'])
 if set(seal['files']).intersection(pres['files']):raise RuntimeError('Successor would overwrite predecessor input')
 for name,digest in seal['files'].items():checked(ROOT,name,digest)
 stamp=dt.datetime.now(dt.timezone.utc).strftime('%Y%m%dT%H%M%SZ')
 runid='crypto-loop-cleanse-functional-closed-'+stamp+'-'+uuid.uuid4().hex[:8]
 out=ROOT/'results/development'/runid;stage=out/'source';checker_output=out/'checker-output'
 stage.mkdir(parents=True);checker_output.mkdir();seen=set()
 with tarfile.open(archive,'r:gz') as tar:
  for member in tar.getmembers():
   name=safe(member.name)
   if name in seen or name not in pres['files'] or not member.isfile():raise RuntimeError('Unapproved preserved member')
   seen.add(name);dest=stage/name;dest.parent.mkdir(parents=True,exist_ok=True)
   with tar.extractfile(member) as src,dest.open('xb') as dst:shutil.copyfileobj(src,dst)
   dest.chmod(member.mode&0o777);checked(stage,name,pres['files'][name])
 if seen!=set(pres['files']):raise RuntimeError('Incomplete predecessor archive')
 sources=dict(pres['files'])
 for name,digest in seal['files'].items():
  dest=stage/name;dest.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(ROOT/name,dest)
  checked(stage,name,digest);sources[name]=digest
 shutil.copy2(sealpath,stage/'component-seal.json');sources['component-seal.json']=args.sha256
 driver=(stage/seal['driver']).read_text();(out/'input.ml').write_text(driver)
 dump(out/'inputs.json',{'seal_sha256':args.sha256,'files':sources})
 dump(out/'started.json',{'run_id':runid,'seal_sha256':args.sha256,'readonly_source_with_no_writable_alias':True,'network':'none','full_O2_pass':False})
 print(json.dumps({'run_dir':str(out.relative_to(ROOT)),'stage':'starting_fresh_HOL'}),flush=True)
 cmd=['docker','run','-i','--rm','--pull','never','--network','none','--platform','linux/arm64','-e','HOLLIGHT_DIR=/work/third_party/hol-light','-v',str(stage)+':/work:ro','-v',str(checker_output)+':/output:rw','-v',str(stage/'proofs/model-extension/decode.ml')+':/work/third_party/s2n-bignum/x86/proofs/decode.ml:ro','-w','/work/third_party/s2n-bignum',seal['checker_image_id'],'/work/third_party/hol-light/ocaml-hol','-init','/work/third_party/hol-light/hol.ml','-safe-string','-I','/work/third_party/hol-light']
 start=time.monotonic()
 with (out/'input.ml').open() as inp,(out/'replay.log').open('w') as log:proc=subprocess.run(cmd,stdin=inp,stdout=log,stderr=subprocess.STDOUT)
 elapsed=time.monotonic()-start
 auditpath=checker_output/'functional-audit.json';audit=json.loads(auditpath.read_text()) if auditpath.exists() else None
 unchanged=all((stage/n).is_file() and sha(stage/n)==h for n,h in sources.items())
 canonical=True
 try:
  integrity();checked(ROOT,args.seal,args.sha256)
  for n,h in seal['files'].items():checked(ROOT,n,h)
 except Exception:canonical=False
 log=re.sub(r'\x1b\[[0-?]*[ -/]*[@-~]','',(out/'replay.log').read_text(errors='replace'))
 records=[] if audit is None else audit['theorems'];names=[t['name'] for t in records]
 passed=(proc.returncode==0 and unchanged and canonical and audit is not None and audit['full_O2_pass'] is False and audit['status']=='PASS_MODELED_CLEANSE_FUNCTIONAL_COMPONENT' and len(names)==len(seal['expected_theorems']) and set(names)==set(seal['expected_theorems']) and all(t['hypothesis_count']==0 and t['new_axioms']==0 and t['conclusion_matches_expected'] is True for t in records) and len(audit['expanded_definitions'])==seal['expected_definition_count'] and all(d['hypothesis_count']==0 for d in audit['expanded_definitions']) and 'CLEANSE_FRESH_FUNCTIONAL_ACCEPTED' in log and re.search(r'(?m)^\s*(?:#\s*)?(?:Error|Exception):',log) is None)
 receipt={'status':'PASS_FRESH_MODELED_CLEANSE_FUNCTIONAL_COMPONENT' if passed else 'FAIL_FRESH_MODELED_CLEANSE_FUNCTIONAL_COMPONENT','run_id':runid,'process_exit':proc.returncode,'elapsed_checking_seconds':elapsed,'construction_interval':seal.get('construction_interval'),'source_unchanged':unchanged,'canonical_inputs_unchanged':canonical,'readonly_source_with_no_writable_alias':True,'network':'none','seal_sha256':args.sha256,'source_set_sha256':sha(out/'inputs.json'),'artifact_binding':bound,'kernel_audit':audit,'raw_log':str((out/'replay.log').relative_to(ROOT)),'full_O2_pass':False,'full_O1_pass':False,'scope':'Whole actual callable OPENSSL_cleanse modeled functionality and destination-only memory frame, exact public finite count under unchanged E2 Pre; full access/ABI/O1/O2 package acceptance separate','model_identifier':None,'model_identifier_null_reason':'Not exposed by execution runtime','token_usage':None,'token_usage_null_reason':'Not exposed by execution runtime','billing_cost':None,'billing_cost_null_reason':'Not exposed by execution runtime'}
 dump(out/'receipt.json',receipt);print(json.dumps({'status':receipt['status'],'run_dir':str(out.relative_to(ROOT))}),flush=True)
 return 0 if passed else 1
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--seal',required=True);p.add_argument('--sha256',required=True);args=p.parse_args()
 try:raise SystemExit(replay(args))
 except Exception as e:print(str(e),file=sys.stderr);raise SystemExit(1)
