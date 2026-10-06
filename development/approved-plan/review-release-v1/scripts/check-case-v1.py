#!/usr/bin/env python3
"""Later checking only: unchanged sealed C1/C2, parent-projected C3 adapter."""
import argparse, datetime, hashlib, json, os, subprocess, sys, time
from pathlib import Path
sys.dont_write_bytecode=True
R='development/approved-plan/review-release-v1'
ROOT=Path(__file__).resolve().parents[4]

def sha(path):
 h=hashlib.sha256()
 with path.open('rb') as stream:
  for block in iter(lambda:stream.read(1024*1024),b''):h.update(block)
 return h.hexdigest()
def write(path,value):
 path.parent.mkdir(parents=True,exist_ok=True)
 with path.open('x') as out:json.dump(value,out,indent=2,sort_keys=True);out.write('\n')
def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('case',choices=['C1','C2','C3']);p.add_argument('--output',type=Path,required=True)
 p.add_argument('--inputs-sha256',required=True);a=p.parse_args()
 manifest=ROOT/(R+'/inputs/release-inputs-v1.json')
 if sha(manifest)!=a.inputs_sha256:raise ValueError('Externally pinned release input manifest changed')
 inputs=json.loads(manifest.read_text())
 for name,digest in inputs['files'].items():
  rel=Path(name)
  if rel.is_absolute() or '..' in rel.parts or (ROOT/rel).is_symlink() or sha(ROOT/rel)!=digest:raise ValueError('Changed delivered input: '+name)
 selected=inputs['cases'][a.case];parent=ROOT/selected['seal'];seal_sha=selected['seal_sha256']
 seal=json.loads(parent.read_text());out=a.output.resolve();out.mkdir(parents=True,exist_ok=False)
 started=datetime.datetime.now(datetime.timezone.utc);timer=time.monotonic();rows=[]
 context=dict(schema='c3-later-checking-context-v1',checking_only=True,start_utc=started.isoformat(),deadline_utc=(started+datetime.timedelta(seconds=5400)).isoformat(),session_limit_seconds=5400,per_invocation_seconds=1800,parent_accepted_seal_sha256=seal_sha,case=a.case)
 seal_path=parent
 if a.case=='C3':
  rel=R+'/consumer/checking-contexts/'+started.strftime('%Y%m%dT%H%M%S')+'-'+os.urandom(4).hex()+'.json';write(ROOT/rel,context)
  seal.update(checking_only=True,release_checking_context=rel,release_checking_context_sha256=sha(ROOT/rel),parent_accepted_seal=selected['seal'],parent_accepted_seal_sha256=seal_sha,host_driver=R+'/replay/c3-fresh-check-v1.py',root_gate=R+'/replay/c3-root-check-v1.py',driver_sha256=sha(ROOT/(R+'/replay/c3-fresh-check-v1.py')))
  for name in [selected['seal'],R+'/STAGE-v1.json',R+'/replay/checking-context-v1.py',seal['host_driver'],seal['root_gate'],rel]:seal['additional_stage_inputs'][name]=sha(ROOT/name)
  seal_path=ROOT/(rel.replace('.json','-seal.json'));write(seal_path,seal);seal_sha=sha(seal_path)
 write(out/'checking-session-v1.json',dict(context,source_root=str(ROOT),original_accepted_seal=selected['seal'],original_accepted_seal_sha256=selected['seal_sha256'],operational_seal=str(seal_path.relative_to(ROOT)),operational_seal_sha256=seal_sha,proof_construction=False,model_tokens=None,model_tokens_reason='Not exposed',cost=None,cost_reason='Not exposed'))
 def run(name,script,argv,cap):
  remaining=5400-(time.monotonic()-timer)
  if remaining<=0:raise TimeoutError('Checking-only case session limit exhausted')
  cmd=[sys.executable,'-B',str(ROOT/script),*map(str,argv)];begin=datetime.datetime.now(datetime.timezone.utc);t=time.monotonic()
  write(out/(name+'-argv.json'),cmd)
  error=None;code=None
  try:
   with (out/(name+'-process.log')).open('xb') as log:code=subprocess.run(cmd,cwd=ROOT,stdout=log,stderr=subprocess.STDOUT,timeout=min(cap,remaining)).returncode
  except Exception as e:error=repr(e)
  row=dict(phase=name,started_utc=begin.isoformat(),ended_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),elapsed_seconds=time.monotonic()-t,elapsed_scope='Inclusive child execution and nested checks; do not add nested durations again',exit_code=code,error=error,argv_file=name+'-argv.json',raw_log=name+'-process.log',proof_construction=False)
  rows.append(row)
  with (out/'later-checking-ledger-v1.jsonl').open('a') as f:f.write(json.dumps(row,sort_keys=True)+'\n')
  if code!=0:raise RuntimeError('Recorded checking failure in '+name+': '+str(code)+' '+str(error))
 base=['--source-root',ROOT,'--seal',seal_path,'--seal-sha256',seal_sha]
 try:
  run('positive',seal['host_driver'],base+['--output',out/'positive','--timeout-seconds','1800'],1830)
  run('positive-gate',seal['root_gate'],base+['--positive-run',out/'positive','--output',out/'positive-gate.json'],300)
  run('integrity-controls',selected['controls'],base+['--positive-run',out/'positive','--output',out/'controls'],600)
  run('missing-binding-probe',selected['probe'],base+['--positive-run',out/'positive','--output',out/'binding-probe'],1860)
  run('complete-gate',seal['root_gate'],base+['--positive-run',out/'positive','--controls',out/'controls','--binding-probe',out/'binding-probe','--output',out/'complete-gate.json'],300)
  gate=json.loads((out/'complete-gate.json').read_text())
  if gate['status']!='FRESH_ACCEPTED_WITH_FIVE_INTEGRITY_CONTROLS_AND_FRESH_BINDING_PROBE' or gate['full_'+a.case+'_acceptance'] is not True:raise ValueError('Incomplete actual gate result')
  result=dict(status='CHECKING_ONLY_CONSUMER_FRESH_ACCEPTED',case=a.case,complete_gate_sha256=sha(out/'complete-gate.json'),started_utc=started.isoformat(),completed_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),elapsed_seconds=time.monotonic()-timer,rows=rows,original_accepted_seal_sha256=selected['seal_sha256'],operational_seal_sha256=seal_sha,proof_construction=False,old_results_used_to_discharge_targets=False,human_review='PENDING')
  write(out/'result-v1.json',result);print(json.dumps({k:v for k,v in result.items() if k!='rows'},indent=2));return 0
 except Exception as e:
  write(out/'failure-v1.json',dict(status='CHECKING_ONLY_CONSUMER_NOT_ACCEPTED',case=a.case,error=repr(e),rows=rows,elapsed_seconds=time.monotonic()-timer,human_review='PENDING'));raise
if __name__=='__main__':sys.exit(main())
