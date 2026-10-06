#!/usr/bin/env python3
from pathlib import Path
import datetime,json,os,subprocess,sys,time,uuid
ROOT=Path(__file__).resolve().parents[5]
LANE=Path(__file__).resolve().parent
stamp=datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ')
run=ROOT/'results/development'/('near-indirect-execution-warm-'+stamp+'-'+uuid.uuid4().hex[:8])
run.mkdir();output=run/'output';output.mkdir();fifo=run/'input.fifo';os.mkfifo(fifo)
image=json.loads((ROOT/'locks/baseline.json').read_text())['checker_image_id']
load=['third_party/s2n-bignum/x86/proofs/base.ml','proofs/qualification/openssl_bytes.ml','development/approved-plan/call-binding/near-indirect-v1/loaded-stub-v1/spec-v2.ml','development/approved-plan/assurance/correspondence.ml','development/approved-plan/assurance/policy.ml','development/approved-plan/assurance/slices.ml','development/approved-plan/assurance/path.ml']
bootstrap='use_file_raise_failure := true;;\nlet r1_execution_initial_axioms=axioms();;\nlet r1_execution_guard f=try f() with e->prerr_endline(Printexc.to_string e);exit 1;;\n'
for p in load: bootstrap+='r1_execution_guard(fun()->loadt '+json.dumps('/work/'+p)+');;\n'
bootstrap+='print_endline "R1_EXECUTION_BOOTSTRAP_COMPLETE";;\n'
(run/'bootstrap.ml').write_text(bootstrap)
command=['docker','run','-i','--rm','--pull','never','--network','none','--memory','2g','--memory-swap','2g','--platform','linux/arm64','-e','HOLLIGHT_DIR=/work/third_party/hol-light','-v',str(ROOT)+':/work:ro','-v',str(output)+':/output:rw','-v',str(ROOT/'development/approved-plan/call-binding/near-indirect-v1/decode-attempt5.ml')+':/work/third_party/s2n-bignum/x86/proofs/decode.ml:ro','-v',str(ROOT/'development/approved-plan/call-binding/near-indirect-v1/x86-attempt5.ml')+':/work/third_party/s2n-bignum/x86/proofs/x86.ml:ro','-w','/work/third_party/s2n-bignum',image,'/work/third_party/hol-light/ocaml-hol','-init','/work/third_party/hol-light/hol.ml','-safe-string','-I','/work/third_party/hol-light']
(run/'launch.json').write_text(json.dumps({'command':command,'load_order':load,'model':'separate candidate5 near-indirect backend; E2 original untouched','human_review':'PENDING','phase':'warm construction only'},indent=2)+'\n')
fd=os.open(fifo,os.O_RDWR)
start=time.monotonic()
with (run/'replay.log').open('wb') as log:
 p=subprocess.Popen(command,stdin=fd,stdout=log,stderr=subprocess.STDOUT)
 print(run,flush=True);print('process '+str(p.pid),flush=True)
 os.write(fd,bootstrap.encode())
 result=p.wait()
(run/'process.json').write_text(json.dumps({'exit_code':result,'elapsed_seconds':time.monotonic()-start,'fresh_replay':False,'full_O1_pass':False,'human_review':'PENDING'},indent=2)+'\n')
sys.exit(result)
