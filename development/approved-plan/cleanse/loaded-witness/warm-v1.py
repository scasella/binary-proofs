#!/usr/bin/env python3
from pathlib import Path
import datetime,json,os,subprocess,sys,time,uuid
ROOT=Path(__file__).resolve().parents[4]
LANE=Path(__file__).resolve().parent
stamp=datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ')
run=ROOT/'results/development'/('cleanse-loaded-witness-warm-'+stamp+'-'+uuid.uuid4().hex[:8])
run.mkdir();output=run/'output';output.mkdir();fifo=run/'input.fifo';os.mkfifo(fifo)
image=json.loads((ROOT/'locks/baseline.json').read_text())['checker_image_id']
load=['third_party/s2n-bignum/x86/proofs/base.ml', 'proofs/qualification/openssl_bytes.ml', 'development/approved-plan/assurance/correspondence.ml', 'development/approved-plan/assurance/policy.ml', 'development/approved-plan/abi-qualification/state-v4.ml', 'development/approved-plan/contract/crypto-pre-v2.ml', 'development/approved-plan/loaded-witness/definitions-v3.ml', 'development/approved-plan/loaded-witness/reference-overlay.ml', 'development/approved-plan/loaded-witness/statements-v3.ml', 'development/approved-plan/loaded-witness/helpers-attempt4.ml', 'development/approved-plan/loaded-witness/witness-proofs-attempt3.ml', 'development/approved-plan/loaded-witness/full-binding/definitions-v2.ml', 'development/approved-plan/loaded-witness/full-binding/statements-v2.ml', 'development/approved-plan/loaded-witness/full-binding/proofs-attempt3.ml', 'development/approved-plan/cleanse/spec-v2.ml', 'development/approved-plan/cleanse/loaded-witness/definitions-v1.ml', 'development/approved-plan/cleanse/loaded-witness/statements-v1.ml']
bootstrap='use_file_raise_failure := true;;\nlet clw_initial_axioms=axioms();;\nlet clw_guard f=try f() with e->prerr_endline(Printexc.to_string e);exit 1;;\n'
for p in load: bootstrap+='clw_guard(fun()->loadt '+json.dumps('/work/'+p)+');;\n'
bootstrap+='print_endline "CLEANSE_LOADED_WITNESS_BOOTSTRAP_COMPLETE";;\n'
(run/'bootstrap.ml').write_text(bootstrap)
command=['docker','run','-i','--rm','--pull','never','--network','none','--memory','2g','--memory-swap','2g','--platform','linux/arm64','-e','HOLLIGHT_DIR=/work/third_party/hol-light','-v',str(ROOT)+':/work:ro','-v',str(output)+':/output:rw','-v',str(ROOT/'proofs/model-extension/decode.ml')+':/work/third_party/s2n-bignum/x86/proofs/decode.ml:ro','-w','/work/third_party/s2n-bignum',image,'/work/third_party/hol-light/ocaml-hol','-init','/work/third_party/hol-light/hol.ml','-safe-string','-I','/work/third_party/hol-light']
(run/'launch.json').write_text(json.dumps({'command':command,'load_order':load,'model':'original pinned+REP_RET','human_review':'PENDING','phase':'warm construction only'},indent=2)+'\n')
fd=os.open(fifo,os.O_RDWR)
start=time.monotonic()
with (run/'replay.log').open('wb') as log:
 p=subprocess.Popen(command,stdin=fd,stdout=log,stderr=subprocess.STDOUT)
 print(run,flush=True);print('process '+str(p.pid),flush=True)
 os.write(fd,bootstrap.encode())
 result=p.wait()
(run/'process.json').write_text(json.dumps({'exit_code':result,'elapsed_seconds':time.monotonic()-start,'fresh_replay':False,'full_O1_pass':False,'human_review':'PENDING'},indent=2)+'\n')
sys.exit(result)
