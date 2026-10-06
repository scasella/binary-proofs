#!/usr/bin/env python3
from pathlib import Path
import json,hashlib,datetime
ROOT=Path(__file__).resolve().parents[5];LANE=Path(__file__).resolve().parent
h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
parentpath=LANE.parent/'qualification-seal-v1.json';parent=json.loads(parentpath.read_text())
pres=json.loads((ROOT/parent['preservation_receipt']).read_text())
files=dict(parent['files'])
extra=['development/approved-plan/abi-qualification/state-v4.ml','development/approved-plan/abi-qualification/extension-v2.ml','development/approved-plan/abi-qualification/expected-definitions-v4.json','development/approved-plan/cleanse/helpers/abi-v5/extension-v5.ml','development/approved-plan/cleanse/helpers/abi-v5/expected-definitions-v5.json','development/approved-plan/call-binding/near-indirect-v1/loaded-stub-v1/spec-v2.ml','development/approved-plan/abi-qualification/docs/intel-vol2a.txt','development/approved-plan/abi-qualification/docs/intel-vol2b-2016.pdf','development/approved-plan/abi-qualification/docs/intel-vol2b-2016.txt']
extra+=['development/approved-plan/assurance/'+f+'.ml' for f in ['correspondence','policy','slices','path']]
extra+=[str(p.relative_to(ROOT))for p in sorted(LANE.rglob('*')) if p.is_file()and'__pycache__'not in p.parts and p.name!='seal-v1.json']
for name in extra:
 p=ROOT/name
 if p.is_symlink():raise RuntimeError('Symlink in seal')
 if name in pres['files']:
  if h(p)!=pres['files'][name]:raise RuntimeError('Preserved input changed')
 else:files[name]=h(p)
for name,digest in files.items():
 if h(ROOT/name)!=digest:raise RuntimeError('Parent frozen input changed:'+name)
seal={k:v for k,v in parent.items()if k!='files'}
seal.update({'id':'BP-E3-NEAR-INDIRECT-EXECUTION-ABI-QUALIFICATION-V1','created_at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'scope':'CANDIDATE_NEAR_INDIRECT_EXECUTION_ABI_QUALIFICATION_ONLY','expected_theorem_count':53,'expected_model_definition_count':41,'expected_terms':str((LANE/'expected-audit-v2.json').relative_to(ROOT)),'driver':str((LANE/'fresh-input-v1.ml').relative_to(ROOT)),'files':files,'parent_candidate_seal':str(parentpath.relative_to(ROOT)),'parent_candidate_seal_sha256':h(parentpath),'trust_assumption_ids':parent['trust_assumption_ids']+['SCALAR_ABI_OMITTED_STATE_V4','SCALAR_ABI_GENERIC_V5','CALLER_ABI_GENERIC_V6_CANDIDATE','TRUSTED_FINAL_CALLER_BYTE_ACQUISITION_V1'],'callee_chains_requalified':False,'caller_composition_proved':False,'R1_pass':False})
(LANE/'seal-v1.json').write_text(json.dumps(seal,indent=2,sort_keys=True)+'\n')
print(h(LANE/'seal-v1.json'));print('supplemental files',len(files))
