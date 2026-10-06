#!/usr/bin/env python3
"""Freeze exact case identity and literal obligations; does not construct any proof."""
import argparse,datetime,hashlib,json,os,re
from pathlib import Path
p=argparse.ArgumentParser()
p.add_argument('--typecheck-status',choices=['PASS','PENDING','FAIL'],required=True)
p.add_argument('--typecheck-record')
a=p.parse_args()
HERE=Path(__file__).resolve().parent
BASE=HERE.parents[1]
ROOT=BASE.parents[2]
sha=lambda path:hashlib.sha256(path.read_bytes()).hexdigest()
rel=lambda path:str(path.relative_to(ROOT))
stage=json.loads((BASE/'STAGE-v1.json').read_text())
now=datetime.datetime.now(datetime.timezone.utc)
prep_deadline=datetime.datetime.fromisoformat(stage['preparation_deadline_utc'])
assert now<=prep_deadline,'PREPARATION_DEADLINE_EXCEEDED_NO_AUTOMATIC_EXTENSION'
out=HERE/'freeze-v1.json';assert not out.exists()
expected_path=HERE/'expected-terms-v1.json'
expected=json.loads(expected_path.read_text())
inventory_path=BASE/'c3/artifact/inventory-v1.json'
inv=json.loads(inventory_path.read_text())
choice=BASE/'c3-selection/choice-freeze-v1.json'
chosen=json.loads(choice.read_text())
for name,digest in chosen['files'].items():
 assert sha(BASE/name)==digest,'CHOSEN_SOURCE_BEHAVIOR_DOMAIN_CHANGED:'+name
assert sha(BASE/'layer/freeze-v1.json')=='266f58bbb1883389a74b8ba0986db11d0b0d6f4c03c1d3961d2db04f51d94193'
layer=json.loads((BASE/'layer/freeze-v1.json').read_text())
layer_pins=dict(layer['candidate_inputs'])
layer_pins.update(layer['direct_dependency_pins'])
for name,digest in layer_pins.items():
 assert sha(ROOT/name)==digest,'FROZEN_LAYER_SOURCE_PIN_CHANGED:'+name
assert sha(BASE/'c3/artifact/compiled-v1/c3.so')==inv['artifact_sha256']
canonical=HERE/'definitions-v2.ml'
witness=HERE/'witness-definitions-v1.ml'
equations={}
for path in [canonical,witness]:
 for name,literal in re.findall(r'let\s+(\w+)\s*=\s*new_definition\s*`(.*?)`;;',path.read_text(),re.S):
  assert name not in equations
  equations[name]=literal
files={rel(x):sha(x) for parent in [BASE/'c3/artifact',HERE] for x in parent.rglob('*') if x.is_file() and x!=out}
for path in [BASE/'STAGE-v1.json',BASE/'layer/freeze-v1.json',choice,BASE/'c3-selection/release-v1.json',BASE/'c3-selection/selection-account-v1.json',BASE/'c3/replay/acquisition-discovery-v1.json']:
 files[rel(path)]=sha(path)
typecheck=None
if a.typecheck_record:
 path=Path(a.typecheck_record).resolve();assert path.is_file()
 typecheck={'path':rel(path),'sha256':sha(path)}
 files[rel(path)]=sha(path)
artifact_freeze=json.loads((BASE/'c3/artifact/freeze-v1.json').read_text())
f={
 'schema':'heldout-c3-final-artifact-domain-literal-freeze-v1',
 'experiment':'BP-20261005-HELD-OUT-TRANSFER-V1',
 'selected_case_count':1,'selector':'/root/heldout_selector',
 'created_utc':now.isoformat(),'preparation_deadline_utc':prep_deadline.isoformat(),
 'construction_start_utc':now.isoformat(),
 'construction_deadline_utc':(now+datetime.timedelta(seconds=10800)).isoformat(),
 'construction_cap_seconds':10800,'main_proof_search_started_at_freeze':False,
 'clock_rule':'Immutable final artifact/domain/literal freeze starts fixed 10800 seconds; no automatic extension; any B continuation uses remaining same budget.',
 'candidate_layer_freeze':{'path':rel(BASE/'layer/freeze-v1.json'),'sha256':sha(BASE/'layer/freeze-v1.json')},
 'layer_source_pin_integrity':{'status':'PASS','source_count':len(layer_pins),'scope':'SHA256-only identity verification; proof source contents not inspected by selector'},
 'release':{'path':rel(BASE/'c3-selection/release-v1.json'),'sha256':sha(BASE/'c3-selection/release-v1.json')},
 'exact_choice':{'path':rel(choice),'sha256':sha(choice)},
 'source_kind':'assembler-authored System V AMD64 machine caller; GCC assembles/links; no C refinement or transfer to compiler-generated C output claim',
 'canonical_definitions':rel(canonical),'canonical_witness_definitions':rel(witness),
 'statements':rel(HERE/'statements-v1.ml'),'witness_statements':rel(HERE/'witness-statements-v1.ml'),
 'formal_targets':expected['end_theorem_bindings'],
 'witness_targets':expected['witness_theorem_bindings'],
 'formal_target_count':len(expected['end_theorem_bindings']),
 'witness_target_count':len(expected['witness_theorem_bindings']),
 'literal_targets':expected['expected_terms'],
 'witness_purpose':'ADMISSIBLE_ENTRY_ONLY_NOT_EXECUTION',
 'representative_families':['null pointers zero length with unreadable address0','disjoint length1','unaligned disjoint length17','identical overlapping length16','forward partial overlap length17','reverse partial overlap length17','page-crossing length15','low/high canonical-edge length1'],
 'expected_terms':{'path':rel(expected_path),'sha256':sha(expected_path)},
 'definition_equations':equations,'definition_count':len(equations),
 'artifact_inventory':{'path':rel(inventory_path),'sha256':sha(inventory_path)},
 'final_elf':{'path':rel(BASE/'c3/artifact/compiled-v1/c3.so'),'sha256':inv['artifact_sha256'],'size':inv['artifact_size']},
 'caller_source':{'path':rel(BASE/'c3/artifact/c3.S'),'sha256':inv['source_sha256']},
 'load_bias':inv['load_bias'],'caller_entry':inv['caller']['loaded_address'],'caller_size':inv['caller']['size'],
 'supplier_artifacts_sha256':artifact_freeze['supplier_artifacts_sha256'],
 'build_image':'sha256:444f775e6378c2e5523f29ceb8bbb184442277ed1114e6d37d873a7f127dfc26',
 'checker_image':'sha256:a19fdc18f1f283ed8e2514229b77f33619df1ba0ea1ae578c97779f4b4eb3c3f',
 'checking_limits':{'cpus':1,'memory_bytes':3221225472,'network':'none','pull':'never','seconds_per_invocation':1800,'cold_dependencies_included':True},
 'domain':'Arbitrary inherited-admissible contents and lengths; p/q may overlap arbitrarily; no buffer premises at zero length; explicit stack/code/GOT/return protection and E5 normal entry.',
 'snapshots':'Initial M0 for first comparison; Mclear(a)=0 on p[0,n),M0 elsewhere for second; q retained only outside overlap with p.',
 'typecheck_status':a.typecheck_status,'typecheck_record':typecheck,
 'typecheck_pending_or_failure_is_not_acceptance':True,
 'proof_construction_by_selector':False,'files':files,
 'human_review':'PENDING','opacity':'Inspection-based source discipline, not formal capability isolation',
 'model':None,'tokens':None,'cost':None,
 'unavailable_reason':'runtime does not expose exact model, token or billing counters'
}
with out.open('x') as stream:
 stream.write(json.dumps(f,sort_keys=True,indent=2)+'\n');stream.flush();os.fsync(stream.fileno())
print(json.dumps({'freeze':rel(out),'freeze_sha256':sha(out),'created_utc':f['created_utc'],'construction_deadline_utc':f['construction_deadline_utc'],'typecheck_status':a.typecheck_status,'formal_target_count':f['formal_target_count'],'witness_target_count':f['witness_target_count']},sort_keys=True))
