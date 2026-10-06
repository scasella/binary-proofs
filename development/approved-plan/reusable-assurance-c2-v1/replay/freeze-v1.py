#!/usr/bin/env python3
"""Seal a concrete C2 source graph against its exact versioned input anchors.

The public end-statements and witness definitions/statements were frozen before
construction. Additive proof-phase definition anchors were created later and
serve acceptance identity checks, not construction preregistration.

This is replay input sealing, not a checking result. No acceptance is asserted.
Supplier materialization/auditing and the E5 environment policy are unchanged.
"""
import argparse,datetime,json,re,types
from pathlib import Path
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[3]
NEW='development/approved-plan/reusable-assurance-c2-v1'
C1='development/approved-plan/reusable-assurance-c1-successor-v1'
C1_SEAL=C1+'/replay/c1-successor-final-v3-seal.json'
C1_SEAL_SHA='556fe357859921992293b7eedd7fc1338bf737502069502b50cdfffe5e114a0c'
def module(path,name):
    obj=types.ModuleType(name);obj.__file__=str(path)
    exec(compile(path.read_bytes(),str(path),'exec'),obj.__dict__);return obj
def write(path,text):
    with path.open('x') as out:out.write(text)
def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--source-root',type=Path,default=ROOT)
    p.add_argument('--loader',required=True)
    p.add_argument('--main-proof',required=True)
    p.add_argument('--theorem-map',required=True)
    p.add_argument('--application-proof',required=True)
    p.add_argument('--application-theorem',default='C2_CRYPTO_INTERFACE_APPLICATION')
    p.add_argument('--name',required=True)
    a=p.parse_args();root=a.source_root.resolve()
    if not re.fullmatch('[A-Za-z0-9_-]+',a.name):raise ValueError('Unsafe freeze name')
    check=module(HERE/'source-check-v1.py','c2_freeze_source_policy')
    predecessor=json.loads(check.checked(root,C1_SEAL,C1_SEAL_SHA).read_text())
    anchors=check.anchor_data(root);check.anchors(root)
    if not a.main_proof.startswith(NEW+'/proofs/') or not a.main_proof.endswith('.ml'):
        raise ValueError('Selected main proof must be concrete C2 source')
    graph=check.load_graph(root,a.loader)
    if a.application_proof not in graph or not a.application_proof.startswith(NEW+'/proofs/'):
        raise ValueError('Application proof must be a concrete C2 closed-graph node')
    if not re.fullmatch('[A-Z][A-Za-z_0-9]*',a.application_theorem):
        raise ValueError('Unsafe application theorem name')
    mapping=json.loads(check.checked(root,a.theorem_map).read_text())
    registry=check.registry(root,mapping,graph)
    outputs=[root/NEW/'replay'/(a.name+s) for s in ['-expected.json','-audit.ml','-seal.json']]
    if any(x.exists() for x in outputs):raise ValueError('Refusing to overwrite frozen C2 replay candidate')
    generator=module(HERE/'generate-audit-v1.py','c2_freeze_actual_auditor')
    expected_path,audit_path,seal_path=outputs
    write(expected_path,json.dumps(registry,indent=2,sort_keys=True)+'\n')
    write(audit_path,generator.generate(registry))
    inv=json.loads(check.checked(root,NEW+'/inventory/inventory-v1.json').read_text())
    extra={**anchors['files'],**anchors['generic_inputs']}
    extra.update({name:r['sha256'] for name,r in graph.items()})
    witness=anchors['witness_registry'];extra.update(witness['files'])
    machinery=['anchors-v1.json','source-check-v1.py','freeze-v1.py','fresh-replay-v1.py','check-root-v1.py',
       'targeted-preflight-controls-v1.py','missing-interface-probe-v1.py','ambient-snapshot-v1.ml',
       'generate-audit-v1.py','crosscheck-c2-image-v1.py','operational-template-pins-v1.json']
    for name in [C1_SEAL,NEW+'/STAGE-v1.json',a.theorem_map,
       str(expected_path.relative_to(root)),str(audit_path.relative_to(root))]+[NEW+'/replay/'+x for x in machinery]:
        extra[name]=check.sha(check.checked(root,name))
    for name,digest in extra.items():check.checked(root,name,digest)
    seal=dict(schema='c2-fresh-closed-replay-seal-v1',created_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
       experiment='BP-20261004-C2-V1',status='FROZEN_REPLAY_INPUTS_NOT_PROOF',human_review='PENDING',
       predecessor_accepted_seal=C1_SEAL,predecessor_accepted_seal_sha256=C1_SEAL_SHA,
       host_inputs=predecessor['host_inputs'],supplier=predecessor['supplier'],
       baseline_driver=predecessor['baseline_driver'],baseline_driver_sha256=predecessor['baseline_driver_sha256'],
       checker_image_id=predecessor['checker_image_id'],gnu_image_id=predecessor['gnu_image_id'],resources=predecessor['resources'],
       loader=a.loader,selected_main_proof_source=a.main_proof,theorem_map=a.theorem_map,graph=graph,formal_graph_node_count=len(graph),
       expected_registry=str(expected_path.relative_to(root)),audit=str(audit_path.relative_to(root)),
       original_target_count=registry['original_target_count'],witness_target_count=registry['witness_target_count'],
       nonvacuity_case_count=registry['nonvacuity_case_count'],all_new_definition_count=len(registry['definitions']),
       host_driver=NEW+'/replay/fresh-replay-v1.py',root_gate=NEW+'/replay/check-root-v1.py',
       source_check=NEW+'/replay/source-check-v1.py',artifact_crosscheck=NEW+'/replay/crosscheck-c2-image-v1.py',
       caller_executed_file_offset=inv['caller']['file_offset'],caller_first_byte=bytes.fromhex(inv['caller']['bytes_hex'])[0],
       application_proof_source=a.application_proof,application_theorem=a.application_theorem,
       additional_stage_inputs=extra,caller_acceptance=False,no_former_caller_proof_loader=True,
       pinned_generic_source_hashes_unchanged=True,
       caller_local_helper_addition_classification='See separately frozen reuse account; no inference from file naming',
       operational_adaptation='Concrete C2 artifact/graph/literals/counts/two supplier edges; existing checking obligations retained')
    seal['driver_sha256']=extra[seal['host_driver']]
    check.validate_development_graph(root,seal)
    write(seal_path,json.dumps(seal,indent=2,sort_keys=True)+'\n')
    print(json.dumps(dict(status=seal['status'],seal=str(seal_path),seal_sha256=check.sha(seal_path),
       original_targets=seal['original_target_count'],witness_targets=seal['witness_target_count'],definitions=seal['all_new_definition_count'],graph_nodes=len(graph),caller_acceptance=False),indent=2))
if __name__=='__main__':main()
