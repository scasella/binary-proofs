#!/usr/bin/env python3
"""Independent root evidence gate. This program never starts Docker or HOL.

The enclosing fresh process remains trusted. JSON/logs alone are not proofs;
this gate checks them against pinned source, actual structured audits, the source
tree, container inspection, and independently recomputed binding policies.
"""
import argparse, hashlib, json, math, os, re, subprocess, sys, types
from datetime import datetime, timezone
from pathlib import Path
sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
OWN = 'development/approved-plan/reusable-assurance-v1'
SUCCESSOR = 'development/approved-plan/reusable-assurance-c1-successor-v1'
POSITIVE = 'FRESH_C1_FULL7_WITNESS21_ALL_DEFINITIONS_AND_SUPPLIER_AUDITS_COMPLETE_PENDING_ROOT_GATES'
STANDARD = ['INFINITY_AX', 'SELECT_AX', 'ETA_AX']
GNU_IMAGE = 'sha256:444f775e6378c2e5523f29ceb8bbb184442277ed1114e6d37d873a7f127dfc26'
HOL_IMAGE = 'sha256:a19fdc18f1f283ed8e2514229b77f33619df1ba0ea1ae578c97779f4b4eb3c3f'

def require(condition, message):
    if not condition: raise ValueError(message)
def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()
def read(path):
    require(not path.is_symlink() and path.is_file(), 'Missing/nonregular evidence: '+str(path))
    return json.loads(path.read_text())
def module(path, name):
    obj = types.ModuleType(name); obj.__file__ = str(path)
    exec(compile(path.read_bytes(), str(path), 'exec'), obj.__dict__)
    return obj
def finite(value):
    return type(value) in (int,float) and math.isfinite(value) and value >= 0

def gate(args):
    root, run = args.source_root.resolve(), args.positive_run.resolve()
    require(re.fullmatch('[0-9a-f]{64}', args.seal_sha256) is not None, 'External seal SHA must be lowercase SHA256')
    seal_path = args.seal.resolve()
    seal_rel = str(seal_path.relative_to(root))
    require(sha(seal_path) == args.seal_sha256, 'Externally pinned seal changed')
    seal = read(seal_path)
    require(seal['schema'] == 'c1-fresh-closed-replay-seal-v1', 'Wrong replay scope')
    require(seal['gnu_image_id']==GNU_IMAGE and seal['checker_image_id']==HOL_IMAGE, 'GNU-only pinned image amendment changed HOL image')
    # Verify before importing any replay policy or source checker.
    host = seal['host_inputs']; extra = seal['additional_stage_inputs']
    for name,digest in {**host,**extra}.items():
        rel = Path(name)
        require(not rel.is_absolute() and '..' not in rel.parts, 'Unsafe sealed input')
        path = root/rel
        require(not any(root.joinpath(*rel.parts[:i]).is_symlink() for i in range(len(rel.parts)+1)), 'Symlink sealed input')
        require(path.is_file() and sha(path)==digest, 'Changed host input: '+name)
    checker = SUCCESSOR+'/replay/source-check-v1.py'
    self_path = SUCCESSOR+'/replay/check-root-v3.py'
    require(seal['root_gate'] == self_path and self_path in extra and sha(Path(__file__)) == extra[self_path], 'Root gate is not the exact sealed source')
    require(checker in host or checker in extra, 'Source checker is not sealed')
    check = module(root/checker, 'c1_root_source_policy')
    supplier = seal['supplier']
    materializer = module(check.checked(root,supplier['materializer'],supplier['materializer_sha256']), 'c1_root_materializer')
    index = materializer.inputs(root)
    require(index['source_files'] and len(index['source_files'])==4534 and supplier['source_count']==4534, 'Supplier source union mismatch')
    expected = dict(index['source_files']); expected[index['seal']]=index['seal_sha256']
    for name,digest in extra.items():
        require(name not in expected or expected[name]==digest, 'Conflicting supplier/caller input')
        expected[name]=digest
    receipt = read(run/'receipt.json')
    require(receipt['status']==POSITIVE and receipt['proof_started'] is True and receipt['exit_code']==0
            and receipt['timeout'] is False and receipt['supplier_marker'] is True
            and receipt['saved_passing_proof_used'] is False, 'No genuine completed fresh positive')
    require(receipt['seal_sha256']==args.seal_sha256 and finite(receipt['elapsed_seconds'])
            and receipt['elapsed_seconds']<=1800 and receipt['readonly_source_closed'] is True, 'Fresh deadline/source closure failed')
    require((receipt['original_target_count'],receipt['witness_target_count'],receipt['nonvacuity_case_count'],receipt['definition_count'])==(7,21,7,46), 'Incomplete caller scope')
    require(receipt['fresh_GNU_C1_crosscheck'] is True, 'Fresh GNU absent')
    bound = [('inputs.json','source_set_sha256'),('runtime/c1-live-audit-v1.json','live_audit_sha256'),
             ('c1-proof.log','c1_log_sha256'),('root-only-supplier/bootstrap.log','supplier_log_sha256')]
    initial_evidence = {name:sha(run/name) for name,_ in bound}
    for name,key in bound: require(initial_evidence[name]==receipt[key], 'Changed runtime evidence: '+name)
    inp = read(run/'inputs.json')
    require(inp['files']==expected and inp['seal_sha256']==args.seal_sha256 and inp['closed_load_graph']==seal['graph'], 'Exact staged input-set mismatch')
    stage, runtime = run/'source', run/'runtime'
    foundation = module(check.checked(root,seal['baseline_driver'],seal['baseline_driver_sha256']), 'c1_root_inherited_permissions')
    def guards():
        foundation.guard_stage_permissions(stage)
        require({str(p.relative_to(stage)) for p in stage.rglob('*') if p.is_file()}==set(expected), 'Added/missing staged source')
        for name,digest in expected.items(): check.checked(stage,name,digest)
        for name,digest in {**host,**extra}.items(): check.checked(root,name,digest)
        materializer.inputs(root)
        check.checked(root,seal_rel,args.seal_sha256)
        check.anchors(stage)
        require(check.load_graph(stage,seal['loader'])==seal['graph'] and len(seal['graph'])==69, 'Changed closed caller graph')
        check.validate_successor_graph(stage,seal)
    guards()
    mapping = read(stage/seal['theorem_map'])
    registry = check.registry(stage,mapping,seal['graph'])
    require(registry==read(stage/seal['expected_registry']), 'Changed raw frozen object/definition registry')
    generator = module(stage/(OWN+'/replay/generate-audit-v1.py'), 'c1_root_audit_generator')
    require((stage/seal['audit']).read_text()==generator.generate(registry), 'Changed actual-object auditor')
    live = read(runtime/'c1-live-audit-v1.json')
    require(live['schema']=='c1-fresh-live-audit-v1' and (live['theorem_count'],live['original_target_count'],live['witness_target_count'],live['nonvacuity_case_count'],live['definition_count'])==(28,7,21,7,46), 'Live scope mismatch')
    require(live['initial_axiom_count']==3 and live['final_axiom_count']==3 and live['axioms_unchanged'] is True and live['standard_axioms']==STANDARD, 'Foundation boundary changed')
    rows = {row['name']:(kind,row) for kind in ['object','definition'] for row in registry['objects' if kind=='object' else 'definitions']}
    actual = live['rows']
    require(len(actual)==74 and len({r['name'] for r in actual})==74 and {r['name'] for r in actual}==set(rows), 'Missing/duplicate live objects')
    for row in actual:
        kind,want=rows[row['name']]
        require(row['kind']==kind and all(type(row[x]) is int and row[x]==0 for x in ['hypothesis_count','free_variable_count','new_axioms']), 'Open/unsound live object: '+row['name'])
        require(row['literal_match'] is True and row['expanded_match'] is True and row['comparison']==want['comparison'] and row['expected_literal_sha256']==want['expected_literal_sha256'] and bool(row['conclusion']) and bool(row['expanded_conclusion']), 'Raw/expanded object mismatch: '+row['name'])
    resources = dict(deadline_seconds=1800,cpu_count=1,memory_bytes=3*1024**3,swap_limit_bytes=3*1024**3)
    require(seal['resources']==resources, 'Frozen resources changed')
    invocation=read(run/'invocation.json')
    require(invocation['kind']=='FRESH_CLOSED_C1_PROOF_ATTEMPT' and invocation['run_id']==receipt['run_id'] and invocation['seal_sha256']==args.seal_sha256 and invocation['resources']==resources and 0<invocation['actual_deadline_seconds']<=1800 and invocation['network']=='none' and invocation['host_stage_read_only'] is True and invocation['former_caller_proof_loader'] is False, 'Wrong actual invocation')
    inspection=read(run/'container-inspect.json'); require(len(inspection)==1,'Ambiguous container inspection')
    obj=inspection[0]; cfg=obj['HostConfig']; state=obj['State']
    require(obj['Id']==(run/'container.cid').read_text().strip() and obj['Image']==seal['checker_image_id'], 'Actual container/image mismatch')
    require(state['ExitCode']==0 and state['OOMKilled'] is False and state['Running'] is False and state['StartedAt']!=state['FinishedAt'], 'Container not successfully completed')
    require(cfg['Memory']==3*1024**3 and cfg['MemorySwap']==3*1024**3 and cfg['NanoCpus']==10**9 and cfg['NetworkMode']=='none', 'Actual resource/network mismatch')
    mounts={m['Destination']:m for m in obj['Mounts']}
    wanted={'/work':stage,'/output':runtime,'/reuse':stage/OWN,'/client-public':stage/check.PUBLIC,
            '/work/third_party/s2n-bignum/x86/proofs/decode.ml':stage/supplier['decoder'],
            '/work/third_party/s2n-bignum/x86/proofs/x86.ml':stage/supplier['executor']}
    require(len(obj['Mounts'])==len(wanted) and set(mounts)==set(wanted),'Unexpected actual mount aliases')
    for dest,path in wanted.items():
        require(Path(mounts[dest]['Source']).resolve()==path.resolve() and mounts[dest]['Type']=='bind' and mounts[dest]['RW'] is (dest=='/output'), 'Actual mount/permission mismatch: '+dest)
    argv=read(run/'checker-argv.json')
    require(argv[argv.index('--platform')+1]=='linux/arm64', 'HOL platform changed')
    require(argv[0:3]==['docker','run','-i'] and '--pull' in argv and argv[argv.index('--pull')+1]=='never' and seal['checker_image_id'] in argv and '/work/third_party/hol-light/ocaml-hol' in argv, 'Wrong actual checker argv')
    for filename in ['c1-proof.log','root-only-supplier/bootstrap.log']:
        require(re.search(r'^(?:# )?\s*(?:Exception:|Error:|Parse error:|Error in included file\b|Fatal\s*error\b)',(run/filename).read_text(errors='replace'),re.M|re.I) is None,'Raw prover error: '+filename)
    for key in ['supplier_cpu_seconds','caller_cpu_seconds','supplier_wall_seconds','caller_wall_seconds']:
        require(finite(receipt[key]), 'Invalid actual phase measurement')
    auditor=module(check.checked(root,supplier['auditor'],supplier['auditor_sha256']), 'c1_root_supplier_auditor')
    supplier_audit=auditor.audit(stage,runtime)
    require((supplier_audit['unique_theorems'],supplier_audit['unique_definitions'],supplier_audit['equation_count'])==(325,119,218), 'Incomplete supplier audit')
    require(supplier_audit==read(run/'root-only-supplier/host-audit-stdout.json'),'Changed recorded supplier audit')
    require(not (run/'root-only-supplier/host-audit-stderr.log').read_text().strip(),'Supplier host audit stderr')
    cross=module(stage/seal['artifact_crosscheck'],'c1_root_fresh_byte_policy')
    image=cross.crosscheck(stage,runtime/'gnu')
    require(image==read(run/'c1-image-crosscheck.json') and image['fresh_GNU'] is True,'Fresh GNU/formal byte/linkage/image mismatch')
    gnu_inspect=read(run/'gnu-image-inspect.json')
    require(gnu_inspect['expected_image_id']==GNU_IMAGE and gnu_inspect['actual_image_id']==GNU_IMAGE
            and type(gnu_inspect['return_code']) is int and gnu_inspect['return_code']==0
            and gnu_inspect['platform']=='linux/amd64' and gnu_inspect['freshly_checked'] is True,
            'Fresh pinned GNU image inspection failed')
    gnu_argv=read(run/'gnu-argv.json')
    expected_gnu=['docker','run','--rm','--cidfile',str(run/'gnu-container.cid'),
        '--pull','never','--network','none','--cpus','1','--memory','3g','--memory-swap','3g',
        '--platform','linux/amd64',
        '-v',str(stage/OWN/'c1/artifact/compiled-v1/c1.so')+':/input/c1.so:ro',
        '-v',str(runtime/'gnu')+':/output:rw',GNU_IMAGE,'/bin/sh','-ec',
        'objcopy -O binary --only-section=.text /input/c1.so /output/gnu-text.bin\n'
        'objcopy -O binary --only-section=.plt /input/c1.so /output/gnu-plt.bin\n'
        'objdump -d -w -Mintel /input/c1.so > /output/disassembly.txt\n'
        'readelf -W -a /input/c1.so > /output/readelf.txt']
    require(gnu_argv==expected_gnu and (run/'gnu-container.cid').read_text().strip(),
            'Changed GNU image/platform/command/input/output/resource argv')
    controls_verified=False
    if args.controls:
        directory=args.controls.resolve(); controls=read(directory/'receipt.json')
        require(controls['schema']=='c1-five-targeted-preflight-controls-v1' and controls['seal_sha256']==args.seal_sha256 and controls['positive_receipt_sha256']==sha(run/'receipt.json') and controls['formal_single_theorem_sensitivity'] is False, 'Unbound/wrong-scope controls')
        cases={'executed-ELF-byte','modeled-GOT-target','contract-model-pin','missing-supplier-public-interface-dependency','missing-caller-proof-with-stale-success'}
        require(len(controls['rows'])==5 and {r['case'] for r in controls['rows']}==cases,'Incomplete targeted controls')
        selected_inputs = {'executed-ELF-byte':OWN+'/c1/artifact/compiled-v1/c1.so',
            'modeled-GOT-target':OWN+'/c1/contract/definitions-v1.ml',
            'contract-model-pin':OWN+'/generic/e5-definitions-v1.ml',
            'missing-supplier-public-interface-dependency':'spec/e2/02-definitions-v1.ml',
            'missing-caller-proof-with-stale-success':seal['selected_main_proof_source']}
        for row in controls['rows']:
            require(row['affected_input']==selected_inputs[row['case']], 'Wrong selected control input')
            require(row['original_sha256']==expected[row['affected_input']], 'Control original input is not sealed')
            neg=directory/row['case']/'attempt'; actual_negative=read(neg/'receipt.json')
            require(sha(neg/'receipt.json')==row['receipt_sha256'] and row['status']=='OBSERVED_PREFLIGHT_INPUT_REJECTION' and row['exit_code']!=0 and row['proof_started'] is False and row['GNU_started'] is False and row['theorem_sensitivity_claim'] is False,'Control evidence mismatch')
            require(actual_negative['status']=='FRESH_C1_REPLAY_REJECTED' and actual_negative['proof_started'] is False and actual_negative['caller_acceptance'] is False and row['affected_input'] in actual_negative['error'] and not (neg/'checker-argv.json').exists() and not (neg/'gnu-argv.json').exists(),'Wrong exact negative boundary')
        controls_verified=True
    binding_probe_verified=False
    if getattr(args, 'binding_probe', None):
        directory=args.binding_probe.resolve(); wrapper=read(directory/'receipt.json')
        require(wrapper['schema']=='c1-successor-missing-usable-public-binding-probe-v1'
            and wrapper['status']=='OBSERVED_FRESH_PUBLIC_INTERFACE_BINDING_TYPE_AVAILABILITY_REJECTION'
            and wrapper['seal_sha256']==args.seal_sha256
            and wrapper['positive_receipt_sha256']==sha(run/'receipt.json')
            and wrapper['formal_dependency_isolation'] is False
            and wrapper['semantic_theorem_sensitivity'] is False
            and wrapper['original_theorem_remains_in_ambient_kernel_theory'] is True,
            'Unbound/wrong-scope fresh binding probe')
        negative=directory/'attempt'; neg=read(negative/'receipt.json')
        require(sha(negative/'receipt.json')==wrapper['attempt_receipt_sha256']
            and neg['status']=='OBSERVED_FRESH_PUBLIC_INTERFACE_BINDING_TYPE_AVAILABILITY_REJECTION'
            and neg['seal_sha256']==args.seal_sha256 and neg['positive_receipt_sha256']==sha(run/'receipt.json')
            and neg['proof_started'] is True and neg['exit_code']==1 and neg['timeout'] is False
            and neg['supplier_marker'] is True and neg['standard3_unchanged_at_rejection'] is True
            and neg['no_c1_objects_before_binding_shadow'] is True
            and neg['former_caller_proof_loader'] is False and neg['saved_passing_proof_used'] is False
            and neg['caller_acceptance'] is False and neg['full_C1_acceptance'] is False
            and neg['formal_dependency_isolation'] is False and neg['semantic_theorem_sensitivity'] is False
            and neg['original_theorem_remains_in_ambient_kernel_theory'] is True
            and neg['unavailable_binding']=='BP_E3_CRYPTO_PUBLIC_CALLER_POLICY'
            and neg['replacement_type']=='unit' and finite(neg['elapsed_seconds']) and neg['elapsed_seconds']<=1800,
            'Fresh binding probe did not actually reject under the original boundary')
        for name,key in [('inputs.json','source_set_sha256'),('c1-proof.log','c1_log_sha256'),
                         ('root-only-supplier/bootstrap.log','supplier_log_sha256')]:
            require(sha(negative/name)==neg[key], 'Changed fresh binding probe evidence: '+name)
        negstage,negruntime=negative/'source',negative/'runtime'
        neginputs=read(negative/'inputs.json')
        require(neginputs['files']==expected and neginputs['seal_sha256']==args.seal_sha256
                and neginputs['closed_load_graph']==seal['graph'], 'Binding probe staged input-set mismatch')
        foundation.guard_stage_permissions(negstage)
        require({str(p.relative_to(negstage)) for p in negstage.rglob('*') if p.is_file()}==set(expected),
                'Binding probe added/missing staged sources')
        for name,digest in expected.items(): check.checked(negstage,name,digest)
        check.anchors(negstage); check.validate_successor_graph(negstage,seal)
        neginvoke=read(negative/'invocation.json')
        require(neginvoke['kind']=='FRESH_C1_INTERFACE_BINDING_CONSTRUCTION_PROBE'
            and neginvoke['run_id']==neg['run_id'] and neginvoke['seal_sha256']==args.seal_sha256
            and neginvoke['resources']==resources and 0<neginvoke['actual_deadline_seconds']<=1800
            and neginvoke['network']=='none' and neginvoke['host_stage_read_only'] is True
            and neginvoke['former_caller_proof_loader'] is False, 'Wrong actual binding probe invocation')
        neginspection=read(negative/'container-inspect.json'); require(len(neginspection)==1,'Ambiguous probe container')
        negobj=neginspection[0]; negcfg=negobj['HostConfig']; negstate=negobj['State']
        require(negobj['Id']==(negative/'container.cid').read_text().strip() and negobj['Image']==HOL_IMAGE
            and negstate['ExitCode']==1 and negstate['OOMKilled'] is False and negstate['Running'] is False
            and negstate['StartedAt']!=negstate['FinishedAt'] and negcfg['Memory']==3*1024**3
            and negcfg['MemorySwap']==3*1024**3 and negcfg['NanoCpus']==10**9 and negcfg['NetworkMode']=='none',
            'Binding probe actual container/resource failure')
        negmounts={m['Destination']:m for m in negobj['Mounts']}
        negwanted={dest:negstage/path.relative_to(stage) if dest!='/output' else negruntime for dest,path in wanted.items()}
        require(len(negobj['Mounts'])==len(negwanted) and set(negmounts)==set(negwanted),'Wrong probe mount aliases')
        for dest,path in negwanted.items():
            require(Path(negmounts[dest]['Source']).resolve()==path.resolve() and negmounts[dest]['Type']=='bind'
                and negmounts[dest]['RW'] is (dest=='/output'), 'Probe mount/permission mismatch: '+dest)
        negargv=read(negative/'checker-argv.json')
        require(negargv[0:3]==['docker','run','-i'] and negargv[negargv.index('--platform')+1]=='linux/arm64'
            and negargv[negargv.index('--pull')+1]=='never' and HOL_IMAGE in negargv
            and '/work/third_party/hol-light/ocaml-hol' in negargv,'Wrong actual probe checker argv')
        negtext=(negative/'c1-proof.log').read_text(errors='replace')
        require('val BP_E3_CRYPTO_PUBLIC_CALLER_POLICY : unit = ()' in negtext
            and 'C1_BINDING_PROBE_INTERFACE_UNAVAILABLE_AS_THEOREM' in negtext
            and 'C1_FRESH_REJECTION_STANDARD3_UNCHANGED' in negtext
            and 'Error in included file /reuse/c1/application/proof-attempt1.ml' in negtext
            and re.search(r'Error:.*?type\s+unit.*?type\s+thm',negtext,re.S) is not None
            and 'val C1_CRYPTO_INTERFACE_APPLICATION : thm' not in negtext,
            'Probe rejection is not the actual required ML type failure')
        negfeed=(negative/'c1-input.ml').read_text()
        shadow='let BP_E3_CRYPTO_PUBLIC_CALLER_POLICY = ();;'
        firstcaller='try needs "/work/'+seal['loader']+'"'
        require(negfeed.count(shadow)==1 and negfeed.index(shadow)<negfeed.index(firstcaller),
            'Binding shadow did not precede any C1 loader')
        negaudit_process=subprocess.run([sys.executable, '-B',
            str(check.checked(root,supplier['auditor'],supplier['auditor_sha256'])),
            '--source-root',str(negstage),'--output',str(negruntime)],
            cwd=root,capture_output=True,timeout=120,check=False)
        require(negaudit_process.returncode==0 and negaudit_process.stderr==b'',
            'Binding probe isolated supplier auditor failed')
        negaudit=json.loads(negaudit_process.stdout)
        require((negaudit['unique_theorems'],negaudit['unique_definitions'],negaudit['equation_count'])==(325,119,218)
            and negaudit==read(negative/'root-only-supplier/host-audit-stdout.json')
            and not (negative/'root-only-supplier/host-audit-stderr.log').read_text().strip(),
            'Binding probe supplier audit failed')
        negimage=cross.crosscheck(negstage,negruntime/'gnu')
        require(negimage==read(negative/'c1-image-crosscheck.json') and negimage['fresh_GNU'] is True,
                'Binding probe fresh GNU image mismatch')
        binding_probe_verified=True
    guards()
    for name,digest in initial_evidence.items(): require(sha(run/name)==digest,'Evidence changed during root gate')
    return dict(schema='c1-successor-independent-root-gate-v1',
        status=('FRESH_ACCEPTED_WITH_FIVE_INTEGRITY_CONTROLS_AND_FRESH_BINDING_PROBE'
            if controls_verified and binding_probe_verified else
            'FRESH_ACCEPTED_POSITIVE_AND_INTEGRITY_CONTROLS_PENDING_BINDING_PROBE' if controls_verified else
            'FRESH_ACCEPTED_POSITIVE_PENDING_CONTROLS'),
        positive_accepted=True,first_milestone_accepted=controls_verified and binding_probe_verified,
        full_C1_acceptance=controls_verified and binding_probe_verified,
        binding_probe_verified=binding_probe_verified,integrity_controls_verified=controls_verified,
        original_targets=7,witness_targets=21,definitions=46,supplier_theorems=325,supplier_definitions=119,supplier_equations=218,
        seal_sha256=args.seal_sha256,source_count=len(expected),root_gate_sha256=sha(Path(__file__)),
        actual_runtime_audit_sha256=sha(runtime/'c1-live-audit-v1.json'),receipt_sha256=sha(run/'receipt.json'),
        runtime_supplier_audit_sha256={n:sha(runtime/n) for n in supplier_audit['audits']},
        gnu_image_id=GNU_IMAGE,gnu_platform='linux/amd64',gnu_image_inspect_sha256=sha(run/'gnu-image-inspect.json'),
        fresh_crosscheck_sha256=sha(run/'c1-image-crosscheck.json'),container_inspect_sha256=sha(run/'container-inspect.json'),
        controls_scope='Input integrity/dependency only; no semantic theorem sensitivity',formal_single_theorem_sensitivity=False,
        capability_or_formal_dependency_isolation=False,hardware_parser_loader_correspondence_proved=False,human_review='PENDING',utc=datetime.now(timezone.utc).isoformat())

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--source-root',type=Path,default=ROOT)
    p.add_argument('--seal',type=Path,required=True)
    p.add_argument('--seal-sha256',required=True)
    p.add_argument('--positive-run',type=Path,required=True)
    p.add_argument('--controls',type=Path)
    p.add_argument('--binding-probe',type=Path)
    p.add_argument('--output',type=Path)
    args=p.parse_args()
    try: result=gate(args)
    except Exception as error:
        print(json.dumps(dict(status='ROOT_GATE_REJECTED',error=str(error),positive_accepted=False,full_C1_acceptance=False)),file=sys.stderr)
        return 1
    text=json.dumps(result,indent=2,sort_keys=True)+'\n'
    if args.output:
        with args.output.open('x') as out: out.write(text)
    print(text,end='')
    return 0
if __name__=='__main__': sys.exit(main())
