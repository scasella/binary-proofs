"""Create additive operational adapters with count-checked literal edits."""
import difflib, hashlib, json
from pathlib import Path
ROOT = Path(__file__).resolve().parents[4]
R = 'development/approved-plan/review-release-v1'
S = 'development/approved-plan/c3-successor-v1'

def replace(text, before, after):
    if text.count(before) != 1: raise ValueError('Adapter anchor not unique: ' + before)
    return text.replace(before, after)

old_driver = ROOT / (S + '/replay/fresh-replay-v1.py')
s = old_driver.read_text()
s = replace(s, 'check = module(HERE / "source-check-v1.py", "c3_fresh_source_check")',
            'check = module(ROOT / SUCCESSOR / "replay/source-check-v1.py", "c3_fresh_source_check")')
s = replace(s, "stage_deadline=datetime.datetime.fromisoformat(stage_data['deadline_utc'])", "context_path='development/approved-plan/review-release-v1/replay/checking-context-v1.py'\n    context_policy=module(check.checked(root,context_path,seal['additional_stage_inputs'][context_path]),'later_checking_policy')\n    checking_context=context_policy.validate(root,seal)\n    stage_deadline=datetime.datetime.fromisoformat(checking_context['deadline_utc'])")
s = replace(s, "raise TimeoutError('C3 successor stage deadline exhausted')", "raise TimeoutError('C3 later checking session deadline exhausted')")
s = replace(s, 'CONTEXT.update(run_id=rid, deadline_seconds=args.timeout_seconds,', "CONTEXT.update(checking_only=True, parent_accepted_seal_sha256=seal['parent_accepted_seal_sha256'],\n        historical_construction_deadline_utc=stage_data['deadline_utc'],\n        release_checking_context_sha256=seal['release_checking_context_sha256'],\n        run_id=rid, deadline_seconds=args.timeout_seconds,")
new_driver = ROOT / (R + '/replay/c3-fresh-check-v1.py'); new_driver.write_text(s)
old_gate = ROOT / (S + '/replay/check-root-v1.py')
t = old_gate.read_text()
t = replace(t, "stage_policy=read(root/(SUCCESSOR+'/STAGE-v1.json'))", "historical_stage_policy=read(root/(SUCCESSOR+'/STAGE-v1.json'))\n    context_path='development/approved-plan/review-release-v1/replay/checking-context-v1.py'\n    context_policy=module(root/context_path,'later_checking_gate_policy')\n    stage_policy=context_policy.validate(root,seal)")
t = replace(t, "self_path = SUCCESSOR+'/replay/check-root-v1.py'", "self_path = 'development/approved-plan/review-release-v1/replay/c3-root-check-v1.py'")
t = replace(t, "return dict(schema='c3-development-independent-root-gate-v1',", "return dict(schema='c3-development-independent-root-gate-v1',\n        checking_only=True, parent_accepted_seal_sha256=seal['parent_accepted_seal_sha256'],\n        historical_construction_deadline_utc=historical_stage_policy['deadline_utc'],\n        release_checking_context_sha256=seal['release_checking_context_sha256'],")
new_gate = ROOT / (R + '/replay/c3-root-check-v1.py'); new_gate.write_text(t)
rows=[]
for old,new in [(old_driver,new_driver),(old_gate,new_gate)]:
 diff=''.join(difflib.unified_diff(old.read_text().splitlines(True),new.read_text().splitlines(True),fromfile=str(old.relative_to(ROOT)),tofile=str(new.relative_to(ROOT))))
 path=ROOT/(R+'/replay/'+new.stem+'-diff-v1.patch');path.write_text(diff)
 rows.append(dict(parent=str(old.relative_to(ROOT)),parent_sha256=hashlib.sha256(old.read_bytes()).hexdigest(),adapter=str(new.relative_to(ROOT)),adapter_sha256=hashlib.sha256(new.read_bytes()).hexdigest(),diff=str(path.relative_to(ROOT))))
(ROOT/(R+'/replay/adapter-record-v1.json')).write_text(json.dumps(dict(schema='operational-checking-adapter-v1',changes=rows,mathematical_inputs='UNCHANGED_ENFORCED_BY_EXACT_PARENT_SEAL_PROJECTION',historical_guards='PRESERVED_UNCHANGED',schedule='Later bounded checking context only; no new construction time',trust='Python policy/extraction remain trusted; not a formal proof of adapter equivalence'),indent=2)+'\n')
