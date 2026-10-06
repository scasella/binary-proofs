"""Generate the sole current release view from selected evidence and later checks."""
import datetime,hashlib,json
from pathlib import Path
ROOT=Path(__file__).resolve().parents[4];R=Path('development/approved-plan/review-release-v1')
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1024*1024),b''):h.update(b)
 return h.hexdigest()
def record(path):
 p=ROOT/path
 return dict(path=str(path),sha256=sha(p),bytes=p.stat().st_size)
def read(path):return json.loads((ROOT/path).read_text())
findings=read(R/'human-review/findings-v1.json')
if findings['blocking_findings_recorded_by_packet_preparation']:raise ValueError('Blocking finding requires explicitly scoped release status')
consumer=read(R/'consumer/results-v1.json')
index=read(R/'index/release-index-draft-v1.json')
index.update(schema='accepted-c1c2c3-authoritative-review-release-v1',authority='AUTHORITATIVE_CURRENT_RELEASE_ONLY',generated_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),purpose='Consolidate exact accepted packages, immutable failures/successors, later checking-only consumption and pending human review; no new proof construction',acceptance_input=False)
for case in ['C1','C2','C3']:
 base=R/'consumer/cases'/case
 result=read(base/'result-v1.json');gate=read(base/'complete-gate.json')
 if result['status']!='CHECKING_ONLY_CONSUMER_FRESH_ACCEPTED' or gate['status']!='FRESH_ACCEPTED_WITH_FIVE_INTEGRITY_CONTROLS_AND_FRESH_BINDING_PROBE' or gate['full_'+case+'_acceptance'] is not True:raise ValueError('Incomplete later case: '+case)
 original=index['cases'][case]['seal']['sha256']
 if result['original_accepted_seal_sha256']!=original or result['complete_gate_sha256']!=sha(ROOT/base/'complete-gate.json'):raise ValueError('Wrong later checking parent/gate')
 index['cases'][case].pop('no_release_replay_claim_in_this_index',None)
 index['cases'][case]['later_checking_only']=dict(status=result['status'],proof_construction=False,result=record(base/'result-v1.json'),complete_gate=record(base/'complete-gate.json'),session=record(base/'checking-session-v1.json'),ledger=record(base/'later-checking-ledger-v1.jsonl'),elapsed_seconds=result['elapsed_seconds'],operational_seal_sha256=result['operational_seal_sha256'],historical_package_unchanged=True)
review={str(p.relative_to(ROOT)):sha(p) for directory in ['human-review','manuscript'] for p in (ROOT/R/directory).rglob('*') if p.is_file()}
index['release']=dict(status='REVIEW_READY_WITH_CHECKING_ONLY_CONSUMER_ACCEPTANCE',human_review='PENDING',human_review_performed=False,external_organizational_validation=False,consumer=record(R/'consumer/results-v1.json'),delivery=record(R/'delivery/delivery-v1.json'),checking_inputs=record(R/'inputs/release-inputs-v1.json'),adapter_record=record(R/'replay/adapter-record-v1.json'),adapter_inspection=record(R/'index/adapter-inspection-v1.json'),review_files=review,review_evidence_map=record(R/'index/review-evidence-inputs-v2.json'),preservation_end=record(R/'index/preservation-end-v1.json'),stage=record(R/'STAGE-v1.json'),observations=record(R/'results/stage-observations-v1.json'),interpretation='Later consumption is a separately measured checking result, not another construction trial or revision of the original capped failure',priority_comparative_claims='UNVERIFIED_NO_ACTUAL_RELATED_WORK_COMPARISON',strongest_supported_publication_claim='Under pinned explicit model/environment and fixed-image assumptions, unchanged production OpenSSL supplier contracts support checked composition through actual linkage for three different experimental callers; integration adaptation and caller-local repair are exposed, including a failed capped held-out trial followed by a separately accepted successor.',unsupported_attractive_claims=['Automatic or arbitrary-caller integration','Unchanged transfer success within original held-out budget','Construction-cost savings or amortization','Formal caller-construction capability isolation','Independent human or external-organizational validation','Unrestricted processor/loader correspondence or whole-library verification'])
index['research_judgments']=dict(H1='SUPPORTED_WITHIN_DECLARED_MODEL_AND_INSPECTION_QUALIFIED_INTERFACE_USE',H2='BOUNDED_REPAIRABLE_TRANSFER_SUPPORTED_ORIGINAL_CAPPED_HELD_OUT_TRIAL_FAILED',H3='NOT_ATTEMPTED_NO_MATCHED_CONSTRUCTION_BASELINE')
index['release']['final_observations']=record(R/'results/final-observations-v1.json')
index['release']['actual_consumer_mounts']=record(R/'consumer/mount-independence-v1.json')
index['release']['preservation_summary']=record(R/'index/preservation-final-summary-v1.json')
index['checking_only_after_deadline']='Original construction guard remains immutable and rejected an actual late historical invocation. Later checking is separately recorded by the three complete consumer gates; the C3 operational adapter preserves the accepted parent mathematical inputs while using a new bounded checking interval. It grants no construction time.'
index['release']['documentary_corrections']=record(R/'results/documentary-corrections-v1.json')
# The registry is documentary. Existing root gates, live reconstruction and sealed math control acceptance.
with (ROOT/R/'release-index-v1.json').open('x') as f:json.dump(index,f,indent=2,sort_keys=True);f.write('\n')
print(json.dumps(dict(status=index['release']['status'],index=record(R/'release-index-v1.json')),indent=2))
