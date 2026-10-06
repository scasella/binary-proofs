#!/usr/bin/env python3
"""Select flat review sources/evidence; never duplicate staged source trees.

The checking archive supplies accepted mathematical dependencies. The companion
supplies review documents and historical observations/failures. Neither stored
receipts nor these hash maps replace fresh theorem reconstruction.
"""
from pathlib import Path
import datetime, hashlib, json, os, re

ROOT=Path(__file__).resolve().parents[4]
R="development/approved-plan/review-release-v1"
B="development/approved-plan/"
OUT=ROOT/R/"index/review-evidence-inputs-v2.json"
PREFIXES=("development/","artifacts/","inventory/","locks/","results/","spec/","report/","clients/","proofs/","third_party/")
TOP={"PROMPT.md","TRUST.md","README.md","REPORT.md","Makefile"}
selected={}
expected={}
deferred=set()
directory_references=set()
rejected=[]

def read(path):return json.loads((ROOT/path).read_text())
def safe(path):
 p=Path(path)
 return not p.is_absolute() and ".." not in p.parts and not any(part in ["source","__pycache__",".pytest_cache"] for part in p.parts) and p.name!=".DS_Store" and p.suffix not in [".pyc",".pyo"]
def add(path,reason,digest=None):
 if not safe(path):
  rejected.append({"path":path,"reason":reason,"why":"Excluded clone/cache/Finder or unsafe path"});return
 p=ROOT/path
 if p.is_dir():directory_references.add(path);return
 if not p.is_file():deferred.add(path);return
 if p.is_symlink():raise ValueError("Review input must be regular and not symlink: "+path)
 selected.setdefault(path,set()).add(reason)
 if digest:
  if path in expected and expected[path]!=digest:raise ValueError("Conflicting identity reference: "+path)
  expected[path]=digest
def pathlike(value):
 return isinstance(value,str) and "\n" not in value and " " not in value and (value.startswith(PREFIXES) or value in TOP)
def references(obj,reason):
 if isinstance(obj,dict):
  if isinstance(obj.get("path"),str) and pathlike(obj["path"]):add(obj["path"],reason,obj.get("sha256"))
  for k,v in obj.items():
   if pathlike(k):
    digest=v if isinstance(v,str) and re.fullmatch("[0-9a-f]{64}",v) else v.get("sha256") if isinstance(v,dict) else None
    add(k,reason,digest)
   if pathlike(v):add(v,reason)
   elif isinstance(v,(dict,list)):references(v,reason)
 elif isinstance(obj,list):
  for v in obj:
   if pathlike(v):add(v,reason)
   elif isinstance(v,(dict,list)):references(v,reason)
def tree(path,reason):
 for directory,dirs,names in os.walk(ROOT/path,followlinks=False):
  dirs[:]=[d for d in dirs if d not in ["source","__pycache__",".pytest_cache"]]
  for name in names:
   p=Path(directory)/name;relative=str(p.relative_to(ROOT))
   if safe(relative):add(relative,reason)

seed_paths=[
 R+"/index/release-index-draft-v1.json",
 R+"/index/historical-evidence-files-v1.json",
 R+"/human-review/source-map-v1.json",
 R+"/manuscript/claim-to-evidence-v1.json",
]
for path in seed_paths:
 add(path,"review_navigation_seed")
 references(read(path),"direct_reference_in_"+path)
for path in ["human-review","manuscript"]:tree(R+"/"+path,"release_review_documents")
for path in ["index/README-v1.md","index/adapter-inspection-v1.json","index/build-review-evidence-inputs-v1.py"]:
 add(R+"/"+path,"release_index_and_inspection")

# The original failure cannot be audited from its final outcome field alone.
# Include canonical attempted sources, exact retained goals, executed raw logs,
# metadata/cost ledgers and source-order records, without duplicating any source
# snapshots. These files may be failed, proposed or unexecuted; identity is not
# a theorem-checking assertion.
supplement_trees={
 B+"held-out-transfer-v1/c3/proofs":"original_C3_trial_attempted_and_unexecuted_sources",
 B+"held-out-transfer-v1/c3/obligations":"original_C3_trial_obligation_and_source_status_records",
 B+"held-out-transfer-v1/c3/replay":"original_C3_trial_failures_and_operational_history",
 B+"held-out-transfer-v1/c3/runs":"original_C3_trial_executed_runs_without_source_clones",
 B+"held-out-transfer-v1/c3/witness-diagnostics":"original_C3_trial_witness_and_suffix_diagnostics",
 B+"held-out-transfer-v1/c3/measurements":"original_C3_trial_effort_and_failure_ledger",
 B+"held-out-transfer-v1/c3-selection":"original_C3_selection_and_exposure_records",
 B+"held-out-transfer-v1/status":"original_C3_candidate_and_outcome_publication_history",
 B+"c3-postmortem-v1":"original_C3_postmortem_inspection_only_history",
 B+"c3-successor-v1/proofs":"C3_successor_accepted_and_superseded_local_proof_sources",
 B+"c3-successor-v1/diagnostics":"C3_successor_construction_failures_and_inspection",
 B+"c3-successor-v1/status":"C3_successor_acceptance_and_history_identity",
 B+"c3-successor-v1/results":"C3_successor_obligations_and_acceptance_records",
 B+"c3-successor-v1/review":"C3_successor_literal_and_architecture_review",
 B+"c3-successor-v1/measurements":"C3_successor_effort_and_failure_ledger",
 B+"c3-successor-v1/runs":"C3_successor_retained_execution_history_without_source_clones",
 B+"reusable-assurance-v1/c1/composition":"failed_C1_predecessor_frozen_proof_attempts",
 B+"reusable-assurance-c1-successor-v1/diagnosis":"C1_successor_failure_diagnosis",
}
for path,reason in supplement_trees.items():
 if (ROOT/path).is_dir():tree(path,reason)

mandatory=[
 B+"held-out-transfer-v1/status/final-publication-v1.json",
 B+"held-out-transfer-v1/results/final-outcome-v1.json",
 B+"held-out-transfer-v1/c3/replay/construction-cap-cleanup-full-context-v1.txt",
 B+"held-out-transfer-v1/c3/replay/construction-cap-cleanup-endpoint-v1.txt",
 B+"held-out-transfer-v1/c3/replay/construction-cap-final-frame-failure-v1.txt",
 B+"held-out-transfer-v1/c3/replay/construction-cap-stop-v1.json",
 B+"c3-postmortem-v1/diagnostics/cleanup-context-index-v1.json",
 B+"c3-successor-v1/status/current-stage-v1.json",
]
for path in mandatory:add(path,"mandatory_history_distinction")
context=read(B+"c3-postmortem-v1/diagnostics/cleanup-context-index-v1.json")
references(context,"postmortem_earliest_retained_context_source")
stop=read(B+"held-out-transfer-v1/c3/replay/construction-cap-stop-v1.json")
run=stop["run"]
for name in ["client-output.log","client-stdin.log","receipt.json","container-inspect.json"]:
 p=run+"/"+name
 if (ROOT/p).is_file():add(p,"original_C3_cap_run_raw_evidence")
source_snapshot=stop.get("source_snapshot",{})
references(source_snapshot,"original_C3_cap_source_identity_snapshot")
if isinstance(source_snapshot,dict):
 for path in source_snapshot:
  if pathlike(path):add(path,"original_C3_cap_source_identity_snapshot")

checking=read(R+"/inputs/release-inputs-v1.json")["files"]
files={};provided={};classifications={};errors=[]
for path,reasons in sorted(selected.items()):
 p=ROOT/path;actual=hashlib.sha256(p.read_bytes()).hexdigest()
 if path in expected and actual!=expected[path]:errors.append({"path":path,"expected":expected[path],"actual":actual})
 target=provided if checking.get(path)==actual else files
 target[path]=actual
 classifications[path]={"reasons":sorted(reasons),"bytes":p.stat().st_size,"delivery":"checking_archive" if target is provided else "review_companion"}
for path in mandatory:
 if path not in files and path not in provided:errors.append({"path":path,"error":"Mandatory history input absent"})
deferred_expected={R+"/release-index-v1.json",R+"/consumer/results-v1.json"}
unexpected_missing=sorted(deferred-deferred_expected)
if unexpected_missing:errors.append({"missing_direct_references":unexpected_missing})
result={
 "schema":"review-release-companion-inputs-v1","created_utc":datetime.datetime.now(datetime.timezone.utc).isoformat(),
 "acceptance_input":False,"review_evidence_not_proof_certificate":True,"human_review":"PENDING",
 "files":files,"file_count":len(files),"provided_by_checking_archive":provided,"provided_by_checking_archive_count":len(provided),
 "checking_input_manifest":R+"/inputs/release-inputs-v1.json",
 "classifications":classifications,"seed_documents":seed_paths,"supplement_scope":supplement_trees,
 "mandatory_history_distinctions":mandatory,
 "excluded_conventions":{"directory_components":["source","__pycache__",".pytest_cache"],"file_names":[".DS_Store"],"file_suffixes":[".pyc",".pyo"],"meaning":"Duplicate materialized source trees and dynamic caches are omitted; canonical exact proof sources remain supplied by checking inputs or companion flat paths"},
 "rejected_reference_paths":rejected,
 "directory_reference_anchors":sorted(directory_references),
 "deferred_release_result_references":sorted(deferred&deferred_expected),
 "deferred_rule":"Root must add separately produced authoritative release/consumer results to final release metadata; these absent future references are not evidence of successful consumption",
 "reference_identity_errors":errors,
 "history_gap_closed":"Initial draft histories identified outcomes/cap summaries but omitted original C3 final-publication, full cleanup context, actual warm-run output and unaccepted attempted sources. This companion explicitly supplies those items without relabeling them accepted.",
 "status_qualification":"Accepted C1/C2/C3 successor versus original C3 C and inspection-only postmortem remain separate. Attempted source, conditional helper, entry witness and saved receipt do not imply whole-caller acceptance.",
}
with OUT.open("x") as f:json.dump(result,f,indent=2,sort_keys=True);f.write("\n")
print(json.dumps({"output":str(OUT.relative_to(ROOT)),"companion_files":len(files),"already_checking":len(provided),"errors":errors,"deferred":sorted(deferred)},indent=2))
if errors:raise SystemExit(1)
