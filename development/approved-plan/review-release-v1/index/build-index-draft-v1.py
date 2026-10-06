#!/usr/bin/env python3
"""Read historical packages; write additive review inventory only.

This reports identities and historical accepted checks. It does not replay HOL
or constitute an acceptance driver. Supplier preserved paths refer to their
pinned archive version; they are not assumed identical to current root files.
"""
from pathlib import Path
import datetime, hashlib, json

ROOT = Path(__file__).resolve().parents[4]
OUT = Path(__file__).resolve().parent
B = "development/approved-plan/"
def read(path):
    return json.loads((ROOT / path).read_text())
def ref(path):
    p = ROOT / path
    return {"path": path, "sha256": hashlib.sha256(p.read_bytes()).hexdigest(), "bytes": p.stat().st_size}
def write(name, value):
    with (OUT / name).open("x") as f:
        json.dump(value, f, indent=2, sort_keys=True)
        f.write("\n")

CONFIG = {
 "C1": {
  "scope": B+"reusable-assurance-c1-successor-v1",
  "seal": B+"reusable-assurance-c1-successor-v1/replay/c1-successor-final-v3-seal.json",
  "positive": B+"reusable-assurance-c1-successor-v1/runs/c1-fresh-final-v3",
  "gate": B+"reusable-assurance-c1-successor-v1/runs/c1-fresh-final-v3/root-full-acceptance-v1.json",
  "controls": B+"reusable-assurance-c1-successor-v1/runs/c1-targeted-controls-v3/receipt.json",
  "probe": B+"reusable-assurance-c1-successor-v1/runs/c1-missing-interface-probe-v3/receipt.json",
  "contract": B+"reusable-assurance-v1/c1/contract/freeze-v1.json",
  "inventory": B+"reusable-assurance-v1/c1/artifact/inventory-v1.json",
  "artifact": B+"reusable-assurance-v1/c1/artifact/compiled-v1/c1.so",
  "status": B+"reusable-assurance-c1-successor-v1/status/registry-final-v2.json",
  "report": B+"reusable-assurance-c1-successor-v1/REPORT-v3.md",
  "costs": B+"reusable-assurance-c1-successor-v1/status/observation-final-v2-cost-failure-ledger.json",
  "kind": "accepted successor to separately preserved capped predecessor",
 },
 "C2": {
  "scope": B+"reusable-assurance-c2-v1",
  "seal": B+"reusable-assurance-c2-v1/replay/c2-final-v1-seal.json",
  "positive": B+"reusable-assurance-c2-v1/runs/c2-fresh-final-v1",
  "gate": B+"reusable-assurance-c2-v1/runs/c2-root-full-acceptance-final-v1.json",
  "controls": B+"reusable-assurance-c2-v1/negative-controls/c2-controls-final-v1/receipt.json",
  "probe": B+"reusable-assurance-c2-v1/runs/c2-binding-probe-final-v1/receipt.json",
  "contract": B+"reusable-assurance-c2-v1/spec/freeze-v1.json",
  "inventory": B+"reusable-assurance-c2-v1/inventory/inventory-v1.json",
  "artifact": B+"reusable-assurance-c2-v1/artifact/compiled-v1/c2.so",
  "status": B+"reusable-assurance-c2-v1/status/stage-result-v2.json",
  "costs": B+"reusable-assurance-c2-v1/measurements/available-costs-final-v2.json",
  "kind": "accepted development case; not held-out",
 },
 "C3": {
  "scope": B+"c3-successor-v1",
  "seal": B+"c3-successor-v1/replay/c3-successor-final-v1-seal.json",
  "positive": B+"c3-successor-v1/runs/fresh-final-v1",
  "gate": B+"c3-successor-v1/results/complete-gate-final-v1.json",
  "controls": B+"c3-successor-v1/runs/controls-final-v1/receipt.json",
  "probe": B+"c3-successor-v1/runs/binding-probe-final-v1/receipt.json",
  "contract": B+"held-out-transfer-v1/c3/contract/freeze-v1.json",
  "inventory": B+"held-out-transfer-v1/c3/artifact/inventory-v1.json",
  "artifact": B+"held-out-transfer-v1/c3/artifact/compiled-v1/c3.so",
  "status": B+"c3-successor-v1/status/current-stage-v1.json",
  "report": B+"c3-successor-v1/REPORT.md",
  "costs": B+"c3-successor-v1/measurements/effort-final-v1.json",
  "kind": "accepted local completion successor; original held-out trial remains outcome C",
 },
}
supplier_index_path = B+"clients-e3/opaque-supplier-v1/source-index-v1.json"
supplier_index = read(supplier_index_path)
supplier_sources = supplier_index["source_files"]
graph_union = {}
additional_union = {}
cases = {}
errors = []
for case, c in CONFIG.items():
    seal, gate = read(c["seal"]), read(c["gate"])
    positive = read(c["positive"]+"/receipt.json")
    audit = read(c["positive"]+f"/runtime/{case.lower()}-live-audit-v1.json")
    inv = read(c["inventory"])
    stage = read(c["scope"]+"/STAGE-v1.json")
    for path, item in seal["graph"].items():
        actual = ref(path)["sha256"]
        if actual != item["sha256"]: errors.append({"case":case,"kind":"graph_identity","path":path})
        if path in graph_union and graph_union[path]["sha256"] != actual:
            errors.append({"case":case,"kind":"graph_version_conflict","path":path})
        graph_union[path] = dict(item)
    for path, digest in seal["additional_stage_inputs"].items():
        actual = ref(path)["sha256"]
        if actual != digest: errors.append({"case":case,"kind":"additional_identity","path":path})
        if path in additional_union and additional_union[path] != digest:
            errors.append({"case":case,"kind":"additional_version_conflict","path":path})
        additional_union[path] = digest
    if gate["seal_sha256"] != ref(c["seal"])["sha256"]:
        errors.append({"case":case,"kind":"gate_seal_identity"})
    if not gate.get(f"full_{case}_acceptance"):
        errors.append({"case":case,"kind":"historical_full_gate_not_positive"})
    # Historical positive receipt deliberately remains pending root gates.
    # The complete gate, rather than receipt.status or seal.status, is decisive.
    cases[case] = {
      "identity_kind": c["kind"],
      "historical_acceptance": gate["status"],
      "accepted_utc": gate["utc"],
      "seal": ref(c["seal"]), "complete_gate": ref(c["gate"]),
      "positive_receipt": ref(c["positive"]+"/receipt.json"),
      "positive_receipt_pending_fields_preserved": True,
      "controls": ref(c["controls"]), "binding_probe": ref(c["probe"]),
      "contract_freeze": ref(c["contract"]), "status_observation": ref(c["status"]),
      "artifact": ref(c["artifact"]), "artifact_inventory": ref(c["inventory"]),
      "load_bias": inv["load_bias"], "linkage": inv["linkage"],
      "image": inv["image"], "needed_metadata": inv["needed"],
      "live_literal_expanded_audit": ref(c["positive"]+f"/runtime/{case.lower()}-live-audit-v1.json"),
      "expected_registry": ref(seal["expected_registry"]),
      "theorem_map": ref(seal["theorem_map"]),
      "original_targets": read(seal["theorem_map"]),
      "graph": seal["graph"], "graph_node_count":len(seal["graph"]),
      "sealed_additional_inputs": seal["additional_stage_inputs"],
      "host_inputs": seal["host_inputs"], "supplier": seal["supplier"],
      "loader": ref(seal["loader"]), "main":ref(seal["selected_main_proof_source"]),
      "audit_program":ref(seal["audit"]),
      "operational_sources":{k:ref(seal[k]) for k in ["host_driver","source_check","root_gate","artifact_crosscheck"]},
      "resources": seal["resources"],
      "construction_stage":ref(c["scope"]+"/STAGE-v1.json"),
      "construction_start_utc":stage.get("start_utc"),
      "construction_deadline_utc":stage.get("construction_deadline_utc",stage.get("deadline_utc")),
      "construction_cap_seconds":stage["construction_cap_seconds"],
      "audit_counts":{k:audit[k] for k in ["original_target_count","witness_target_count","nonvacuity_case_count","definition_count","initial_axiom_count","final_axiom_count"]},
      "supplier_audit_counts":{k:gate[k] for k in ["supplier_theorems","supplier_definitions","supplier_equations"]},
      "historical_replay_measurements":{k:positive.get(k) for k in ["elapsed_seconds","checker_wall_seconds","supplier_wall_seconds","supplier_cpu_seconds","caller_wall_seconds","caller_cpu_seconds","wall_scope","cpu_scope"]},
      "cost_failure_ledger":ref(c["costs"]),
      "human_review":"PENDING",
      "no_release_replay_claim_in_this_index":True,
    }
    if c.get("report"):cases[case]["historical_report"]=ref(c["report"])

layer_path=B+"held-out-transfer-v1/layer/freeze-v1.json"
layer=read(layer_path)
for path,digest in {**layer["candidate_inputs"],**layer["direct_dependency_pins"]}.items():
    if ref(path)["sha256"] != digest: errors.append({"kind":"candidate_identity","path":path})
history = {
 "failed_C1_predecessor":{
  "experiment":"BP-20261004-REUSE-V1", "status":"BLOCKED_FROZEN_CONSTRUCTION_LIMIT", "C1":"NOT_ACCEPTED",
  "registry":ref(B+"reusable-assurance-v1/status/registry-final-v4.json"),
  "seal":ref(B+"reusable-assurance-v1/replay/c1-final-v3-seal.json"),
  "last_failed_receipt":ref(B+"reusable-assurance-v1/runs/c1-fresh-final-v3/receipt.json"),
  "last_failed_raw_log":ref(B+"reusable-assurance-v1/runs/c1-fresh-final-v3/c1-proof.log"),
 },
 "failed_C3_held_out":{
  "experiment":"BP-20261005-HELD-OUT-TRANSFER-V1", "outcome":"C", "C3":"NOT_ACCEPTED",
  "frozen_case":ref(B+"held-out-transfer-v1/c3/contract/freeze-v1.json"),
  "outcome_record":ref(B+"held-out-transfer-v1/results/final-outcome-v1.json"),
  "cap_record":ref(B+"held-out-transfer-v1/c3/replay/construction-cap-stop-v1.json"),
  "cleanup_endpoint":ref(B+"held-out-transfer-v1/c3/replay/construction-cap-cleanup-endpoint-v1.txt"),
  "frame_failure":ref(B+"held-out-transfer-v1/c3/replay/construction-cap-final-frame-failure-v1.txt"),
 },
 "C3_postmortem":{
  "experiment":"BP-20261005-C3-POSTMORTEM-V1",
  "stage":ref(B+"c3-postmortem-v1/STAGE-v1.json"),
  "result":ref(B+"c3-postmortem-v1/results-v1.json"),
  "report":ref(B+"c3-postmortem-v1/REPORT.md"),
 },
}
regressions={}
for case in ["c1","c2"]:
    path=B+f"held-out-transfer-v1/regression/{case}-result-v1.json"
    j=read(path)
    regressions[case.upper()]={
      "summary":ref(path),"status":j["status"],"historical_package_modified":j["historical_package_modified"],
      "historical_controls_not_relabeled":j["historical_controls_not_relabeled"],
      "actual_consumption":j["actual_consumption"],
      "run_receipt":ref(j["run_receipt"]),"gate":ref(j["source_regression_gate"]),
      "transformation_ledger":ref(j["source_patch_ledger"]),
      "not_historical_package_migration":True,"not_held_out":True,"not_savings_evidence":True,
    }

index={
 "schema":"review-release-index-draft-v1", "generated_utc":datetime.datetime.now(datetime.timezone.utc).isoformat(),
 "authority":"DRAFT_FOR_ROOT_RELEASE_AUTHORITY", "acceptance_input":False,
 "purpose":"Identity and evidence map of unchanged accepted historical packages, not a theorem checker",
 "path_convention":"Paths are relative to delivered repository root; no original developer path needed",
 "cases":cases, "histories":history,
 "candidate_layer":{
  "freeze":ref(layer_path),"candidate":layer["candidate"],
  "exports":ref(B+"held-out-transfer-v1/layer/exports-v1.json"),
  "dependencies":ref(B+"held-out-transfer-v1/layer/dependencies-v1.json"),
  "policy":ref(layer["supported_class_and_allowed_work"]),
  "formal_export_count":layer["formal_export_count"],"formal_export_names":layer["formal_export_names"],
  "automation_export_names":layer["automation_export_names"],
  "candidate_inputs":layer["candidate_inputs"],"direct_dependency_pins":layer["direct_dependency_pins"],
  "preparation_adaptation":layer["preparation_adaptation"],
  "regressions":regressions,
 },
 "supplier":{
  "index":ref(supplier_index_path),"archive":ref(supplier_index["archive_path"]),
  "source_count":len(supplier_sources),
  "source_version_rule":"Use digest-checked BP-E1 archive plus index.extra_files through pinned materializer; archive versions of mutable historical top-level documentation need not equal current root files",
  "live_public_interfaces":supplier_index["required_live_public_interfaces"],
  "freeze":ref(B+"clients-e3/opaque-supplier-v1/freeze-v2.json"),
  "baseline_lock":ref("locks/baseline.json"),"artifact_inventory":ref("inventory/artifacts.json"),
  "artifacts":[ref(p) for p in read("locks/baseline.json")["artifacts"]],
  "artifacts_reached_by_scoped_callers":["artifacts/baseline/libcrypto.so.3"],
  "other_inventory_artifacts_are_not_verified_closure":True,
  "packages":read("locks/baseline.json")["packages"],
  "declared_profile":ref("results/profile/baseline.json"),
 },
 "trust_and_assumptions":{
  "permitted_axioms":["INFINITY_AX","SELECT_AX","ETA_AX"],
  "model":"Pinned E3 decode-attempt5.ml and x86-attempt5.ml; E5 normal-entry RF=TF=0; original architectural interpretation unchanged",
  "post_initialization":"Fixed code/data placement, explicit resolved GOT entries, stable ordinary memory and permissions, absence of interposition/concurrency; dynamic loader not verified",
  "opacity":"Source/tactic-input inspection and live literal audits; ambient supplier theorem/model objects remain, prior exposure disclosed; no formal transitive dependency/capability isolation",
  "hardware":"Kernel-checked mathematical model plus explicit architectural interpretation; no unrestricted processor or parser/loader correspondence claim",
  "human_review":"PENDING",
  "references":[ref(p) for p in ["PROMPT.md","TRUST.md","report/FORMAL-AND-TRUST.md","spec/e5/CLAIM-CHANGES-v1.md",B+"held-out-transfer-v1/layer/CLASS-AND-EXTENSION-POINTS-v1.md",B+"c3-successor-v1/review/final-literal-contract-view-v1.json",B+"c3-successor-v1/status/selected-reuse-account-v1.json",B+"c3-successor-v1/diagnostics/transport-final-selected-graph-review-v2.json"]],
 },
 "checking_only_after_deadline":"Original construction guard remains immutable. Later checking is a separately recorded release operation over exact sealed sources; packaging-only adapter and consumption result are owned by root, not asserted by this draft",
 "new_stage_prohibitions":["new caller","glibc expansion","framework generalization","economics"],
 "identity_validation":{"selected_graphs_and_additional_inputs_current_hash_checked":True,"errors":errors,"formal_validation":False},
 "missing_metrics":{"exclusive_active_construction_seconds":None,"exclusive_coordination_seconds":None,"tokens":None,"model_identifier":None,"cost":None,"reason":"Not fully instrumented or exposed; historical ledgers retain partial/overlapping observations"},
}
write("release-index-draft-v1.json",index)
write("selected-inputs-v1.json",{
 "schema":"review-selected-inputs-union-v1","acceptance_input":False,
 "supplier_index":ref(supplier_index_path),"supplier_source_paths":supplier_sources,
 "supplier_archive_versioning_required":True,
 "selected_formal_graph":graph_union,"selected_additional_inputs":additional_union,
 "selected_formal_graph_node_count":len(graph_union),"selected_additional_input_count":len(additional_union),
 "source_validation_errors":errors,
})
print(json.dumps({"cases":{k:{"graph":v["graph_node_count"],"audit":v["audit_counts"]} for k,v in cases.items()},"union_graph":len(graph_union),"additional_inputs":len(additional_union),"errors":errors},indent=2))
if errors:raise SystemExit(1)
