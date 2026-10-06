#!/usr/bin/env python3
"""Freeze one finalized C1 loader; reuses the existing opaque supplier closure."""
import argparse, datetime, hashlib, json, sys, types
from pathlib import Path
sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
OWN = "development/approved-plan/reusable-assurance-v1"

def load(path, name):
    m = types.ModuleType(name)
    m.__file__ = str(path)
    exec(compile(path.read_bytes(), str(path), "exec"), m.__dict__)
    return m

def write_new(path, value):
    with path.open("x") as f:
        f.write(value)

def main():
    p = argparse.ArgumentParser()
    p.add_argument("--source-root", type=Path, default=ROOT)
    p.add_argument("--loader", required=True)
    p.add_argument("--theorem-map", type=Path, required=True)
    p.add_argument("--name", default="c1-final-v3")
    args = p.parse_args()
    if not args.name.replace("-", "").replace("_", "").isalnum():
        raise ValueError("Unsafe freeze name")
    root = args.source_root.resolve()
    check = load(HERE / "source-check-v1.py", "c1_source_check")
    generator = load(HERE / "generate-audit-v1.py", "c1_audit_generator")
    mapping_path = args.theorem_map.resolve()
    mapping_path.relative_to(root)
    if mapping_path.is_symlink():
        raise ValueError("Theorem-map symlink")
    mapping = json.loads(mapping_path.read_text())
    graph = check.load_graph(root, args.loader)
    registry = check.registry(root, mapping, graph)
    # A missing final binding is a readiness failure, never a replay success.
    text = "\n".join((root / name).read_text() for name in graph)
    import re
    for row in registry["objects"]:
        if not re.search(r"\blet\s+" + re.escape(row["name"]) + r"\s*=", text):
            raise ValueError("Full C1 binding is absent from the closed loader graph: " + row["name"])
    out = root / OWN / "replay"
    expected_path = out / (args.name + "-expected.json")
    audit_path = out / (args.name + "-audit.ml")
    seal_path = out / (args.name + "-seal.json")
    if any(path.exists() for path in [expected_path, audit_path, seal_path]):
        raise ValueError("Refusing to replace a frozen replay candidate")
    write_new(expected_path, json.dumps(registry, indent=2, sort_keys=True) + "\n")
    write_new(audit_path, generator.generate(registry))
    baseline_driver = "development/approved-plan/normal-entry-e5-v1/fresh-replay-v1.py"
    supplier = dict(
        materializer="development/approved-plan/clients-e3/opaque-supplier-v1/materialize-v1.py",
        materializer_sha256="6e21316921cc6c5dd5bbd718dc6d8d32eee4a6a1bc24dac17a355e13357b21f1",
        auditor="development/approved-plan/clients-e3/opaque-supplier-v1/audit-v2.py",
        auditor_sha256="9c219d8d9f4a9efa878f7f744404ae15da869bd2e9c3e8a1915c8f93532836d2",
        index=check.SUPPLIER_INDEX, index_sha256=check.SUPPLIER_INDEX_SHA,
        freeze="development/approved-plan/clients-e3/opaque-supplier-v1/freeze-v2.json",
        freeze_sha256="d24b79f84eb6468a9fe6fba05e8df0452ffda00d7423243c870b6e85b805fa9d",
        loader="development/approved-plan/call-binding/near-indirect-v1/callee-requalification-v1/opaque-callee-loader-v3.ml",
        decoder="development/approved-plan/call-binding/near-indirect-v1/decode-attempt5.ml",
        executor="development/approved-plan/call-binding/near-indirect-v1/x86-attempt5.ml",
        source_count=4534, theorem_count=325, definition_count=119, equation_count=218)
    host_inputs = {}
    for key in ["materializer", "auditor", "index", "freeze"]:
        check.checked(root, supplier[key], supplier[key + "_sha256"])
        host_inputs[supplier[key]] = supplier[key + "_sha256"]
    host_inputs[baseline_driver] = check.sha(check.checked(root, baseline_driver))
    files = {name: row["sha256"] for name, row in graph.items()}
    additional = [
        "scripts/inventory.py", OWN + "/c1/artifact/inventory-v1.json",
        OWN + "/c1/artifact/caller.bin", OWN + "/c1/artifact/plt-prefix.bin",
        OWN + "/c1/artifact/compiled-v1/c1.so",
        check.E5_EXPECTED, check.CONTRACT + "/freeze-v1.json",
        check.SUPPLIER_INDEX,
        str(mapping_path.relative_to(root)),
        str(expected_path.relative_to(root)), str(audit_path.relative_to(root)),
    ]
    additional += [check.CONTRACT + "/" + x for x in check.CONTRACT_HASHES]
    contract_freeze = json.loads(check.checked(root, check.CONTRACT + "/freeze-v1.json", check.CONTRACT_FREEZE_SHA).read_text())
    additional += [check.CONTRACT + "/" + x for x in contract_freeze["files"]]
    additional += [OWN + "/c1/artifact/" + x for x in check.ARTIFACT_INPUTS]
    additional += list(registry["helper_anchor_inputs"])
    additional += [OWN + "/replay/" + x for x in [
        "source-check-v1.py", "generate-audit-v1.py", "crosscheck-c1-image-v1.py",
        "freeze-final-v4.py", "fresh-replay-v3.py", "check-root-v2.py", "targeted-preflight-controls-v1.py",
        "root-gate-template-v1.json", "README-v1.md", "source-provenance-v1.json",
        "source-freeze-v1.json", "local-validation-v2.json"]]
    for name in additional:
        files[name] = check.sha(check.checked(root, name))
    seal = dict(
        schema="c1-fresh-closed-replay-seal-v1", created_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
        status="FROZEN_REPLAY_INPUTS_NOT_PROOF", experiment="BP-20261004-REUSE-V1",
        host_driver=OWN + "/replay/fresh-replay-v3.py",
        driver_sha256=files[OWN + "/replay/fresh-replay-v3.py"],
        baseline_driver=baseline_driver, baseline_driver_sha256=host_inputs[baseline_driver],
        checker_image_id="sha256:a19fdc18f1f283ed8e2514229b77f33619df1ba0ea1ae578c97779f4b4eb3c3f",
        gnu_image_id="sha256:444f775e6378c2e5523f29ceb8bbb184442277ed1114e6d37d873a7f127dfc26",
        supplier=supplier, host_inputs=host_inputs, additional_stage_inputs=files,
        loader=args.loader, graph=graph, expected_registry=str(expected_path.relative_to(root)),
        audit=str(audit_path.relative_to(root)), original_c1_targets=sorted(mapping),
        theorem_map=str(mapping_path.relative_to(root)),
        witness_target_count=21, nonvacuity_case_count=7, all_new_definition_count=46,
        source_check=OWN + "/replay/source-check-v1.py",
        artifact_crosscheck=OWN + "/replay/crosscheck-c1-image-v1.py",
        resources=dict(deadline_seconds=1800, cpu_count=1, memory_bytes=3*1024**3, swap_limit_bytes=3*1024**3),
        no_former_caller_proof_loader=True, caller_acceptance=False, human_review="PENDING",
        pending=["Root source/runtime/output gate", "Full positive replay", "Applicable targeted controls"])
    write_new(seal_path, json.dumps(seal, indent=2, sort_keys=True) + "\n")
    print(json.dumps(dict(status=seal["status"], seal=str(seal_path),
                         seal_sha256=check.sha(seal_path), caller_acceptance=False), indent=2))

if __name__ == "__main__":
    main()
