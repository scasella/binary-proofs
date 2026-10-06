#!/usr/bin/env python3
"""Freeze selected successor proof replacements against the immutable predecessor."""
import argparse, datetime, hashlib, json, re, sys, types
from pathlib import Path
sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
OLD = "development/approved-plan/reusable-assurance-v1"
NEW = "development/approved-plan/reusable-assurance-c1-successor-v1"
PREDECESSOR = OLD + "/replay/c1-final-v3-seal.json"
PREDECESSOR_SHA = "2ee5de28e859c9355321ba660b4b93f015baf56ef61f7b648acfbce3f0db7080"

def module(path, name):
    value = types.ModuleType(name)
    value.__file__ = str(path)
    exec(compile(path.read_bytes(), str(path), "exec"), value.__dict__)
    return value

def write(path, text):
    with path.open("x") as stream:
        stream.write(text)

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--source-root", type=Path, default=ROOT)
    parser.add_argument("--main-proof", required=True)
    parser.add_argument("--helper-proof")
    parser.add_argument("--name", default="c1-successor-v1")
    args = parser.parse_args()
    root = args.source_root.resolve()
    if not re.fullmatch(r"[A-Za-z0-9_-]+", args.name):
        raise ValueError("Unsafe freeze name")
    check = module(HERE / "source-check-v1.py", "successor_source_check")
    predecessor = json.loads(check.checked(root, PREDECESSOR, PREDECESSOR_SHA).read_text())
    for key, value in predecessor["additional_stage_inputs"].items():
        check.checked(root, key, value)
    for key, value in predecessor["host_inputs"].items():
        check.checked(root, key, value)
    for path in [args.main_proof] + ([args.helper_proof] if args.helper_proof else []):
        if not path.startswith(NEW + "/proofs/") or not path.endswith(".ml"):
            raise ValueError("Proof source must be in the owned successor proofs lane")
        check.checked(root, path)
    replacements = {OLD + "/replay/c1-final-loader-v3.ml": NEW + "/replay/c1-loader-"+args.name+".ml",
                    OLD + "/c1/composition/proof-attempt3.ml": args.main_proof}
    if args.helper_proof:
        replacements[OLD + "/c1/composition/helpers-proof-attempt9.ml"] = args.helper_proof
    loader = replacements[OLD + "/replay/c1-final-loader-v3.ml"]
    source = check.checked(root, OLD + "/replay/c1-final-loader-v3.ml").read_text()
    for previous, selected in replacements.items():
        if previous.endswith("c1-final-loader-v3.ml"):
            continue
        old_import = '"/reuse/' + previous[len(OLD)+1:] + '"'
        if source.count(old_import) != 1:
            raise ValueError("Unexpected predecessor selected source import")
        source = source.replace(old_import, '"/work/' + selected + '"')
    loader_path = root / loader
    outputs = [loader_path] + [root / NEW / "replay" / (args.name + suffix) for suffix in ["-expected.json", "-audit.ml", "-seal.json"]]
    if any(path.exists() for path in outputs):
        raise ValueError("Refusing to replace a frozen successor candidate")
    write(loader_path, source)
    graph = check.load_graph(root, loader)
    mapping = json.loads(check.checked(root, predecessor["theorem_map"]).read_text())
    registry = check.registry(root, mapping, graph)
    original_registry = json.loads(check.checked(root, predecessor["expected_registry"],
        predecessor["additional_stage_inputs"][predecessor["expected_registry"]]).read_text())
    if registry != original_registry:
        raise ValueError("Successor changes frozen 7/21/46 expected rows")
    text = "\n".join(check.checked(root, path).read_text() for path in graph)
    for row in registry["objects"]:
        if not re.search(r"\blet\s+" + re.escape(row["name"]) + r"\s*=", text):
            raise ValueError("Selected closed graph lacks full binding: " + row["name"])
    seal = dict(predecessor)
    seal.update(created_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
        experiment="BP-20261004-C1-SUCCESSOR-V1", predecessor_seal=PREDECESSOR,
        predecessor_seal_sha256=PREDECESSOR_SHA, selected_source_replacements=replacements,
        selected_main_proof_source=args.main_proof, loader=loader, graph=graph,
        root_gate=NEW + "/replay/check-root-v3.py", host_driver=NEW + "/replay/fresh-replay-v5.py",
        source_check=NEW + "/replay/source-check-v1.py", caller_acceptance=False,
        status="FROZEN_REPLAY_INPUTS_NOT_PROOF", human_review="PENDING")
    check.validate_successor_graph(root, seal)
    generator = module(root / OLD / "replay/generate-audit-v1.py", "inherited_actual_audit_generator")
    expected_path, audit_path, seal_path = outputs[1:]
    write(expected_path, json.dumps(registry, indent=2, sort_keys=True)+"\n")
    write(audit_path, generator.generate(registry))
    seal["expected_registry"] = str(expected_path.relative_to(root))
    seal["audit"] = str(audit_path.relative_to(root))
    files = dict(predecessor["additional_stage_inputs"])
    # Preserve every original formal graph node as a protected input even if its
    # loader/main has an additive replacement. Presence does not execute a proof.
    files.update({name: row["sha256"] for name, row in predecessor["graph"].items()})
    files.update({name: row["sha256"] for name, row in graph.items()})
    stage_path = NEW + "/STAGE-v1.json"
    stage = json.loads(check.checked(root, stage_path).read_text())
    for entry in stage["protected_inputs"]:
        check.checked(root, entry["path"], entry["sha256"])
        files[entry["path"]] = entry["sha256"]
    for path in [PREDECESSOR, stage_path, str(expected_path.relative_to(root)), str(audit_path.relative_to(root)),
                 NEW + "/replay/freeze-v7.py", NEW + "/replay/source-check-v1.py",
                 NEW + "/replay/fresh-replay-v5.py", NEW + "/replay/check-root-v3.py",
                 NEW + "/replay/targeted-preflight-controls-v3.py", NEW + "/replay/missing-interface-probe-v3.py",
                 NEW + "/replay/OPACITY-v1.md", NEW + "/replay/machinery-source-pins-v1.json", NEW + "/replay/ambient-snapshot-v1.ml", NEW + "/replay/probe-driver-source-pins-v1.json", NEW + "/replay/OPACITY-v2.md", NEW + "/replay/ambient-observation-v1.json", NEW + "/replay/audit-ambient-v1.py", NEW + "/replay/local-validation-v1.json"]:
        files[path] = check.sha(check.checked(root, path))
    for path, digest in files.items():
        check.checked(root, path, digest)
    seal["additional_stage_inputs"] = files
    seal["driver_sha256"] = files[seal["host_driver"]]
    write(seal_path, json.dumps(seal, indent=2, sort_keys=True)+"\n")
    print(json.dumps(dict(status=seal["status"], seal=str(seal_path), seal_sha256=check.sha(seal_path),
        formal_graph_nodes=len(graph), original_objects=7, witness_objects=21, definitions=46,
        caller_acceptance=False, inherited_source_checks_retained=True), indent=2))

if __name__ == "__main__":
    main()
