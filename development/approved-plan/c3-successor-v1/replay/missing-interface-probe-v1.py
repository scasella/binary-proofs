#!/usr/bin/env python3
"""Separate fresh usable-interface-binding construction probe, after a positive."""
import argparse, hashlib, json, subprocess, sys, types
from pathlib import Path
sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent

def module(path, name):
    value = types.ModuleType(name); value.__file__ = str(path)
    exec(compile(path.read_bytes(), str(path), "exec"), value.__dict__)
    return value

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-root", type=Path, required=True)
    parser.add_argument("--seal", type=Path, required=True)
    parser.add_argument("--seal-sha256", required=True)
    parser.add_argument("--positive-run", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    root = args.source_root.resolve()
    check = module(HERE / "source-check-v1.py", "probe_source_check")
    seal_rel = str(args.seal.resolve().relative_to(root))
    seal = json.loads(check.checked(root, seal_rel, args.seal_sha256).read_text())
    own = str(Path(__file__).resolve().relative_to(root))
    if sha(Path(__file__)) != seal["additional_stage_inputs"][own]:
        raise ValueError("Probe harness is outside the frozen seal")
    gate = module(check.checked(root, seal["root_gate"],
        seal["additional_stage_inputs"][seal["root_gate"]]), "probe_genuine_positive_gate")
    positive = gate.gate(argparse.Namespace(source_root=root, seal=args.seal,
        seal_sha256=args.seal_sha256, positive_run=args.positive_run, controls=None))
    if positive["positive_accepted"] is not True:
        raise ValueError("Probe requires genuine positive first")
    out = args.output.resolve(); out.mkdir(parents=True, exist_ok=False)
    argv = [sys.executable, "-B", str(root / seal["host_driver"]), "--source-root", str(root),
        "--seal", str(args.seal.resolve()), "--seal-sha256", args.seal_sha256,
        "--output", str(out / "attempt"), "--timeout-seconds", "1800",
        "--unavailable-interface-binding-probe", "--genuine-positive-run", str(args.positive_run.resolve())]
    (out / "argv.json").write_text(json.dumps(argv, indent=2)+"\n")
    with (out / "process.log").open("xb") as log:
        process = subprocess.run(argv, stdout=log, stderr=subprocess.STDOUT, timeout=1830)
    actual = json.loads((out / "attempt/receipt.json").read_text())
    if (process.returncode != 1 or actual["status"] != "OBSERVED_FRESH_PUBLIC_INTERFACE_BINDING_TYPE_AVAILABILITY_REJECTION"
        or actual["proof_started"] is not True or actual["timeout"] is not False
        or actual["supplier_marker"] is not True or actual["caller_acceptance"] is not False
        or actual["full_C3_acceptance"] is not False or actual["formal_dependency_isolation"] is not False
        or actual["semantic_theorem_sensitivity"] is not False
        or actual["original_theorem_remains_in_ambient_kernel_theory"] is not True
        or actual["positive_receipt_sha256"] != sha(args.positive_run / "receipt.json")):
        raise ValueError("Fresh binding probe did not reach its exact required rejection stage")
    result = dict(schema="c3-development-missing-usable-public-binding-probe-v1",
        status="OBSERVED_FRESH_PUBLIC_INTERFACE_BINDING_TYPE_AVAILABILITY_REJECTION",
        positive_receipt_sha256=sha(args.positive_run / "receipt.json"),
        attempt_receipt_sha256=sha(out / "attempt/receipt.json"), seal_sha256=args.seal_sha256,
        unavailable_binding="BP_E3_CRYPTO_PUBLIC_CALLER_POLICY", replacement_type="unit",
        rejection_stage=actual["rejection_stage"], genuine_positive_prerequisite=True,
        original_theorem_remains_in_ambient_kernel_theory=True,
        no_old_caller_proof_objects_loaded=True, formal_dependency_isolation=False,
        semantic_theorem_sensitivity=False, full_C3_acceptance=False,
        scope="Usable ML public theorem-binding/type availability during fresh C3 construction")
    (out / "receipt.json").write_text(json.dumps(result, indent=2, sort_keys=True)+"\n")
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()
