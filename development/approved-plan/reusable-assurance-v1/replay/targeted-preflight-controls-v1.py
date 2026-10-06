#!/usr/bin/env python3
"""Five bounded input-integrity controls, after a genuine positive replay only."""
import argparse, datetime, hashlib, json, os, shutil, subprocess, sys, types
from pathlib import Path
sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
OWN = "development/approved-plan/reusable-assurance-v1"
POSITIVE = "FRESH_C1_FULL7_WITNESS21_ALL_DEFINITIONS_AND_SUPPLIER_AUDITS_COMPLETE_PENDING_ROOT_GATES"

def module(path, name):
    obj = types.ModuleType(name); obj.__file__ = str(path)
    exec(compile(path.read_bytes(), str(path), "exec"), obj.__dict__)
    return obj

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def main():
    p = argparse.ArgumentParser()
    p.add_argument("--source-root", type=Path, required=True)
    p.add_argument("--seal", type=Path, required=True)
    p.add_argument("--seal-sha256", required=True)
    p.add_argument("--positive-run", type=Path, required=True)
    p.add_argument("--output", type=Path, required=True)
    args = p.parse_args()
    root, positive = args.source_root.resolve(), args.positive_run.resolve()
    check = module(HERE / "source-check-v1.py", "c1_control_source_check")
    seal_rel = str(args.seal.resolve().relative_to(root))
    seal = json.loads(check.checked(root, seal_rel, args.seal_sha256).read_text())
    receipt = json.loads((positive / "receipt.json").read_text())
    if (receipt["status"] != POSITIVE or receipt["exit_code"] != 0
        or receipt["timeout"] is not False or receipt["seal_sha256"] != args.seal_sha256
        or receipt["original_target_count"] != 7 or receipt["witness_target_count"] != 21
        or receipt["nonvacuity_case_count"] != 7 or receipt["definition_count"] != 46
        or receipt["proof_started"] is not True or receipt["fresh_GNU_C1_crosscheck"] is not True):
        raise ValueError("Controls require the genuine full positive replay first")
    for relative, key in [
        ("runtime/c1-live-audit-v1.json", "live_audit_sha256"),
        ("inputs.json", "source_set_sha256"), ("c1-proof.log", "c1_log_sha256"),
        ("root-only-supplier/bootstrap.log", "supplier_log_sha256")]:
        if sha(positive / relative) != receipt[key]:
            raise ValueError("Changed genuine positive evidence: " + relative)
    for name, digest in seal["host_inputs"].items(): check.checked(root, name, digest)
    for name, digest in seal["additional_stage_inputs"].items(): check.checked(root, name, digest)
    if check.sha(Path(__file__)) != seal["additional_stage_inputs"][OWN + "/replay/targeted-preflight-controls-v1.py"]:
        raise ValueError("Control source is outside the frozen replay seal")
    supplier = seal["supplier"]
    materializer = module(check.checked(root, supplier["materializer"], supplier["materializer_sha256"]),
                          "c1_control_existing_materializer")
    index = materializer.inputs(root)
    files = {**seal["host_inputs"], **seal["additional_stage_inputs"], **index["extra_files"],
             seal_rel: args.seal_sha256}
    for key in ["seal", "preservation_receipt", "archive_path"]:
        files[index[key]] = index[key.replace("_path", "") + "_sha256"] if key == "archive_path" else index[key + "_sha256"]
    for name, digest in files.items(): check.checked(root, name, digest)
    cases = [
        ("executed-ELF-byte", OWN + "/c1/artifact/compiled-v1/c1.so", "byte"),
        ("modeled-GOT-target", OWN + "/c1/contract/definitions-v1.ml", "got"),
        ("contract-model-pin", OWN + "/generic/e5-definitions-v1.ml", "model"),
        ("missing-supplier-public-interface-dependency", "spec/e2/02-definitions-v1.ml", "missing"),
        ("missing-caller-proof-with-stale-success", OWN + "/c1/composition/proof-attempt2.ml", "stale"),
    ]
    out = args.output.resolve(); out.mkdir(parents=True, exist_ok=False)
    rows = []
    for name, affected, kind in cases:
        case = out / name; clone = case / "source"; clone.mkdir(parents=True)
        for relative in files:
            dest = clone / relative; dest.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(root / relative, dest)
        target = clone / affected
        original_sha = sha(target)
        if kind == "byte":
            data = bytearray(target.read_bytes())
            if data[0x1110] != 0x48: raise ValueError("Unexpected frozen executed ELF byte")
            data[0x1110] ^= 1; target.write_bytes(data)
        elif kind == "got":
            source = target.read_text()
            start = source.index("let c1_got = new_definition")
            finish = source.index(";;", start)
            term = source[start:finish]
            if term.count("word 0x10241840") != 1: raise ValueError("Unexpected frozen GOT literal")
            target.write_text(source[:start] + term.replace("word 0x10241840", "word 0x10241841") + source[finish:])
        elif kind == "model":
            source = target.read_text()
            if source.count("cpl=3") != 1: raise ValueError("Unexpected frozen E5 model literal")
            target.write_text(source.replace("cpl=3", "cpl=0"))
        else:
            target.unlink()
            if kind == "stale":
                stale = clone / OWN / "runs/stale-success"; stale.mkdir(parents=True)
                shutil.copyfile(positive / "receipt.json", stale / "receipt.json")
                shutil.copyfile(positive / "runtime/c1-live-audit-v1.json", stale / "c1-live-audit-v1.json")
        mutation = dict(case=name, affected_input=affected, original_sha256=original_sha,
                        mutated_sha256=sha(target) if target.exists() else None,
                        kind="INPUT_INTEGRITY_PREFLIGHT_ONLY", theorem_sensitivity_claim=False)
        (case / "mutation.json").write_text(json.dumps(mutation, indent=2) + "\n")
        attempt = case / "attempt"
        argv = [sys.executable, str(clone / seal["host_driver"]), "--source-root", str(clone),
                "--seal", str(clone / seal_rel), "--seal-sha256", args.seal_sha256,
                "--output", str(attempt), "--preflight-only"]
        (case / "argv.json").write_text(json.dumps(argv, indent=2) + "\n")
        with (case / "process.log").open("wb") as log:
            process = subprocess.run(argv, stdout=log, stderr=subprocess.STDOUT, timeout=1800)
        actual = json.loads((attempt / "receipt.json").read_text())
        if (process.returncode == 0 or actual["status"] != "FRESH_C1_REPLAY_REJECTED"
            or actual["proof_started"] is not False or actual["caller_acceptance"] is not False
            or affected not in actual["error"] or (attempt / "checker-argv.json").exists()
            or (attempt / "gnu-argv.json").exists()):
            raise ValueError("Negative control did not reject at its exact input boundary: " + name)
        rows.append(dict(mutation, status="OBSERVED_PREFLIGHT_INPUT_REJECTION",
                         exit_code=process.returncode, proof_started=False, GNU_started=False,
                         actual_error=actual["error"], receipt_sha256=sha(attempt / "receipt.json")))
    result = dict(schema="c1-five-targeted-preflight-controls-v1",
        utc=datetime.datetime.now(datetime.timezone.utc).isoformat(), seal_sha256=args.seal_sha256,
        positive_receipt_sha256=sha(positive / "receipt.json"), rows=rows,
        status="FIVE_INPUT_INTEGRITY_CONTROLS_OBSERVED_PENDING_ROOT_GATE",
        formal_single_theorem_sensitivity=False, caller_acceptance=False, full_C1_acceptance=False,
        scope="Hash/closed-source dependency boundaries only; no semantic proof sensitivity demonstrated")
    (out / "receipt.json").write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()
