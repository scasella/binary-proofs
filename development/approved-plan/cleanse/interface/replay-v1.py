#!/usr/bin/env python3
"""Fresh E2 OPENSSL_cleanse whole-callable proof, with copy-control preflight.

Saved receipts and raw logs never discharge a proof obligation. Preflight
validates inputs and acquisition only; it starts no HOL or target routine.
"""
import argparse
import datetime as dt
import importlib.util
import json
from pathlib import Path, PurePosixPath
import re
import shutil
import subprocess
import sys
import tarfile
import time
import uuid

ROOT = Path(__file__).resolve().parents[4]
sys.path.insert(0, str(ROOT / "scripts"))
from check import integrity, binding, sha


def dump(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")


def safe(name):
    path = PurePosixPath(name)
    if path.is_absolute() or ".." in path.parts or not path.parts:
        raise ValueError("Unsafe frozen input path: " + name)
    return name


def checked(root, name, digest):
    path = root / safe(name)
    if not path.is_file() or path.is_symlink() or sha(path) != digest:
        raise ValueError("Frozen input mismatch or missing dependency: " + name)
    return path


def module_at(root, name):
    spec = importlib.util.spec_from_file_location("cleanse_boundary_" + uuid.uuid4().hex,
                                                  root / safe(name))
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def boundary_checks(root, seal):
    acquired = module_at(root, seal["acquisition_program"]).acquire()
    image = module_at(root, seal["image_crosscheck_program"]).crosscheck()
    registry = json.loads((root / seal["decode_registry"]).read_text())["sites"]
    formal = (root / seal["decode_site_source"]).read_text()
    pairs = [(int(a), int(b)) for a, b in re.findall(
        r"off\s*=\s*(\d+)\s*/\\\s*len\s*=\s*(\d+)", formal)]
    if pairs != [(r["offset"], r["length"]) for r in registry]:
        raise ValueError("Registered decode lengths disagree with formal site clauses")
    covered = set()
    for offset, width in pairs:
        if width <= 0 or offset < 0 or offset + width > 97:
            raise ValueError("Decoded instruction interval lies outside bound code")
        span = set(range(offset, offset + width))
        if covered & span:
            raise ValueError("Registered decoded instruction intervals overlap")
        covered |= span
    if covered != set(range(33)) | set(range(48, 97)) or len(pairs) != 25:
        raise ValueError("Expected 82 covered bytes / 15 padding bytes / 25 sites")
    if acquired["code_bytes"] != 97 or acquired["code_loaded_address"] != 0x102417d0:
        raise ValueError("Wrong whole-file cleanse binding")
    return {"whole_file_map_acquisition": acquired, "image_clause_crosscheck": image,
            "declared_code_bytes": 97, "registered_site_count": 25,
            "unique_covered_instruction_bytes": 82, "padding_bytes": 15,
            "covered_intervals": [[0, 33], [48, 97]],
            "reachability": "proved by fresh ALL_LENGTH covered-run invariant; registry alone is not reachability"}


def preflight(args):
    stamp = dt.datetime.now(dt.timezone.utc).strftime("%Y%m%dT%H%M%SZ")
    run = ROOT / "results/development" / ("crypto-loop-cleanse-preflight-" + stamp + "-" + uuid.uuid4().hex[:8])
    ledger = {"preflight_only": True, "proof_started": False,
              "target_routine_executed": False, "full_O1_pass": False,
              "full_O2_pass": False, "seal": args.seal, "seal_sha256": args.sha256}
    try:
        seal = json.loads(checked(ROOT, args.seal, args.sha256).read_text())
        if seal["scope"] != "E2_CLEANSE_ORIGINAL_MODEL_WHOLE_CALLABLE":
            raise ValueError("Unexpected routine proof scope")
        pres = json.loads(checked(ROOT, seal["preservation_receipt"],
                                  seal["preservation_receipt_sha256"]).read_text())
        archive = checked(ROOT, pres["archive_path"], pres["archive_sha256"])
        if set(pres["files"]) & set(seal["files"]):
            raise ValueError("Successor supplement overwrites preserved source")
        for name, digest in seal["files"].items():
            checked(ROOT, name, digest)
        lock = integrity()
        if lock["checker_image_id"] != seal["checker_image_id"]:
            raise ValueError("Original checker backend pin mismatch")
        bound = binding()  # GNU extraction tooling; never HOL or target execution.
        boundaries = boundary_checks(ROOT, seal)
        ledger.update(status="PASS_PREFLIGHT_NOT_PROOF", canonical_E1_integrity=True,
                      source_file_count=len(pres["files"]) + len(seal["files"]),
                      artifact_binding=bound, **boundaries)
        dump(run / "ledger.json", ledger)
        if args.preflight:
            print(json.dumps({"status": ledger["status"], "preflight_only": True,
                              "proof_started": False, "target_routine_executed": False,
                              "ledger": str((run / "ledger.json").relative_to(ROOT))}), flush=True)
        return seal, pres, archive, ledger, run
    except Exception as exc:
        ledger.update(status="FAIL_PREFLIGHT_NOT_PROOF", error=str(exc))
        dump(run / "ledger.json", ledger)
        print(json.dumps({"status": ledger["status"], "error": str(exc),
                          "preflight_only": True, "proof_started": False,
                          "target_routine_executed": False,
                          "ledger": str((run / "ledger.json").relative_to(ROOT))}), flush=True)
        raise


def replay(args):
    seal, pres, archive, boundary, pre = preflight(args)
    if args.preflight:
        return 0
    stamp = dt.datetime.now(dt.timezone.utc).strftime("%Y%m%dT%H%M%SZ")
    runid = "crypto-loop-cleanse-routine-closed-" + stamp + "-" + uuid.uuid4().hex[:8]
    run = ROOT / "results/development" / runid
    stage, output = run / "source", run / "checker-output"
    stage.mkdir(parents=True); output.mkdir()
    seen = set()
    with tarfile.open(archive, "r:gz") as saved:
        for member in saved.getmembers():
            name = safe(member.name)
            if name in seen or name not in pres["files"] or not member.isfile():
                raise ValueError("Unexpected preservation archive member: " + name)
            seen.add(name)
            dest = stage / name; dest.parent.mkdir(parents=True, exist_ok=True)
            with saved.extractfile(member) as inp, dest.open("xb") as out:
                shutil.copyfileobj(inp, out)
            dest.chmod(member.mode & 0o777)
            checked(stage, name, pres["files"][name])
    if seen != set(pres["files"]):
        raise ValueError("Incomplete predecessor archive")
    sources = dict(pres["files"])
    for name, digest in seal["files"].items():
        dest = stage / name; dest.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(ROOT / name, dest); checked(stage, name, digest); sources[name] = digest
    dump(run / "inputs.json", {"seal_sha256": args.sha256, "files": sources})
    dump(run / "boundary-checks.json", boundary_checks(stage, seal))
    shutil.copy2(stage / seal["driver"], run / "input.ml")
    command = ["docker", "run", "-i", "--rm", "--pull", "never", "--network", "none",
               "--memory", "2g", "--memory-swap", "2g", "--platform", "linux/arm64",
               "-e", "HOLLIGHT_DIR=/work/third_party/hol-light",
               "-v", str(stage) + ":/work:ro", "-v", str(output) + ":/output:rw",
               "-v", str(stage / "proofs/model-extension/decode.ml") +
                   ":/work/third_party/s2n-bignum/x86/proofs/decode.ml:ro",
               "-w", "/work/third_party/s2n-bignum", seal["checker_image_id"],
               "/work/third_party/hol-light/ocaml-hol", "-init", "/work/third_party/hol-light/hol.ml",
               "-safe-string", "-I", "/work/third_party/hol-light"]
    dump(run / "started.json", {"proof_started": True, "target_routine_executed": False,
                                "network": "none", "readonly_source_no_writable_alias": True,
                                "command": command, "preflight_ledger": str((pre / "ledger.json").relative_to(ROOT))})
    print(json.dumps({"run_dir": str(run.relative_to(ROOT)), "stage": "starting_fresh_HOL"}), flush=True)
    start = time.monotonic()
    with (run / "input.ml").open("rb") as inp, (run / "replay.log").open("wb") as log:
        result = subprocess.run(command, stdin=inp, stdout=log, stderr=subprocess.STDOUT)
    elapsed = time.monotonic() - start
    audits = {}
    for name in ("functional", "access", "interface", "supplement"):
        path = output / (name + ".json")
        audits[name] = json.loads(path.read_text()) if path.exists() else None
    rows = [r for a in audits.values() if a for r in a["theorems"]]
    definitions = [] if not audits["supplement"] else audits["supplement"]["expanded_definitions"]
    names = [r["name"] for r in rows]; defnames = [r["name"] for r in definitions]
    unchanged = all(checked(stage, n, h) for n, h in sources.items())
    canonical = True
    try:
        integrity(); checked(ROOT, args.seal, args.sha256)
        for n, h in seal["files"].items(): checked(ROOT, n, h)
    except Exception: canonical = False
    log = re.sub(r"\x1b\[[0-?]*[ -/]*[@-~]", "", (run / "replay.log").read_text(errors="replace"))
    passed = bool(result.returncode == 0 and all(audits.values()) and unchanged and canonical and
                  len(names) == len(set(names)) == len(seal["expected_theorems"]) and
                  set(names) == set(seal["expected_theorems"]) and
                  all(r["hypothesis_count"] == 0 and r["new_axioms"] == 0 and
                      r["conclusion_matches_expected"] is True for r in rows) and
                  len(defnames) == len(set(defnames)) == seal["expected_definition_count"] and
                  all(r["hypothesis_count"] == 0 and r["new_axioms"] == 0 and
                      r["conclusion_matches_expected"] is True for r in definitions) and
                  audits["supplement"]["all_equation_check_count"] == 97 and
                  "CLEANSE_AGGREGATE_FRESH_ACCEPTED" in log and
                  re.search(r"(?m)^\s*(?:#\s*)?(?:Error|Exception):", log) is None)
    receipt = {"status": "PASS_FRESH_E2_CLEANSE_WHOLE_CALLABLE" if passed else
                         "FAIL_FRESH_E2_CLEANSE_WHOLE_CALLABLE", "experiment_id": seal["experiment_id"],
               "process_exit": result.returncode, "elapsed_checking_seconds": elapsed,
               "construction_intervals": seal["construction_intervals"],
               "full_O1_pass": passed, "full_O2_pass": False,
               "properties": {k: passed for k in ("functionality", "access_safety", "termination", "ABI")},
               "kernel_audit": {"theorems": rows, "expanded_definitions": definitions,
                                "theorem_count": len(rows), "expanded_definition_count": len(definitions)},
               "artifact_binding": boundary["artifact_binding"], "boundary_checks": boundary_checks(stage, seal),
               "same_pre_witnesses": True if passed else False, "human_review": "PENDING",
               "physical_ISA_fidelity": "EXPLICIT_TRUST_BOUNDARY_OF_PINNED_MODELS_AND_V5_SCALAR_EFFECTS",
               "initial_image_only": True, "final_initialized_RW_map_preservation_required": False,
               "proof_started": True, "target_routine_executed": False, "source_unchanged": bool(unchanged),
               "canonical_inputs_unchanged": canonical, "readonly_source_with_no_writable_alias": True,
               "network": "none", "seal_sha256": args.sha256, "source_set_sha256": sha(run / "inputs.json"),
               "raw_log": str((run / "replay.log").relative_to(ROOT)), "model_identifier": None,
               "model_identifier_null_reason": "Not exposed by execution runtime", "token_usage": None,
               "token_usage_null_reason": "Not exposed by execution runtime", "billing_cost": None,
               "billing_cost_null_reason": "Not exposed by execution runtime"}
    dump(run / "receipt.json", receipt)
    print(json.dumps({"status": receipt["status"], "run_dir": str(run.relative_to(ROOT))}), flush=True)
    return 0 if passed else 1


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--seal", required=True); parser.add_argument("--sha256", required=True)
    parser.add_argument("--preflight", action="store_true")
    try: raise SystemExit(replay(parser.parse_args()))
    except Exception as exc: raise SystemExit("Cleanse aggregate replay rejected: " + str(exc))
