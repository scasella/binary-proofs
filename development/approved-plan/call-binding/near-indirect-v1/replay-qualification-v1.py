#!/usr/bin/env python3
"""Offline fresh candidate ISA qualification; cannot accept a client proof."""
import argparse
import datetime as dt
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

def dump(path, obj):
    path.write_text(json.dumps(obj, indent=2, sort_keys=True) + "\n")

def safe(name):
    p = PurePosixPath(name)
    if p.is_absolute() or ".." in p.parts or not name:
        raise RuntimeError("Unsafe input path: " + name)
    return name

def checked(root, name, digest):
    p = root / safe(name)
    if not p.is_file() or p.is_symlink() or sha(p) != digest:
        raise RuntimeError("Frozen input mismatch: " + name)
    return p

def replay(args):
    sealpath = checked(ROOT, args.seal, args.sha256)
    seal = json.loads(sealpath.read_text())
    if seal["scope"] != "CANDIDATE_NEAR_INDIRECT_ISA_QUALIFICATION_ONLY":
        raise RuntimeError("This driver cannot accept a routine or client theorem")
    integrity()
    byte_binding = binding()
    ppath = checked(ROOT, seal["preservation_receipt"], seal["preservation_receipt_sha256"])
    pres = json.loads(ppath.read_text())
    archive = checked(ROOT, pres["archive_path"], pres["archive_sha256"])
    if set(seal["files"]).intersection(pres["files"]):
        raise RuntimeError("Candidate would replace a preserved predecessor input")
    for name, digest in seal["files"].items():
        checked(ROOT, name, digest)
    spec = json.loads(checked(ROOT, seal["expected_terms"], seal["files"][seal["expected_terms"]]).read_text())
    expected = [t["name"] for t in spec["decoder_claims"] + spec["executor_claims"]]
    if len(expected) != 53 or len(set(expected)) != 53 or len(spec["definitions"]) != 7:
        raise RuntimeError("Invalid frozen obligation registry")
    stamp = dt.datetime.now(dt.timezone.utc).strftime("%Y%m%dT%H%M%SZ")
    runid = "near-indirect-qualification-closed-" + stamp + "-" + uuid.uuid4().hex[:8]
    out = ROOT / "results/development" / runid
    stage, output = out / "source", out / "checker-output"
    stage.mkdir(parents=True)
    output.mkdir()
    seen = set()
    with tarfile.open(archive, "r:gz") as tar:
        for member in tar.getmembers():
            name = safe(member.name)
            if name in seen or name not in pres["files"] or not member.isfile():
                raise RuntimeError("Unapproved preserved member")
            seen.add(name)
            dest = stage / name
            dest.parent.mkdir(parents=True, exist_ok=True)
            with tar.extractfile(member) as src, dest.open("xb") as dst:
                shutil.copyfileobj(src, dst)
            dest.chmod(member.mode & 0o777)
            checked(stage, name, pres["files"][name])
    if seen != set(pres["files"]):
        raise RuntimeError("Incomplete preserved checking archive")
    sources = dict(pres["files"])
    for name, digest in seal["files"].items():
        dest = stage / name
        dest.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(ROOT / name, dest)
        checked(stage, name, digest)
        sources[name] = digest
    shutil.copy2(sealpath, stage / "qualification-seal.json")
    sources["qualification-seal.json"] = args.sha256
    dump(out / "inputs.json", {"seal_sha256": args.sha256, "files": sources})
    # One guarded include: a parse failure cannot silently fall through to EOF.
    bootstrap = ('use_file_raise_failure := true;;\n'
                 'try loadt "/work/' + seal["driver"] + '"\n'
                 'with e -> prerr_endline(Printexc.to_string e);exit 1;;\n')
    (out / "bootstrap.ml").write_text(bootstrap)
    dump(out / "started.json", {"run_id": runid, "seal_sha256": args.sha256,
                                "readonly_source_with_no_writable_alias": True,
                                "network": "none", "model_candidate_accepted_for_clients": False})
    print(json.dumps({"run_dir": str(out.relative_to(ROOT)), "stage": "fresh_HOL_candidate_qualification"}), flush=True)
    cmd = ["docker", "run", "-i", "--rm", "--pull", "never", "--network", "none",
           "--memory", "2g", "--memory-swap", "2g", "--platform", "linux/arm64",
           "-e", "HOLLIGHT_DIR=/work/third_party/hol-light",
           "-v", str(stage) + ":/work:ro", "-v", str(output) + ":/output:rw",
           "-v", str(stage / seal["decoder"]) + ":/work/third_party/s2n-bignum/x86/proofs/decode.ml:ro",
           "-v", str(stage / seal["executor"]) + ":/work/third_party/s2n-bignum/x86/proofs/x86.ml:ro",
           "-w", "/work/third_party/s2n-bignum", seal["checker_image_id"],
           "/work/third_party/hol-light/ocaml-hol", "-init", "/work/third_party/hol-light/hol.ml",
           "-safe-string", "-I", "/work/third_party/hol-light"]
    start = time.monotonic()
    with (out / "bootstrap.ml").open() as inp, (out / "replay.log").open("w") as log:
        process = subprocess.run(cmd, stdin=inp, stdout=log, stderr=subprocess.STDOUT)
    elapsed = time.monotonic() - start
    apath = output / "qualification-audit.json"
    audit = json.loads(apath.read_text()) if apath.exists() else None
    rows = [] if audit is None else audit["theorems"]
    names = [t["name"] for t in rows]
    unchanged = all((stage / n).is_file() and sha(stage / n) == h for n, h in sources.items())
    canonical = True
    try:
        integrity()
        checked(ROOT, args.seal, args.sha256)
        for n, h in seal["files"].items():
            checked(ROOT, n, h)
    except Exception:
        canonical = False
    logtext = re.sub(r"\x1b\[[0-?]*[ -/]*[@-~]", "", (out / "replay.log").read_text(errors="replace"))
    passed = (process.returncode == 0 and unchanged and canonical and audit is not None
              and audit["expanded_definition_count"] == 7
              and len(names) == 53 and set(names) == set(expected)
              and all(t["hypothesis_count"] == 0 and t["new_axioms"] == 0
                      and t["conclusion_matches_expected"] is True for t in rows)
              and re.search(r"(?m)^\s*(?:#\s*)?(?:Error|Exception):", logtext) is None)
    receipt = {"experiment_id": seal["experiment_id"], "run_id": runid,
               "status": "PASS_FRESH_CANDIDATE_ISA_QUALIFICATION" if passed else "FAIL_FRESH_CANDIDATE_ISA_QUALIFICATION",
               "process_exit": process.returncode, "elapsed_checking_seconds": elapsed,
               "seal_sha256": args.sha256, "source_set_sha256": sha(out / "inputs.json"),
               "source_unchanged": unchanged, "canonical_inputs_unchanged": canonical,
               "readonly_source_with_no_writable_alias": True, "network": "none",
               "model_candidate_accepted_for_clients": False,
               "callee_chains_requalified": False, "client_ABI_access_qualification_complete": False,
               "R1_pass": False, "core_complete": False, "human_review": "PENDING",
               "backend_files": {seal["decoder"]: seal["files"][seal["decoder"]],
                                 seal["executor"]: seal["files"][seal["executor"]]},
               "trust_assumption_ids": seal["trust_assumption_ids"],
               "artifact_binding": byte_binding, "kernel_audit": audit,
               "raw_log": str((out / "replay.log").relative_to(ROOT)),
               "scope": "Four generic near-memory executor/conservative lemmas;49 finite decoder facts;7 exact model definitions. This is not a proof of a caller or a library routine.",
               "peak_memory_bytes": None, "peak_memory_null_reason": "Not observed for checker process",
               "model_identifier": None, "model_identifier_null_reason": "Not exposed by execution runtime",
               "token_usage": None, "token_usage_null_reason": "Not exposed by execution runtime",
               "billing_cost": None, "billing_cost_null_reason": "Not exposed by execution runtime"}
    dump(out / "receipt.json", receipt)
    print(json.dumps({"status": receipt["status"], "run_dir": str(out.relative_to(ROOT))}), flush=True)
    return 0 if passed else 1

if __name__ == "__main__":
    p = argparse.ArgumentParser()
    p.add_argument("--seal", required=True)
    p.add_argument("--sha256", required=True)
    args = p.parse_args()
    try:
        raise SystemExit(replay(args))
    except Exception as e:
        print(str(e), file=sys.stderr)
        raise SystemExit(1)
