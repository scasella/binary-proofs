#!/usr/bin/env python3
"""Fresh read-only exact-term full-image witness component replay.

Requires an explicit expected seal digest. Stored PASS records are never
inputs. An isolated source closure is reconstructed from the unchanged V2
preservation archive and the sealed assurance-V3 supplement. No source has a
writable mount alias. This component cannot accept a routine milestone.
"""
import argparse
import datetime
import hashlib
import importlib.util
import json
from pathlib import Path, PurePosixPath
import shutil
import subprocess
import tarfile
import time
import uuid

ROOT = Path(__file__).resolve().parents[4]
HERE = Path(__file__).resolve().parent


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def local(name):
    path = PurePosixPath(name)
    if path.is_absolute() or ".." in path.parts or not path.parts:
        raise ValueError("Unsafe sealed relative path")
    return ROOT / path


def check(root, name, digest):
    relative = local(name).relative_to(ROOT)
    path = root / relative
    if not path.is_file() or path.is_symlink() or sha(path) != digest:
        raise ValueError("Sealed input drift: " + name)
    return path


def dump(path, value):
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")


def replay(args):
    seal_path = check(ROOT, args.seal, args.sha256)
    seal = json.loads(seal_path.read_text())
    if seal["scope"] != "CLEANSE_FULL_IMAGE_INITIAL_WITNESS_COMPONENT_ONLY":
        raise ValueError("Incorrect witness-component scope")
    base_path = check(ROOT, seal["base_seal"], seal["base_seal_sha256"])
    base = json.loads(base_path.read_text())
    preservation_path = check(ROOT, base["preservation_receipt"], base["preservation_receipt_sha256"])
    preservation = json.loads(preservation_path.read_text())
    archive = check(ROOT, preservation["archive_path"], preservation["archive_sha256"])
    files = dict(preservation["files"])
    if files.keys() & base["files"].keys():
        raise ValueError("Assurance supplement overwrites preserved source")
    files.update(base["files"])
    if files.keys() & seal["files"].keys():
        raise ValueError("Witness supplement overwrites preceding source")
    files.update(seal["files"])
    for name, digest in base["files"].items():
        check(ROOT, name, digest)
    for name, digest in seal["files"].items():
        check(ROOT, name, digest)
    stamp = datetime.datetime.now(datetime.timezone.utc).strftime("%Y%m%dT%H%M%SZ")
    run = ROOT / "results/development" / ("cleanse-loaded-witness-closed-" + stamp + "-" + uuid.uuid4().hex[:8])
    source = run / "source"
    output = run / "checker-output"
    source.mkdir(parents=True)
    output.mkdir()
    seen = set()
    with tarfile.open(archive, "r:gz") as saved:
        for member in saved.getmembers():
            name = str(local(member.name).relative_to(ROOT))
            if name in seen or name not in preservation["files"] or not member.isfile():
                raise ValueError("Unexpected preservation archive member")
            seen.add(name)
            destination = source / name
            destination.parent.mkdir(parents=True, exist_ok=True)
            with saved.extractfile(member) as inp, destination.open("xb") as out:
                shutil.copyfileobj(inp, out)
            destination.chmod(member.mode & 0o777)
            check(source, name, preservation["files"][name])
    if seen != set(preservation["files"]):
        raise ValueError("Incomplete preserved source closure")
    for supplement in (base["files"], seal["files"]):
        for name, digest in supplement.items():
            destination = source / name
            destination.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(ROOT / name, destination)
            check(source, name, digest)
    dump(run / "inputs.json", {"seal_sha256": args.sha256, "files": files})
    spec = importlib.util.spec_from_file_location("full_image_acquisition", source / seal["acquisition_program"])
    acquisition = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(acquisition)
    acquired = acquisition.acquire()
    dump(run / "acquisition.json", acquired)
    cross = subprocess.run([__import__("sys").executable,
        str(source / "development/approved-plan/loaded-witness/full-binding/crosscheck-image-clauses-v1.py")],
        cwd=source, capture_output=True,text=True)
    (run / "image-crosscheck.stdout").write_text(cross.stdout)
    (run / "image-crosscheck.stderr").write_text(cross.stderr)
    if cross.returncode != 0:
        raise ValueError("Full image source clauses rejected")
    cross_record=json.loads(cross.stdout)
    if cross_record["status"] != "PASS_FORMAL_SOURCE_IMAGE_INTERVAL_CROSSCHECK":
        raise ValueError("Incorrect image crosscheck scope")
    # Source declarations, frozen literal expected terms and recipes all come
    # from the closed read-only source tree, with writable output elsewhere.
    driver = "use_file_raise_failure := true;;\nlet clw_initial_axioms = axioms();;\n"
    driver += 'let clw_guard f = try f() with e -> prerr_endline(Printexc.to_string e); exit 1;;\n'
    for name in seal["load_order"]:
        if name not in files:
            raise ValueError("Load path absent from sealed closure: " + name)
        driver += "clw_guard(fun () -> loadt " + json.dumps("/work/" + name) + ");;\n"
    driver += '''clw_guard(fun () ->
 let out = open_out "/output/cleanse-witness-audit.json" in
 output_string out ("{\\\"status\\\":\\\"PASS_CLEANSE_INITIAL_WITNESSES\\\",\\\"full_O1_pass\\\":false,\\\"human_review\\\":\\\"PENDING\\\",\\\"expanded_definition_count\\\":41,\\\"theorems\\\":[" ^ String.concat "," clw_audit_rows ^ "]}\\n");
 close_out out);;
clw_guard(fun () -> if not(clw_axioms_unchanged()) then failwith "new axioms");;
print_endline "CLEANSE_LOADED_WITNESS_FRESH_REPLAY_COMPLETED";;
exit 0;;
'''
    (run / "input.ml").write_text(driver)
    command = ["docker", "run", "-i", "--rm", "--pull", "never", "--network", "none",
               "--memory", "2g", "--memory-swap", "2g", "--platform", "linux/arm64", "-e", "HOLLIGHT_DIR=/work/third_party/hol-light",
               "-v", str(source) + ":/work:ro", "-v", str(output) + ":/output:rw",
               "-v", str(source / "proofs/model-extension/decode.ml") +
                   ":/work/third_party/s2n-bignum/x86/proofs/decode.ml:ro",
               "-w", "/work/third_party/s2n-bignum", base["checker_image_id"],
               "/work/third_party/hol-light/ocaml-hol", "-init", "/work/third_party/hol-light/hol.ml",
               "-safe-string", "-I", "/work/third_party/hol-light"]
    print(run, flush=True)
    start = time.monotonic()
    with (run / "input.ml").open("rb") as inp, (run / "replay.log").open("wb") as log:
        result = subprocess.run(command, stdin=inp, stdout=log, stderr=subprocess.STDOUT)
    audit_path = output / "cleanse-witness-audit.json"
    audit = json.loads(audit_path.read_text()) if audit_path.exists() else None
    unchanged = all(check(source, name, digest) for name, digest in files.items())
    canonical = all(check(ROOT, name, digest) for name, digest in
                    {**base["files"], **seal["files"]}.items())
    names = [row["name"] for row in audit["theorems"]] if audit else []
    passed = (result.returncode == 0 and audit is not None and
              audit["expanded_definition_count"] == 41 and
              len(names) == len(set(names)) == len(seal["expected_theorems"]) and
              set(names) == set(seal["expected_theorems"]) and
              all(row["hypothesis_count"] == 0 and row["new_axioms"] == 0 and
                  row["conclusion_matches_expected"] for row in audit["theorems"]))
    record = {"status": "PASS_FRESH_CLEANSE_FULL_IMAGE_INITIAL_WITNESSES" if passed else
                        "FAIL_FRESH_CLEANSE_FULL_IMAGE_INITIAL_WITNESSES", "process_exit": result.returncode,
              "elapsed_seconds": time.monotonic() - start, "seal_sha256": args.sha256,
              "full_O1_pass": False, "human_review": "PENDING", "kernel_audit": audit,
              "target_function_executed":False, "routine_behavior_property":False,
              "destination_output_read_premise":False, "initial_image_only":True,
              "abstract_canonical_edges_are_linux_user_maps":False,
              "whole_file_map_acquisition": acquired, "image_clause_crosscheck":cross_record, "source_unchanged": bool(unchanged),
              "canonical_inputs_unchanged": bool(canonical), "source_file_count": len(files),
              "readonly_source_with_no_writable_alias": True, "network": "none",
              "raw_log": str((run / "replay.log").relative_to(ROOT))}
    dump(run / "receipt.json", record)
    print(json.dumps({k: v for k, v in record.items() if k not in
                      ("kernel_audit", "whole_file_map_acquisition")}), flush=True)
    return 0 if passed else 1


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--seal", required=True)
    parser.add_argument("--sha256", required=True)
    args = parser.parse_args()
    try:
        raise SystemExit(replay(args))
    except (OSError, ValueError, KeyError) as e:
        raise SystemExit("Full image witness replay rejected: " + str(e))
