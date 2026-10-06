#!/usr/bin/env python3
"""Minimal C2 adaptation of the existing fresh E5 replay and opaque supplier APIs.

Actual full7/definition audits are necessary. Acceptance remains a root gate.
"""
import argparse, datetime, json, os, re, shutil, subprocess, sys, threading, time, types
from pathlib import Path
sys.dont_write_bytecode = True
os.environ["PYTHONDONTWRITEBYTECODE"] = "1"
HERE = Path(__file__).resolve().parent
GNU_IMAGE_ID = "sha256:444f775e6378c2e5523f29ceb8bbb184442277ed1114e6d37d873a7f127dfc26"
ROOT = HERE.parents[3]
OWN = "development/approved-plan/reusable-assurance-v1"
SUCCESSOR = "development/approved-plan/reusable-assurance-c2-v1"
MARKER = b"E3_OPAQUE_CALLEE_INTERFACE_LOADED_AND_LIVE_AUDITED"
AUDIT_MARKER = "C2_FRESH_ALL_FROZEN_TARGETS_WITNESSES_ALL_DEFINITIONS_EXPANDED_HYP0_FREES0_STANDARD3_LIVE_AUDIT_PASS"
OUT = None
CONTEXT = dict(proof_started=False, target_routine_executed=False, caller_acceptance=False)

def module(path, name):
    m = types.ModuleType(name)
    m.__file__ = str(path)
    exec(compile(path.read_bytes(), str(path), "exec"), m.__dict__)
    return m

def save(name, value):
    (OUT / name).write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")

def main():
    global OUT
    p = argparse.ArgumentParser()
    p.add_argument("--source-root", type=Path, default=ROOT)
    p.add_argument("--seal", type=Path, required=True)
    p.add_argument("--seal-sha256", required=True)
    p.add_argument("--output", type=Path)
    p.add_argument("--preflight-only", action="store_true")
    p.add_argument("--unavailable-interface-binding-probe", action="store_true")
    p.add_argument("--genuine-positive-run", type=Path)
    p.add_argument("--timeout-seconds", type=int, default=1800)
    args = p.parse_args()
    if not 0 < args.timeout_seconds <= 1800:
        raise ValueError("External replay limit must be 1..1800 seconds")
    root = args.source_root.resolve()
    check = module(HERE / "source-check-v1.py", "c2_fresh_source_check")
    seal_path = args.seal.resolve()
    seal_path.relative_to(root)
    check.checked(root, str(seal_path.relative_to(root)), args.seal_sha256)
    seal = json.loads(seal_path.read_text())
    if seal["schema"] != "c2-fresh-closed-replay-seal-v1":
        raise ValueError("Wrong fresh C2 scope")
    if check.sha(Path(__file__)) != seal["driver_sha256"]:
        raise ValueError("Driver differs from the externally pinned seal")
    if seal["resources"] != dict(deadline_seconds=1800, cpu_count=1,
                                 memory_bytes=3*1024**3, swap_limit_bytes=3*1024**3):
        raise ValueError("Frozen CPU/memory/deadline resource limits differ")
    rid = datetime.datetime.now(datetime.timezone.utc).strftime("%Y%m%dT%H%M%SZ") + "-" + os.urandom(4).hex()
    OUT = (args.output or root / SUCCESSOR / "runs" / ("c2-fresh-" + rid)).resolve()
    OUT.mkdir(parents=True, exist_ok=False)
    started = time.monotonic()
    def remaining():
        value = args.timeout_seconds - (time.monotonic() - started)
        if value <= 0: raise TimeoutError("External C2 replay deadline exhausted")
        return value
    CONTEXT.update(run_id=rid, deadline_seconds=args.timeout_seconds,
        unavailable_interface_binding_probe=args.unavailable_interface_binding_probe)
    if args.unavailable_interface_binding_probe:
        if args.preflight_only or args.genuine_positive_run is None:
            raise ValueError("Construction probe requires actual fresh mode and a genuine positive")
        positive_gate = module(check.checked(root, seal["root_gate"],
            seal["additional_stage_inputs"][seal["root_gate"]]), "probe_positive_gate")
        result = positive_gate.gate(argparse.Namespace(source_root=root, seal=args.seal,
            seal_sha256=args.seal_sha256, positive_run=args.genuine_positive_run, controls=None))
        if result["positive_accepted"] is not True:
            raise ValueError("Construction probe requires independently gated positive")
        CONTEXT["positive_receipt_sha256"] = check.sha(args.genuine_positive_run / "receipt.json")
    for name, digest in seal["host_inputs"].items():
        check.checked(root, name, digest)
    for name, digest in seal["additional_stage_inputs"].items():
        check.checked(root, name, digest)
    check.anchors(root)
    if check.load_graph(root, seal["loader"]) != seal["graph"]:
        raise ValueError("Closed C2 load graph changed")
    check.validate_development_graph(root, seal)
    registry = json.loads((root / seal["expected_registry"]).read_text())
    mapping = json.loads(check.checked(root, seal["theorem_map"]).read_text())
    if registry != check.registry(root, mapping, seal["graph"]):
        raise ValueError("Changed original target, witness, or transitive definition registry")
    generator = module(root / SUCCESSOR / "replay/generate-audit-v1.py", "c2_fresh_audit_generator")
    if (root / seal["audit"]).read_text() != generator.generate(registry):
        raise ValueError("Frozen actual-object audit differs from canonical source generator")
    if (seal["witness_target_count"],seal["nonvacuity_case_count"],seal["all_new_definition_count"]) != (registry["witness_target_count"],registry["nonvacuity_case_count"],len(registry["definitions"])):
        raise ValueError("Incomplete frozen witness/definition boundary")
    foundation = module(check.checked(root, seal["baseline_driver"], seal["baseline_driver_sha256"]),
                        "c2_existing_fresh_replay_guards")
    supplier = seal["supplier"]
    materializer = module(check.checked(root, supplier["materializer"], supplier["materializer_sha256"]),
                          "c2_existing_opaque_materializer")
    materializer.inputs(root)
    if args.preflight_only:
        save("receipt.json", dict(status="STRICT_C2_SOURCE_PREFLIGHT_NOT_PROOF",
             proof_started=False, caller_acceptance=False, target_routine_executed=False,
             full_C2_targets=registry["original_target_count"], witness_targets=registry["witness_target_count"], nonvacuity_cases=registry["nonvacuity_case_count"], definitions=len(registry["definitions"]),
             GNU_or_HOL_started=False, seal_sha256=args.seal_sha256))
        return 0
    stage, runtime, private = OUT / "source", OUT / "runtime", OUT / "root-only-supplier"
    runtime.mkdir(); private.mkdir()
    materializer.materialize(root, stage)
    index = json.loads(check.checked(root, supplier["index"], supplier["index_sha256"]).read_text())
    if len(index["source_files"]) != supplier["source_count"] or supplier["source_count"] != 4534:
        raise ValueError("Existing opaque supplier source-index count mismatch")
    sources = dict(index["source_files"])
    sources[index["seal"]] = index["seal_sha256"]
    for name, digest in seal["additional_stage_inputs"].items():
        if name in sources and sources[name] != digest:
            raise ValueError("C2 source conflicts with preserved supplier file: " + name)
        dest = stage / name
        dest.parent.mkdir(parents=True, exist_ok=True)
        if not dest.exists(): shutil.copyfile(check.checked(root, name, digest), dest)
        check.checked(stage, name, digest)
        sources[name] = digest
    foundation.lock_stage(stage)
    def guard():
        foundation.guard_stage_permissions(stage)
        actual = {str(x.relative_to(stage)) for x in stage.rglob("*") if x.is_file()}
        if actual != set(sources): raise ValueError("Added/missing source in complete staged tree")
        for name, digest in sources.items(): check.checked(stage, name, digest)
        check.anchors(stage)
        if check.load_graph(stage, seal["loader"]) != seal["graph"]:
            raise ValueError("Staged closed C2 load graph changed")
    guard()
    save("inputs.json", dict(seal_sha256=args.seal_sha256, files=sources, closed_load_graph=seal["graph"]))
    image = seal["checker_image_id"]
    inspected_image = subprocess.run(["docker", "image", "inspect", image, "--format", "{{.Id}}"],
                                     capture_output=True, text=True, timeout=min(30, remaining()))
    if inspected_image.returncode or inspected_image.stdout.strip() != image:
        raise ValueError("Pinned local checker image unavailable/changed")
    gnu_image = seal["gnu_image_id"]
    if gnu_image != GNU_IMAGE_ID:
        raise ValueError("Pinned GNU AMD64 image differs from the artifact compiler image")
    inspected_gnu_image = subprocess.run(
        ["docker", "image", "inspect", gnu_image, "--format", "{{.Id}}"],
        capture_output=True, text=True, timeout=min(30, remaining()))
    save("gnu-image-inspect.json", dict(expected_image_id=gnu_image,
         actual_image_id=inspected_gnu_image.stdout.strip(),
         return_code=inspected_gnu_image.returncode, platform="linux/amd64",
         freshly_checked=True))
    if inspected_gnu_image.returncode or inspected_gnu_image.stdout.strip() != gnu_image:
        raise ValueError("Pinned local GNU AMD64 image unavailable/changed")
    gnu = runtime / "gnu"; gnu.mkdir()
    elf_input = stage / SUCCESSOR / "artifact/compiled-v1/c2.so"
    gnu_cidfile = OUT / "gnu-container.cid"
    gnu_argv = ["docker", "run", "--rm", "--cidfile", str(gnu_cidfile), "--pull", "never", "--network", "none",
        "--cpus", "1", "--memory", "3g", "--memory-swap", "3g", "--platform", "linux/amd64",
        "-v", str(elf_input) + ":/input/c2.so:ro", "-v", str(gnu) + ":/output:rw",
        gnu_image, "/bin/sh", "-ec",
        "objcopy -O binary --only-section=.text /input/c2.so /output/gnu-text.bin\n"
        "objcopy -O binary --only-section=.plt /input/c2.so /output/gnu-plt.bin\n"
        "objdump -d -w -Mintel /input/c2.so > /output/disassembly.txt\n"
        "readelf -W -a /input/c2.so > /output/readelf.txt"]
    save("gnu-argv.json", gnu_argv)
    with (OUT / "gnu-process.log").open("wb") as log:
        try:
            gnu_process = subprocess.run(gnu_argv, stdout=log, stderr=subprocess.STDOUT,
                                         timeout=remaining())
        except subprocess.TimeoutExpired:
            if gnu_cidfile.exists():
                subprocess.run(["docker", "kill", gnu_cidfile.read_text().strip()],
                               stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, timeout=30)
            raise
    if gnu_process.returncode: raise ValueError("Fresh GNU byte/image crosscheck command failed")
    crosscheck = module(stage / seal["artifact_crosscheck"], "c2_fresh_image_crosscheck")
    save("c2-image-crosscheck.json", crosscheck.crosscheck(stage, gnu))
    cidfile = OUT / "container.cid"
    argv = ["docker", "run", "-i", "--cidfile", str(cidfile), "--pull", "never",
        "--network", "none", "--cpus", "1", "--memory", "3g", "--memory-swap", "3g",
        "--platform", "linux/arm64", "-e", "HOLLIGHT_DIR=/work/third_party/hol-light",
        "-v", str(stage) + ":/work:ro", "-v", str(runtime) + ":/output:rw",
        "-v", str(stage / supplier["decoder"]) + ":/work/third_party/s2n-bignum/x86/proofs/decode.ml:ro",
        "-v", str(stage / supplier["executor"]) + ":/work/third_party/s2n-bignum/x86/proofs/x86.ml:ro",
        "-v", str(stage / OWN) + ":/reuse:ro",
        "-v", str(stage / check.PUBLIC) + ":/client-public:ro",
        "-w", "/work/third_party/s2n-bignum", image,
        "/work/third_party/hol-light/ocaml-hol", "-init", "/work/third_party/hol-light/hol.ml",
        "-safe-string", "-I", "/work/third_party/hol-light"]
    save("checker-argv.json", argv)
    save("invocation.json", dict(run_id=rid, kind=("FRESH_C2_INTERFACE_BINDING_CONSTRUCTION_PROBE"
         if args.unavailable_interface_binding_probe else "FRESH_CLOSED_C2_PROOF_ATTEMPT"),
         resources=seal["resources"], actual_deadline_seconds=args.timeout_seconds,
         network="none", host_stage_read_only=True, former_caller_proof_loader=False,
         seal_sha256=args.seal_sha256, caller_acceptance=False, target_routine_executed=False,
         model=None, tokens=None, cost=None))
    print(json.dumps(dict(status="FRESH_C2_CHECK_STARTING_NOT_ACCEPTANCE", output=str(OUT))), flush=True)
    proc = subprocess.Popen(argv, stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT, bufsize=0)
    CONTEXT["proof_started"] = True
    checker_start = time.monotonic(); supplier_finished = None
    timed_out = threading.Event()
    def stop():
        if proc.poll() is None:
            timed_out.set()
            try:
                if cidfile.exists():
                    subprocess.run(["docker", "kill", cidfile.read_text().strip()],
                                   stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, timeout=30)
            finally:
                if proc.poll() is None: proc.terminate()
    timer = threading.Timer(remaining(), stop); timer.daemon = True; timer.start()
    bootstrap = ('use_file_raise_failure := true;;\n'
        'if axioms()<>[INFINITY_AX;SELECT_AX;ETA_AX] then exit 1;;\n'
        'let fresh_initial_axioms=axioms();;\n'
        'needs "/work/' + SUCCESSOR + '/replay/ambient-snapshot-v1.ml";;\n'
        'c2_development_ambient_snapshot "before-supplier" "/output/ambient-before-supplier-v1.json";;\n'
        'let fresh_supplier_cpu_start=Sys.time();;\n'
        'try needs "/work/' + supplier["loader"] + '" with e -> '
        'prerr_endline(Printexc.to_string e); exit 1;;\n')
    (OUT / "bootstrap-input.ml").write_text(bootstrap)
    proc.stdin.write(bootstrap.encode()); proc.stdin.flush()
    ready = False
    with (private / "bootstrap.log").open("wb") as hidden, (OUT / "c2-proof.log").open("wb") as visible:
        for line in iter(proc.stdout.readline, b""):
            if not ready:
                hidden.write(line); hidden.flush()
                if line.rstrip(b"\r\n") == MARKER:
                    ready = True; supplier_finished = time.monotonic()
                    loader_mount = "/work/" + seal["loader"]
                    audit_mount = "/work/" + seal["audit"]
                    probe_phrase = ('let BP_E3_CRYPTO_PUBLIC_CALLER_POLICY = ();;\n'
                        'print_endline "C2_BINDING_PROBE_INTERFACE_UNAVAILABLE_AS_THEOREM";;\n'
                        if args.unavailable_interface_binding_probe else '')
                    caller_load = ('try needs "' + loader_mount + '" with e -> '
                        'prerr_endline(Printexc.to_string e); '
                        'if axioms()<>fresh_initial_axioms then exit 2; '
                        'print_endline "C2_FRESH_REJECTION_STANDARD3_UNCHANGED"; exit 1;;\n')
                    feed = ('if axioms()<>fresh_initial_axioms then exit 1;;\n'
                        'let reuse_c2_foundation_axioms=fresh_initial_axioms;;\n'
                        'print_endline("C2_FRESH_SUPPLIER_CPU "^string_of_float(Sys.time()-.fresh_supplier_cpu_start));;\n'
                        'let c2_fresh_cpu_start=Sys.time();;\n'
                        'c2_development_ambient_snapshot "after-supplier-before-caller" "/output/ambient-after-supplier-v1.json";;\n'
                        + probe_phrase + caller_load +
                        'try needs "' + audit_mount + '" with e -> prerr_endline(Printexc.to_string e); exit 1;;\n'
                        'print_endline("C2_FRESH_CALLER_CPU "^string_of_float(Sys.time()-.c2_fresh_cpu_start));;\n'
                        'if axioms()<>fresh_initial_axioms then exit 1;;\n'
                        'print_endline "C2_FRESH_FINAL_STANDARD3_AXIOMS_UNCHANGED";;\nexit 0;;\n')
                    (OUT / "c2-input.ml").write_text(feed)
                    proc.stdin.write(feed.encode()); proc.stdin.close()
            else:
                visible.write(line); visible.flush()
                sys.stdout.buffer.write(line); sys.stdout.buffer.flush()
    code = proc.wait(); finished = time.monotonic(); timer.cancel()
    CONTEXT.update(exit_code=code, timeout=timed_out.is_set(), supplier_marker=ready,
                   elapsed_seconds=finished-started, checker_wall_seconds=finished-checker_start)
    inspection = subprocess.run(["docker", "inspect", cidfile.read_text().strip()],
                                capture_output=True, text=True, timeout=30) if cidfile.exists() else None
    state = None
    if inspection and inspection.returncode == 0:
        (OUT / "container-inspect.json").write_text(inspection.stdout)
        obj, = json.loads(inspection.stdout); state = obj["State"]
        cfg = obj["HostConfig"]
        if cfg["Memory"] != 3*1024**3 or cfg["MemorySwap"] != 3*1024**3 or cfg["NanoCpus"] != 10**9 or cfg["NetworkMode"] != "none":
            raise ValueError("Actual checker resource/network limits differ")
        for mount in obj["Mounts"]:
            if mount["Destination"] != "/output" and mount["RW"]:
                raise ValueError("Writable source alias in actual checker mounts")
    if args.unavailable_interface_binding_probe:
        text = (OUT / "c2-proof.log").read_text(errors="replace")
        if (code != 1 or timed_out.is_set() or not ready or state is None or state.get("OOMKilled")
            or "val BP_E3_CRYPTO_PUBLIC_CALLER_POLICY : unit = ()" not in text
            or "C2_BINDING_PROBE_INTERFACE_UNAVAILABLE_AS_THEOREM" not in text
            or "C2_FRESH_REJECTION_STANDARD3_UNCHANGED" not in text
            or ("Error in included file /work/"+seal["application_proof_source"]) not in text
            or "unit" not in text or "thm" not in text
            or ("val "+seal["application_theorem"]+" : thm") in text
            or AUDIT_MARKER in text):
            save("receipt.json", dict(CONTEXT, status="FRESH_INTERFACE_BINDING_PROBE_INCONCLUSIVE",
                docker_state=state, caller_acceptance=False, full_C2_acceptance=False))
            return 1
        auditor = check.checked(root, supplier["auditor"], supplier["auditor_sha256"])
        result = subprocess.run([sys.executable, str(auditor), "--source-root", str(stage), "--output", str(runtime)],
            capture_output=True, text=True, timeout=min(120, remaining()))
        (private / "host-audit-stdout.json").write_text(result.stdout)
        (private / "host-audit-stderr.log").write_text(result.stderr)
        if result.returncode or result.stderr.strip():
            raise ValueError("Binding probe supplier audit failed")
        actual_supplier = json.loads(result.stdout)
        if (actual_supplier["unique_theorems"], actual_supplier["unique_definitions"], actual_supplier["equation_count"]) != (325,119,218):
            raise ValueError("Binding probe supplier audit incomplete")
        materializer.inputs(root); guard()
        check.validate_development_graph(stage, seal)
        check.checked(root, str(seal_path.relative_to(root)), args.seal_sha256)
        for name, digest in seal["host_inputs"].items(): check.checked(root, name, digest)
        for name, digest in seal["additional_stage_inputs"].items(): check.checked(root, name, digest)
        remaining()
        save("receipt.json", dict(CONTEXT,
            status="OBSERVED_FRESH_PUBLIC_INTERFACE_BINDING_TYPE_AVAILABILITY_REJECTION",
            seal_sha256=args.seal_sha256,
            rejection_stage="C2_CRYPTO_INTERFACE_APPLICATION_ML_TYPE_CHECK",
            unavailable_binding="BP_E3_CRYPTO_PUBLIC_CALLER_POLICY", replacement_type="unit",
            supplier_theorems=325, supplier_definitions=119, supplier_equations=218,
            standard3_unchanged_at_rejection=True, no_c2_objects_before_binding_shadow=True,
            former_caller_proof_loader=False, saved_passing_proof_used=False,
            original_theorem_remains_in_ambient_kernel_theory=True,
            formal_dependency_isolation=False, semantic_theorem_sensitivity=False,
            caller_acceptance=False, full_C2_acceptance=False, docker_state=state,
            source_set_sha256=check.sha(OUT / "inputs.json"), c2_log_sha256=check.sha(OUT / "c2-proof.log"),
            supplier_log_sha256=check.sha(private / "bootstrap.log"),
            scope="Usable ML theorem-binding availability in an actual fresh construction attempt only"))
        return 1
    if code or timed_out.is_set() or not ready or state is None or state.get("OOMKilled"):
        save("receipt.json", dict(CONTEXT, status="FRESH_C2_PROOF_FAILED", docker_state=state,
                                 full_C2_acceptance=False))
        return 1
    text = (OUT / "c2-proof.log").read_text()
    for path in [OUT / "c2-proof.log", private / "bootstrap.log"]:
        if re.search(r"^(?:# )?\s*(?:Exception:|Error:|Parse error:|Error in included file\b|Fatal\s*error\b)",
                     path.read_text(errors="replace"), re.M | re.I):
            raise ValueError("Raw prover log error: " + path.name)
    markers = [x.removeprefix("# ").strip() for x in text.splitlines()]
    if AUDIT_MARKER not in markers or "C2_FRESH_FINAL_STANDARD3_AXIOMS_UNCHANGED" not in markers:
        raise ValueError("Full frozen targets/witnesses/all-definition actual-object audit did not finish")
    audit = json.loads((runtime / "c2-live-audit-v1.json").read_text())
    expected_rows = {r["name"]: (kind, r) for kind, rows in [
        ("object", registry["objects"]), ("definition", registry["definitions"])] for r in rows}
    rows = audit["rows"]
    if (audit["schema"] != "c2-fresh-live-audit-v1" or audit["theorem_count"] != len(registry["objects"])
        or audit["original_target_count"] != registry["original_target_count"] or audit["witness_target_count"] != registry["witness_target_count"]
        or audit["nonvacuity_case_count"] != registry["nonvacuity_case_count"] or audit["definition_count"] != len(registry["definitions"])):
        raise ValueError("Structured full C2 audit count mismatch")
    if len(rows) != len(expected_rows) or len({r["name"] for r in rows}) != len(rows) or {r["name"] for r in rows} != set(expected_rows):
        raise ValueError("Structured C2 audit missing/duplicate/unexpected rows")
    if audit["initial_axiom_count"] != 3 or audit["final_axiom_count"] != 3 or audit["axioms_unchanged"] is not True or audit["standard_axioms"] != ["INFINITY_AX","SELECT_AX","ETA_AX"]:
        raise ValueError("Structured standard-three foundation boundary mismatch")
    for row in rows:
        kind, expected = expected_rows[row["name"]]
        if row["kind"] != kind or any(type(row[x]) is not int or row[x] != 0 for x in ["hypothesis_count","free_variable_count","new_axioms"]):
            raise ValueError("Live C2 kind/hyp/free/axiom mismatch: " + row["name"])
        if row["literal_match"] is not True or row["expanded_match"] is not True or row["comparison"] != expected["comparison"] or row["expected_literal_sha256"] != expected["expected_literal_sha256"]:
            raise ValueError("Live C2 original/expanded literal mismatch: " + row["name"])
        if not row["conclusion"] or not row["expanded_conclusion"]:
            raise ValueError("Missing actual C2 conclusion")
    auditor = check.checked(root, supplier["auditor"], supplier["auditor_sha256"])
    result = subprocess.run([sys.executable, str(auditor), "--source-root", str(stage), "--output", str(runtime)],
                            capture_output=True, text=True, timeout=min(120, remaining()))
    (private / "host-audit-stdout.json").write_text(result.stdout)
    (private / "host-audit-stderr.log").write_text(result.stderr)
    if result.returncode: raise ValueError("Existing full opaque supplier host audit failed")
    json.loads(result.stdout)
    materializer.inputs(root); guard()
    check.checked(root, str(seal_path.relative_to(root)), args.seal_sha256)
    for name, digest in seal["host_inputs"].items(): check.checked(root, name, digest)
    for name, digest in seal["additional_stage_inputs"].items(): check.checked(root, name, digest)
    def cpu(marker):
        values = re.findall(r"^(?:# )?" + re.escape(marker) + r" ([0-9.eE+-]+)\s*$", text, re.M)
        if len(values) != 1: raise ValueError("Missing/repeated actual phase CPU: " + marker)
        return float(values[0])
    remaining()  # Includes post-check host auditing and final source guards.
    receipt = dict(CONTEXT, status="FRESH_C2_FULL_FROZEN_TARGETS_WITNESSES_ALL_DEFINITIONS_AND_SUPPLIER_AUDITS_COMPLETE_PENDING_ROOT_GATES",
        elapsed_seconds=time.monotonic()-started,
        caller_acceptance=False, full_C2_acceptance=False, original_target_count=registry["original_target_count"],
        witness_target_count=registry["witness_target_count"], nonvacuity_case_count=registry["nonvacuity_case_count"],
        definition_count=len(registry["definitions"]), readonly_source_closed=True,
        supplier_cpu_seconds=cpu("C2_FRESH_SUPPLIER_CPU"), caller_cpu_seconds=cpu("C2_FRESH_CALLER_CPU"),
        supplier_wall_seconds=supplier_finished-checker_start, caller_wall_seconds=finished-supplier_finished,
        cpu_scope="Supplier CPU begins after fresh HOL initialization and includes supplier load/live audit; caller CPU includes all selected caller/generic/helper/witness loads and final exact/expanded audit; no exclusive main/helper CPU is claimed",
        wall_scope="Elapsed wall includes preparation, fresh GNU, HOL initialization/reconstruction, and host postguards; supplier wall includes HOL initialization, unlike supplier CPU",
        source_set_sha256=check.sha(OUT / "inputs.json"), seal_sha256=args.seal_sha256,
        live_audit_sha256=check.sha(runtime / "c2-live-audit-v1.json"),
        c2_log_sha256=check.sha(OUT / "c2-proof.log"), supplier_log_sha256=check.sha(private / "bootstrap.log"),
        fresh_GNU_C2_crosscheck=True, saved_passing_proof_used=False, model=None, tokens=None, cost=None,
        human_review="PENDING", ambient_namespace_is_not_capability_isolated=True,
        pending=["Independent root source/runtime/output gate", "Full positive acceptance", "Applicable targeted controls"])
    save("receipt.json", receipt)
    print(json.dumps(dict(status=receipt["status"], output=str(OUT), caller_acceptance=False)), flush=True)
    return 0

if __name__ == "__main__":
    try:
        sys.exit(main())
    except Exception as error:
        if OUT is not None:
            save("receipt.json", dict(CONTEXT, status="FRESH_C2_REPLAY_REJECTED", error=str(error),
                                     caller_acceptance=False, full_C2_acceptance=False))
        print("FRESH_C2_REPLAY_REJECTED: " + str(error), file=sys.stderr)
        sys.exit(1)
