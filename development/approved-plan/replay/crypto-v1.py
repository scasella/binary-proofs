#!/usr/bin/env python3
"""Offline fresh reconstruction of the sealed production CRYPTO_memcmp routine.

This command accepts only the one CRYPTO_memcmp routine and architectural trace property, never overall O1 or the core. It requires the caller's expected seal digest;
saved PASS records never discharge an obligation. Source and writable output
are separate mounts, with no writable alias of the checking source tree.
"""
import argparse
import datetime as dt
import hashlib
import json
from pathlib import Path, PurePosixPath
import shutil
import subprocess
import sys
import tarfile
import time
import uuid

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / 'scripts'))
from check import binding, integrity, sha


def dump(path, obj):
    path.write_text(json.dumps(obj, indent=2, sort_keys=True) + '\n')


def relative_file(name):
    parts = PurePosixPath(name)
    if parts.is_absolute() or '..' in parts.parts or not name:
        raise RuntimeError('Unsafe input path: ' + name)
    return name


def checked_input(root, name, digest):
    path = root / relative_file(name)
    if not path.is_file() or path.is_symlink() or sha(path) != digest:
        raise RuntimeError('Frozen input mismatch: ' + name)
    return path


def replay(args):
    seal_path = ROOT / relative_file(args.seal)
    checked_input(ROOT, args.seal, args.sha256)
    seal = json.loads(seal_path.read_text())
    if seal['scope'] != 'CRYPTO_MEMCMP_COMPLETE_ROUTINE_ONLY' or seal['full_O1_pass'] is not False:
        raise RuntimeError('This driver cannot accept any different scope')
    integrity()
    byte_binding = binding()
    preservation = checked_input(ROOT, seal['preservation_receipt'], seal['preservation_receipt_sha256'])
    preserved = json.loads(preservation.read_text())
    archive = checked_input(ROOT, preserved['archive_path'], preserved['archive_sha256'])
    new_files = seal['files']
    if set(new_files).intersection(preserved['files']):
        raise RuntimeError('New component would overwrite predecessor input')
    for name, digest in new_files.items():
        checked_input(ROOT, name, digest)
    # Trusted extraction/image checks are freshly executed, never read from a PASS file.
    acquired = []
    for script in [
        'development/approved-plan/loaded-witness/full-binding/acquire-file-map-v2.py',
        'development/approved-plan/loaded-witness/full-binding/crosscheck-image-clauses-v1.py']:
        proc = subprocess.run([sys.executable, str(ROOT / script)],
                              cwd=ROOT, capture_output=True, text=True)
        if proc.returncode != 0:
            raise RuntimeError('Trusted acquisition/image check rejected: ' + proc.stderr)
        acquired.append(json.loads(proc.stdout))
    if (acquired[0]['status'] != 'PASS_TRUSTED_WHOLE_FILE_MAP_ACQUISITION' or
        acquired[1]['status'] != 'PASS_FORMAL_SOURCE_IMAGE_INTERVAL_CROSSCHECK'):
        raise RuntimeError('Unexpected artifact/image check scope')
    if args.preflight_only:
        print(json.dumps({'status': 'PASS_ROUTINE_INPUT_PREFLIGHT',
                          'proof_started': False, 'routine_properties_verified': False,
                          'seal_sha256': args.sha256,
                          'artifact_binding': byte_binding,
                          'whole_image_checks': acquired}))
        return 0
    stamp = dt.datetime.now(dt.timezone.utc).strftime('%Y%m%dT%H%M%SZ')
    run_id = 'crypto-routine-closed-' + stamp + '-' + uuid.uuid4().hex[:8]
    out = ROOT / 'results/development' / run_id
    stage = out / 'source'
    checker_output = out / 'checker-output'
    stage.mkdir(parents=True)
    checker_output.mkdir()
    seen = set()
    with tarfile.open(archive, 'r:gz') as inp:
        for member in inp.getmembers():
            name = relative_file(member.name)
            if name in seen or name not in preserved['files'] or not member.isfile():
                raise RuntimeError('Unapproved or duplicate preserved member')
            seen.add(name)
            dest = stage / name
            dest.parent.mkdir(parents=True, exist_ok=True)
            with inp.extractfile(member) as src, dest.open('xb') as dst:
                shutil.copyfileobj(src, dst)
            dest.chmod(member.mode & 0o777)
            checked_input(stage, name, preserved['files'][name])
    if seen != set(preserved['files']):
        raise RuntimeError('Preservation archive is incomplete')
    sources = dict(preserved['files'])
    for name, digest in new_files.items():
        dest = stage / name
        dest.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(ROOT / name, dest)
        checked_input(stage, name, digest)
        sources[name] = digest
    shutil.copy2(seal_path, stage / 'component-seal.json')
    sources['component-seal.json'] = args.sha256
    input_text = (stage / 'development/approved-plan/replay/crypto-input-v1.ml').read_text()
    (out / 'input.ml').write_text(input_text)
    dump(out / 'inputs.json', {'seal_sha256': args.sha256, 'files': sources})
    cmd = ['docker', 'run', '-i', '--rm', '--pull', 'never', '--network', 'none',
           '--platform', 'linux/arm64', '-e', 'HOLLIGHT_DIR=/work/third_party/hol-light',
           '-v', str(stage) + ':/work:ro', '-v', str(checker_output) + ':/output:rw',
           '-v', str(stage / 'proofs/model-extension/decode.ml') +
           ':/work/third_party/s2n-bignum/x86/proofs/decode.ml:ro',
           '-w', '/work/third_party/s2n-bignum', seal['checker_image_id'],
           '/work/third_party/hol-light/ocaml-hol', '-init',
           '/work/third_party/hol-light/hol.ml', '-safe-string', '-I',
           '/work/third_party/hol-light']
    started = time.monotonic()
    with (out / 'input.ml').open() as inp, (out / 'replay.log').open('w') as log:
        process = subprocess.run(cmd, stdin=inp, stdout=log, stderr=subprocess.STDOUT)
    elapsed = time.monotonic() - started
    audits = []
    groups_ok = True
    definitions_checked = 0
    for group in seal['groups']:
        path = checker_output / group['file']
        audit = json.loads(path.read_text()) if path.exists() else None
        audits.append(audit)
        if audit is None:
            groups_ok = False
            continue
        rows = audit['theorems']
        names = [t['name'] for t in rows]
        groups_ok = groups_ok and (set(names) == set(group['theorems']) and
                                  len(names) == len(group['theorems']))
        key = group['definitions_key']
        if key is not None:
            ds = audit[key]
            groups_ok = groups_ok and len(ds) == group['definition_count']
            groups_ok = groups_ok and all(d['equation_matches_expected'] is True for d in ds)
        else:
            groups_ok = groups_ok and audit['expanded_definition_count'] == group['definition_count']
        definitions_checked += group['definition_count'] if groups_ok else 0
    live = [t for audit in audits if audit is not None for t in audit['theorems']]
    # The shared universal decode bridge is audited in two groups; count it once.
    unique = {}
    for theorem in live:
        name = theorem['name']
        if name in unique and unique[name]['statement'] != theorem['statement']:
            groups_ok = False
        unique[name] = theorem
    unchanged = all((stage / name).is_file() and sha(stage / name) == digest
                    for name, digest in sources.items())
    canonical = True
    try:
        integrity()
        checked_input(ROOT, args.seal, args.sha256)
        for name, digest in new_files.items():
            checked_input(ROOT, name, digest)
    except Exception:
        canonical = False
    passed = (process.returncode == 0 and unchanged and canonical and groups_ok and
              definitions_checked == seal['expected_definition_count'] and
              set(unique) == set(seal['expected_unique_theorems']) and
              all(t['hypothesis_count'] == 0 and t['new_axioms'] == 0 and
                  t['conclusion_matches_expected'] is True for t in live))
    receipt = {
        'experiment_id': seal['experiment_id'], 'run_id': run_id,
        'component_bundle': seal['id'], 'seal_sha256': args.sha256,
        'status': 'PASS_CRYPTO_MEMCMP_ROUTINE_AND_ARCHITECTURAL_TRACE' if passed else 'FAIL_CRYPTO_MEMCMP_ROUTINE_PACKAGE',
        'process_exit': process.returncode, 'elapsed_checking_seconds': elapsed,
        'full_O1_pass': False, 'CRYPTO_memcmp_four_property_pass': passed,
        'O2_architectural_trace_pass': passed, 'core_complete': False,
        'library_wide_complete': False, 'human_review': 'PENDING',
        'expected_unique_theorem_count': len(seal['expected_unique_theorems']),
        'live_unique_theorem_count': len(unique), 'expanded_definitions_checked': definitions_checked,
        'approved_assumption_ids': seal['approved_assumption_ids'],
        'source_unchanged': unchanged, 'canonical_inputs_unchanged': canonical,
        'artifact_binding': byte_binding, 'whole_image_checks': acquired, 'kernel_audits': audits,
        'source_set_sha256': sha(out / 'inputs.json'),
        'raw_log': str((out / 'replay.log').relative_to(ROOT)),
        'readonly_source_with_no_writable_alias': True, 'network': 'none',
        'peak_memory_bytes': None, 'peak_memory_null_reason': 'Not observed for checker process',
        'model_identifier': None, 'model_identifier_null_reason': 'Not exposed by execution runtime',
        'token_usage': None, 'token_usage_null_reason': 'Not exposed by execution runtime',
        'billing_cost': None, 'billing_cost_null_reason': 'Not exposed by execution runtime',
        'scope': seal['positive_claim'],
        'integrity_controls_scope': 'Copy-only controls1/2/5 checked by separate negative-control command; R1 controls3/4 remain incomplete'}
    dump(out / 'receipt.json', receipt)
    print(json.dumps({'status': receipt['status'], 'run_dir': str(out.relative_to(ROOT))}))
    return 0 if passed else 1


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--seal', required=True)
    parser.add_argument('--sha256', required=True)
    parser.add_argument('--preflight-only', action='store_true', help='Only validate sealed inputs/artifact/image; never accept a theorem')
    args = parser.parse_args()
    invocation_id = 'crypto-invocation-' + dt.datetime.now(dt.timezone.utc).strftime('%Y%m%dT%H%M%SZ') + '-' + uuid.uuid4().hex[:8]
    began = time.monotonic()
    outcome = None
    error = None
    try:
        outcome = replay(args)
    except Exception as e:
        outcome = 1
        error = str(e)
        print(error, file=sys.stderr)
    attempt = {'run_id': invocation_id, 'experiment_id': 'BP-20260930-E2',
               'command': 'crypto-v1.py', 'seal': args.seal, 'seal_sha256': args.sha256,
               'preflight_only': args.preflight_only, 'exit_code': outcome,
               'outcome': 'PASS' if outcome == 0 else 'FAIL', 'error': error,
               'elapsed_command_seconds': time.monotonic() - began,
               'construction_seconds': None, 'peak_memory_bytes': None,
               'model_identifier': None, 'token_usage': None, 'billing_cost': None,
               'null_reason': 'Not observed/exposed by this execution runtime',
               'human_interventions': ['User approved expert plan'],
               'trust_assumption_ids': ['HOL_KERNEL_RUNTIME_V1','S2N_X86_PINNED_V1','ABI_SCALAR_ADDED_STATE_V4','FINAL_ELF_ACQUISITION_LOADING_V2','SEQUENTIAL_ORDINARY_MEMORY_PROFILE_V1']}
    ledger = ROOT / 'results/development/crypto-invocations.jsonl'
    ledger.parent.mkdir(parents=True, exist_ok=True)
    with ledger.open('a') as out:
        out.write(json.dumps(attempt, sort_keys=True) + '\n')
    raise SystemExit(outcome)
