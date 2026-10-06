#!/usr/bin/env python3
"""Offline fresh reconstruction of the explicitly sealed all-length assurance component.

This command cannot accept O1. It requires the caller's expected seal digest;
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
    if seal['scope'] != 'ALL_LENGTH_ASSURANCE_COMPONENT_ONLY' or seal['full_O1_pass'] is not False:
        raise RuntimeError('This driver cannot accept a full routine package')
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
    stamp = dt.datetime.now(dt.timezone.utc).strftime('%Y%m%dT%H%M%SZ')
    run_id = 'assurance-closed-' + stamp + '-' + uuid.uuid4().hex[:8]
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
    input_text = (stage / 'development/approved-plan/replay/assurance-input-v3.ml').read_text()
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
    for name in ['assurance-audit.json']:
        path = checker_output / name
        audits.append(json.loads(path.read_text()) if path.exists() else None)
    live = [t for audit in audits if audit is not None for t in audit['theorems']]
    actual_names = [t['name'] for t in live]
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
    expected = seal['expected_theorems']
    passed = (process.returncode == 0 and unchanged and canonical and
              all(audit is not None and audit['full_O1_pass'] is False for audit in audits) and
              set(actual_names) == set(expected) and len(actual_names) == len(expected) and
              len(audits[0]['definitions']) == seal['expected_definition_count'] and
              all(d['equation_matches_expected'] is True for d in audits[0]['definitions']) and
              all(t['hypothesis_count'] == 0 and t['new_axioms'] == 0 and
                  t['conclusion_matches_expected'] is True for t in live))
    receipt = {
        'experiment_id': seal['experiment_id'], 'run_id': run_id,
        'component_bundle': seal['id'], 'seal_sha256': args.sha256,
        'status': 'PASS_FRESH_ALL_LENGTH_ASSURANCE_COMPONENT' if passed else 'FAIL_FRESH_ALL_LENGTH_ASSURANCE_COMPONENT',
        'process_exit': process.returncode, 'elapsed_checking_seconds': elapsed,
        'full_O1_pass': False, 'source_unchanged': unchanged, 'canonical_inputs_unchanged': canonical,
        'artifact_binding': byte_binding, 'kernel_audits': audits,
        'source_set_sha256': sha(out / 'inputs.json'),
        'raw_log': str((out / 'replay.log').relative_to(ROOT)),
        'readonly_source_with_no_writable_alias': True, 'network': 'none',
        'peak_memory_bytes': None, 'peak_memory_null_reason': 'Not observed for checker process',
        'model_identifier': None, 'model_identifier_null_reason': 'Not exposed by execution runtime',
        'token_usage': None, 'token_usage_null_reason': 'Not exposed by execution runtime',
        'billing_cost': None, 'billing_cost_null_reason': 'Not exposed by execution runtime',
        'scope': 'All-length exact scalar Pre policy/function/frame/actual-RET and qualified ABI extension at synchronized endpoint; full loaded-image witness/binding acceptance incomplete'}
    dump(out / 'receipt.json', receipt)
    print(json.dumps({'status': receipt['status'], 'run_dir': str(out.relative_to(ROOT))}))
    return 0 if passed else 1


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--seal', required=True)
    parser.add_argument('--sha256', required=True)
    args = parser.parse_args()
    try:
        raise SystemExit(replay(args))
    except Exception as e:
        print(str(e), file=sys.stderr)
        raise SystemExit(1)
