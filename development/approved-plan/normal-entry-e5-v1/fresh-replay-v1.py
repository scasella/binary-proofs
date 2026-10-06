#!/usr/bin/env python3
"""Fresh closed caller replay. Root audit and later controls remain separate.

Opaque supplier materialization/audit APIs are pinned root-owned programs;
this caller driver never displays or semantically inspects their recipes.
"""
import argparse
import datetime
import hashlib
import types
import json
import os
from pathlib import Path
import re
import shutil
import stat
import subprocess
import sys
import threading
import time

sys.dont_write_bytecode = True
os.environ['PYTHONDONTWRITEBYTECODE'] = '1'
ROOT = Path(__file__).resolve().parents[3]
HERE = Path(__file__).resolve().parent
IMAGE = 'sha256:a19fdc18f1f283ed8e2514229b77f33619df1ba0ea1ae578c97779f4b4eb3c3f'
SUPPLIER_MARKER = b'E3_OPAQUE_CALLEE_INTERFACE_LOADED_AND_LIVE_AUDITED'
CLIENT_MARKER = 'CLIENT_SECRET_SUCCESSFUL_ONLY_ALL10_RECONSTRUCTED_AND_EXACT_AUDITED'
RUN_OUTPUT = None
RUN_CONTEXT = {'proof_started': False, 'target_routine_executed': False}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def checked(root, name, expected):
    relative = Path(name)
    if relative.is_absolute() or '..' in relative.parts:
        raise ValueError('Input name is not a contained relative path: ' + name)
    for count in range(len(relative.parts) + 1):
        if root.joinpath(*relative.parts[:count]).is_symlink():
            raise ValueError('Symlink in input path: ' + name)
    path = root / name
    if path.is_symlink() or not path.is_file() or sha(path) != expected:
        raise ValueError('Frozen source mismatch: ' + name)
    return path


def lock_stage(stage):
    """Remove host write permission while preserving every executable bit."""
    paths = [stage] + list(stage.rglob('*'))
    for path in paths:
        mode = path.lstat().st_mode
        if stat.S_ISLNK(mode) or not (stat.S_ISDIR(mode) or stat.S_ISREG(mode)):
            raise ValueError('Nonregular or symlink staged input')
    for path in paths:
        mode = path.lstat().st_mode
        if stat.S_ISREG(mode):
            path.chmod((stat.S_IMODE(mode) & 0o555) | 0o444)
    for path in reversed(paths):
        if path.is_dir():
            path.chmod(0o555)
    guard_stage_permissions(stage)


def guard_stage_permissions(stage):
    for path in [stage] + list(stage.rglob('*')):
        mode = path.lstat().st_mode
        if stat.S_ISDIR(mode):
            if stat.S_IMODE(mode) != 0o555:
                raise ValueError('Staged directory is not host read-only')
        elif stat.S_ISREG(mode):
            if stat.S_IMODE(mode) & 0o222 or stat.S_IMODE(mode) & 0o444 != 0o444:
                raise ValueError('Staged file permissions changed')
        else:
            raise ValueError('Nonregular or symlink staged input')


def module(path, name):
    # Compile sealed Python source directly; never select a host bytecode cache.
    obj = types.ModuleType(name)
    obj.__file__ = str(path)
    exec(compile(path.read_bytes(), str(path), 'exec'), obj.__dict__)
    return obj


def main():
    global RUN_OUTPUT
    parser = argparse.ArgumentParser()
    parser.add_argument('--source-root', type=Path, default=ROOT)
    parser.add_argument('--output', type=Path)
    parser.add_argument('--seal', type=Path)
    parser.add_argument('--seal-sha256', required=True)
    parser.add_argument('--preflight-only', action='store_true')
    parser.add_argument('--timeout-seconds', type=int, default=1800)
    args = parser.parse_args()
    if args.timeout_seconds <= 0:
        raise ValueError('Timeout must be positive')
    root = args.source_root.resolve()
    run_id = datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ') + '-' + os.urandom(4).hex()
    output = args.output or root / 'results/development' / ('normal-entry-e5-cold-' + run_id)
    output = output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    RUN_OUTPUT = output
    sys.pycache_prefix = str(output / 'disabled-python-cache')
    RUN_CONTEXT['run_id'] = run_id
    seal_path = args.seal or root / 'development/approved-plan/normal-entry-e5-v1/fresh-seal-v1.json'
    if not re.fullmatch('[0-9a-f]{64}', args.seal_sha256) or seal_path.is_symlink() or not seal_path.is_file() or sha(seal_path) != args.seal_sha256:
        raise ValueError('Externally pinned seal mismatch')
    seal = json.loads(seal_path.read_text())
    if sha(Path(__file__)) != seal['driver_sha256']:
        raise ValueError('Driver source differs from reviewed seal')
    stage = output / 'source'
    runtime = output / 'runtime'
    runtime.mkdir()
    private = output / 'root-only-supplier'
    private.mkdir()
    started = time.monotonic()

    def save(name, value):
        (output / name).write_text(json.dumps(value, indent=2, sort_keys=True) + '\n')

    for name, digest in seal['host_inputs'].items():
        checked(root, name, digest)
    supplier = seal['opaque_supplier']
    materializer = module(checked(root, supplier['materializer'], supplier['materializer_sha256']),
                          'fresh_root_opaque_materializer')
    materializer.inputs(root)
    if args.preflight_only:
        save('receipt.json', {'status': 'STRICT_INPUT_PREFLIGHT_COMPLETE_NOT_A_PROOF',
             'proof_started': False, 'caller_acceptance': False,
             'target_routine_executed': False,
             'seal_sha256': args.seal_sha256, 'GNU_or_HOL_started': False})
        return 0
    materializer.materialize(root, stage)
    supplier_index = json.loads(checked(root, supplier['index'], supplier['index_sha256']).read_text())

    def guard_supplier_stage():
        if len(supplier_index['source_files']) != 4534:
            raise ValueError('Supplier full source index count mismatch')
        for name, digest in supplier_index['source_files'].items():
            checked(stage, name, digest)
        checked(stage, supplier_index['seal'], supplier_index['seal_sha256'])

    def guard_complete_stage():
        guard_stage_permissions(stage)
        guard_supplier_stage()
        for name, digest in seal['additional_stage_inputs'].items():
            checked(stage, name, digest)
        expected_paths = set(supplier_index['source_files']) | {supplier_index['seal']} | set(seal['additional_stage_inputs'])
        actual_paths = set()
        for path in stage.rglob('*'):
            if path.is_symlink():
                raise ValueError('Symlink in staged source tree')
            if path.is_file():
                actual_paths.add(str(path.relative_to(stage)))
        if actual_paths != expected_paths:
            raise ValueError('Added or missing file in full staged source tree')

    guard_supplier_stage()
    # Copy only pinned caller/public sources and external-tool inputs. The
    # opaque helper alone restores the historical supplier/framework tree.
    for name, digest in seal['additional_stage_inputs'].items():
        source = checked(root, name, digest)
        dest = stage / name
        dest.parent.mkdir(parents=True, exist_ok=True)
        if dest.exists() and sha(dest) != digest:
            raise ValueError('Conflicting staged input: ' + name)
        if not dest.exists():
            shutil.copyfile(source, dest)
    for name, digest in seal['additional_stage_inputs'].items():
        checked(stage, name, digest)
    lock_stage(stage)
    guard_complete_stage()
    save('invocation.json', {'run_id': run_id, 'kind': 'FRESH_CLOSED_PROOF_ATTEMPT',
        'seal_sha256': sha(seal_path), 'checker_image': IMAGE,
        'memory_bytes': 3 * 1024**3, 'swap_limit_bytes': 3 * 1024**3,
        'network': 'none', 'supplier_source_restoration': 'Pinned opaque root helper',
        'model_tokens': None, 'model_cost': None, 'usage_reason': 'Not exposed',
        'host_stage_read_only': True, 'target_routine_executed': False,
        'human_review': 'PENDING', 'physical_RF_TF_correspondence': 'NORMAL_ENTRY_REFINEMENT_PENDING_ACCEPTANCE'})

    crosscheck_path = stage / seal['client_image_crosscheck']['program']
    crosscheck = module(crosscheck_path, 'fresh_client_formal_image_crosscheck')
    image_check = crosscheck.crosscheck(gnu=True)
    save('client-image-crosscheck.json', image_check)

    cidfile = output / 'container.cid'
    decode = stage / supplier['decoder']
    execute = stage / supplier['executor']
    own_stage = stage / 'development/approved-plan/clients-e3/secret-v1'
    public_stage = stage / 'development/approved-plan/clients-e3/public-inputs-v1'
    e5_stage = stage / 'development/approved-plan/normal-entry-e5-v1'
    argv = ['docker', 'run', '-i', '--cidfile', str(cidfile), '--pull', 'never',
        '--network', 'none', '--memory', '3g', '--memory-swap', '3g',
        '--platform', 'linux/arm64', '-e', 'HOLLIGHT_DIR=/work/third_party/hol-light',
        '-v', str(stage) + ':/work:ro', '-v', str(runtime) + ':/output:rw',
        '-v', str(decode) + ':/work/third_party/s2n-bignum/x86/proofs/decode.ml:ro',
        '-v', str(execute) + ':/work/third_party/s2n-bignum/x86/proofs/x86.ml:ro',
        '-v', str(own_stage) + ':/client:ro', '-v', str(public_stage) + ':/client-public:ro',
        '-v', str(e5_stage) + ':/e5:ro',
        '-w', '/work/third_party/s2n-bignum', IMAGE,
        '/work/third_party/hol-light/ocaml-hol', '-init', '/work/third_party/hol-light/hol.ml',
        '-safe-string', '-I', '/work/third_party/hol-light']
    save('checker-argv.json', argv)
    print(json.dumps({'status': 'FRESH_PROOF_STARTING', 'run_id': run_id,
                      'output': str(output), 'private_supplier_log': str(private / 'bootstrap.log')}), flush=True)
    proc = subprocess.Popen(argv, stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT, bufsize=0)
    RUN_CONTEXT['proof_started'] = True
    checker_started = time.monotonic()
    supplier_finished = None
    timed_out = threading.Event()

    def stop_timeout():
        if proc.poll() is None:
            timed_out.set()
            try:
                if cidfile.exists():
                    subprocess.run(['docker', 'kill', cidfile.read_text().strip()],
                                   stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, timeout=30)
            finally:
                if proc.poll() is None:
                    proc.terminate()

    timer = threading.Timer(args.timeout_seconds, stop_timeout)
    timer.daemon = True
    timer.start()
    bootstrap = ('use_file_raise_failure := true;;\n'
        'if length(axioms())<>3 || axioms()<>[INFINITY_AX;SELECT_AX;ETA_AX] then '
        '(prerr_endline "FRESH_INITIAL_STANDARD_THREE_AXIOMS"; exit 1);;\n'
        'let fresh_initial_axioms=axioms();;\n'
        'let e5_initial_axioms=axioms();;\n'
        'let fresh_supplier_cpu_start=Sys.time();;\n'
        'try needs "/work/' + supplier['loader'] + '" with e -> '
        'prerr_endline(Printexc.to_string e); exit 1;;\n')
    proc.stdin.write(bootstrap.encode())
    proc.stdin.flush()
    ready = False
    with (private / 'bootstrap.log').open('wb') as hidden, (output / 'client-proof.log').open('wb') as visible:
        for line in iter(proc.stdout.readline, b''):
            if not ready:
                hidden.write(line)
                hidden.flush()
                if line.rstrip(b'\r\n') == SUPPLIER_MARKER:
                    ready = True
                    supplier_finished = time.monotonic()
                    print('FRESH_SUPPLIER_KERNEL_MARKER_SEEN_NOT_ACCEPTANCE', flush=True)
                    client_input = ('if axioms()<>fresh_initial_axioms then '
                        '(prerr_endline "FRESH_SUPPLIER_AXIOMS_CHANGED"; exit 1);;\n'
                        'print_endline("FRESH_SUPPLIER_CPU " ^ string_of_float(Sys.time()-.fresh_supplier_cpu_start));;\n'
                        'try needs "/client/closed-components-loader-v2.ml" with e -> '
                        'prerr_endline(Printexc.to_string e); exit 1;;\n'
                        'let e5_cold_cpu_start=Sys.time();;\n'
                        'try needs "/e5/closed-loader-v1.ml" with e -> '
                        'prerr_endline(Printexc.to_string e); exit 1;;\n'
                        'print_endline("E5_COLD_CHECK_CPU " ^ string_of_float(Sys.time()-.e5_cold_cpu_start));;\n'
                        'if axioms()<>fresh_initial_axioms || length(axioms())<>3 then '
                        '(prerr_endline "FRESH_FINAL_AXIOMS_CHANGED"; exit 1);;\n'
                        'print_endline "FRESH_FULL_STANDARD3_FOUNDATION_AXIOMS_UNCHANGED";;\n'
                        'let fresh_resource_channel=open_in "/proc/1/status";;\n'
                        'let fresh_resource_output=open_out "/output/checker-proc-status.txt";;\n'
                        'try while true do output_string fresh_resource_output (input_line fresh_resource_channel ^ "\\n") done '
                        'with End_of_file -> close_in fresh_resource_channel; close_out fresh_resource_output;;\n'
                        'exit 0;;\n')
                    proc.stdin.write(client_input.encode())
                    proc.stdin.close()
            else:
                visible.write(line)
                visible.flush()
                sys.stdout.buffer.write(line)
                sys.stdout.buffer.flush()
    code = proc.wait()
    checker_finished = time.monotonic()
    RUN_CONTEXT.update(exit_code=code, timeout=timed_out.is_set(), supplier_marker=ready,
        elapsed_seconds=time.monotonic() - started,
        checker_total_wall_seconds=checker_finished - checker_started)
    if supplier_finished is not None:
        RUN_CONTEXT.update(supplier_wall_seconds=supplier_finished - checker_started,
                           caller_wall_seconds=checker_finished - supplier_finished)
    timer.cancel()
    if cidfile.exists():
        inspection = subprocess.run(['docker', 'inspect', cidfile.read_text().strip()],
                                    capture_output=True, text=True, timeout=30)
        (output / 'container-inspect.json').write_text(inspection.stdout)
    if code or timed_out.is_set() or not ready:
        save('receipt.json', {'status': 'FRESH_PROOF_FAILED', 'exit_code': code,
            'timeout': timed_out.is_set(), 'supplier_marker': ready,
            'elapsed_seconds': time.monotonic() - started, 'caller_acceptance': False,
            'proof_started': True, 'target_routine_executed': False})
        return 1
    text = (output / 'client-proof.log').read_text()
    for log_path in [output / 'client-proof.log', private / 'bootstrap.log']:
        if re.search(r'^(?:# )?\s*(?:Exception:|Error:|Parse error:|Error in included file\b|Fatal\s*error\b)',
                     log_path.read_text(errors='replace'), re.M | re.I):
            raise ValueError('Fresh raw prover log contains an error: ' + log_path.name)
    markers = [line.removeprefix('# ').strip() for line in text.splitlines()]
    for required in [CLIENT_MARKER, 'CLIENT_SECRET_ALL10_ORIGINAL_LITERALS_LIVE_AUDIT_PASS',
        'CLIENT_CLOSED_EXPORTS_RAW_125_HYP0_FREES0_STD3_AXIOMS_PASS',
        'CLIENT_CLOSED_EXPORT_REQUIRED125_UNIQUE_EXACT_NAMESET_PASS',
        'FRESH_FULL_STANDARD3_FOUNDATION_AXIOMS_UNCHANGED',
        'E5_ALL24_GOALS_7_EXPANDED_DEFINITIONS_HYP0_FREES0_STANDARD3_LIVE_AUDIT_PASS']:
        if required not in markers:
            raise ValueError('Missing actual checked runtime marker: ' + required)
    registry = json.loads((stage / seal['client_registry']).read_text())
    actual_goals = set(re.findall(r'^(?:# )?(?:CLIENT_SECRET_LIVE_CHECKED |RSW_LIVE_EXACT:|FINAL_COMPOSITION_DRAFT_AUDIT_PASS:)(\w+)', text, re.M))
    actual_defs = set(re.findall(r'^(?:# )?(?:CLIENT_SECRET_LIVE_DEFINITION_CHECKED |RSW_LIVE_DEF_EXACT:)(\w+)', text, re.M))
    if actual_goals != set(registry['theorem_names']) or actual_defs != set(registry['definition_names']):
        raise ValueError('Fresh literal audit registry name/count mismatch')
    actual_audit = json.loads((runtime / 'client-live-audit-v1.json').read_text())
    expected_audit = json.loads((stage / seal['client_expected_registry']).read_text())
    expected_rows = {**expected_audit['objects'], **expected_audit['definitions']}
    rows = actual_audit['rows']
    if actual_audit['theorem_count'] != 125 or actual_audit['definition_count'] != 45 or len(rows) != 170:
        raise ValueError('Structured client live audit count mismatch')
    if len({r['name'] for r in rows}) != 170 or {r['name'] for r in rows} != set(expected_rows):
        raise ValueError('Structured live client audit name set or uniqueness mismatch')
    if actual_audit['initial_axiom_count'] != 3 or actual_audit['final_axiom_count'] != 3 or actual_audit['axioms_unchanged'] is not True or actual_audit['standard_axioms'] != ['INFINITY_AX', 'SELECT_AX', 'ETA_AX']:
        raise ValueError('Structured client original standard axiom boundary mismatch')
    for row in rows:
        expected = expected_rows[row['name']]
        if row['kind'] != ('object' if row['name'] in expected_audit['objects'] else 'definition'):
            raise ValueError('Structured client object kind mismatch: ' + row['name'])
        for field in ['hypothesis_count', 'free_variable_count', 'new_axioms']:
            if type(row[field]) is not int or row[field] != 0:
                raise ValueError('Structured live client nonzero audit field: ' + row['name'])
        if row['literal_match'] is not True or row['comparison'] != expected['comparison'] or row['expected_literal_sha256'] != expected['expected_literal_sha256']:
            raise ValueError('Structured live client literal mismatch: ' + row['name'])
        if not isinstance(row['conclusion'], str) or not row['conclusion']:
            raise ValueError('Missing actual client theorem/definition conclusion')
    e5_audit = json.loads((runtime / 'e5-live-audit-v1.json').read_text())
    e5_expected = {'objects': {}, 'definitions': {}}
    for name in seal['e5_expected_registries']:
        expected_part = json.loads((stage / name).read_text())
        for row in expected_part['rows']:
            kind = 'definitions' if 'equation' in row else 'objects'
            obj = row['name']
            if obj in e5_expected[kind]: raise ValueError('Duplicate E5 frozen target')
            literal = row['equation'] if kind == 'definitions' else row['statement']
            digest = row['equation_sha256'] if kind == 'definitions' else row['statement_sha256']
            if hashlib.sha256(literal.encode()).hexdigest() != digest:
                raise ValueError('E5 frozen literal digest mismatch')
            e5_expected[kind][obj] = {'comparison':row['check_mode'], 'expected_literal_sha256':digest}
    e5_rows = e5_audit['rows']
    if e5_audit['schema'] != 'e5-normal-entry-live-audit-v1' or e5_audit['theorem_count'] != 24 or e5_audit['definition_count'] != 7 or len(e5_rows) != 31:
        raise ValueError('E5 actual row count/schema mismatch')
    if {r['name'] for r in e5_rows} != set(e5_expected['objects'])|set(e5_expected['definitions']) or len({r['name'] for r in e5_rows}) != 31:
        raise ValueError('E5 actual object names mismatch')
    if e5_audit['initial_axiom_count'] != 3 or e5_audit['final_axiom_count'] != 3 or e5_audit['axioms_unchanged'] is not True or e5_audit['standard_axioms'] != ['INFINITY_AX','SELECT_AX','ETA_AX']:
        raise ValueError('E5 standard-three-axiom mismatch')
    for row in e5_rows:
        kind = 'objects' if row['name'] in e5_expected['objects'] else 'definitions'
        expected = e5_expected[kind][row['name']]
        if row['kind'] != ('object' if kind == 'objects' else 'definition'):
            raise ValueError('E5 object kind mismatch')
        if any(type(row[field]) is not int or row[field] != 0 for field in ['hypothesis_count','free_variable_count','new_axioms']):
            raise ValueError('E5 nonzero live hypothesis/free/axiom count')
        if row['literal_match'] is not True or row['comparison'] != expected['comparison'] or row['expected_literal_sha256'] != expected['expected_literal_sha256']:
            raise ValueError('E5 exact live literal mismatch')
        if not isinstance(row['conclusion'],str) or not row['conclusion']:
            raise ValueError('E5 missing actual conclusion')
    # A fresh subprocess keeps the root audit's restored-tree module imports isolated.
    audit_program = checked(root, supplier['auditor'], supplier['auditor_sha256'])
    audit_process = subprocess.run([sys.executable, str(audit_program), '--source-root', str(stage),
        '--output', str(runtime)], capture_output=True, text=True, timeout=120)
    (private / 'host-audit-stdout.json').write_text(audit_process.stdout)
    (private / 'host-audit-stderr.log').write_text(audit_process.stderr)
    if audit_process.returncode:
        raise ValueError('Fresh full opaque supplier host audit rejected the run')
    json.loads(audit_process.stdout)
    materializer.inputs(root)
    guard_complete_stage()
    if sha(seal_path) != args.seal_sha256:
        raise ValueError('External seal changed during the replay')
    for name, digest in seal['host_inputs'].items():
        checked(root, name, digest)
    for name, digest in seal['additional_stage_inputs'].items():
        checked(stage, name, digest)
    def cpu_marker(name):
        values = re.findall(r'^(?:# )?' + re.escape(name) + r' ([0-9.eE+-]+)\s*$', text, re.M)
        if len(values) != 1:
            raise ValueError('Missing or repeated actual phase CPU measurement: ' + name)
        return float(values[0])
    save('receipt.json', {'status': 'FRESH_CLOSED_PROCESS_AND_LITERAL_AUDITS_COMPLETE_PENDING_ROOT_CROSSAUDIT',
        'caller_acceptance': False, 'exit_code': code, 'run_id': run_id,
        'target_routine_executed': False, 'host_stage_read_only': True,
        'elapsed_seconds': time.monotonic() - started,
        'proof_started': True, 'checker_total_wall_seconds': checker_finished - checker_started,
        'supplier_wall_seconds': supplier_finished - checker_started,
        'caller_wall_seconds': checker_finished - supplier_finished,
        'supplier_cpu_seconds': cpu_marker('FRESH_SUPPLIER_CPU'),
        'caller_cpu_seconds': cpu_marker('CLIENT_CLOSED_MARGINAL_CPU'),
        'e5_check_cpu_seconds': cpu_marker('E5_COLD_CHECK_CPU'),
        'e5_live_theorem_count': 24, 'e5_live_definition_count': 7,
        'e5_live_audit_sha256': sha(runtime / 'e5-live-audit-v1.json'),
        'client_literal_theorem_count': len(actual_goals), 'client_definition_count': len(actual_defs),
        'public_length_objects': 2, 'original_main_count': 10,
        'raw_named_exports_hyp0_frees0': 125, 'original_axiom_count': 3,
        'standard_axioms': ['INFINITY_AX', 'SELECT_AX', 'ETA_AX'],
        'opaque_full_supplier_host_audit_exit': audit_process.returncode,
        'saved_passing_proof_used': False, 'fresh_GNU_client_image_crosscheck': True,
        'client_log_sha256': sha(output / 'client-proof.log'),
        'client_live_structured_audit_sha256': sha(runtime / 'client-live-audit-v1.json'),
        'supplier_log_sha256': sha(private / 'bootstrap.log'),
        'host_supplier_audit_sha256': sha(private / 'host-audit-stdout.json'),
        'model_tokens': None, 'model_cost': None,
        'human_review': 'PENDING', 'physical_RF_TF_correspondence': 'NORMAL_ENTRY_REFINEMENT_PENDING_ACCEPTANCE',
        'pending': ['Independent root runtime/source/output crossaudit', 'Client-dependent controls3/4']})
    print('FRESH_CLOSED_REPLAY_COMPLETE_PENDING_ROOT_CROSSAUDIT', flush=True)
    return 0


if __name__ == '__main__':
    try:
        sys.exit(main())
    except Exception as error:
        if RUN_OUTPUT is not None:
            failed = dict(RUN_CONTEXT, status='FRESH_CLOSED_REPLAY_REJECTED',
                          caller_acceptance=False, error=str(error))
            (RUN_OUTPUT / 'receipt.json').write_text(json.dumps(failed, indent=2) + '\n')
        print('FRESH_CLOSED_REPLAY_REJECTED: ' + str(error), file=sys.stderr)
        sys.exit(1)
