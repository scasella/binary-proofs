#!/usr/bin/env python3
"""Check fresh supplier live-object audits against its original sealed policy.

The supplier's pinned ML auditors reconstruct and inspect theorem objects.
This host check cannot convert saved JSON or a success log into a proof.
Its caller must enforce the fresh checking process and immutable inputs.
"""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import sys

INDEX_SHA = '0381c183d1d86da7b4b030224281c1668379f3b7c52154843e1afd20ac206905'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def audit(source_root, output):
    index_path = Path(__file__).with_name('source-index-v1.json')
    if sha(index_path) != INDEX_SHA:
        raise ValueError('Supplier index changed')
    index = json.loads(index_path.read_text())
    for key in ['seal', 'host_driver']:
        path = source_root / index[key]
        if path.is_symlink() or not path.is_file() or sha(path) != index[key + '_sha256']:
            raise ValueError('Supplier checking policy changed: ' + key)
    seal = json.loads((source_root / index['seal']).read_text())
    cached_check = sys.modules.get('check')
    if cached_check is not None and Path(cached_check.__file__).resolve() != (source_root / 'scripts/check.py').resolve():
        raise ValueError('Supplier host policy would reuse a check module from another source root')
    spec = importlib.util.spec_from_file_location('opaque_e3_original_host_policy',
                                               source_root / index['host_driver'])
    module = importlib.util.module_from_spec(spec)
    previous_bytecode_policy = sys.dont_write_bytecode
    try:
        sys.dont_write_bytecode = True
        spec.loader.exec_module(module)
    finally:
        sys.dont_write_bytecode = previous_bytecode_policy
    if Path(sys.modules['check'].__file__).resolve() != (source_root / 'scripts/check.py').resolve():
        raise ValueError('Supplier host policy imported check from another source root')
    audits = {}
    for group in seal['groups']:
        filename = group.get('audit_file', group.get('file'))
        if not filename:
            raise ValueError('Supplier group audit filename absent')
        path = output / filename
        if path.is_symlink() or not path.is_file():
            raise ValueError('Missing fresh supplier audit: ' + filename)
        audits[filename] = json.loads(path.read_text())
    exact = audits.get('e3-interface.json')
    if exact is None or exact.get('all_equation_check_count') != 218:
        raise ValueError('Missing complete supplier equation audit')
    expanded_rows = exact.get('expanded_definitions', [])
    exact_rows = {row['name']: row for row in expanded_rows}
    if len(expanded_rows) != len(exact_rows) or len(exact_rows) != 119:
        raise ValueError('Incomplete exact supplier definition registry')
    theorem_names = set()
    definition_names = set()
    for group in seal['groups']:
        filename = group.get('audit_file', group.get('file'))
        value = audits[filename]
        if not module.validate_group(value, group, exact_rows):
            raise ValueError('Supplier live audit rejected: ' + filename)
        theorem_names.update(row['name'] for row in value.get('theorems', []))
        key = group.get('definitions_key')
        if key:
            group_names = [row['name'] for row in value.get(key, [])]
            if len(group_names) != len(set(group_names)):
                raise ValueError('Duplicate supplier definition row: ' + filename)
            definition_names.update(group_names)
    if (theorem_names != set(seal['expected_unique_theorems'])
            or set(exact_rows) != set(seal['expected_definition_names'])
            or len(theorem_names) != 325):
        raise ValueError('Supplier complete theorem/definition registry mismatch')
    return {'status': 'PASS_SUPPLIER_LIVE_AUDIT_POLICY', 'group_count': len(audits),
            'unique_theorems': len(theorem_names), 'unique_definitions': len(exact_rows),
            'equation_count': 218, 'audits': audits,
            'freshness_and_source_immutability_required_from_enclosing_driver': True,
            'saved_receipt_alone_accepted': False}


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--source-root', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    print(json.dumps(audit(args.source_root, args.output), indent=2, sort_keys=True))
