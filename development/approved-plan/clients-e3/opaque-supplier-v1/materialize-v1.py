#!/usr/bin/env python3
"""Restore frozen supplier sources; this operation grants no proof acceptance."""
import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath
import shutil
import tarfile

INDEX_SHA = '0381c183d1d86da7b4b030224281c1668379f3b7c52154843e1afd20ac206905'


def sha(path):
    h = hashlib.sha256()
    with path.open('rb') as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b''):
            h.update(chunk)
    return h.hexdigest()


def safe(name):
    p = PurePosixPath(name)
    if p.is_absolute() or '..' in p.parts or not p.parts:
        raise ValueError('Unsafe supplier path: ' + name)
    return name


def checked(root, name, digest):
    path = root / safe(name)
    if path.is_symlink() or not path.is_file() or sha(path) != digest:
        raise ValueError('Missing/changed supplier input: ' + name)
    return path


def inputs(source_root):
    path = Path(__file__).with_name('source-index-v1.json')
    if sha(path) != INDEX_SHA:
        raise ValueError('Supplier index changed')
    index = json.loads(path.read_text())
    for key in ['seal', 'preservation_receipt', 'archive_path']:
        checked(source_root, index[key], index[key.replace('_path', '') + '_sha256']
                if key == 'archive_path' else index[key + '_sha256'])
    for name, digest in index['extra_files'].items():
        checked(source_root, name, digest)
    if (len(index['preserved_files']) != 4049 or len(index['extra_files']) != 485
            or len(index['source_files']) != 4534
            or set(index['preserved_files']) & set(index['extra_files'])
            or index['source_files'] != {**index['preserved_files'], **index['extra_files']}):
        raise ValueError('Unexpected supplier source partition')
    return index


def materialize(source_root, destination):
    index = inputs(source_root)
    destination.mkdir(parents=True, exist_ok=False)
    seen = set()
    with tarfile.open(source_root / index['archive_path'], 'r:gz') as archive:
        for member in archive.getmembers():
            name = safe(member.name)
            if name in seen or name not in index['preserved_files'] or not member.isfile():
                raise ValueError('Unexpected preservation member: ' + name)
            seen.add(name)
            path = destination / name
            path.parent.mkdir(parents=True, exist_ok=True)
            with archive.extractfile(member) as source, path.open('xb') as target:
                shutil.copyfileobj(source, target)
            path.chmod(member.mode & 0o777)
            checked(destination, name, index['preserved_files'][name])
    if seen != set(index['preserved_files']):
        raise ValueError('Incomplete preservation archive')
    for name, digest in index['extra_files'].items():
        path = destination / name
        path.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(checked(source_root, name, digest), path)
        checked(destination, name, digest)
    # The acyclic enclosing seal is host-policy metadata, outside the 4534
    # executable/foundation source union. Host auditing imports only this
    # restored tree, including its original pinned scripts/check.py.
    seal_path = destination / index['seal']
    seal_path.parent.mkdir(parents=True, exist_ok=True)
    shutil.copy2(checked(source_root, index['seal'], index['seal_sha256']), seal_path)
    checked(destination, index['seal'], index['seal_sha256'])
    return index


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--source-root', type=Path, required=True)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    index = (materialize(args.source_root, args.output) if args.output
             else inputs(args.source_root))
    print(json.dumps({'status': 'PASS_SOURCE_GUARDS_NOT_PROOF', 'source_count': 4534,
                      'index_sha256': INDEX_SHA, 'proof_started': False,
                      'source_materialized': args.output is not None}, sort_keys=True))
