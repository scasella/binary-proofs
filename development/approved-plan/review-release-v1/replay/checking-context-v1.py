"""Operational-only C3 checking seal projection; no theorem or ISA changes."""
import datetime, hashlib, json
from pathlib import Path
R = 'development/approved-plan/review-release-v1'
PARENT = 'development/approved-plan/c3-successor-v1/replay/c3-successor-final-v1-seal.json'
PARENT_SHA = '903c92086ade0594eda090832ee769e3415c741dfc20573a4c94fef1c6612f46'

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def validate(root, seal):
    if sha(root / PARENT) != PARENT_SHA:
        raise ValueError('Original accepted C3 seal changed')
    parent = json.loads((root / PARENT).read_text())
    newkeys = {'checking_only', 'release_checking_context', 'release_checking_context_sha256',
               'parent_accepted_seal', 'parent_accepted_seal_sha256'}
    changed = {'host_driver', 'root_gate', 'driver_sha256', 'additional_stage_inputs'}
    if set(seal) != set(parent) | newkeys:
        raise ValueError('Unexpected checking seal fields')
    for key in set(parent) - changed:
        if seal[key] != parent[key]:
            raise ValueError('Protected original C3 seal field changed: ' + key)
    for key in ('host_inputs', 'additional_stage_inputs'):
        for path, digest in parent[key].items():
            if seal[key].get(path) != digest:
                raise ValueError('Protected original input changed: ' + path)
    if (seal['checking_only'] is not True or seal['parent_accepted_seal'] != PARENT
        or seal['parent_accepted_seal_sha256'] != PARENT_SHA
        or seal['host_driver'] != R + '/replay/c3-fresh-check-v1.py'
        or seal['root_gate'] != R + '/replay/c3-root-check-v1.py'
        or seal['driver_sha256'] != sha(root / seal['host_driver'])):
        raise ValueError('Wrong checking-only adapter identity')
    additions = set(seal['additional_stage_inputs']) - set(parent['additional_stage_inputs'])
    wanted = {PARENT, R + '/STAGE-v1.json', R + '/replay/checking-context-v1.py',
              seal['host_driver'], seal['root_gate'], seal['release_checking_context']}
    if additions != wanted:
        raise ValueError('Unexpected checking-only additional inputs')
    for path in wanted:
        rel = Path(path)
        if rel.is_absolute() or '..' in rel.parts or (root / rel).is_symlink():
            raise ValueError('Unsafe checking context path')
        if sha(root / rel) != seal['additional_stage_inputs'][path]:
            raise ValueError('Changed checking operational input: ' + path)
    context = json.loads((root / seal['release_checking_context']).read_text())
    if (sha(root / seal['release_checking_context']) != seal['release_checking_context_sha256']
        or context['schema'] != 'c3-later-checking-context-v1'
        or context['checking_only'] is not True
        or context['parent_accepted_seal_sha256'] != PARENT_SHA
        or context['session_limit_seconds'] != 5400
        or context['per_invocation_seconds'] != 1800):
        raise ValueError('Wrong later checking policy')
    start = datetime.datetime.fromisoformat(context['start_utc'])
    deadline = datetime.datetime.fromisoformat(context['deadline_utc'])
    if start.utcoffset() != datetime.timedelta(0) or deadline - start != datetime.timedelta(seconds=5400):
        raise ValueError('Wrong later checking clock envelope')
    policy = json.loads((root / (R + '/STAGE-v1.json')).read_text())
    if (policy['checking_case_session_limit_seconds'] != 5400 or policy['checking_limits'] != dict(
        per_invocation_seconds=1800, cpu_count=1, memory_bytes=3221225472,
        swap_limit_bytes=3221225472, network='none')):
        raise ValueError('Changed release resource policy')
    return context
