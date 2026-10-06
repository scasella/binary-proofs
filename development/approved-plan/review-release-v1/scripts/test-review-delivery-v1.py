"""Consume the sealed document companion without changing mathematical inputs."""
import datetime, hashlib, json, subprocess, sys, tempfile, time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[4]
R = Path('development/approved-plan/review-release-v1')

def sha(path):
    h = hashlib.sha256()
    with path.open('rb') as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b''):
            h.update(block)
    return h.hexdigest()

delivery_path = ROOT / R / 'delivery/DELIVERY-FINAL-v1.json'
delivery = json.loads(delivery_path.read_text())
base = Path(tempfile.mkdtemp(prefix='bp-review-companion-', dir='/private/tmp'))
source = base / 'source'
started = datetime.datetime.now(datetime.timezone.utc).isoformat()
tick = time.monotonic()
commands = [
    [sys.executable, '-B', str(ROOT / R / 'delivery/extract-v1.py'),
     '--archive', str(ROOT / R / 'delivery/checking-sources-v1.tar.gz'),
     '--sha256', '7434fae0f89c9b3a0c58f455a3bd33826502213befea5be5f58bcb5355073e2a',
     '--output', str(source)],
    [sys.executable, '-B', str(ROOT / R / 'delivery/extract-review-v1.py'),
     '--archive', str(ROOT / delivery['review_archive']['path']),
     '--sha256', delivery['review_archive']['sha256'], '--output', str(source)]
]
steps = []
for number, command in enumerate(commands, 1):
    result = subprocess.run(command, text=True, capture_output=True, timeout=180)
    log = base / ('extraction-' + str(number) + '.log')
    log.write_text(result.stdout + result.stderr)
    steps.append(dict(argv=command, exit_code=result.returncode, log=str(log), log_sha256=sha(log)))
    if result.returncode:
        raise RuntimeError('Document consumption failed; diagnostic log: ' + str(log))

math = json.loads((source / R / 'inputs/release-inputs-v1.json').read_text())
for name, expected in math['files'].items():
    if sha(source / name) != expected:
        raise ValueError('Mathematical input changed during companion overlay: ' + name)
index = source / delivery['release_index']['path']
if sha(index) != delivery['release_index']['sha256']:
    raise ValueError('Extracted release index differs')
record = dict(
    schema='review-companion-consumption-v1',
    status='SEALED_COMPANION_EXTRACTED_AND_MATHEMATICAL_INPUT_IDENTITIES_PRESERVED',
    started_utc=started,
    completed_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
    elapsed_seconds=time.monotonic() - tick,
    source_root=str(source), steps=steps,
    delivery_manifest_sha256=sha(delivery_path),
    review_archive_sha256=delivery['review_archive']['sha256'],
    release_index_sha256=sha(index),
    mathematical_files_checked=len(math['files']),
    new_theorem_checking=False, human_review='PENDING',
    independence='Same host, fresh extraction root; no Docker use or human review',
    scope='Trusted Python extraction/identity checks after the complete mathematical consumer replay; not formal parser verification',
    evidence_placement='Supplement written after the sealed companion; not a member of that archive'
)
output = ROOT / R / 'delivery/companion-consumption-v1.json'
with output.open('x') as stream:
    json.dump(record, stream, indent=2, sort_keys=True)
    stream.write('\n')
print(json.dumps(dict(status=record['status'], receipt=str(output), seconds=record['elapsed_seconds']), indent=2))
