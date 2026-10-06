"""Seal companion documents/evidence without changing the consumed math bundle."""
import hashlib,json,tarfile
from pathlib import Path
ROOT=Path(__file__).resolve().parents[4];R=Path('development/approved-plan/review-release-v1')
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1024*1024),b''):h.update(b)
 return h.hexdigest()
selected=json.loads((ROOT/R/'index/review-evidence-inputs-v2.json').read_text());files=dict(selected['files'])
math=json.loads((ROOT/R/'inputs/release-inputs-v1.json').read_text())['files']
for p in (ROOT/R).rglob('*'):
 if not p.is_file():continue
 name=str(p.relative_to(ROOT))
 if name in math:continue
 if p.name.endswith('.tar') or p.name.endswith('.tar.gz'):
  if name!=str(R/'consumer/evidence-v1.tar.gz'):continue
 # Outer/self manifests are acyclic and written after this seal.
 if name in [str(R/'delivery/DELIVERY-FINAL-v1.json'),str(R/'inputs/review-companion-v1.json')]:continue
 if p.suffix=='.pyc' or '__pycache__' in p.parts:continue
 files[name]=sha(p)
for name,digest in files.items():
 p=ROOT/name
 if p.is_symlink() or not p.is_file() or sha(p)!=digest:raise ValueError('Changed/nonregular companion input: '+name)
manifest=ROOT/R/'inputs/review-companion-v1.json'
with manifest.open('x') as f:json.dump(dict(schema='review-release-companion-v1',files=dict(sorted(files.items())),checking_source_archive_identity='7434fae0f89c9b3a0c58f455a3bd33826502213befea5be5f58bcb5355073e2a',mathematical_replay_inputs='Unchanged separate already-consumed checking source archive',human_review='PENDING',role='Documents and recorded historical/consumer evidence; never a substitute for fresh theorem reconstruction'),f,indent=2,sort_keys=True);f.write('\n')
archive=ROOT/R/'delivery/review-evidence-v1.tar.gz'
with archive.open('xb') as stream:
 with tarfile.open(fileobj=stream,mode='w:gz') as tar:
  for name in sorted([*files,str(manifest.relative_to(ROOT))]):tar.add(ROOT/name,arcname=name,recursive=False)
record=dict(schema='review-release-final-delivery-v1',release_index=dict(path=str(R/'release-index-v1.json'),sha256=sha(ROOT/R/'release-index-v1.json')),review_archive=dict(path=str(archive.relative_to(ROOT)),sha256=sha(archive),bytes=archive.stat().st_size,files=len(files)+1),review_manifest=dict(path=str(manifest.relative_to(ROOT)),sha256=sha(manifest)),checking_source_delivery=json.loads((ROOT/R/'delivery/delivery-v1.json').read_text()),bootstrap_extractors={x:sha(ROOT/R/'delivery'/x) for x in ['extract-v1.py','extract-review-v1.py']},human_review='PENDING',status='REVIEW_READY_WITH_CHECKING_ONLY_CONSUMER_ACCEPTANCE')
with (ROOT/R/'delivery/DELIVERY-FINAL-v1.json').open('x') as f:json.dump(record,f,indent=2,sort_keys=True);f.write('\n')
print(json.dumps(record,indent=2))
