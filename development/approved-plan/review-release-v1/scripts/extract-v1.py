#!/usr/bin/env python3
"""Digest-checked, non-link, relative-path release extraction; trusted Python."""
import argparse,hashlib,json,shutil,tarfile
from pathlib import Path,PurePosixPath

def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for block in iter(lambda:f.read(1024*1024),b''):h.update(block)
 return h.hexdigest()
p=argparse.ArgumentParser();p.add_argument('--archive',type=Path,required=True);p.add_argument('--sha256',required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args()
if sha(a.archive)!=a.sha256:raise ValueError('Delivered archive digest mismatch')
a.output.mkdir(parents=True,exist_ok=False);seen=set()
with tarfile.open(a.archive,'r:gz') as ar:
 for m in ar:
  rel=PurePosixPath(m.name)
  if rel.is_absolute() or '..' in rel.parts or not rel.parts or str(rel)!=m.name or not m.isfile() or m.name in seen:raise ValueError('Unsafe/duplicate/nonregular delivered member')
  seen.add(m.name);dest=a.output/m.name;dest.parent.mkdir(parents=True,exist_ok=True)
  with ar.extractfile(m) as src,dest.open('xb') as out:shutil.copyfileobj(src,out)
  dest.chmod(m.mode&0o777)
manifest=a.output/'development/approved-plan/review-release-v1/inputs/release-inputs-v1.json';data=json.loads(manifest.read_text())
for path,digest in data['files'].items():
 if sha(a.output/path)!=digest:raise ValueError('Extracted input differs: '+path)
if seen!=set(data['files'])|{str(manifest.relative_to(a.output))}:raise ValueError('Delivered archive has unlisted/missing input')
print(json.dumps(dict(status='EXTRACTED_INPUT_IDENTITIES_CHECKED_NOT_PROOF',file_count=len(seen),input_manifest_sha256=sha(manifest),root=str(a.output.resolve())),indent=2))
