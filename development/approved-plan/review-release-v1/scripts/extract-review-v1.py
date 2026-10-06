#!/usr/bin/env python3
"""Extract sealed review companion; never replace a differing existing file."""
import argparse,hashlib,json,shutil,tarfile
from pathlib import Path,PurePosixPath
R='development/approved-plan/review-release-v1'
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1024*1024),b''):h.update(b)
 return h.hexdigest()
p=argparse.ArgumentParser();p.add_argument('--archive',type=Path,required=True);p.add_argument('--sha256',required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args()
if sha(a.archive)!=a.sha256:raise ValueError('Review archive differs from external digest')
a.output.mkdir(parents=True,exist_ok=True);seen=set()
with tarfile.open(a.archive,'r:gz') as tar:
 manifest_name=R+'/inputs/review-companion-v1.json';m=tar.getmember(manifest_name)
 if not m.isfile():raise ValueError('Review manifest is not regular')
 with tar.extractfile(m) as f:manifest=json.load(f)
 for member in tar:
  rel=PurePosixPath(member.name)
  if rel.is_absolute() or '..' in rel.parts or not rel.parts or str(rel)!=member.name or not member.isfile() or member.name in seen:raise ValueError('Unsafe/duplicate review member')
  if member.name not in manifest['files'] and member.name!=manifest_name:raise ValueError('Unlisted review member')
  seen.add(member.name);dest=a.output/member.name
  if any(a.output.joinpath(*rel.parts[:i]).is_symlink() for i in range(len(rel.parts)+1)):raise ValueError('Symlink review destination')
  expected=manifest['files'].get(member.name)
  if dest.exists():
   if not dest.is_file() or expected is None or sha(dest)!=expected:raise ValueError('Refusing differing existing review destination')
   continue
  dest.parent.mkdir(parents=True,exist_ok=True)
  with tar.extractfile(member) as src,dest.open('xb') as out:shutil.copyfileobj(src,out)
  dest.chmod(member.mode&0o777)
  if expected is not None and sha(dest)!=expected:raise ValueError('Extracted review digest mismatch')
if seen!=set(manifest['files'])|{manifest_name}:raise ValueError('Incomplete review archive')
print(json.dumps(dict(status='REVIEW_COMPANION_IDENTITIES_CHECKED_NOT_HUMAN_REVIEW_OR_PROOF',file_count=len(seen),output=str(a.output.resolve())),indent=2))
