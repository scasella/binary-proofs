"""Build a closed checking-source archive; immutable accepted inputs, no caches."""
import hashlib,json,tarfile
from pathlib import Path
ROOT=Path(__file__).resolve().parents[4];R='development/approved-plan/review-release-v1'
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for block in iter(lambda:f.read(1024*1024),b''):h.update(block)
 return h.hexdigest()
cases={
 'C1':dict(seal='development/approved-plan/reusable-assurance-c1-successor-v1/replay/c1-successor-final-v3-seal.json',seal_sha256='556fe357859921992293b7eedd7fc1338bf737502069502b50cdfffe5e114a0c',controls='development/approved-plan/reusable-assurance-c1-successor-v1/replay/targeted-preflight-controls-v3.py',probe='development/approved-plan/reusable-assurance-c1-successor-v1/replay/missing-interface-probe-v3.py'),
 'C2':dict(seal='development/approved-plan/reusable-assurance-c2-v1/replay/c2-final-v1-seal.json',seal_sha256='8f9e56c35e5a60f376356dc7abd242decbd788e1cb54d0e9f4ef23d8f1af9022',controls='development/approved-plan/reusable-assurance-c2-v1/replay/targeted-preflight-controls-v1.py',probe='development/approved-plan/reusable-assurance-c2-v1/replay/missing-interface-probe-v1.py'),
 'C3':dict(seal='development/approved-plan/c3-successor-v1/replay/c3-successor-final-v1-seal.json',seal_sha256='903c92086ade0594eda090832ee769e3415c741dfc20573a4c94fef1c6612f46',controls='development/approved-plan/c3-successor-v1/replay/targeted-preflight-controls-v1.py',probe='development/approved-plan/c3-successor-v1/replay/missing-interface-probe-v1.py')}
files={}
def add(path,digest):
 if path in files and files[path]!=digest:raise ValueError('Conflicting sealed input: '+path)
 if sha(ROOT/path)!=digest:raise ValueError('Changed selected input: '+path)
 files[path]=digest
for case in cases.values():
 add(case['seal'],case['seal_sha256']);s=json.loads((ROOT/case['seal']).read_text())
 for key in ['host_inputs','additional_stage_inputs']:
  for path,digest in s[key].items():add(path,digest)
 for path,node in s['graph'].items():add(path,node['sha256'])
 supplier=s['supplier'];add(supplier['index'],supplier['index_sha256']);ix=json.loads((ROOT/supplier['index']).read_text())
 for path,digest in ix['extra_files'].items():add(path,digest)
 for key in ['seal','preservation_receipt','archive_path']:add(ix[key],ix[key.replace('_path','')+'_sha256'])
# Evidence is review material, never an alternative to the source reconstruction.
evidence=json.loads((ROOT/(R+'/index/historical-evidence-files-v1.json')).read_text())
# selected review index contains evidence map separately; archive only necessary checking inputs.
for dir in ['replay','scripts']:
 for p in (ROOT/R/dir).iterdir():
  if p.is_file():add(str(p.relative_to(ROOT)),sha(p))
add(R+'/STAGE-v1.json',sha(ROOT/(R+'/STAGE-v1.json')))
manifest=ROOT/(R+'/inputs/release-inputs-v1.json')
with manifest.open('x') as f:json.dump(dict(schema='review-release-checking-inputs-v1',cases=cases,files=dict(sorted(files.items())),supplier_source_partition='4049 exact preserved sources inside digest-checked archive plus485 exact extras; materializer reconstructs all4534 from source',human_review='PENDING',proof_objects_in_package=False,saved_success_used_for_proof=False),f,indent=2,sort_keys=True);f.write('\n')
archive=ROOT/(R+'/delivery/checking-sources-v1.tar.gz')
with archive.open('xb') as stream:
 with tarfile.open(fileobj=stream,mode='w:gz') as tar:
  for path in sorted([*files,str(manifest.relative_to(ROOT))]):tar.add(ROOT/path,arcname=path,recursive=False)
record=dict(schema='review-release-delivery-v1',checking_source_archive=str(archive.relative_to(ROOT)),checking_source_archive_sha256=sha(archive),checking_source_bytes=archive.stat().st_size,input_manifest=str(manifest.relative_to(ROOT)),input_manifest_sha256=sha(manifest),delivered_file_count=len(files)+1,docker_image_archive=R+'/delivery/docker-images-v1.tar',docker_image_archive_sha256=sha(ROOT/(R+'/delivery/docker-images-v1.tar')),docker_image_archive_bytes=(ROOT/(R+'/delivery/docker-images-v1.tar')).stat().st_size,scope='Immutable checking inputs; final review documents/evidence delivered separately. This archive does not contain saved caller theorem objects. Historical JSON metadata is not proof acceptance.',human_review='PENDING')
with (ROOT/(R+'/delivery/delivery-v1.json')).open('x') as f:json.dump(record,f,indent=2,sort_keys=True);f.write('\n')
print(json.dumps(record,indent=2))
