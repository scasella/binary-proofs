#!/usr/bin/env python3
"""Snapshot protected historical inputs, without modifying those inputs.

Use --output for a new immutable snapshot, then --compare START for an end
comparison. File content, symlink targets and file type are checked. Dynamic
bytecode caches and Finder metadata are excluded by an explicit convention.
Permissions/times are not claimed as preserved by this content check.
"""
from pathlib import Path
import argparse, datetime, hashlib, json, os, stat

ROOT=Path(__file__).resolve().parents[4]
R="development/approved-plan/review-release-v1"
B="development/approved-plan/"
TREES=[
 B+"reusable-assurance-v1",
 B+"reusable-assurance-c1-successor-v1",
 B+"reusable-assurance-c2-v1",
 B+"held-out-transfer-v1",
 B+"c3-postmortem-v1",
 B+"c3-successor-v1",
]
def load(p):return json.loads((ROOT/p).read_text())
def identity(p):
 st=p.lstat()
 if stat.S_ISLNK(st.st_mode):return {"kind":"symlink","target":os.readlink(p)}
 if stat.S_ISREG(st.st_mode):
  h=hashlib.sha256()
  with p.open("rb") as f:
   for chunk in iter(lambda:f.read(1024*1024),b""):h.update(chunk)
  return {"kind":"file","sha256":h.hexdigest(),"bytes":st.st_size}
 return {"kind":"other","file_type":stat.S_IFMT(st.st_mode)}
def excluded(rel):
 return any(part in ["__pycache__",".pytest_cache"] for part in rel.parts) or rel.name==".DS_Store" or rel.suffix in [".pyc",".pyo"]

p=argparse.ArgumentParser()
p.add_argument("--output",type=Path,required=True)
p.add_argument("--compare",type=Path)
a=p.parse_args()
out=a.output.resolve()
if ROOT not in out.parents or R not in str(out.relative_to(ROOT)):
 raise SystemExit("Output must be a new path under review-release-v1")
paths=set()
tree_counts={}
exclusions=[]
for tree in TREES:
 count=0
 for directory,dirs,names in os.walk(ROOT/tree,followlinks=False):
  retained=[]
  for d in dirs:
   q=Path(directory)/d;rel=q.relative_to(ROOT)
   if excluded(rel):exclusions.append(str(rel));continue
   if q.is_symlink():paths.add(rel);count+=1
   else:retained.append(d)
  dirs[:]=retained
  for n in names:
   q=Path(directory)/n;rel=q.relative_to(ROOT)
   if excluded(rel):exclusions.append(str(rel));continue
   paths.add(rel);count+=1
 tree_counts[tree]=count

# Exact accepted model/supplier/caller source paths and supporting inputs.
# The supplier's archive version is independently identified; root-path content
# is snapshotted as found, rather than assumed equal to a preserved archive.
index_path=B+"clients-e3/opaque-supplier-v1/source-index-v1.json"
index=load(index_path)
extra_sources=set(index["source_files"])
extra_sources.add(index_path)
extra_sources.add(index["archive_path"])
for path in ["locks/baseline.json","locks/proof-inputs.json","locks/local-images.json",
 "locks/client-toolchain.json","inventory/artifacts.json","PROMPT.md","TRUST.md",
 "report/FORMAL-AND-TRUST.md","spec/e5/CLAIM-CHANGES-v1.md"]:
 extra_sources.add(path)
draft=load(R+"/index/release-index-draft-v1.json")
for case in draft["cases"].values():
 extra_sources.update(case["graph"])
 extra_sources.update(case["sealed_additional_inputs"])
 extra_sources.update(case["host_inputs"])
 for item in case["operational_sources"].values():extra_sources.add(item["path"])
extra_sources.update(draft["candidate_layer"]["candidate_inputs"])
extra_sources.update(draft["candidate_layer"]["direct_dependency_pins"])
absent=[]
for path in sorted(extra_sources):
 rel=Path(path)
 if str(rel).startswith(R) or excluded(rel):continue
 q=ROOT/rel
 if q.exists() or q.is_symlink():paths.add(rel)
 else:absent.append(path)
files={str(path):identity(ROOT/path) for path in sorted(paths)}
result={
 "schema":"review-release-protected-input-preservation-v1",
 "created_utc":datetime.datetime.now(datetime.timezone.utc).isoformat(),
 "source_root":str(ROOT),"acceptance_input":False,
 "protected_trees":TREES,"tree_entry_counts":tree_counts,
 "identity_scope":"File contents and types plus symbolic-link targets; no permission/time preservation claim",
 "excluded_conventions":{"directories":["__pycache__",".pytest_cache"],"file_names":[".DS_Store"],"file_suffixes":[".pyc",".pyo"],"release_workstream":R},
 "observed_excluded_paths":sorted(set(exclusions)),
 "extra_supplier_model_input_paths":sorted(extra_sources),
 "absent_root_paths_from_historical_supplier_index":absent,
 "supplier_archive_path":index["archive_path"],"supplier_archive_expected_sha256":index["archive_sha256"],
 "historical_archive_version_rule":"Current-root snapshots preserve what was present. Accepted supplier reconstruction uses pinned archive plus extra_files, not current mutable root versions by name.",
 "file_count":len(files),"files":files,
}
if a.compare:
 old=json.loads(a.compare.read_text())
 oldfiles=old["files"]
 removed=sorted(set(oldfiles)-set(files));added=sorted(set(files)-set(oldfiles))
 changed=sorted(k for k in set(oldfiles)&set(files) if oldfiles[k]!=files[k])
 result["comparison"]={"start_path":str(a.compare),"start_sha256":hashlib.sha256(a.compare.read_bytes()).hexdigest(),
  "removed":removed,"added":added,"changed":changed,"status":"PASS" if not (removed or added or changed) else "FAIL"}
with out.open("x") as f:json.dump(result,f,indent=2,sort_keys=True);f.write("\n")
print(json.dumps({"output":str(out),"file_count":len(files),"tree_entry_counts":tree_counts,"absent_root_path_count":len(absent),"comparison":result.get("comparison")},indent=2))
if result.get("comparison",{}).get("status")=="FAIL":raise SystemExit(1)
