#!/usr/bin/env python3
"""Index historical check outputs; omit duplicate materialized source trees.

Omitted source trees remain protected historical inputs. Their canonical exact
versions are already enumerated by seals/source indices, not reconstructed by
this navigation manifest. Copied negative fixtures are not new positive runs.
"""
from pathlib import Path
import hashlib, json, os

ROOT=Path(__file__).resolve().parents[4]
OUT=Path(__file__).resolve().parent
B="development/approved-plan/"
groups={
 "C1_final_positive":[B+"reusable-assurance-c1-successor-v1/runs/c1-fresh-final-v3"],
 "C1_final_controls":[B+"reusable-assurance-c1-successor-v1/runs/c1-targeted-controls-v3",B+"reusable-assurance-c1-successor-v1/runs/c1-missing-interface-probe-v3"],
 "C2_final_positive":[B+"reusable-assurance-c2-v1/runs/c2-fresh-final-v1"],
 "C2_final_controls":[B+"reusable-assurance-c2-v1/negative-controls/c2-controls-final-v1",B+"reusable-assurance-c2-v1/runs/c2-binding-probe-final-v1"],
 "C3_final_positive":[B+"c3-successor-v1/runs/fresh-final-v1"],
 "C3_final_controls":[B+"c3-successor-v1/runs/controls-final-v1",B+"c3-successor-v1/runs/binding-probe-final-v1"],
 "candidate_regressions":[B+"held-out-transfer-v1/regression/runs/c1-fresh-v1",B+"held-out-transfer-v1/regression/runs/c2-fresh-v1"],
 "C1_predecessor_failed_checks":[B+f"reusable-assurance-v1/runs/c1-fresh-final-v{i}" for i in [1,2,3]],
 "C3_postmortem":[B+"c3-postmortem-v1"],
}
result={"schema":"review-historical-evidence-file-map-v1","acceptance_input":False,
 "purpose":"Navigation and identity of raw historical checking/diagnostic outputs; copied fixture receipts never counted as positive attempts",
 "excluded_directory_components":["source","__pycache__"],"excluded_file_names":[".DS_Store"],
 "canonical_inputs":"Seals and selected-inputs-v1.json remain the versioned source authority",
 "groups":{}}
for group,roots in groups.items():
 files={}
 for root in roots:
  for directory,dirs,names in os.walk(ROOT/root):
   dirs[:]=[d for d in dirs if d not in ["source","__pycache__"]]
   for name in names:
    if name==".DS_Store":continue
    p=Path(directory)/name
    if not p.is_file():continue
    files[str(p.relative_to(ROOT))]={"sha256":hashlib.sha256(p.read_bytes()).hexdigest(),"bytes":p.stat().st_size}
 result["groups"][group]={"roots":roots,"file_count":len(files),"files":files}
with (OUT/"historical-evidence-files-v1.json").open("x") as f:
 json.dump(result,f,sort_keys=True,indent=2);f.write("\n")
print({k:v["file_count"] for k,v in result["groups"].items()})
