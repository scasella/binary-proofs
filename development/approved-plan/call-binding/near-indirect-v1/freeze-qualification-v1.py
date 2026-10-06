#!/usr/bin/env python3
"""Seal the successful candidate qualification recipes without replacing E2."""
import datetime
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
names = ["requirements.freeze-v1.json", "checking-freeze-v5.json",
         "decode-attempt5.ml", "x86-attempt5.ml", "candidate5-manifest.json",
         "build-overlay-attempt5.py", "REVIEW-v1.md",
         "qualification-statements-v1.ml", "qualification-proof-attempt2.ml",
         "expected-qualification-v1.json", "decoder-qualification-proof-attempt2.ml",
         "qualification-audit-v2.ml", "fresh-qualification-input-v1.ml",
         "replay-qualification-v1.py", "freeze-qualification-v1.py",
         "prepare-decoder-qualification-v1.py", "build-qualification-audit-v1.py",
         "build-decoder-qualification-attempt2.py"]
paths = [HERE / n for n in names]
paths += [ROOT / "third_party/hol-light/pa_j.ml",
          ROOT / "third_party/hol-light/update_database.ml",
          ROOT / "development/approved-plan/integrity/runtime-supplement.json",
          ROOT / "development/approved-plan/abi-qualification/docs/intel-vol2a.pdf"]
def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()
out = HERE / "qualification-seal-v1.json"
if out.exists():
    raise RuntimeError("A new seal version is required")
seal = {"id": "BP-E3-NEAR-INDIRECT-CANDIDATE5-QUALIFICATION-V1",
        "experiment_id": "BP-20260930-E3-NEAR-INDIRECT",
        "created_at_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "scope": "CANDIDATE_NEAR_INDIRECT_ISA_QUALIFICATION_ONLY",
        "human_review": "PENDING", "model_candidate_accepted_for_clients": False,
        "E2_original_acceptance_unchanged": True,
        "checker_image_id": "sha256:a19fdc18f1f283ed8e2514229b77f33619df1ba0ea1ae578c97779f4b4eb3c3f",
        "preservation_receipt": "results/preservation/BP-E1-CHECKING-V2.json",
        "preservation_receipt_sha256": "c7a88d2909f9cfd8e60bb4a682b1033dbcfb926048f662c93caa78b682ce8d38",
        "decoder": str((HERE / "decode-attempt5.ml").relative_to(ROOT)),
        "executor": str((HERE / "x86-attempt5.ml").relative_to(ROOT)),
        "driver": str((HERE / "fresh-qualification-input-v1.ml").relative_to(ROOT)),
        "expected_terms": str((HERE / "expected-qualification-v1.json").relative_to(ROOT)),
        "expected_theorem_count": 53, "expected_model_definition_count": 7,
        "trust_assumption_ids": ["HOL_KERNEL_RUNTIME_V1", "S2N_X86_PINNED_V1",
                                 "REP_RET_DECODER_V1", "NEAR_INDIRECT_GENERIC_LONGMODE_V1_CANDIDATE5",
                                 "FINAL_ELF_ACQUISITION_LOADING_V2"],
        "files": {str(p.relative_to(ROOT)): sha(p) for p in paths}}
out.write_text(json.dumps(seal, indent=2, sort_keys=True) + "\n")
print(json.dumps({"seal": str(out.relative_to(ROOT)), "sha256": sha(out),
                  "scope": seal["scope"]}))
