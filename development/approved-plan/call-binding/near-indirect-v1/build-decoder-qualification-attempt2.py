#!/usr/bin/env python3
import hashlib
from pathlib import Path
HERE = Path(__file__).resolve().parent
original = HERE / "decoder-qualification-proof-v1.ml"
if hashlib.sha256(original.read_bytes()).hexdigest() != "fbeac509dcd0f128e99ab8f7b796a9e5ea4d7ed571db9a0525de43fa1c94a67d":
    raise RuntimeError("Preserved failed recipe changed")
out = HERE / "decoder-qualification-proof-attempt2.ml"
if out.exists():
    raise RuntimeError("Never overwrite proof attempts")
text = original.read_text()
before = "REWRITE_TAC(r1_near_register :: r1_near_operand64 :: GPR_thms)"
assert text.count(before) == 49
out.write_text(text.replace(before, "REWRITE_TAC(JNE :: r1_near_register :: r1_near_operand64 :: GPR_thms)"))
print(hashlib.sha256(out.read_bytes()).hexdigest())
