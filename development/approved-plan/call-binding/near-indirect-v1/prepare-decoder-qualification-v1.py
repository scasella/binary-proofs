#!/usr/bin/env python3
"""Freeze independent long-mode decoder expectations before proof construction.

The finite cases supplement generic executor lemmas. They are not a universal
decoder-correctness claim or a production-client correctness claim.
"""
import datetime
import hashlib
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
prefixes = {"NONE": [], "REX0": [0x40], "REXW": [0x48],
            "OSZ": [0x66], "OSZ_REX0": [0x66, 0x40],
            "OSZ_REXW": [0x66, 0x48]}
forms = {
    "RIP_JMP": ([0xff, 0x25, 0x92, 0x2f, 0, 0],
                "JMP(Memop Quadword (Riprel(word 0x2f92)))"),
    "RIP_CALL": ([0xff, 0x15, 0x92, 0x2f, 0, 0],
                 "CALL(Memop Quadword (Riprel(word 0x2f92)))"),
    "REGISTER_JMP": ([0xff, 0xe0], "JMP(Register rax)"),
    "REGISTER_CALL": ([0xff, 0xd0], "CALL(Register rax)"),
    "RSP_CALL_TOP": ([0xff, 0x14, 0x24],
                     "CALL(Memop Quadword (%%(rsp,0)))"),
    "RSP_CALL_ALIAS": ([0xff, 0x54, 0x24, 0xf8],
                       "CALL(Memop Quadword (%%(rsp,18446744073709551608)))"),
    "RSP_JMP_NEXT": ([0xff, 0x64, 0x24, 8],
                     "JMP(Memop Quadword (%%(rsp,8)))")}
claims = []
def add(name, code, instruction):
    encoded = ";".join("word 0x%x" % b for b in code)
    claims.append({"name": name,
                   "statement": f"decode [{encoded}] = SOME({instruction},[])",
                   "bytes_hex": bytes(code).hex(), "instruction": instruction})
for symbol, displacement in [("CRYPTO_MEMCMP", 0x2f92),
                              ("OPENSSL_CLEANSE", 0x2f8a),
                              ("MEMCMP", 0x2f82)]:
    add("R1_NEAR_PLT_" + symbol,
        [0xff, 0x25] + list(displacement.to_bytes(4, "little")),
        "JMP(Memop Quadword (Riprel(word 0x%x)))" % displacement)
for p_name, prefix in prefixes.items():
    for f_name, (code, instruction) in forms.items():
        add("R1_NEAR_DECODE_" + p_name + "_" + f_name,
            prefix + code, instruction)
add("R1_RELATIVE_DECODE_CALL", [0xe8, 1, 0, 0, 0], "CALL(Imm32(word 1))")
add("R1_RELATIVE_DECODE_JMP", [0xe9, 1, 0, 0, 0], "JMP(Imm32(word 1))")
add("R1_RELATIVE_DECODE_JNZ", [0x75, 1], "JUMP Condition_NZ (Imm8(word 1))")
add("R1_PREVIOUS_REP_RET_DECODE", [0xf3, 0xc3], "RET")
assert len(claims) == 49
frozen_executor = HERE / "qualification-statements-v1.ml"
source = frozen_executor.read_text()
executor_claims = []
for name, statement in re.findall(r"let (\w+)_STATEMENT\s*=\s*`(.*?)`;;", source, re.S):
    executor_claims.append({"name": name, "statement": statement})
assert len(executor_claims) == 4
definitions = []
for path, names in [(HERE / "decode-attempt5.ml",
                      ["r1_near_register", "r1_near_operand64", "decode_hi", "decode_aux"]),
                    (HERE / "x86-attempt5.ml",
                      ["r1_indirect_operand", "x86_JMP_ABSOLUTE", "x86_execute"])]:
    content = path.read_text()
    for name in names:
        m = re.search(r"let " + re.escape(name) + r"\s*=\s*(?:define|new_definition)\s*`(.*?)`;;", content, re.S)
        if m is None:
            raise RuntimeError("Missing explicit model definition: " + name)
        # Generalized free variables are stripped on the checked side as well.
        definitions.append({"name": name, "equation": m.group(1),
                            "source": str(path.relative_to(ROOT)),
                            "source_sha256": hashlib.sha256(path.read_bytes()).hexdigest()})
out = HERE / "expected-qualification-v1.json"
if out.exists():
    raise RuntimeError("Never overwrite frozen expectations")
out.write_text(json.dumps({"created_at_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
                          "id": "NEAR_INDIRECT_QUALIFICATION_EXPECTATIONS_V1",
                          "human_review": "PENDING",
                          "decoder_expectations_frozen_before_construction": True,
                          "executor_statement_source_pre_search_sha256": hashlib.sha256(frozen_executor.read_bytes()).hexdigest(),
                          "decoder_claims": claims, "executor_claims": executor_claims,
                          "definitions": definitions}, indent=2) + "\n")
print(json.dumps({"path": str(out.relative_to(ROOT)),
                  "sha256": hashlib.sha256(out.read_bytes()).hexdigest(),
                  "decoder_count": len(claims), "executor_count": len(executor_claims),
                  "model_definitions": len(definitions)}))
