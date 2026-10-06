#!/usr/bin/env python3
"""Create an explicit candidate; never mutate the original model or target ELF."""
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[4]
HERE = Path(__file__).resolve().parent


def replace_once(text, before, after):
    if text.count(before) != 1:
        raise RuntimeError("Pinned source pattern changed")
    return text.replace(before, after)


decoder_path = ROOT / "proofs/model-extension/decode.ml"
executor_path = ROOT / "third_party/s2n-bignum/x86/proofs/x86.ml"
decoder = decoder_path.read_text()
executor = executor_path.read_text()
decoder_helpers = r'''
(* NEAR_INDIRECT_GENERIC_LONGMODE_V1 candidate. No target identity is used. *)
let r1_near_register = define
 `r1_near_register (Gpr r sz) = Gpr r Full_64`;;
let r1_near_operand64 = define
 `(r1_near_operand64 (Register r) = Register (r1_near_register r)) /\
  (r1_near_operand64 (Simdregister simd_r) = Simdregister simd_r) /\
  (r1_near_operand64 (Imm8 immediate8) = Imm8 immediate8) /\
  (r1_near_operand64 (Imm16 immediate16) = Imm16 immediate16) /\
  (r1_near_operand64 (Imm32 immediate32) = Imm32 immediate32) /\
  (r1_near_operand64 (Imm64 immediate64) = Imm64 immediate64) /\
  (r1_near_operand64 (Memop w ea) = Memop Quadword ea)`;;

'''
decoder = replace_once(decoder, "let decode_hi = new_definition", decoder_helpers + "let decode_hi = new_definition")
decoder = replace_once(decoder, "| T,T,2 -> SOME (CALL rm,l)", "| T,T,2 -> SOME (CALL (r1_near_operand64 rm),l)")
decoder = replace_once(decoder, "| T,T,4 -> SOME (JMP rm,l)", "| T,T,4 -> SOME (JMP (r1_near_operand64 rm),l)")
# The fast decoder's CPS evaluator retains this application as a constructor;
# the public wrapper then proves its normalization using the HOL definitions.
decoder = replace_once(decoder, '["IMUL"; "JMP"] @', '["IMUL"; "JMP"; "r1_near_operand64"] @')

# Only near-indirect CALL/JMP admit the ignored operand-size override.
# Other FF-group instructions retain their original prefix rejection.
decoder = replace_once(decoder,
    r"""  | [0xf:4; x; 0b11:2; v] -> if has_pfxs pfxs then NONE else
    let sz = op_size_W rex v pfxs in
    read_opcode_ModRM_operand rex sz l >>= \((opc,rm),l).
    decode_hi x v (to_wordsize sz) opc rm l""",
    r"""  | [0xf:4; x; 0b11:2; v] ->
    let sz = op_size_W rex v pfxs in
    read_opcode_ModRM_operand rex sz l >>= \((opc,rm),l).
    if x /\ v /\ (val opc = 2 \/ val opc = 4) then
      if has_unhandled_pfxs pfxs then NONE else
      decode_hi x v (to_wordsize sz) opc rm l
    else if has_pfxs pfxs then NONE else
      decode_hi x v (to_wordsize sz) opc rm l""")


# Conservative proof-conversion cases needed by the generic prefix guard.
# Each conversion returns HOL rewrite evidence; no decoder behavior is assumed.
decoder = replace_once(decoder,
    '    | Tyapp("word",_) -> eval_binary f a b F WORD_RED_CONV',
    '    | Tyapp("word",_) -> eval_binary f a b F WORD_RED_CONV\n    | Tyapp("num",[]) -> eval_binary f a b F NUM_REDUCE_CONV')
decoder = replace_once(decoder,
    r"""  | Comb((Const("val",_) as f),a) -> eval_unary f a F WORD_VAL_CONV""",
    r"""  | Comb(Comb((Const("\\/",_) as f),a),b) ->
    eval_binary f a b F (GEN_REWRITE_CONV I [OR_CLAUSES])
  | Comb((Const("val",_) as f),a) -> eval_unary f a F WORD_VAL_CONV""")

decoder += r'''
let R1_UNNORMALIZED_DECODE_CONV = DECODE_CONV;;
let DECODE_CONV tm =
  CONV_RULE (RAND_CONV
    (REWRITE_CONV [r1_near_operand64; r1_near_register]))
    (R1_UNNORMALIZED_DECODE_CONV tm);;
'''

executor_helpers = r'''
(* NEAR_INDIRECT_GENERIC_LONGMODE_V1 candidate. Relative branches unchanged. *)
let r1_indirect_operand = define
 `(r1_indirect_operand (Register r) <=> T) /\
  (r1_indirect_operand (Simdregister simd_r) <=> F) /\
  (r1_indirect_operand (Imm8 immediate8) <=> F) /\
  (r1_indirect_operand (Imm16 immediate16) <=> F) /\
  (r1_indirect_operand (Imm32 immediate32) <=> F) /\
  (r1_indirect_operand (Imm64 immediate64) <=> F) /\
  (r1_indirect_operand (Memop w ea) <=> T)`;;
let x86_JMP_ABSOLUTE = new_definition
 `x86_JMP_ABSOLUTE target s =
    (events := CONS (EventJump (read RIP s,target)) (read events s) ,,
     RIP := target) s`;;

'''
executor = replace_once(executor, "let x86_execute = define", executor_helpers + "let x86_execute = define")
old_call = '''    | CALL off ->
        (let ip' = word_add (read RIP s)
                            (read (OPERAND64 off s) s) in
         x86_CALL ip' s)'''
new_call = '''    | CALL off ->
        (if r1_indirect_operand off then
          (add_load_event off s ,,
           x86_CALL (read (OPERAND64 off s) s)) s
         else
          (let ip' = word_add (read RIP s)
                              (read (OPERAND64 off s) s) in
           x86_CALL ip' s))'''
executor = replace_once(executor, old_call, new_call)
old_jump_start = '''    | JUMP cc off ->
        (events := CONS'''
new_jump_start = r'''    | JUMP cc off ->
        (if cc = Unconditional /\ r1_indirect_operand off then
          (add_load_event off s ,,
           x86_JMP_ABSOLUTE (read (OPERAND64 off s) s)) s
         else
        (events := CONS'''
executor = replace_once(executor, old_jump_start, new_jump_start)
executor = replace_once(executor,
    '''           else read RIP s) s
    | LEA dest bsid ->''',
    '''           else read RIP s) s)
    | LEA dest bsid ->''')
executor = replace_once(executor, "x86_CALL_ALT; x86_CLC;", "x86_CALL_ALT; x86_JMP_ABSOLUTE; x86_CLC;")
executor = replace_once(executor, "REWRITE_CONV[add_store_event;add_load_event;SEQ_ID]", "REWRITE_CONV[r1_indirect_operand;add_store_event;add_load_event;SEQ_ID]")

sources = {"decode-attempt5.ml": decoder, "x86-attempt5.ml": executor}
for name, content in sources.items():
    path = HERE / name
    if path.exists():
        raise RuntimeError("Explicit candidate output already exists: " + name)
    path.write_text(content)
manifest = {
    "id": "NEAR_INDIRECT_GENERIC_LONGMODE_V1_CANDIDATE5",
    "accepted": False,
    "original_inputs": {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
                        for p in [decoder_path, executor_path]},
    "candidate_files": {str((HERE / n).relative_to(ROOT)): hashlib.sha256((HERE / n).read_bytes()).hexdigest()
                        for n in sources},
    "semantic_review": "PENDING",
    "human_review": "PENDING",
    "target_correctness_axioms": "prohibited",
    "qualification_and_conservative_checks": "NOT_ATTEMPTED"
}
(HERE / "candidate5-manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
print(json.dumps(manifest, indent=2))
