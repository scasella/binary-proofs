# C1 fresh replay source candidate

This lane has not run Docker, GNU tools, HOL, or the targeted controls. The
selected loader is `c1-final-loader-v2.ml`: root development-loader-v4, witness
load-v2, composition helper proof3, and composition main proof2. Loader v1 is
retained as the earlier source candidate. Source checks do not prove readiness.
Root must obtain the full seven live theorem audits before sealing this input.

From the isolated worktree, after root readiness:

```sh
python3 development/approved-plan/reusable-assurance-v1/replay/freeze-v1.py \
  --source-root . \
  --loader development/approved-plan/reusable-assurance-v1/replay/c1-final-loader-v2.ml \
  --theorem-map development/approved-plan/reusable-assurance-v1/replay/theorem-map-v1.json \
  --name c1-final-v1
```

The command refuses existing candidate outputs and prints the external seal
SHA-256. Use that printed digest, never a digest inferred from a stale receipt:

```sh
python3 development/approved-plan/reusable-assurance-v1/replay/fresh-replay-v1.py \
  --source-root . \
  --seal development/approved-plan/reusable-assurance-v1/replay/c1-final-v1-seal.json \
  --seal-sha256 PRINTED_SEAL_SHA256 \
  --timeout-seconds 1800
```

`--preflight-only` checks input integrity without starting GNU or HOL. A full
attempt uses the unchanged pinned opaque supplier materializer and host auditor.
It reconstructs the supplier in a new namespace, then loads the selected caller
sources. The same complete stage is mounted at `/work:ro`, its new workstream at
`/reuse:ro`, and the two approved public exports at `/client-public:ro`. Original
source paths and bytes are unchanged. The graph records each import spelling
and its canonical source file. Both readonly aliases support the witness loader.

The registry requires all seven original C1 literals, 21 original witness
literals representing seven fixed admissible-entry cases, and every new
definition: 25 C1, seven E5, two completion, two tail, and ten witness equations.
The 74 actual theorem/definition objects require closed conclusions, empty
hypotheses, unchanged standard three axioms, original raw literal agreement, and
agreement after expanding all newly introduced nonrecursive definitions. The
recursive RF equations are separately audited and are excluded from recursive
rewriting. Every new definition in the transitive caller load graph must have an
independent original literal or pre-proof file freeze; additional unanchored
definition constructors fail source validation. The preserved supplier auditor
retains its original source/model/artifact and public definition boundaries.

The image check compares the frozen final ELF against its source/build/artifact
pins, formal caller and PLT bytes, fresh GNU section extraction/disassembly,
GNU program headers/relocation/version, and independently derived PT_LOAD and
RELRO permissions. It is trusted tooling evidence; it does not establish an
ELF-loader, decoder, or physical-ISA theorem. The original scalar qualification,
original caller precondition, every-successor semantics, shifted index policy,
and human-review status are unchanged.

The external bound is 1800 seconds; both fresh GNU and HOL containers use one
CPU, 3 GiB memory, a 3 GiB total memory/swap limit, the exact existing local
image ID, no network, and readonly sources. Actual resource settings, mount
permissions, OOM state, raw logs, source hashes and postguards are recorded.
Supplier CPU starts after HOL initialization and includes supplier construction
and live auditing. Caller CPU includes all selected generic/helper/witness/main
loads and the final literal audit. Supplier wall includes HOL initialization;
elapsed wall includes preparation, GNU, reconstruction and host postguards.
No exclusive main, helper, or composition CPU is inferred.

Only after a genuine full positive replay, run the five requested controls:

```sh
python3 development/approved-plan/reusable-assurance-v1/replay/targeted-preflight-controls-v1.py \
  --source-root . \
  --seal development/approved-plan/reusable-assurance-v1/replay/c1-final-v1-seal.json \
  --seal-sha256 PRINTED_SEAL_SHA256 \
  --positive-run ACTUAL_POSITIVE_RUN_DIRECTORY \
  --output NEW_CONTROL_OUTPUT_DIRECTORY
```

They copy the necessary frozen inputs into independent local directories and
invoke the same driver's preflight. They change an executed ELF byte, the
modeled GOT target, an E5 model pin, a supplier public-contract source dependency,
or remove the caller proof while supplying stale success metadata. These are
input-integrity and closed-dependency controls. No single-theorem semantic
sensitivity follows, and missing interface-source rejection qualifies only that
dependency boundary. The positive receipt and actual evidence digests are
required before the control script can run.

`root-gate-template-v1.json` remains pending for independent root review.
Neither a frozen input, local validation, full replay candidate, nor these
controls alone changes caller acceptance. This is one ambient HOL namespace
after supplier reconstruction; source closure and public-interface discipline
do not provide capability or theorem-dependency isolation.
