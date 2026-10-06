# C3 local-completion successor

**A — The unchanged C3 package is freshly accepted through the declared public-interface construction.** This is successor experiment `BP-20261005-C3-SUCCESSOR-V1`. The original held-out **C / NOT_ACCEPTED_WITHIN_FIXED_EVALUATION_BUDGET** remains unchanged. Accepted C1/C2, the failed C1 predecessor, original C3 and its postmortem remain preserved. This later result does not revise that trial.

The authoritative entry for this stage is [current-stage-v1.json](/Users/scasella/Downloads/binary-proofs/.forks/reusable-binary-assurance/development/approved-plan/c3-successor-v1/status/current-stage-v1.json). This report is generated from it. Historical status pointers and reports stay unchanged. Human review remains **PENDING**.

## Actual guarantees

The target is the original 89-byte, 32-instruction assembly-authored experimental C3 caller and its two actual six-byte linkage prefixes in the concrete frozen image. Caller ELF SHA-256: `f3736185c45667d23d80e235245da36d99bb79e6ee1b0c7f13725fa590c53b3f`. Supplier libcrypto SHA-256: `76dd3d93e5ee48950a92a58d59b94de8143847f91a80d9682c938767b991577d`. Supplier proofs are reuse; no entire ELF or library-wide verification follows.

The caller compares the initial inputs, clears the first region, and compares the current inputs. It returns exactly2 when the initial inputs differ, otherwise1 if the comparison after clearing is equal and0 if it differs. This original C3 caller clears on both outcomes of its first comparison. The second result uses `c3_cleansed_memory`, preserving admitted identical and partially overlapping regions. Zero length returns1 without buffer access or buffer permission premises.

Accepted properties are functionality, strict buffer access with separately declared stack/code/GOT/return accesses, finite progress for every modeled successor, actual return, stack and callee-saved register restoration, and the frozen memory/frame effects. All four suffix paths,12/12/9/9 steps, reach actual RET. The four saved eight-byte slots are restored; the incoming return slot at S is distinct from the nested slot at S−48. Current code/GOT and memory snapshots are derived from the actual states. Writable library pages are not assumed to retain initial contents.

| Original target | Status |
| --- | --- |
| `C3_HANDOFF` | FRESH_ACCEPTED |
| `C3_COUNT` | FRESH_ACCEPTED |
| `C3_CHECKED` | FRESH_ACCEPTED |
| `C3_INTERFACE` | FRESH_ACCEPTED |
| `C3_NORMAL_CHECKED` | FRESH_ACCEPTED |
| `C3_RF_NORMAL_CHECKED` | FRESH_ACCEPTED |
| `C3_NORMAL_INTERFACE` | FRESH_ACCEPTED |

All three frozen entry-membership targets and eight witness families are freshly reconstructed. They supplement the universal execution theorem. Live audits check exact closed conclusions,47 definition equations and their expansions, zero hypotheses/free variables and the unchanged standard axioms. Supplier checking separately reconstructs325 theorems,119 definitions and218 equations; the frozen candidate audits34 exports. These counts identify the package boundary; counts alone are not proof evidence.

## Literal theorem and domain

```text
!lib_file lib_rw lib_padding client_file client_rw client_padding
    stackpointer ra p q n m rp wp xp ordinary s a.
    c3_pre lib_file lib_rw lib_padding client_file client_rw client_padding
      stackpointer ra p q n m rp wp xp ordinary (s,a)
    ==> assurance_checked_run (c3_steps p q n m)
      (c3_scalar_post stackpointer ra p q n m s)
      (c3_step_policy stackpointer p q n m rp wp xp ordinary) s
```

```text
!lib_file lib_rw lib_padding client_file client_rw client_padding
    stackpointer ra p q n m rp wp xp ordinary s a.
    c3_pre lib_file lib_rw lib_padding client_file client_rw client_padding
      stackpointer ra p q n m rp wp xp ordinary (s,a)
    ==> eventually_n e5_rf_retired_extended_step (c3_steps p q n m)
      (\t. c3_public_post stackpointer ra p q n m s a t /\
           e5_normal_flags(FST t)) (s,a)
```

[Literal review supplement](/Users/scasella/Downloads/binary-proofs/.forks/reusable-binary-assurance/development/approved-plan/c3-successor-v1/review/FINAL-LITERAL-SUPPLEMENT-v1.md) and [full literal preconditions and policies](/Users/scasella/Downloads/binary-proofs/.forks/reusable-binary-assurance/development/approved-plan/c3-successor-v1/review/final-literal-contract-view-v1.json) preserve exact equations and source digests. [Inherited expanded definitions](/Users/scasella/Downloads/binary-proofs/.forks/reusable-binary-assurance/development/approved-plan/held-out-transfer-v1/human-review/expanded-baseline-contracts-v1.json) includes the unchanged supplier policies, machine/ABI state and checked-run definition. The sealed registry retains all original targets. No caller premise, admitted domain, model or contract changed.

The original domain admits arbitrary contents and lengths below2^64 whose explicit canonical, nonwrapping ordinary-memory spans hold. The first region is readable/writable; the second readable. Both exclude48-byte mutable scratch. The cleared region also excludes incoming return, code and GOT. No new p/q separation is imposed. Stack alignment, return address distinct from entry, restored-pointer bounds and access permissions remain explicit. E5 retains RF=TF=0, DF=AC=0 and canonical FS base, with the inherited long-mode/CPL3/no-debug/no-asynchronous/no-CET-interference interpretation.

Kernel/runtime, ISA/model/decoder, omitted-state interpretation, extraction/loading and declared post-initialization image remain the inherited trust boundary. Actual CALL/PLT/GOT transitions are proved in that image; loader execution, interposition and arbitrary ASLR are outside this scope. There is no caller trace theorem, unrestricted processor correspondence, C-language refinement, hardware constant-time or physical-secret-erasure claim.

## Repair, composition and reuse

The earliest exclusion helper discarded a needed pointer/scratch premise. The successor retains it explicitly, deriving exclusions from original premises. Cleanup uses actual u6 GOT at the PLT-derived IP, u7 saved-prefix/register facts and actual accumulated-frame inclusion. `C3S_CLEANUP_CHAIN` connects the complete endpoint to original entry through the first public comparison.

Local proofs transport all saved slots, incoming return, current code/GOT and the alias-aware snapshot after discharging its premises. The second actual handoff and public comparison establish the real suffix entry. Final cancellation uses the actual relation/list association. Every final endpoint and whole/interface/E5 target is executed; no suffix endpoint is assumed in the whole theorem.

At literal offset73 the frozen convenience qualifier omits a rewrite for the already-defined immediate-operand predicate and its search fails. A concrete MOV EAX,Imm32(2) decode/class/fetch/events theorem applies existing GEN_STEP/CLIENT/R1 primitives at that one site. Parentheses fix the tactic-list branch; local NUM_REDUCE reconciles1+6 with7. No callback, matching/normalization/dispatch behavior, new universal integration rule, model or supplier contract changed. This is a fixed-site proof, not automatic arbitrary immediate-MOV support.

[Selected reuse account](/Users/scasella/Downloads/binary-proofs/.forks/reusable-binary-assurance/development/approved-plan/c3-successor-v1/status/selected-reuse-account-v1.json), [83-node source review](/Users/scasella/Downloads/binary-proofs/.forks/reusable-binary-assurance/development/approved-plan/c3-successor-v1/diagnostics/transport-final-selected-graph-review-v2.json) and [concrete dependency map](/Users/scasella/Downloads/binary-proofs/.forks/reusable-binary-assurance/development/approved-plan/c3-successor-v1/results/dependency-map-v2.json) distinguish unchanged supplier/generic logic from caller addresses, snapshots, stack facts and branch/endpoint reasoning. The v1 dependency-map spelling error is preserved and corrected in v2. The selected graph seals83 nodes. No new reusable algorithm is introduced.

Opacity remains inspection-qualified source/tactic discipline in a shared ambient HOL namespace. Caller construction uses public supplier guarantees according to the retained inspections, while fresh checking reconstructs supplier proofs. Prior C3 and supplier-recipe exposure stays disclosed. No formal capability isolation, kernel transitive-dependency certificate, never-read construction or independent human review is claimed.

## Acceptance, controls and costs

Development checking, sealed fresh reconstruction, positive acceptance and complete root acceptance are separate results. Complete acceptance follows source reconstruction and all inherited checks, not log phrases, helper counts or process exit. Seal SHA-256: `903c92086ade0594eda090832ee769e3415c741dfc20573a4c94fef1c6612f46`.

Five disposable-copy controls reject a changed executed caller byte, changed modeled GOT target, changed E5 binding, missing supplier source and missing caller proof despite stale success metadata. These are input-identity/dependency rejections, not semantic counterexamples or ISA validation. The fresh unavailable-public-binding probe replaces the required comparison theorem with unit; construction fails at its actual application with unchanged standard axioms. This establishes required usable ML binding in that path, not single-theorem formal proof sensitivity. Canonical inputs remain unchanged.

- [complete_root_gate](/Users/scasella/Downloads/binary-proofs/.forks/reusable-binary-assurance/development/approved-plan/c3-successor-v1/results/complete-gate-final-v1.json) — SHA-256 `0e1aa8598bd85d1015f5e85a71744fa1cd9403cfcba4b7529c04a0acb901784e`
- [positive_root_gate](/Users/scasella/Downloads/binary-proofs/.forks/reusable-binary-assurance/development/approved-plan/c3-successor-v1/results/positive-gate-final-v1.json) — SHA-256 `65dd828391a5b8cb7f5d68be3b7c25ce24ee33f047f6a7e3ecc8b3dae85ea7a2`
- [sealed_inputs](/Users/scasella/Downloads/binary-proofs/.forks/reusable-binary-assurance/development/approved-plan/c3-successor-v1/replay/c3-successor-final-v1-seal.json) — SHA-256 `903c92086ade0594eda090832ee769e3415c741dfc20573a4c94fef1c6612f46`
- [fresh_reconstruction](/Users/scasella/Downloads/binary-proofs/.forks/reusable-binary-assurance/development/approved-plan/c3-successor-v1/runs/fresh-final-v1/receipt.json) — SHA-256 `ca9a4a58417a54dd8f4c9a839471943430fc3c1f11c95a7c0c55fb08643d76ee`
- [live_literal_and_expanded_audit](/Users/scasella/Downloads/binary-proofs/.forks/reusable-binary-assurance/development/approved-plan/c3-successor-v1/runs/fresh-final-v1/runtime/c3-live-audit-v1.json) — SHA-256 `7b67bb6f8a4660a16b8523a5adbfa9b731e46e85837cfa834d68d4166423e35f`
- [artifact_linkage_crosscheck](/Users/scasella/Downloads/binary-proofs/.forks/reusable-binary-assurance/development/approved-plan/c3-successor-v1/runs/fresh-final-v1/c3-image-crosscheck.json) — SHA-256 `6f840527d7a9d7b00b43c5071871df602ce7eefe4ac73fc491d2293883cdaa66`
- [five_integrity_controls](/Users/scasella/Downloads/binary-proofs/.forks/reusable-binary-assurance/development/approved-plan/c3-successor-v1/runs/controls-final-v1/receipt.json) — SHA-256 `4a90752080a0d1642c56d897711536919da9beeda4eab2c97e9682b1323cf793`
- [fresh_missing_public_binding_probe](/Users/scasella/Downloads/binary-proofs/.forks/reusable-binary-assurance/development/approved-plan/c3-successor-v1/runs/binding-probe-final-v1/receipt.json) — SHA-256 `07230bd574e316befce595753fd2d0c0f962affef01982ede23ffe8660890d66`
- [fresh_probe_actual_construction](/Users/scasella/Downloads/binary-proofs/.forks/reusable-binary-assurance/development/approved-plan/c3-successor-v1/runs/binding-probe-final-v1/attempt/receipt.json) — SHA-256 `51f5efd2da60459639fe923784cb9f07225aeff1cb9b1eefe8b36c9dec08ae5e`
- [protected_inputs_preservation](/Users/scasella/Downloads/binary-proofs/.forks/reusable-binary-assurance/development/approved-plan/c3-successor-v1/status/runtime-protected-final-v1.json) — SHA-256 `1d7bddb6d0f7ae015b71ca6de4ddd9c58798fad0f1d5682933ce77d835a9639b`
- [historical_packages_preservation](/Users/scasella/Downloads/binary-proofs/.forks/reusable-binary-assurance/development/approved-plan/c3-successor-v1/status/runtime-history-final-v1.json) — SHA-256 `75a7739bb9fe1bb8b966e79672fd5dc5432202eb3e2ea78429514e1a8e8e2077`
- [postmortem_preservation](/Users/scasella/Downloads/binary-proofs/.forks/reusable-binary-assurance/development/approved-plan/c3-successor-v1/status/runtime-postmortem-final-v1.json) — SHA-256 `74656112d72e5ab34b8a31a8c63682b3e98bbf5080fdc2b64f457ff301cf7ee3`
- [sealed_graph_inspection](/Users/scasella/Downloads/binary-proofs/.forks/reusable-binary-assurance/development/approved-plan/c3-successor-v1/diagnostics/transport-final-selected-graph-review-v2.json) — SHA-256 `55b1a3cb83c3d63096db34b514fd06acc1f63f0ec0102803ee293932b892cb3c`
- [reuse_account](/Users/scasella/Downloads/binary-proofs/.forks/reusable-binary-assurance/development/approved-plan/c3-successor-v1/status/selected-reuse-account-v1.json) — SHA-256 `6c397e06abdf85222f2cfccac0f0a93ebcd2bd04eca74eb7ceee31da37a3f360`
- [dependency_map](/Users/scasella/Downloads/binary-proofs/.forks/reusable-binary-assurance/development/approved-plan/c3-successor-v1/results/dependency-map-v2.json) — SHA-256 `6544ed0828c22bf7b89f2f3971696c95c959a702b3e47fe7972cf1717d9cbc24`
- [literal_contract_review](/Users/scasella/Downloads/binary-proofs/.forks/reusable-binary-assurance/development/approved-plan/c3-successor-v1/review/final-literal-contract-view-v1.json) — SHA-256 `436a74c715bff8875c179d3762d5e9fe495438a809fdb859d26a6796cdf927be`
- [effort_ledger](/Users/scasella/Downloads/binary-proofs/.forks/reusable-binary-assurance/development/approved-plan/c3-successor-v1/measurements/effort-final-v1.json) — SHA-256 `7ae82e4a16c04291f2f510353ea8bef7cce7c638cfb20dc0632c8ef2a0fb6c25`
- [effort_validation](/Users/scasella/Downloads/binary-proofs/.forks/reusable-binary-assurance/development/approved-plan/c3-successor-v1/measurements/effort-final-v1-validation.json) — SHA-256 `ab525ee5ba31292ce29599a3d0d6fe553292af12ab89a3755d3170af7eb54be0`
- [executed_commands](/Users/scasella/Downloads/binary-proofs/.forks/reusable-binary-assurance/development/approved-plan/c3-successor-v1/replay/commands-executed-final-v1.json) — SHA-256 `c7695efb96d7e83760d40a8aa82c055f3e5b4ada1f1db536f7d85c21dc9f817a`
- [reporting_failure](/Users/scasella/Downloads/binary-proofs/.forks/reusable-binary-assurance/development/approved-plan/c3-successor-v1/results/reporting-failure-v1.json) — SHA-256 `3ddd19b39e09b5a1cc4d3f155afd0cab5ac40095087b4a1b213ff6b7f33f77ac`

All runs share the local host/Docker service. Fresh checking uses read-only sealed source, offline pinned ARM64 HOL,1 CPU and3GiB. GNU x86-64 extraction is emulated. This is not external-consumer or native-x86 execution evidence.

The stage keeps10800 seconds for construction and1800 seconds per check. Fresh positive wall: **591.303s**. Supplier/caller phase wall and available CPU are recorded separately from construction observations, checking/control costs and coordination. The [final effort ledger](/Users/scasella/Downloads/binary-proofs/.forks/reusable-binary-assurance/development/approved-plan/c3-successor-v1/measurements/effort-final-v1.json) retains failures and stage-local/cumulative histories. Wall unions merge overlaps; inclusive concurrent totals are not construction elapsed time. Active construction/reasoning/exclusive coordination, complete aggregate CPU/peak memory, model/tokens/billing are unavailable rather than invented. Host child usage excludes Docker. A fast replay does not establish construction savings.

[Executed commands](/Users/scasella/Downloads/binary-proofs/.forks/reusable-binary-assurance/development/approved-plan/c3-successor-v1/replay/commands-executed-final-v1.json) records the existing fresh driver, controls, binding probe and complete gate. Their bounded construction-stage driver intentionally rejects after its frozen deadline; a later fresh checking invocation must be separately recorded and cannot silently extend or revise this stage. Sealed sources, actual Docker arguments/input files and exact audits remain available for reconstruction.

## Research judgment

This successor shows that the unchanged public contracts and frozen integration algorithms support this multiple-call caller after explicit caller-local repairs and additional measured work. The original held-out fixed-budget attempt remains failed. Addresses, alias snapshots, stack transport, branches, endpoints and one site qualification remain caller work. The strongest supported claim is bounded repairable transfer for this concrete case within the declared class. Automatic/general caller integration and construction-cost savings remain unsupported.

No frozen C3 package obligation remains open in this successor. Human review and declared trust limitations remain. No economics trial ran. No next caller, framework stage, glibc expansion or economics experiment is launched.
