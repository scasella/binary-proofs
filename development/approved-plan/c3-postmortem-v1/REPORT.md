# C3 diagnostic postmortem — outcome C preserved

**Recommendation: local proof completion in a separately authorized stage.** This inspection identifies premise retention, state selection, normalization, and uncompleted transport/composition obligations. It identifies no demonstrated need to change the supplier contracts, caller domain, linked bytes, or model. It does not prove that the remaining obligations can all be completed by this method.

The held-out trial remains **C / NOT_ACCEPTED_WITHIN_FIXED_EVALUATION_BUDGET**. C1, C2, the failed C1 predecessor, the candidate layer, and all historical C3 inputs/results remain unchanged. This workstream contains diagnostics only: no HOL invocation, proof repair, new bridge theorem, acceptance attempt, or new caller. Human review remains pending.

The [stage record](STAGE-v1.json) imposed a 2,700-second wall cap and permitted at most one optional inspection-only checker invocation. None was used. Diagnostic command observations and preservation checks are separate from the predecessor's construction and checking measurements; [resource observations](measurements/observations-v1.json) state the limits of the measurements. No construction-cost conclusion follows.

## Earliest endpoint

The authoritative [retained goal](../held-out-transfer-v1/c3/replay/construction-cap-cleanup-endpoint-v1.txt) and [307-assumption context](../held-out-transfer-v1/c3/replay/construction-cap-cleanup-full-context-v1.txt) are the starting evidence. The goal is `assurance_checked_run 0` at `u7` asserting the public cleanse precondition, the saved-prefix predicate, the first comparison Boolean in R13, preservation of R14/R15, and the accumulated caller frame. Zero remaining steps reduce to the asserted postcondition; they do not establish it automatically.

The [exact obligation map](review/cleanup-obligation-map-v1.json) expands this into 48 leaves and records every required proposition, relevant original context IDs, public support, source hashes/lines, classification, and execution status. These premise slices are relevance analyses, not checked sufficiency theorems or additional caller assumptions. The [cleanup analysis](review/cleanup-analysis-v1.md) explains the map.

| Obligation | Available evidence | Remaining gap |
|---|---|---|
| Saved-prefix and R13/R14/R15 endpoint facts | All 20 leaves have literal `u7` facts after executed core6. | Assemble them into the enclosing predicate; no completed cleanup endpoint theorem. |
| Public cleanse precondition | Current code/image, arguments, permissions, stack geometry and caller exclusions are retained. | Normalize concrete stack/return sites, select the **u6** GOT fact for the PLT-derived RIP, and derive the slot/code exclusions from the original premises. Public-v4 was not executed. |
| Accumulated MID frame | Checked total-frame inclusion and the `initial→entry`, `entry→returned`, `returned→u7` relations. | Apply the existing inclusion with the two actual intermediate states. The local `returned→u7` frame alone is insufficient. The application source was not executed. |

A concrete source defect affects the proposed p/return-slot helper: `DISCH_TAC` introduces the p/scratch exclusion, but the subsequent `MESON_TAC []` clears assumptions under the pinned HOL definition. Public-v3 records `solve_goal: Too deep`; no helper binding or public-unfold return marker exists. Source order locates the likely defect before application of the public-pre tactic. Public-v4 retains that helper unchanged. The premise-clearing behavior is directly inspectable; localization of the historical exception is a static inference, not a new execution result. The earlier registry's goal-order narrative does not establish that the public-pre application ran.

## Transport and later paths

The [transport and extension-policy audit](review/transport-audit-v1.json) records literal statements, available public guarantees, original caller premises, and each missing implication.

| Obligation | Established scope | Uncompleted implication or path |
|---|---|---|
| Saved comparison result | Working-state preservation through the public cleanse frame is development-checked. | Discharge the actual cleanup-entry predicate and connect that conditional result to the whole chain. |
| Four saved slots | Entry slot values, outside-destination preservation and p/scratch exclusion are available. | Preserve the full eight-byte components and transport the entry equalities. Saved-bindings v1 fails compilation; v2/v3 searches were interrupted without a theorem. Their exact inner stalled goals were not retained. |
| Incoming return slot at S | Initial `bytes64 S = ra`, memory snapshot M0, outside-scratch entry equality, nonwrap and p/slot exclusion. | Aggregate the eight pointwise entry-byte equalities into `bytes64 S`, then preserve it through cleanse. The callee's own return slot **S−48** does not supply this fact. |
| Code and GOT | Five entry code arrays and two concrete GOT values; explicit destination exclusions; public frame/preservation. | Component-specific transport. Preserve the current loaded image; do not assume writable library pages still equal their original initial values. |
| Memory snapshots | Alias-aware v6 has a literal checked development binding: p is zero; q observes `c3_cleansed_memory M0 p n`; outside p/scratch equals M0. | Apply its unchanged premises in the actual chain. The second comparison concerns the cleansed snapshot, including admitted overlap. |
| Second handoff | Opaque second-CRYPTO application is checked **conditional on** the second-entry predicate. | The five-instruction caller/PLT handoff (three MOVs, CALL, PLT JMP) and its endpoint source were not executed; saved bindings and frame composition remain dependencies. |
| Final paths | Only initial-equal/current-equal reaches actual RET in a conditional 12-step diagnostic. | All four endpoint proofs remain unproved. The other 12-step case and both 9-step cases were not executed. |

The [later-path analysis](review/later-analysis-v1.md) and [dependency map](review/later-obligation-map-v1.json) separate those conditional diagnostics from execution from the original caller precondition. The private suffix starts by assuming its complete entry bundle; the actual whole-chain implication to that bundle is unproved. Four preservation lemmas and three fixed saved-list splits precede the observed `seqapply: Length mismatch`. Inspection identifies an association mismatch in the first cancellation application: forward `SEQ_ASSOC` leaves the desired saved-list pair without the subtree required by the reverse list-split rewrite. The exact runtime subgoal count was not retained, so the subsequent tactic-list mismatch is a causal interpretation, not an independently reproduced result. Frame-v4 changes tactic grouping but retains the questioned rewrite; it and the full suffix sources are unexecuted proposals, with no evidence that they close the obligations.

The five whole-caller targets remain unexecuted: `C3_CHECKED`, `C3_INTERFACE`, `C3_NORMAL_CHECKED`, `C3_RF_NORMAL_CHECKED`, and `C3_NORMAL_INTERFACE`. Their E5 lifts retain RF=TF=0 and the existing architectural interpretation. No caller trace claim, loader proof, unrestricted processor correspondence, or stronger erasure claim is introduced.

## Frozen-layer classification

The reviewed automation matches its pre-case pin and archived construction source. Closed POP-site identities, the fixed scratch bound 48, and policy/return callback data fit the frozen extension schemas. Removing exact obsolete initial code facts after deriving current-state bindings is inspected caller-context selection, not a changed decoder or normalizer algorithm.

The alias-aware v6 lemma uses the actual cleanse entry/return addresses, stack adjustment, frozen C3 saved-prefix predicate and specified snapshot obligations. Its internal alias arithmetic is a fixed local proof sequence; it exports no new universal region-inversion or composition rule. Under the written local-lemma clause, the inspected work supports the reported **unchanged-layer classification**. This is a qualified source-policy judgment, not a formal capability/dependency certificate. Generalizing or promoting that transport logic to the reusable surface would count as adaptation. Potential generalizability and ambient ML automation remain disclosed; human interpretation of the policy is pending.

## Recommendation and evidence boundary

If a subsequent completion stage is authorized, address the actual endpoint first: retain the exclusion premise, resolve the public-pre applications and normalizations using the recorded states (including the u6 GOT/RIP selection), and instantiate the already checked frame inclusion. Then isolate the exact saved-bindings implication, the second handoff, and each final path. A need for a new universal bridge or callback/normalization behavior must be recorded as integration adaptation before using it. No such stage is started here.

This diagnosis supports a local-completion recommendation because the public interfaces and original premises provide the relevant results and protection facts; the missing applications and transport implications are explicit. It establishes neither completeness of that method nor absence of every possible specification gap. Preserving outcome C is essential: the fixed-budget held-out trial produced no accepted whole caller and no construction-savings result. The postmortem adds an auditable explanation, not a successful transfer claim.

Final identity checks are [the protected-tree comparison](evidence/protected-final-v1.json) and [historical preservation check](evidence/predecessor-history-final-v1.json). They check content, sizes, timestamps, symlinks and additions against the recorded seals; they are integrity evidence, not formal verification or acceptance controls for a positive C3 package. The [delivery record](results-v1.json) records this diagnostic outcome without changing the authoritative historical acceptance registry.
