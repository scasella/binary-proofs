# Consolidated C1/C2/C3 review release

REVIEW_READY_WITH_CHECKING_ONLY_CONSUMER_ACCEPTANCE. All three accepted mathematical packages were reconstructed from the delivered checking sources and passed their complete gates, including the five inherited integrity controls and fresh missing-public-binding probes. Human review remains **PENDING**. This is a checking-only release; no new caller or proof repair was undertaken.

## Exact acceptance and behavior

| Case | Guarantee over the frozen domain | Original accepted seal SHA-256 | Later full checking wall seconds |
| --- | --- | --- | --- |
| C1 | Initial equality as exactly 1/0; strict access, finite actual return, ABI/frame preservation. | `556fe357859921992293b7eedd7fc1338bf737502069502b50cdfffe5e114a0c` | 938.757 |
| C2 | Initial equality as 1/0; clear destination only on equality; both paths satisfy strict access/termination/ABI/frame. | `8f9e56c35e5a60f376356dc7abd242decbd788e1cb54d0e9f4ef23d8f1af9022` | 1025.771 |
| C3 | Always clear destination; return 2 for initial mismatch, otherwise post-clear equality as 1/0; admitted aliases use current cleared snapshot; strict access/termination/ABI/frame. | `903c92086ade0594eda090832ee769e3415c741dfc20573a4c94fef1c6612f46` | 1085.823 |

The literal end-theorems and expanded definitions control the domain: arbitrary admissible contents/lengths, zero-width buffer permission exceptions, admitted aliases, stack/code/GOT separation and E5 RF=TF=0 normal entry. Concrete caller/supplier images and linkage remain unchanged. Actual CALL/PLT/GOT transitions and supplier preconditions are proved; loading/initialization and declared architectural interpretation remain assumptions.

## Preservation and checking

`release-index-v1.json` is the sole current release authority. It identifies selected seals, accepted receipts, supplier artifacts, candidate freeze, dependencies and assumptions. The original failed C1 construction and capped C3 held-out outcome C, postmortem and accepted successor remain separate. Their sources, seals, clocks, failures and receipts are unchanged. The additive preservation comparison records the actual byte identities before/after this stage.

`delivery/CHECKING-v1.md` provides the exact checking-only commands and resource bounds. C1/C2 use their accepted drivers. C3 uses an explicitly hashed operational adapter and exact-parent mathematical projection, with a new bounded checking context. Its original historical deadline guard remains and was tested separately after expiry. This adapter does not grant new construction time or relax the acceptance checks.

`consumer/results-v1.json`, compact actual case receipts and the sealed raw-evidence archive record package consumption. Read its independence fields literally: a new filesystem location and fresh source/container checking on the same local host/Docker service are exercised. Another agent with prior context is not independent human, host/service or external-organizational validation. No filesystem relocation theorem about arbitrary binary ASLR is implied.

## Trust and human review

The packet includes all 21 literal targets and expanded policies, the checked-run definition, supplier/generic statements, frame/snapshot arguments and artifact/linkage assumptions. `human-review/ARCHITECTURE-AND-TRUST-v1.md` separates kernel/runtime, ISA/decoder and observations, added ABI state, E5, extraction/loading, automation and physical/environment assumptions. Canonical GOT targets are concrete; C3 MOV qualification is a closed actual-site proof using unchanged semantics/algorithms, inspection-classified under the predeclared extension policy. Human interpretation review remains pending.

The five controls are artifact/closed-source identity rejection, not semantic mutation proofs. The fresh probe demonstrates unusable public ML binding/type rejection at application, with the original theorem still present in the ambient theory. Source/tactic inspection is the opacity qualification; there is no formal capability isolation or transitive kernel dependency certificate. Successful model checking does not validate the ISA/extraction tools in general.

## Measurements and research judgment

The table reports complete later checking-session wall time, including nested positive/control/probe/gate phases. Supplier/caller phase durations are inclusive portions of those runs and must not be added again. Setup/image export, packaging failures, historical construction attempts and successor effort retain separate ledgers. Active reasoning/exclusive coordination, complete historic supplier construction, tokens and costs are unavailable where marked null; they are not inferred from replay. No construction savings or matched economics trial is established.

H1: supported within the declared model and inspection-qualified interface-use boundary. H2: bounded repairable transfer is supported by these concrete callers; the original held-out C3 trial failed within its cap and successor completion does not turn it into an original-budget unchanged-transfer success. H3: not attempted; no matched interface-free construction baseline.

`manuscript/CASE-STUDY-v1.md` and `manuscript/claim-to-evidence-v1.json` give the mechanism, unchanged versus caller-specific/adapted work and claim evidence. Priority/comparative novelty remains **UNVERIFIED**: no related-work comparison was performed in this consolidation stage.

## Release judgment

Release: review ready with checking-only consumer acceptance. Human review: pending. External-organizational validation: not performed.

Strongest supported publication claim: Under pinned explicit model/environment and fixed-image assumptions, unchanged production OpenSSL supplier contracts support checked composition through actual linkage for three different experimental callers; integration adaptation and caller-local repair are exposed, including a failed capped held-out trial followed by a separately accepted successor.

No further caller, library family, glibc path, generic framework or economics stage starts automatically.
