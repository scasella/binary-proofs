Outcome **C — NOT_ACCEPTED_WITHIN_FIXED_EVALUATION_BUDGET**. The 10,800-second C3 construction stage ended at 2026-10-05T04:38:37.273874Z. No complete C3 theorem package, fresh acceptance or positive-dependent control result exists. Historical C1, C2 and the failed C1 predecessor remain unchanged. This is a bounded construction failure, not a proof that transfer is impossible.

This view is generated from [the authoritative status snapshot](../../../results/status/snapshots/193750904c4159baa64f4ed8954cd3a7665d828baf08b1ac51773c9b792a5496.json). Reporting is not an acceptance driver. [Final outcome](results/final-outcome-v1.json), [cap/source snapshot](c3/replay/construction-cap-stop-v1.json) and [main obligation map](c3/obligations/map-v10-final-cap.json) retain the actual result.

The small candidate surface was frozen before exact case exposure: unchanged supplier public contracts; parameterized checked-run, ABI, frame, span and E5 rules; address-free C2 helper fragments; and frozen instruction/linkage/policy/normalization callbacks. [Export map](layer/exports-v1.json), [dependencies](layer/dependencies-v1.json) and [supported class/extensions](layer/CLASS-AND-EXTENSION-POINTS-v1.md) distinguish theorem exports from metadata and C1/C2-specific facts. Candidate freeze is 266f58bbb1883389a74b8ba0986db11d0b0d6f4c03c1d3961d2db04f51d94193. Callback parameterization was preparation adaptation, recorded before selection; it is not retroactively called unchanged C2 integration.

Both development cases were freshly reconstructed against that candidate before C3 selection. C1 cold checking took 455.764 seconds; C2 took 529.182 seconds. These are checking observations, not construction savings. Separate fresh processes shared the host and Docker service. [Regression results and exact receipts](regression/RESULTS-v1.md) state which aliases/callbacks each case consumed and preserve original acceptance packages.

C3 was selected in a separate agent context after those regressions. The main construction agent knew the multiple-call family, C0/C1/C2 and previous supplier proof recipes; it did not see the exact C3 before the candidate freeze. The selector later constructed witness/suffix work and knew its own selected case. This is independent selection under frozen rules, not never-read construction or an economics baseline.

The frozen C3 is **assembly-authored experimental caller code**, assembled and finally linked by pinned GCC/binutils. Its ELF SHA-256 is f3736185c45667d23d80e235245da36d99bb79e6ee1b0c7f13725fa590c53b3f. The libcrypto production bytes/contracts are unchanged. [Final case freeze](c3/contract/freeze-v1.json) is cadd70ed4c3ed403db153ab8a3d21db9e4d0a11dec58cfb1f7022c99915d682a. GNU/Python [extraction/image cross-check](c3/replay/schema-crosscheck-v2.json) binds three actual CALL sites, two PLT prefixes and resolved GOT targets; extraction/loading remain trusted mechanisms.

Its intended behavior compares p/q against initial memory M0, retains that equality across an unconditional cleanse of p, and compares again against Mclear, which is zero inside p and M0 elsewhere. Return is 2 when the initial comparison differs, 1 when both comparisons agree, and 0 when only the initial comparison agrees. Partial and identical-pointer aliases are admitted; the second comparison never assumes original contents after clearing. Zero length returns 1 without buffer permission premises. Arbitrary admissible contents and lengths remain; no cap or domain reduction was introduced. Readable inputs, writable destination, fixed 48-byte scratch, protected incoming return/code/GOT regions and ordinary sequential memory are explicit. [Behavior/domain](c3/contract/CONTRACT-v1.md) and [literal definitions](c3/contract/definitions-v2.ml) are frozen.

The **unproved whole-caller target** is literal source text below. All seven target statements, elaborated types and expanded preconditions/policies are in the human-review packet; the following proposition is a target, not an accepted theorem.

```ocaml
!lib_file lib_rw lib_padding client_file client_rw client_padding
    stackpointer ra p q n m rp wp xp ordinary s a.
    c3_pre lib_file lib_rw lib_padding client_file client_rw client_padding
      stackpointer ra p q n m rp wp xp ordinary (s,a)
    ==> assurance_checked_run (c3_steps p q n m)
      (c3_scalar_post stackpointer ra p q n m s)
      (c3_step_policy stackpointer p q n m rp wp xp ordinary) s
```

| Required object | Current result | Meaning |
|---|---|---|
| C3_HANDOFF | DEVELOPMENT_CHECKED | Ten actual initial caller/CALL/PLT transitions, all successors and access policy, reach the public CRYPTO entry precondition. |
| C3_COUNT | DEVELOPMENT_CHECKED | Algebraic step formula only. |
| Three entry-witness targets | DEVELOPMENT_CHECKED | Eight representative layout/alias families with arbitrary payload; entry membership only. |
| C3_CHECKED | NOT_ACCEPTED; NOT_EXECUTED whole target | Complete functionality/access/termination/actual return/frame missing. |
| C3_INTERFACE | NOT_ACCEPTED; NOT_EXECUTED | Depends on C3_CHECKED and existing ABI lift. |
| C3_NORMAL_CHECKED, C3_RF_NORMAL_CHECKED, C3_NORMAL_INTERFACE | NOT_ACCEPTED; NOT_EXECUTED | Depend on full checked run and frozen E5/RF/extended lifts. |
| Fresh acceptance and required C3 controls | NOT_ATTEMPTED | Incomplete required sources/targets; no genuine positive package. |

[Literal/expanded live audits](human-review/C3-STAGE-CAP-EVIDENCE-v2.json) establish only the listed development bindings. Seven cleanup transitions executed diagnostically, but their final public cleanse precondition/saved-prefix/MID-frame conjunction remains open. Core memory/image/initial-snapshot/R13/AC/alignment facts checked. The alias-aware conditional cleanse transport lemma checked; its premises still must be discharged in whole composition. Second5 CALL/PLT handoff source was not executed. One initial-equal/current-equal 12-step final path reached actual RET, leaving scalar postcondition/frame open; the other three final paths are unestablished.

The earliest obligation is the [literal cleanup endpoint](c3/replay/construction-cap-cleanup-endpoint-v1.txt), with its [307-assumption context](c3/replay/construction-cap-cleanup-full-context-v1.txt). The [suffix record](c3/witness-diagnostics/final-return-cap-account-v2.json) preserves the failed fixed cancellation application (seqapply: Length mismatch), exact post-RET goal and unexecuted repairs. Saved slot/incoming-RA/code/GOT transport through cleanse, second handoff, all suffix paths, whole checked-run composition and four lifts remain. [Partial source graph](c3/obligations/partial-main-source-graph-v1.json) explicitly forbids complete acceptance.

Observed failures include proof-term type/application errors, broad search exhaustion, one OOM and five checker watchdog endings. The actual SET R13B word join is 56+8 bits; a supplied 32+32 quotation was rejected by tactic validation. Literal diagnoses also found a reversed WORD_ADD rewrite, an unreduced conditional goal and a stale initial-state code premise selected by frozen automation. These are concrete proof/context issues. No ISA or contract counterexample was established, and no model/contract/binary change was made to repair them.

**Reuse account.** Supplier contracts, model/E5 scope and candidate source algorithms were unchanged after freeze. Concrete addresses, instruction arrays/sites, 48-byte stack/return slots, branch/result snapshots, spans, local callback parameter data and fixed frame/cancellation instantiations remained caller-specific. Removing exactly five obsolete initial code premises was caller context management; it changed no matching algorithm. No integration adaptation was introduced in this held-out stage. This is an unchanged-layer attempt that failed within the cap, not an A success. The unexecuted repairs do not retrospectively complete it.

Supplier bodies were reconstructed for checking. Inspected caller tactic inputs use public supplier policy/postconditions and caller/PLT execution arrays; no supplier-body execution was observed in those inspected sources. This is inspection-qualified opacity, with ambient supplier objects/global simplifier and previous recipe exposure disclosed. It is not formal capability isolation or a transitive derivation certificate. The unfinished derivation cannot certify an interface-only whole-C3 proof.

**Measurements.** Preparation had a separately frozen 3,600-second cap. Construction used the fixed 10,800-second inclusive window, containing checking, idle/coordination and source work. Active proof-construction and coordination seconds are separately null because they were not independently timed; source-emission runtimes do not measure agent reasoning. Seven offline development invocations each had 1 CPU, 3 GiB memory/swap and an 1,800-second cap including cold supplier reconstruction.

| Checker start UTC | Inclusive wall s | CPU s | Peak bytes | Ending |
|---|---:|---:|---:|---|
| 014327 | 1800.180 | unavailable | unavailable | watchdog |
| 021420 | 1663.849 | unavailable | unavailable | OOM |
| 024132 | 1800.076 | unavailable | unavailable | watchdog |
| 031008 | 1800.071 | unavailable | unavailable | watchdog |
| 033543 | 1800.078 | unavailable | unavailable | watchdog |
| 035611 | 1800.084 | unavailable | unavailable | watchdog |
| 041652 | 1439.169 | 649.031 | 1101668352 | explicit stage stop |

Checker wall sum was 12,103.507 seconds with overlap. Container-lifetime union clipped to construction was 10,455.125 seconds and includes idle/startup; neither is exclusive proof construction. No aggregate checker CPU can be recovered from unrecorded earlier counters. Warm7 CPU/peak include cold reconstruction and diagnostics. Its process stop at 04:40:53 followed metadata capture after proof work stopped at the cap; the lag is disclosed. [Resource ledger](c3/replay/stage-resource-observations-v2.json) and [command/failure history](measurements/attempts-v1.jsonl) retain failed efforts: 44 direct source-inclusion failures across 41 sources, a narrower count than all unsuccessful attempts. Private diagnostics, setup failures and interruptions remain separate. Exact model/token/billing counters are unavailable; no construction savings are inferred.

The [post-cap preservation check](status/post-cap-history-check-v1.json) compares all 93,732 historical records, including hashes/size/mtime, and passes. [Protected input check](status/final-protected-pin-check-v1.json) passes the same 85 candidate/stage/spec/artifact pins; it is identity evidence, not ISA validation. Canonical proof files were not edited after the deadline. The existing [complete replay/acceptance/control commands](c3/replay/COMMANDS-v1.md) were preserved. Controls reject package identities/dependencies, not semantic behavior; C3 controls remain unqualified without a positive. No controls from old accepted cases are relabeled as C3 successes.

Normal entry retains RF=TF=0, DF=AC=0, canonical FS and the fixed long-mode/CPL3/no-async/debug/CET architectural interpretation. Actual linkage is through the fixed post-initialization image/GOT assumptions. No dynamic-loader proof, arbitrary ASLR, caller trace, C refinement, physical erasure, unrestricted processor correspondence or library-wide verification follows. Human review is **PENDING**. [Compact packet](human-review/INDEX-v3.md) contains literal contracts, expanded policies, checked-run and generic rules, artifact/linkage assumptions and cap evidence.

**Judgments.** H1 remains supported by accepted development-case interface use within its inspection qualification; C3 adds conditional applications, not a completed caller. H2 is not established: the one frozen held-out case was not accepted within its cap; this does not refute all possible transfer. H3 was not attempted. The supported publication claim is a frozen production-supplier package and explicit composition surface freshly regressed on two development callers, followed by a failed, preserved held-out multiple-call attempt exposing remaining caller-specific integration work. Successful held-out transfer and reduced construction effort remain unsupported. No next caller, economics trial, library family or glibc stage was launched.
