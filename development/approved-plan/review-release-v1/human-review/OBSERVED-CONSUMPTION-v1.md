# Observed delivered-package consumption

**C1, C2 and C3 all passed complete checking-only consumer acceptance.** This is the later consumption observation recorded at `2026-10-05T16:10:26.994360+00:00`, not a new construction result. Original accepted packages, failed trials, postmortem and successor history remain unchanged. Human review is **PENDING**.

This supplement resolves the pending consumer-status references in the earlier packet without editing those versioned documents. The authoritative result is `development/approved-plan/review-release-v1/consumer/results-v1.json`; actual mount properties are in `consumer/mount-independence-v1.json`. The release-wide index retains package/reconstruction identities separately.

## Sealed inputs and complete results

The consumer used delivered source archive SHA-256 `7434fae0f89c9b3a0c58f455a3bd33826502213befea5be5f58bcb5355073e2a` and input manifest SHA-256 `bb91c404411554fc48a1c34fe1107278067ffbf76cdc759b20c833bffd85a1fd`. Its extracted source root was `/private/tmp/bp-review-consumer-o803245s/source`; original developer source paths were not accessed after handoff. Saved results were not used to discharge targets. No proof construction or source repair occurred in this consumption run.

Every case reconstructed all seven original end-targets, its required witnesses and exact literal/expanded definitions, together with the complete supplier chain. Each complete gate verified positive acceptance, the original five integrity controls and fresh unusable-public-binding construction rejection. The gate files below are retained compact copies; the evidence archive preserves full logs/inspection/audits rather than relying on a former temporary filesystem.

| Case | Complete consumer gate relative to `review-release-v1/` | SHA-256 |
| --- | --- | --- |
| C1 | `consumer/cases/C1/complete-gate.json` | `cc7438e633c8defe117f8025f5ebaba53fce1efe276e31a0668631c45ce8ace4` |
| C2 | `consumer/cases/C2/complete-gate.json` | `2fa77ea1d8b94cbccf80acffa1a6766809b4da5d9e8cc715b6e26b170b3d0502` |
| C3 | `consumer/cases/C3/complete-gate.json` | `111416ed28985c9abc5fb810f72bcfa49a658e72d2ae73b2e99d6f84434ac323` |

C1/C2 retain their original accepted seals. C3's operational checking seal is `9e2a4a07a4c3b8590806ea7d4662e8e1a11afd605c2f320b2463c9a465cf3260`, with exact protected parent projection to accepted seal `903c92086ade0594eda090832ee769e3415c741dfc20573a4c94fef1c6612f46`. Its separate adapter identity/context is described in `LATER-CHECKING-v1.md`; the projection and Python orchestration remain trusted, source-inspected mechanisms rather than a formal adapter-equivalence theorem.

## Checking observations

| Case | Positive reconstruction wall, s | Nested supplier/caller wall, s | Fresh binding probe wall, s | Complete case session wall, s |
| --- | --- | --- | --- | --- |
| C1 | 476.700 | 425.356 / 45.527 | 452.890 | 938.757 |
| C2 | 540.036 | 419.048 / 116.157 | 468.100 | 1025.771 |
| C3 | 562.565 | 433.484 / 122.392 | 502.696 | 1085.823 |

Supplier/caller durations are included within the positive duration; positive/probe/control/gate work is included within the case session. They must not be added a second time. The three sequential case sessions total 3050.351 seconds. Full consumer-episode elapsed wall is 3216.793 seconds; the intercase 166.429 seconds include coordination, latency, copying and other host activity and are not an exclusive active coordination measurement. The tiny historical guard diagnostic overlaps C2's session and is not added again.

All case sessions remained below 5400 seconds, and every proof invocation retained the 1800-second limit. Inspection of six positive/probe containers confirmed one CPU, 3 GiB memory with equal swap limit, network `none`, five read-only source mounts and one writable output mount each, no OOM/dead container and the expected success/rejection exit. The original target/kernel/foundation and acceptance controls were not changed. Tokens/model/billing and exclusive coordination are unavailable rather than inferred.

At `2026-10-05T15:46:00.665801+00:00`, after the unchanged original C3 successor deadline `2026-10-05T15:45:12.242465+00:00`, the consumer invoked the original driver and original seal. It rejected with `C3 successor stage deadline exhausted`, exit 1, before GNU work or proof execution. The recorded elapsed is 0.078172 seconds. The separately identified later checking adapter then reconstructed and accepted C3; it did not extend that historical construction guard or turn the guard rejection into a proof result.

## Independence exercised and not exercised

The consumer used a relocated filesystem root and fresh checking containers from the delivered inputs. Every inspected source/output mount lay within the temporary consumer base; none came from the original developer checkout. The operator was `/root/release_runtime`, a distinct agent from the release builder, with previous source/case/context exposure disclosed. The root agent performed read-only coordination. This tests delivered source closure and path independence, not formal capability isolation or a fresh no-exposure construction context.

The same `MacBook-Pro.local` ARM64 Darwin host and Docker Desktop `desktop-linux` service were shared. Exact preinstalled image IDs were reused after read-only validation. Image loading from the delivered sidecar was **not exercised**. Native ARM HOL checked the x86 model; GNU x86 extraction was emulated. The run is not independent-host, independent-Docker-service, independent-human, external-organizational or native-x86 validation. Filesystem relocation is not binary relocation or arbitrary-ASLR proof.

Full evidence is `consumer/evidence-v1.tar.gz`, SHA-256 `5eb6115f42ce71e6374a598c2cd2aaf1de37419922f6f8afc1b975e34142bb32`, with 353 indexed files and index SHA-256 `a65383fcc370ac7559b3894edd70c025b83fe9dd005b9e9393ef55f2a8906a4d`. These observations strengthen the checking-only delivery claim. They do not change interface-opacity qualifications, architectural trust, pending human review, original held-out failure or lack of a construction-cost experiment.
