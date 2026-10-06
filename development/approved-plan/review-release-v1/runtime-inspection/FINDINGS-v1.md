# Checking-only reconstruction findings

This inspection changes no accepted input, proof, seal, receipt or historical deadline. It does not reconstruct a theorem. The machine-readable inspection pins the current identities and computes a minimal historical host-input union; release documentation, adapters and evidence are separate additions.

## Existing reconstruction paths

| Case | Accepted source seal | Driver | Root gate | Later checking barrier |
| --- | --- | --- | --- | --- |
| C1 | `reusable-assurance-c1-successor-v1/replay/c1-successor-final-v3-seal.json` | `fresh-replay-v5.py` | `check-root-v3.py` | None; the per-invocation 1800-second limit remains |
| C2 | `reusable-assurance-c2-v1/replay/c2-final-v1-seal.json` | `fresh-replay-v1.py` | `check-root-v1.py` | None; the per-invocation 1800-second limit remains |
| C3 successor | `c3-successor-v1/replay/c3-successor-final-v1-seal.json` | `fresh-replay-v1.py` | `check-root-v1.py` | The original successor wall deadline remains enforced |

All paths above have prefix `development/approved-plan/`. C1/C2 can be invoked unchanged under an extracted repository root. They resolve proof inputs by relative repository paths, use the existing source materializer and reconstruct supplier and caller objects from source. They have no stage-wall deadline check. Their self-hash checks require the exact original driver and gate bytes. Each successful raw reconstruction still needs the corresponding root gate and applicable integrity controls. Saved logs and metadata cannot replace it.

C3's driver lines 61–67 reads the immutable `STAGE-v1.json`, clamps the per-check timeout to its historical deadline, and rejects once it is exhausted. Its gate additionally checks invocation/completion timestamps, actual Docker container timestamps and missing-interface probe timestamps against that same wall interval. That is an experiment-accounting boundary, separate from its unchanged mathematical inputs. A later consumer must not bypass it by falsifying the clock, editing STAGE or claiming a stage extension.

## Smallest permitted adapter

Use additive, checking-only C3 driver and root-gate sources, with a separately sealed operational input projection. Keep every original sealed file and the original seal digest as immutable references. Change only the new sources' own identity/location, their lookup of the original source checker, and the historical stage-wall scheduling condition. Preserve the 1800-second invocation deadline, one CPU, 3 GiB memory/swap, offline execution, closed source tree, all literal/expanded live-object audits, axiom inventory, byte/linkage checks, root-gate checks and controls.

The adapter must verify that its formal graph, supplier binding, loader, registry, audit, model/artifact dependencies and original source digests are identical to the accepted C3 seal. A new operational seal is necessary: the original driver checks `__file__` against `driver_sha256`, and the original gate checks its exact path/hash. An unsealed wrapper or renamed copy will not satisfy those controls. Record real invocation and completion time, the retained historical stage deadline and a clear checking-only purpose in later receipts. These later runs are not construction-stage effort or a revision of the historical result.

The existing C3 `targeted-preflight-controls-v1.py` and `missing-interface-probe-v1.py` can remain unchanged. They obtain driver/root-gate paths dynamically from the supplied seal; retain their original self-pins in the derived operational seal. Their source-checker imports resolve from their unchanged historical directories. The new driver/gate must refer explicitly to the original source checker when placed in the release directory. No proof loader or generic composition source needs modification.

## Source closure and offline dependencies

The immutable supplier materializer restores 4049 files from the local 30,494,586-byte `artifacts/checking-bundles/BP-E1-CHECKING-V2.tar.gz`, checks every member hash, and adds 485 pinned supplementary files. The restored supplier union is 4534 files and 189,750,055 uncompressed bytes. The archive is retained because the accepted drivers themselves restore it on every check; it is not a saved theorem object. The 485 supplements total 16,830,731 bytes. The materializer, index, enclosing supplier seal, preservation receipt, every case host/extra source pin and accepted case seals must all be available under their unchanged relative paths. The inspection JSON enumerates and hash-checks their combined host closure.

Pinned checker image: `sha256:a19fdc18f1f283ed8e2514229b77f33619df1ba0ea1ae578c97779f4b4eb3c3f`, Linux ARM64, inspected local image size 1,215,240,297 bytes. Pinned GNU extraction image: `sha256:444f775e6378c2e5523f29ceb8bbb184442277ed1114e6d37d873a7f127dfc26`, Linux AMD64, inspected local image size 762,960,049 bytes. Both are installed in the same local Docker service. Image inspection was read-only and did not start a checker or target.

The old 1,994,384,384-byte Docker sidecar with SHA `94d2a9f376ee70bc7b5cabf6565b571bbc87844232c5a03663211e12e36c1f9b` is not present in this worktree or the parent repository. Historical delivery indexes refer to it but cannot supply its bytes. Either co-deliver a newly recorded export of the two exact installed images, with its own hash, or state that consumers must preprovision those exact image IDs. Do not claim the missing sidecar was delivered or reuse its old hash for a newly generated export.

## Reuse of existing delivery conventions

The prior `replay/portable-secret-v1/build-v1.py`, `extract-v1.py` and `check-v1.py` provide regular-file-only assembly, digest-pinned extraction and delegated fresh reconstruction patterns. Their immutable manifests cover earlier E2/E3/C0 scope, not C1/C2/C3; using them as if they already covered this release would be wrong. Use the existing materializer and these safety conventions, with a new additive release closure. Do not import the prior 2-GiB Docker wrapper: C1/C2/C3 already enforce their frozen 3-GiB cap explicitly.

## Command shape and consumer claims

After extraction into a new arbitrary `ROOT`, C1/C2 checking uses their unchanged driver with `--source-root ROOT --seal ROOT/<accepted-seal> --seal-sha256 <published-digest> --output ROOT/<new-run> --timeout-seconds 1800`; root gating follows with `--positive-run`, then newly run controls and fresh binding probe as required. C3 uses the separately pinned checking-only adapter/operational seal with the same arguments. Package inventory and image-load setup are not proofs. Actual checking is offline with `--pull never --network none`; Python 3 and a compatible Docker service are prerequisites.

A same-host extracted-tree consumer exercises removal of the developer path, fresh source materialization and new live objects. It does not exercise independent hardware, Docker service, organization or human review. A different agent can add operator/context separation only to the extent actually observed. No replay timing establishes construction savings. Human review remains pending.
