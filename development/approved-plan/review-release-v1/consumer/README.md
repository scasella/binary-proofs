# Consumer reconstruction evidence

All three cases completed fresh checking from the delivered source archive in a new filesystem root. See `results-v1.json` for actual outcomes, timings, seals and qualifications. Human review remains **PENDING**. The consumer shared the original host and Docker service and had prior context exposure; it is not external-organizational or independent human validation. No proof source changed.

The compact complete gates are `cases/C1/complete-gate.json`, `cases/C2/complete-gate.json` and `cases/C3/complete-gate.json`. Each case directory also preserves the actual result, checking session, positive receipt, five-control receipt, binding-probe receipts and phase ledger under their original relative paths. `copies-v1.json` and the enclosing `reporting-copies-v1.json` record exact-copy hashes. C3's separately generated checking-only context and seal are in `operational-context/`. The unchanged historical driver's actual late rejection is in `historical-deadline-guard/`.

## Raw archive

`evidence-v1.tar.gz` is **4,215,523 bytes** with SHA-256:

```text
5eb6115f42ce71e6374a598c2cd2aaf1de37419922f6f8afc1b975e34142bb32
```

It contains 353 regular files. `evidence-index-v1.json` lists their paths, sizes and hashes. Verify the archive using the independently supplied release digest, then list or unpack it into a new directory:

```sh
shasum -a 256 evidence-v1.tar.gz
tar -tzf evidence-v1.tar.gz
mkdir raw-evidence
tar -xzf evidence-v1.tar.gz -C raw-evidence
```

The archive preserves original relative paths below the consumer base. For every raw reference beginning `/private/tmp/bp-review-consumer-o803245s/`, remove that prefix and prepend your extraction directory. For example:

| Recorded reference suffix | Extracted path |
| --- | --- |
| `runs/C1/positive/c1-proof.log` | `raw-evidence/runs/C1/positive/c1-proof.log` |
| `runs/C2/positive/root-only-supplier/bootstrap.log` | `raw-evidence/runs/C2/positive/root-only-supplier/bootstrap.log` |
| `runs/C3/binding-probe/attempt/c3-proof.log` | `raw-evidence/runs/C3/binding-probe/attempt/c3-proof.log` |
| `runs/C3/complete-gate.json` | `raw-evidence/runs/C3/complete-gate.json` |
| `historical-deadline-guard/result-v1.json` | `raw-evidence/historical-deadline-guard/result-v1.json` |

Each `runs/C*/` directory includes the actual Docker argument lists, container inspection, live audits, extraction cross-checks, receipts, ledgers and raw logs. The generated C3 context and operational seal retain their archived paths under `source/development/approved-plan/review-release-v1/consumer/checking-contexts/`. Top-level environment and delivery observations are also archived.

The archive deliberately omits duplicate initial and staged/cloned source trees. The separately sealed checking-source archive supplies original source identities; generated C3 context/seal files are retained here. Raw evidence is for review, not a replacement for fresh reconstruction. Absolute paths inside recorded Docker inspections identify the actual historical mounts; they are not instructions to reuse those temporary paths. `mount-independence-v1.json` records the later inspection of all six actual checker/probe containers and the shared-service limitations.
