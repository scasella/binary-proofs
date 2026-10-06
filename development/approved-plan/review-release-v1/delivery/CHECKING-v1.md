# Checking-only consumption

This release reconstructs the accepted C1/C2/C3 statements from source. It does not extend their construction budgets or replace their historical packages. Human review is pending. The authoritative package/evidence index is `development/approved-plan/review-release-v1/release-index-v1.json` in the review companion archive.

## Delivered files and dependencies

Keep these files together: `checking-sources-v1.tar.gz`, `docker-images-v1.tar`, `extract-v1.py`, `delivery-v1.json`, the review companion archive/manifest, and `licenses/`. The checking archive SHA-256 is `7434fae0f89c9b3a0c58f455a3bd33826502213befea5be5f58bcb5355073e2a`; its input manifest SHA-256 is `bb91c404411554fc48a1c34fe1107278067ffbf76cdc759b20c833bffd85a1fd`. The image archive SHA-256 is `6c01c3490963fe4d7b530195aaadcc2161636047e1d4899837e4aa18258e0eb4`. The bootstrap extractor SHA-256 is `2359a3fbbbe585c937100df11e1ddc2f8536ca2102bbd1090436807872ae773a` and matches the extractor inside the sealed input manifest. Authenticate these digests through the release index, not an untrusted nearby manifest alone.

Requirements: Python 3.10 or later with its standard library; Docker CLI and a running Linux Docker Engine that can execute both linux/arm64 and linux/amd64 containers; filesystem space for the 2 GB image sidecar, extracted inputs and fresh checking outputs. The observed consumer used macOS on Apple Silicon and the existing Docker service. Other platforms have not been qualified by this consumption result. Docker emulation/platform support is an environment dependency. The pinned images contain the OCaml/HOL runtime and GNU extraction tools; no network, AI credentials or proof search repair is needed.

Verify the image archive SHA-256 before provisioning. A new consumer can load the delivered exact images with:

```sh
docker load --input docker-images-v1.tar
docker image inspect sha256:a19fdc18f1f283ed8e2514229b77f33619df1ba0ea1ae578c97779f4b4eb3c3f
docker image inspect sha256:444f775e6378c2e5523f29ceb8bbb184442277ed1114e6d37d873a7f127dfc26
```

Loading is setup, not theorem checking. The consumer experiment recorded whether it reused already installed identical images; it did not test a fresh Docker service. Preserve the images' included licenses and the release license metadata.

## Reconstruct

Run from an otherwise empty delivery directory. Choose a new extraction and output directory; these commands contain no original developer path:

```sh
python3 -B extract-v1.py --archive checking-sources-v1.tar.gz --sha256 7434fae0f89c9b3a0c58f455a3bd33826502213befea5be5f58bcb5355073e2a --output source
python3 -B source/development/approved-plan/review-release-v1/scripts/check-case-v1.py C1 --output runs/C1 --inputs-sha256 bb91c404411554fc48a1c34fe1107278067ffbf76cdc759b20c833bffd85a1fd
python3 -B source/development/approved-plan/review-release-v1/scripts/check-case-v1.py C2 --output runs/C2 --inputs-sha256 bb91c404411554fc48a1c34fe1107278067ffbf76cdc759b20c833bffd85a1fd
python3 -B source/development/approved-plan/review-release-v1/scripts/check-case-v1.py C3 --output runs/C3 --inputs-sha256 bb91c404411554fc48a1c34fe1107278067ffbf76cdc759b20c833bffd85a1fd
```

Every case reconstructs the supplier and caller live theorem objects, verifies exact literal conclusions/expanded definitions, empty hypotheses/free variables, permitted axioms, closed sources, artifact/image binding and independent GNU cross-checks. It then runs all five inherited disposable-copy integrity controls, a fresh unavailable-public-binding probe, and the complete root gate. Every HOL invocation retains 1800 seconds, one CPU and 3 GiB RAM/swap limit, read-only staged sources and network none. Each later checking session has a 5400-second envelope for the positive, controls, probe and gates. A failure or timeout returns nonzero; no saved success is substituted.

Expected final files are `runs/C*/result-v1.json` with `CHECKING_ONLY_CONSUMER_FRESH_ACCEPTED`, and `runs/C*/complete-gate.json` with `FRESH_ACCEPTED_WITH_FIVE_INTEGRITY_CONTROLS_AND_FRESH_BINDING_PROBE` and the case's complete acceptance flag true. Preliminary positive receipts retain their historical pending status until the gates pass. The checker logs, exact inputs, invocation/container inspections, live audits, GNU evidence and phase ledger remain alongside each result. Resource envelopes are caps, not predictions; observed times are in the consumer evidence.

C1/C2 invoke their unchanged accepted drivers and seals. C3 invokes separately hashed packaging adapters: its original accepted seal is preserved, and an exact parent projection prohibits changes to all mathematical/model/artifact/source inputs and original input hashes. Only operational driver/gate identities, additional checking metadata and a fresh checking interval are changed. The original C3 deadline guard is preserved and still rejects late historical-stage invocations. The C3 adapter creates a new explicit bounded checking context on every consumer invocation; it grants no construction time.

## Interpret the result

The extraction/hash checks are trusted Python/GNU mechanisms, not formally verified parsers or loading. The controls establish package identity and missing-input rejection. The missing-binding probe establishes availability/type dependence of the actual public ML application, with the original theorem still in the ambient theory; it does not certify formal capability isolation or semantic single-theorem sensitivity. Later checking is measured separately from historical construction, failures and successor effort. Same-host relocation, another agent and new containers do not establish independent human/external organizational validation. Read the E5/model/loader assumptions and literal contracts before interpreting these as claims about a real deployment.
