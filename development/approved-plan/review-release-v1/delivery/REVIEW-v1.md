# Review companion

The release has two source/evidence archives and one pinned Docker-image sidecar. The already consumed `checking-sources-v1.tar.gz` supplies the exact reconstruction inputs. `review-evidence-v1.tar.gz` adds the authoritative release index, current generated report, human-review views, manuscript, actual consumer receipts and selected immutable historical failures/successor evidence. It does not replace the tested mathematics bundle.

`DELIVERY-FINAL-v1.json` supplies the outer archive/index/bootstrap digests. Obtain those expected digests through the release handoff. After checking the outer digest, extract the mathematics with the exact commands in `CHECKING-v1.md`. Then overlay the review companion into that fresh source tree:

```sh
python3 -B extract-review-v1.py --archive review-evidence-v1.tar.gz --sha256 REVIEW_ARCHIVE_SHA256_FROM_DELIVERY_FINAL --output source
```

Substitute the actual review-archive digest from `DELIVERY-FINAL-v1.json`. The extractor rejects traversal, symlinks, unlisted/duplicate/nonregular members and differing existing files. It checks every extracted file against the sealed companion manifest. This is trusted Python extraction/identity checking, not formal parser verification or human review.

Start the human review at `source/development/approved-plan/review-release-v1/human-review/README.md`. The literal contracts and expanded terms are provided alongside checked-run/access/frame/snapshot rules, E5/architecture interpretation, concrete artifact/linkage assumptions, the candidate extension policy and exact C3 MOV qualification sources. The source maps identify canonical accepted files. Archived unsuccessful and unexecuted sources are evidence of those attempts, not positive proof packages.

Current status is controlled by `source/development/approved-plan/review-release-v1/release-index-v1.json`. Historical gates and chronological reports retain their original meanings; the current index does not rewrite them. The candidate-layer regression packages are additive checks, not migrations of C1/C2's historical accepted proofs. Later consumer runs are checking only. Source/deadline/identity controls, inspecting code and collecting live kernel results provide different kinds of evidence; none constitutes completed human or external-organizational validation.

Review status remains pending until a human performs it. Record any blocking finding in a separately versioned record identifying exact definitions/theorems, affected claims and evidence; suspend affected current claims rather than rewriting old results. No proof/model repair or new research stage is authorized by the review packet.

Licenses in `licenses/`, the preserved foundation archive and distribution images remain part of the delivery. The final review companion preserves the actual historical digest identities. Required original dependencies and artifacts are locally available through the checking archive/images; no moving-branch fetch is part of replay.
