# BP-20260930-E2 candidate trust inventory

This successor candidate preserves E1 and its checking bundle. It adds an
explicit canonical return address and nonwrapping restored stack pointer to the
machine entry domain. Human specification review remains **PENDING**. No full
routine, core, or library-wide result is accepted by this document.

The original [TRUST.md](/Users/scasella/Downloads/binary-proofs/TRUST.md) remains
frozen. This document records additional development components and does not
retroactively change the predecessor's claims.

## Logical foundation and runtime

HOL Light revision `b19af6934759eed622d7aca25092367f81656eee` checks conservative
proof constructions. The pinned ARM64 checker image is
`sha256:a19fdc18f1f283ed8e2514229b77f33619df1ba0ea1ae578c97779f4b4eb3c3f`.
The exact image ID in each frozen component seal controls execution. OCaml 4.14.1, Camlp5 8.02.01,
compiled parser bytes, platform runtime and HOL kernel are trusted. No target
correctness axiom, unverified solver result, or postulated loop invariant is
permitted. Final live-object audits require empty theorem hypotheses, exact
frozen conclusions and an unchanged foundational axiom set.

The predecessor preservation archive omitted generated `update_database.ml`
required by initialization and the generated parser source `pa_j.ml`. The
[correction](/Users/scasella/Downloads/binary-proofs/development/approved-plan/integrity/RUNTIME-DEPENDENCY-CORRECTION.md)
pins these supplements. The theorem database's use of runtime reflection and
`Obj.magic` is part of the HOL/runtime trust review. The closure correction is
preserved explicitly; predecessor preservation was not proof of closure.

## ISA and observations

The original x86 transition relation is the pinned s2n-bignum model at revision
`4d1356a7470663c752660a59375dc3a9ef548428`. Its flat total memory does not
establish physical memory permission. Fetch and access-policy predicates check
mathematical nonwrap, 48-bit canonical addresses, declared ordinary-memory
permissions and the full width of each access independently of successful model
reads. New observation and policy lemmas retain **every original successor**;
they do not filter out bad transitions.

`REP_RET_DECODER_V1` recognizes the actual `F3 C3` bytes as the existing near-RET
constructor. It is a separately frozen decoder extension, with primary
architectural documentation and limited emulated execution diagnostics. The
original decoder stays preserved. Its operation correspondence is a reviewed
model assumption, not a claim that the physical processor was verified.

The scalar ABI extension's final state inventory is V4. Its fourteen added
fields are x87 control/status/tag/opcode/IP/DP/registers/FCS/FDS, MXCSR, and FS/GS
selectors and bases. `extension-v2.ml` supplies a generic opcode class, independent
of a library, PC, or byte identity. It keeps the original decode and execute
relation; documented scalar instructions preserve the added fields, while
other decoded instructions leave them unconstrained. Unsupported instructions
are not no-ops. Projection, every-successor backlift, actual target-site
qualification and path lifting are kernel-checked structural results.

Physical correspondence of these added scalar effects is an **explicit new
trusted semantic-model clause**, justified by pinned primary manuals and opcode
reviews. It is not proved by the product relation, preservation tautology, or
execution tests. All reached instruction sites must be qualified before a
routine can use it. Original scalar frames separately preserve SIMD/opmask and
callee-saved integer state. The required ABI controls include x87 CW, MXCSR
control bits 6–15, and FS selector/base; the fourteen-field equality is stronger.

The 53-theorem fresh assurance component audits 22 expanded helper definitions
as well as their frozen theorem terms. The extension's final source and
architectural document hashes are in
[v4-final.freeze.json](/Users/scasella/Downloads/binary-proofs/development/approved-plan/abi-qualification/v4-final.freeze.json).
FXSAVE64 diagnostics do not observe FCS/FDS or FS/GS; they do not establish the
architectural model's physical fidelity. Emulated diagnostics make no native
x86 or verified-emulator claim.

## Artifact extraction and loading

Unchanged Debian production library artifacts, the target container, recorded
profile and 95-byte `CRYPTO_memcmp` region stay identical to E1. Its region is
`0x241840` in the final libcrypto ELF, with SHA-256
`a20666fb4b0acdf9789fa7316a023fdc47b8c6671a064ba9800b49980e83ad45`.
Fresh acceptance cross-checks the independently written ELF parser with GNU
objcopy, checks PT_LOAD offset/address correspondence and rejects code relocation
overlap. Neither parser nor this cross-check is formally verified.

The explicit
[post-initialization image declaration](/Users/scasella/Downloads/binary-proofs/development/approved-plan/loading/declared-postimage-v1.json)
uses positive page-aligned load bias `0x10000000`, entry `0x10241840`, frozen
PT_LOAD file intervals, initial BSS zero-fill, page permissions and post-init
RELRO. Loader relocation, capability initialization, writable global poststate,
page enforcement and symbol binding remain environmental assumptions. No target
functional behavior is assumed in these postconditions. CRYPTO_memcmp reaches
no helper, external call or library global read. Thus its theorem does not
require particular unused writable global values.

The first eight scalar witnesses are kernel-checked instances of the scalar
entry predicate. Their isolated code placement and byte-granule permission map
do **not** extend a full loaded library. They remain component evidence. The
new loaded-witness family must preserve an independently bound reference image
and use page-granule permissions. Abstract canonical-top witnesses are not
claims that Linux user mode can map those addresses. Full loaded-image witness
composition remains an explicit obligation.

## Automation and acceptance

Tactics and proof recipes construct HOL theorem objects; they are not accepted
through a textual success log. Each fresh driver requires an externally supplied
seal SHA-256, exact source set, source/output mounts with no writable alias, no
network, pinned checker image, source hash rechecks, required live theorem names,
empty hypotheses, expected conclusions and no added axioms. Stored results are
observations only. The functional and scalar-domain drivers cannot accept O1.
Meaning changes require a new preserved version and dependency seal.

Complete callable guarantees additionally need the exact-count safety,
functional, frame and ABI endpoints composed under the same explicit domain;
actual RET history; code/image binding; admissible witnesses; and negative
controls. No assumed callee interface can replace any of these. Client reuse,
public call-binding composition and full core clean replay are still absent.

## Real-machine and environment boundary

The sequential model assumes stable code, logical inputs, return slot,
permissions and public configuration, ordinary memory, no concurrent writes,
48-bit canonical addressing, AC clear, CET disabled, and the frozen CPU/OS
profile. It verifies neither kernel/page tables, loader/startup, physical ISA
implementation, concurrency, nor microarchitectural timing. Permission truth is
provided by the declared environment; total model memory does not supply it.
Architectural event equality alone is not full instruction-trace noninterference.
