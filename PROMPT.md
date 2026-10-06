Binary-level verification of glibc and OpenSSL

1. Mission

Act as an autonomous formal-verification and systems-engineering agent. Build and execute a reproducible experiment that establishes reusable, machine-checked guarantees about actual production binaries of glibc and OpenSSL.

Deliver working proof artifacts, executable verification commands, and an evidence-based report. Do not stop at a proposal, repository scaffold, disassembly, tests, or an abstract model.

The motivating article, Bootstrapping the Verified Software Stack, argues for verifying production machine code and reusing verified runtime interfaces across dependent programs. It does not supply this implementation recipe. The targets, contracts, milestones, and acceptance criteria below define our experiment, not the authors’ completed system or a promise of success.[1]

The required chain is:

Pinned production library artifact
    -> exact linked bytes and declared loaded-memory image
    -> existing formal instruction-set semantics
    -> checked implementation theorems
    -> checked callable-interface theorems
    -> checked proofs of separately compiled callers

Existing binaries are valid starting points; rebuilding is not mandatory. Source, headers, debug information, and disassembly may assist discovery. They must not replace the final binary as the proof target.

The project targets are glibc and OpenSSL. Individual routines are initial work units, not substitutes for those targets. Preserve an explicit inventory of the remaining library-level obligations.

2. Operating defaults and boundaries

Use Linux x86-64, little-endian execution, and the System V AMD64 ABI. Use one immutable nixpkgs revision and its production binary artifacts where available. Record the package derivations, outputs, revisions, and hashes. Do not claim to reproduce the article’s particular snapshot without establishing that correspondence.

If Nix is unavailable, use coherent production distribution packages from a pinned container image or repository snapshot. A normal, reproducibly configured upstream release build is a further fallback. Record which provenance class you used. Distribution patches are permitted when they belong to the unchanged pinned package recipe; proof-motivated patches are not.

Inventory glibc, its matching dynamic loader, OpenSSL’s libcrypto, libssl, and applicable provider modules. OpenSSL distinguishes its crypto and protocol libraries and can include built-in or loadable providers; inspect the selected build rather than assuming every operation lives in one shared object.[8]

Freeze the baseline CPU/OS capability profile before assessing proof difficulty. Use the execution environment’s actual x86-64 profile when available. On other hardware, declare the emulated or modeled profile and distinguish emulated testing from native testing. Record relevant processor features, OS-enabled register state, page-permission assumptions, and runtime configuration.

Do not simplify the baseline libraries. Do not replace glibc with musl, OpenSSL with another crypto library, or either target with rewritten code. Do not disable assembly, optimization, hardening, or runtime implementation selection to obtain easier proofs. A deliberately different supported profile may be a separately identified experiment; it must not silently replace the baseline.

Work in an isolated project environment. Do not replace the host’s libc or OpenSSL installation. Use available authorized resources; do not purchase compute, invoke paid external services, publish a repository, or modify unrelated systems without authorization.

Make reasonable implementation choices under these defaults and record them. Do not pause merely to ask which prover, package revision, or directory name to use. Persist progress and exact blockers when resources run out.

3. Milestones and completion levels

|ID|Required result                                                                                                                                                                      |
|--|-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
|P0|Pin artifacts and environment, inventory target instructions, qualify a binary-proof backend, and establish exact-byte binding.                                                      |
|O1|Prove functional correctness, access safety, termination, and ABI preservation for actual `CRYPTO_memcmp` and `OPENSSL_cleanse` implementations.                                     |
|G1|Prove the corresponding properties for the actual glibc `memcmp` implementation selected by the baseline profile.                                                                    |
|O2|Prove the defined secret-independent execution-trace property for `CRYPTO_memcmp`.                                                                                                   |
|D1|Prove the relevant compiled glibc implementation selector under the declared configuration, and compose its result with G1. Document the remaining loader/initialization assumptions.|
|R1|Verify two compiled callers against the established glibc/OpenSSL interfaces without reopening the callee implementation proofs.                                                     |

Suggested execution order: P0, the smaller O1 routine, the rest of O1, G1, O2, D1, R1. Independent work may proceed in parallel. A blocked glibc proof must not prevent useful OpenSSL work, or vice versa.

Meaningful partial result: At least one actual target routine has exact-artifact binding and all four O1/G1 obligations checked. Identify the routine and scope; do not label the core complete.

Core complete: P0, O1, G1, O2, D1, and R1 pass, with the integrity controls and clean replay below. Core completion is conditional on the explicitly stated machine and loading assumptions.

Library-wide verification: Not established by these milestones. It requires the remaining declared entry points, configurations, state invariants, and dependencies to be covered. Report library-wide completion as incomplete until that work is actually done.

Backend examples are setup tests, not project results. Obtain a proof about a target-library artifact before building extensive orchestration or dashboards.

4. Artifact inventory and byte binding

Create a machine-readable inventory keyed by artifact digest, entry point, implementation variant, configuration predicate, and contract digest.

For each artifact, record its provenance, package/revision identifiers, SHA-256, ELF build ID when present, architecture, ABI, loadable segments, permissions, symbol versions, dependencies, and relocations. Preserve source and build metadata when obtainable; explicitly mark unavailable metadata rather than reconstructing it by guesswork.

For each target, record the exact file offsets, virtual-address relationships, code bytes, referenced data, reachable helpers, dispatch paths, and external calls. Obtain matching debug information when useful, but verify that it matches the target. Symbol names and source resemblance are not sufficient artifact binding.

At every accepted replay, independently check that the byte sequence named by the theorem matches the frozen final-linked artifact and its declared loaded image. Account for load bias, relevant relocations, and immutable constants. If a proof begins from an intermediate object, supply a checked connection to the final linked bytes.

Disassemblers may help discover code. An unverified translation into pseudocode is not the execution semantics. A lifted intermediate representation is acceptable only when its connection to the exact machine-code semantics is checked.

A hash identifies an artifact; it does not establish correct extraction, relocation, or loading. Keep those mechanisms in the trust inventory, and cross-check extraction with an independent tool. Do not describe that cross-check as formal verification of the parser.

Include all code reachable under the contract. A static call graph is discovery evidence, not a proof that indirect targets or branches are exhaustive. Prove that execution remains within the covered code or calls only established interfaces with discharged preconditions.

When separate artifacts contain identical code, reuse only with checked byte/address/data correspondence. Recompiling the same source is not sufficient. Count reused proofs as reuse, not new proof discovery.

5. Proof foundation and trust policy

Use an existing formal x86-64 model and a proof-checking foundation. First evaluate HOL Light with the s2n-bignum x86 infrastructure: it provides machine-code proofs tied to its own object-code artifacts. This is a candidate foundation, not a claim of turnkey support for the selected glibc/OpenSSL binaries.[2]

Qualify the backend against the actual target instruction encodings, vector operations, flags, memory behavior, and required trace properties. Replay an existing example to validate installation, then establish a target-specific path to proof.

Another existing binary-level framework is permitted if better suited. Record the choice and freeze the version. Reusing another project’s theorem does not certify these libraries’ different bytes.

Do not treat unsupported instructions as no-ops or invent a simplified target-specific ISA. New tactics and conservative lemmas are allowed. A necessary semantic-model extension must be separately versioned, justified against architectural documentation, tested against independent execution where possible, and explicitly added to the trust review. Requalify affected proofs; never conceal the extension.

The accepted final obligations must be checked by the declared logical foundation. No unfinished proofs, newly postulated target-correctness axioms, assumed invariants, or unverified solver answers may discharge them. Solvers and search tools may assist when their proof evidence is accepted through the declared checking policy.

Write TRUST.md separating the logical kernel/runtime, ISA model and decoder, artifact extraction/loading, proof automation, external tools, and real-machine/environment assumptions. Pin the trusted components and audit the dependencies of each final theorem.

A functional theorem and final-state frame condition alone do not establish that all intermediate accesses are permitted. The s2n-bignum soundness documentation makes this distinction and describes separate safety/trace infrastructure; inspect what the pinned backend actually proves.[3]

If access events are added, establish their correspondence to the original machine transitions. An unrelated trace interpreter is insufficient. If the machine model has total flat memory, prove a separate access-policy theorem; do not interpret successful model reads as evidence of real memory permissions.

6. Freeze contracts before main proof search

Perform artifact inspection and contract design first. Then freeze human-readable requirements, formal statements, environment predicates, and approved assumptions under spec/ before attempting the main proofs.

Keep this prompt immutable as the requirements baseline. Specification files may formalize it, not redefine success to fit the implementation. Human review remains pending unless a human actually reviews them; another agent’s review is not human approval.

A meaning-changing revision creates a new experiment ID and preserves the previous result. A weaker or restricted-domain theorem can be useful partial evidence, but it cannot pass an unchanged milestone.

Common machine-level requirements

Quantify over all allowed input contents and all machine-representable lengths whose required regions satisfy the explicit preconditions. Do not impose a small length cap, assume equal inputs, or require alignment that the selected interface does not require merely to simplify proof search.

Define initial register placement, program counter, stack alignment, return address, preserved registers, flags, processor state, and code/data loading conditions. Decode every helper predicate used in the theorem; no opaque catch-all valid_state with hidden behavioral assumptions.

Make address arithmetic precise. Exclude unintended wraparound and noncanonical or inaccessible accessed addresses through explicit region predicates, not an arbitrary signed-size restriction.

For nonempty comparisons, require readable, stable logical input regions. For clearing, require a writable destination, plus readability only where actual reads require it. Define these permissions separately from logical bounds.

For comparisons, permit identical and partially overlapping inputs. Separate inputs and output regions from mutable scratch and code where required. For zero length, require no buffer access and no buffer readability/writability premise. This is a machine-level contract, not an assertion about null-pointer legality in every C-language context.

State a sequential execution model with no concurrent modification of relevant state. Assume only explicitly declared environment behavior; do not claim kernel, hardware, loader, or concurrency verification.

For every target, prove the following package:

Functional correctness. Establish the target-specific result over the initial logical inputs.

Access safety. Account for every data read, data write, implicit stack access, and instruction fetch, including the full architectural width of each access. For masked or special memory operations, use the pinned semantics rather than guessing from register width. Prohibit forbidden intermediate writes even when the value is restored later.

Termination and covered control flow. Prove finite return for every permitted execution, including allowed ISA nondeterminism. Cover all reachable branches and calls. Bounded unrolling, one terminating path, or correctness conditional on termination is insufficient. Define completion through the actual return transition; exclude a zero-step “proof” caused by the return address equaling the initial program counter.

ABI and frame preservation. Prove the specified return state, callee-saved state, stack restoration, and preservation outside the permitted write footprint. Bound scratch space from the implementation. Protect the routine’s incoming return-address slot while accounting for legitimate nested-call stack writes.

Non-vacuity checks must provide machine-checked witnesses of admissible states for empty, equal, unequal, misaligned, identical-pointer, overlapping, and relevant boundary cases. Include byte values above 127. For clearing, include nonzero initial memory. These witnesses supplement the universal theorem; they do not replace it.

7. Memory contracts: keep logical bounds separate from mapped pages

Define two named properties and report them separately.

STRICT_BUFFER_ACCESS: Buffer reads remain within the logical input ranges; buffer writes remain within the designated output ranges. Separately declared stack, code, and immutable-data accesses remain permitted.

MAPPED_PAGE_ACCESS: Reads may include surrounding bytes only within the explicitly defined readable pages intersecting the logical inputs. Writes remain restricted to the designated outputs and scratch. This does not establish strict object-bound access or confidentiality of neighboring bytes.

This distinction is necessary to investigate production implementations rather than silently reject or rewrite them. For example, the referenced glibc AVX2 memcmp source includes wider short-input loads after a page-crossing check; confirm the behavior of the selected binary instead of assuming this example describes it.[5]

For baseline G1, use MAPPED_PAGE_ACCESS and separately attempt/report STRICT_BUFFER_ACCESS. Define a permission granule P, defaulting to 4096 bytes for this modeled configuration:

PageCover(p, 0, P) = empty set

PageCover(p, n, P) = union of the P-byte aligned pages
                    intersecting the mathematical interval [p, p+n)
                    when n > 0

Require those pages to be accessible under the declared permission model, stable for the call, and ordinary memory rather than device memory. Prove that every non-stack input-related read lies within the union of the two PageCover sets. Enumerate other permitted reads separately. Do not grant access to all mapped process memory.

Do not constrain the values of extra readable bytes to zero, equal each other, or satisfy the desired result. Establish that changing only those extra bytes, while preserving logical inputs and required public state, cannot change the comparison result. Do not infer timing confidentiality from that result-independence theorem.

For O1, require STRICT_BUFFER_ACCESS. Do not silently switch an OpenSSL target to the weaker page property after a failed proof. Record a contract mismatch and any alternative theorem separately.

A failure of strict access in an optimized routine is not automatically a production vulnerability. Classify results against the specific contract and environment, not against an assumed interpretation of “memory safe.”

8. G1: glibc memcmp

Identify the exact implementation selected by ordinary baseline dispatch. Prove that implementation in its frozen final library, not only a generic source fallback or a conveniently named symbol.

Let A and B be the initial sequences of n unsigned bytes at p and q. Let r be the signed 32-bit ABI return value. Require:

If every A[i] equals B[i] for 0 <= i < n:
    r = 0.

Otherwise, with j the first differing index:
    sign(r) = sign(A[j] - B[j]).

For n = 0, return zero without input-buffer access. Do not require a particular magnitude for nonzero results or constrain unspecified upper return-register bits.

Prove mapped-page access safety, termination, and ABI/frame preservation. Neither logical input may be written. Record strict-access status separately.

If the selected implementation uses unsupported instructions, preserve the blocker. A proof of another genuine implementation may count as variant-specific progress, but not as proof of baseline G1.

9. O1: OpenSSL memory primitives

Identify the implementations actually supplied by the frozen libcrypto artifact. Check for wrappers, internal calls, assembly variants, configuration reads, and symbol binding. Do not assume all OpenSSL functions go through provider dispatch.

CRYPTO_memcmp

OpenSSL documents equality testing, not lexicographic ordering: zero means equal and any nonzero result means unequal.[6]

Using the same initial unsigned byte sequences:

r = 0  if and only if  A[i] = B[i] for every 0 <= i < n.

Require strict buffer access, no input writes, termination, and ABI/frame preservation. For zero length, return zero without buffer access. Do not require positive/negative ordering or a specific nonzero value.

OPENSSL_cleanse

OpenSSL documents overwriting the designated region with zeros.[7] For initial destination p and length n, require:

For every 0 <= i < n:
    final_memory[p+i] = 0.

Prove strict buffer access, termination, ABI preservation, and that every write stays within the destination or explicitly permitted scratch. Show that no other memory changes. For zero length, perform no destination access.

This theorem concerns the designated memory region. It does not establish removal of every secret copy, clearing of all registers, physical storage erasure, or absence of microarchitectural remnants.

10. O2: secret-independent execution traces

Define and freeze an observation model for CRYPTO_memcmp before its relational proof.

Public inputs include length, addresses, mappings, code, CPU/configuration state, entry/return state, and any other explicitly declared public state. Compared byte contents may differ between the two executions, subject to consistency where input regions overlap.

The architectural observation trace must include instruction/control-flow observations sufficient to expose branches and iteration counts, plus each data-access address, width, and read/write kind. Loaded/stored secret values and the returned equality result are not part of this trace.

Prove:

For any two allowed initial states agreeing on public state,
execution to return produces the same defined observation trace.

The quantification must include cases with different equality results and mismatch positions. Do not assume both inputs are equal, both comparisons return the same result, or the secret buffers are identical across runs. Handle public nondeterministic choices explicitly; existence of one convenient matching pair is insufficient.

The intentionally returned equality information is allowed to differ. Scope ends at the return boundary, not after arbitrary caller behavior.

Call the result architectural trace noninterference under the declared observation model. Do not advertise constant elapsed time on all processors. Document instructions with potentially operand-dependent timing and any stronger timing assumptions separately. An empirical timing test is supplementary, not a proof.

A claim of the same property for a caller requires proofs for that caller and every reached callee; it does not follow solely from CRYPTO_memcmp.

11. D1: prove implementation selection and state the loading boundary

The referenced glibc x86-64 selector chooses among implementations using feature/configuration conditions. Treat that as motivation to inspect the frozen resolver, not a substitute for proving its compiled behavior.[4]

Separate three claims:

Implementation: Entry at address X satisfies contract C. This is G1.

Selector: Under configuration predicate Q, the actual resolver’s machine code returns an implementation address satisfying C. Prove the baseline branch and every dependency reached under Q. Broader profile coverage requires all selectable implementations under the broader predicate.

Loaded call binding: The public call, including any relevant procedure linkage table (PLT), global offset table (GOT), symbol version, or resolved pointer, reaches that implementation in the modeled post-initialization image.

For the core experiment, loader execution and CPU-feature initialization may remain explicit environmental assumptions. Define their exact postconditions: code/data placement, resolved entries, stable capability data, allowed symbol binding, and absence of unmodeled interposition. Do not assume target functional correctness within those postconditions.

Discharge the selector-to-interface implication and prove call transitions from that declared state. A source-level selector proof, one debugger observation, or assuming “dispatch is correct” does not pass D1.

For OpenSSL, inventory comparable selection mechanisms where they actually affect the scoped routines. Do not impose nonexistent provider dependencies, or omit providers when later targets genuinely reach them.

Report this as a conditional public-interface guarantee, not verification of process startup, the dynamic loader, or every deployment configuration.

12. R1: demonstrate reusable proofs in compiled callers

Create and compile these two small experimental callers against the same frozen libraries:

#include <stddef.h>
#include <string.h>
#include <openssl/crypto.h>

int public_buffers_equal(const void *a, const void *b, size_t n) {
    return memcmp(a, b, n) == 0;
}

int secret_equal_and_clear(void *secret, const void *expected, size_t n) {
    int equal = (CRYPTO_memcmp(secret, expected, n) == 0);
    OPENSSL_cleanse(secret, n);
    return equal;
}

These callers are new demonstration code, not production downstream packages.

Prove their actual final-linked machine code. Prevent builtin substitution and cross-library inlining for these client calls using recorded client-only build choices. Do not change the production libraries. Confirm that calls reach the intended implementations rather than another host installation.

The first caller must return exactly 1 for equal initial byte sequences and 0 otherwise. The second must return that same equality predicate over its initial inputs and leave its secret region zero on return. If the regions overlap, the equality result still concerns their initial contents; no preservation claim applies to bytes inside the cleared region.

Both callers require access safety, termination, ABI/frame preservation, and discharged call-site preconditions. The first inherits the glibc access contract; do not upgrade it to strict access without proof. No trace guarantee for either caller is implied unless separately established.

Use a fixed post-initialization loaded image or a proved permitted load-bias range with the original frozen libraries. Include the actual linkage stubs or indirect-call transitions traversed. Reusing an interface under explicit loader-state assumptions is permitted; silently replacing the library with copied code is not.

Package each callee’s public theorem with its code-binding predicate, preconditions, postconditions, permitted effects, termination/access guarantees, configuration assumptions, and trace theorem where available.

Client proofs must apply those interface theorems without unfolding callee instruction semantics. Final replay must still check the complete callee proof chain. An assumed or stubbed interface is not reuse.

Where fresh worker contexts are available, give the client worker interfaces and call-binding information but not implementation proof scripts. Otherwise report that isolation was unavailable; do not claim an independent-agent experiment.

Record callee construction cost, marginal caller cost, and complete replay cost separately. One or two compositions do not establish ecosystem-scale savings.

13. Extend coverage after the core milestones

Maintain a prioritized backlog within the actual pinned libraries. Prefer work that discharges outstanding dependencies or enables additional verified callers. Distinguish observed call dependencies, package runtime references, and inferred reuse potential; do not equate them.

G2 — Additional glibc interfaces and variants. Extend dispatch coverage and add an appropriate memory-primitive family. Freeze each API’s semantics independently, including overlap behavior and return values. Do not copy memcmp assumptions into other functions indiscriminately.

K1 — A substantial OpenSSL kernel. Target the actual SHA-256 block-processing path selected in the pinned build. Pin an authoritative mathematical compression specification, prove the selected machine code for all permitted states and block counts, and connect one actual caller through a reusable theorem. Separate a compression theorem from full padded-hash correctness, provider selection, TLS correctness, and cryptographic security claims.

M1 — Maintenance and proof repair. Select one explicit later package revision or changed normal build, freeze its artifact, and attempt the same public contract. Check artifact binding afresh; compare inherited proof repair with fresh construction where genuine isolation is available. Report unchanged byte regions as reuse, not newly discovered proofs.

The optimization-level matrix is optional and lower priority than production dispatch and proof reuse. Do not spend the core budget manufacturing simplified builds.

Before broader stateful APIs or libssl, define shared-state invariants and valid call sequences. Do not infer whole-library correctness from isolated stateless routines. Group mutually dependent functions with joint invariants rather than inventing a circular chain of assumed contracts.

14. Tests and acceptance-integrity controls

Add deterministic differential tests against independent simple references. Exercise empty inputs, misalignment, overlaps, signed/unsigned-byte distinctions, first/last mismatches, and length/alignment boundaries actually present in the code. Vary extra page bytes while holding logical inputs fixed.

Use local page-boundary/guard-page tests to diagnose access assumptions. Keep tests within an isolated local harness. Tests and counterexamples are diagnostic evidence, not substitutes for a universal proof or claims about production exploitability.

Show that native or emulated tests execute the frozen target bytes. Record seeds, counts, hardware/profile, and limitations. Instrumented or separately rebuilt binaries are different artifacts and cannot inherit the target’s proof by name.

Provide automated negative controls:

1. Mutate a verified code byte in a copy of the ELF without changing its manifest/proof. Acceptance must reject it before execution.
2. Change a frozen contract or trusted dependency while retaining old results. Reject stale success and invalidate affected caches.
3. Remove a required callee theorem from a clean R1 replay. The client must fail rather than use an assumed interface.
4. Change a modeled resolved call target to an unproved implementation. Binding/composition checks must reject it.
5. Remove a required theorem while leaving a plausible success log. Acceptance must reject the incomplete proof package.

Run negative controls on copies. Do not mutate the canonical frozen inputs.

The acceptance driver must check expected theorem statements, approved assumptions, dependencies, and artifact bindings—not filenames, log phrases, exit codes from unrelated commands, or stored status fields. Any skipped required obligation, timeout, unsupported instruction, or missing dependency produces non-success.

15. Reproducibility and repository interface

Deliver at least:

README.md
TRUST.md
PROMPT.md
locks/                  # packages, environment, toolchain, proof backend
artifacts/              # frozen targets or digest-checked acquisition manifest
inventory/              # code regions, variants, configuration/dependency graph
spec/                   # readable requirements, formal statements, review status
proofs/                 # implementations, interfaces, dispatch, clients
clients/                # demonstration source and pinned build commands
tests/                  # deterministic native/emulated diagnostics
negative-controls/      # integrity rejection tests
scripts/                # acquisition, binding, checking, measurement, reporting
results/                # structured outcomes and raw logs
REPORT.md

Large artifacts may use digest-checked acquisition instead of vendoring. Preserve required licenses. Make all dependencies needed for replay locally available after setup.

Expose these commands or direct documented equivalents:

make setup              # Fetch/provision pinned dependencies; network permitted.
make freeze             # Create a new explicit baseline; never silently overwrite.
make inventory          # Record artifacts, entry points, variants, dependencies.
make verify-openssl     # Check O1 and report each routine separately.
make verify-glibc       # Check G1 for the baseline implementation.
make verify-traces      # Check O2.
make verify-dispatch    # Check D1.
make verify-clients     # Check R1 and complete callee proof dependencies.
make negative-controls  # Check all required rejection cases.
make verify-clean      # Replay the full core in a fresh checking environment.
make report             # Generate the report from actual recorded evidence.

verify-clean must work offline after setup, without model credentials, AI calls, interactive repair, or target-specific success caches. Reconstruct/check proofs from their sources or accepted proof certificates. Pinned foundational artifacts may be reused only through the declared trust policy.

Verification commands return nonzero when their required obligations are incomplete. Reporting may still run to explain failures. Do not make clean verification fetch a moving branch or silently regenerate a specification.

16. Measurements and reporting

Record every attempt, including failures, in structured JSON/JSONL. Include experiment/run ID, target and variant, artifact/spec/backend hashes, configuration and trust-assumption IDs, theorem names, outcomes, failed obligations, proof dependencies, reuse status, elapsed proof-construction and checking time, peak memory when available, human interventions, and raw-log locations.

Use exact model/agent identifiers supplied by the execution environment when available. Record observed token usage and costs only when exposed. Otherwise use null with a reason. Do not invent billing, infer model identity from self-description, or omit unsuccessful workers from totals.

Separate setup from marginal proof work and proof construction from checking. Record separately unique covered instruction bytes, declared code-region bytes, associated data, and dependencies. Do not count an entire ELF as verified because one entry point passed, or count shared bytes repeatedly.

Track each property separately. Use statuses such as PASS, PARTIAL, BLOCKED, NOT_ATTEMPTED, and COUNTEREXAMPLE, with explanations. A proved counterexample must identify the exact formal contract it refutes. Distinguish a model mismatch, implementation/contract mismatch, proof-search failure, and environment/tooling failure.

Lead REPORT.md with the real completion level. Include the literal formal statements and plain-English meaning, exact artifact/configuration scope, trust boundary, per-milestone and per-property status, coverage inventory, remaining obligations, negative-control results, replay commands, and measured costs.

Do not extrapolate dollars per kilobyte or ecosystem completion dates from this small experiment. Do not claim that memory safety implies arbitrary functional correctness, that trace noninterference proves all hardware timing properties, or that selected routine proofs establish glibc/OpenSSL/library-closure correctness.

17. Start now

Inspect the environment, pin coherent glibc/OpenSSL artifacts, record the baseline execution profile, and locate the actual target implementations. Qualify the binary-proof backend and freeze the contracts. Then construct and check a theorem about one real target routine.

Continue through the milestones as dependencies and resources allow. When blocked, preserve the exact artifact, attempted proof, last verified obligation, and next concrete technical action; work on another independent milestone where productive.

The deliverable is a growing set of checked guarantees about real library bytes, connected to reusable interfaces and compiled callers—not a rewritten library, a favorable test run, or a large framework surrounding unproved models.

Reference starting points

These are background and navigation references, not immutable version pins. Resolve authoritative sources and freeze relevant revisions during setup. This prompt’s requirements are complete without the prior conversation or the article attachment.

[1] Theorem, Bootstrapping the Verified Software Stack, September 29, 2026; especially “Our setup” and “The order of work.” https://theorem.dev/blog/verified-software-stack/

[2] s2n-bignum repository and proof workflow. https://github.com/awslabs/s2n-bignum

[3] s2n-bignum soundness/trust and safety documentation. https://github.com/awslabs/s2n-bignum/blob/main/SOUNDNESS.md

[4] Reference glibc x86-64 implementation selector; inspect the chosen release rather than treating this moving/mirrored reference as the experiment’s artifact. https://github.com/bminor/glibc/blob/master/sysdeps/x86_64/multiarch/ifunc-memcmp.h

[5] Reference glibc AVX2 comparison implementation and page-boundary handling. https://github.com/bminor/glibc/blob/master/sysdeps/x86_64/multiarch/memcmp-avx2-movbe.S

[6] OpenSSL’s CRYPTO_memcmp contract. https://github.com/openssl/openssl/blob/master/doc/man3/CRYPTO_memcmp.pod

[7] OpenSSL memory-function documentation, including OPENSSL_cleanse. https://github.com/openssl/openssl/blob/master/doc/man3/OPENSSL_malloc.pod

[8] OpenSSL library/provider structure. https://github.com/openssl/openssl/blob/master/doc/man7/ossl-guide-libraries-introduction.pod
