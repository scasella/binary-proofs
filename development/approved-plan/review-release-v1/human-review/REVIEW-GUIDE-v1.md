# Review guide: the accepted supplier/caller chain

All three callers have complete historical fresh acceptance within their frozen domains. C1 and C3 required separately recorded successor stages. Their capped failures remain failures. Review status is **PENDING**, and a later consumer replay is separate from this document's source inspection.

## Mathematical meaning

The exact common definition in `contracts-and-rules-v1.json` is:

```text
(assurance_checked_run 0 (P:x86state->bool)
    (C:num->x86state->x86state->bool) s <=> P s) /\
(assurance_checked_run (SUC n) P C s <=>
   (?s'. x86 s s') /\
   !s'. x86 s s' ==> C (SUC n) s s' /\
                      assurance_checked_run n P C s')
```

For positive remaining count, a successor must exist and every successor of the original `x86` relation must meet the local policy and remaining run obligation. Policy compliance is a conclusion about transitions; it is not a condition that filters unsafe successors out of the relation. The exact count is finite for every admitted mathematical length. Each caller's last-step policy requires the actual decoded `RET` transition, including its eight-byte memory read; entry and return-address inequalities exclude a zero-step return. Final-state frame conditions alone are not the access-safety evidence.

`assurance_span_ok perm a width` states nonwrapping `a+width <= 2 EXP 64` and, for every `j < width`, canonical48 address and the explicit permission predicate at `a+j`. A zero-width buffer span has no byte-permission requirement. Full architectural load/store widths are checked, and instruction fetch spans are separate. Memory in the ISA is total; permission truth and ordinary stable memory are supplied by the declared environment, not by successful model reads.

The supplier interfaces `BP_E3_CRYPTO_PUBLIC_CALLER_POLICY` and `BP_E3_CLEANSE_PUBLIC_CALLER_POLICY` provide the established finite checked runs at fixed production entries. The caller proves the public entry precondition through its actual `CALL`, six-byte PLT prefix and eight-byte resolved GOT load. The interface gives comparison/zeroing, access, termination and frame facts; the caller transports snapshots and saved state to its next phase. `RA_CHECKED_RUN_APPEND`, `POST_MONO`, `POLICY_MONO` and `THREE_SEGMENT` compose these segments. Existing ABI/E5 rules lift the resulting scalar run to the public extended-state interfaces. Literal conclusions and leading quantified types are included for inspection; an export manifest is not itself a proof.

## The cases and their exact domains

| Case | Behavior and snapshot | Writes and return slots | Historical result |
| --- | --- | --- | --- |
| C1 | Boolean wrapper: RAX is exactly 1 iff initial `n` byte pairs are equal, otherwise 0. | Only the eight-byte nested-call slot `[S-16,S-8)` is writable scratch; incoming return slot is `[S,S+8)`. All other memory is preserved. | Accepted successor; capped predecessor remains `BLOCKED_FROZEN_CONSTRUCTION_LIMIT / NOT_ACCEPTED`. |
| C2 | Compare initial memory; return exactly 1 for equality and 0 otherwise. Clear `p` only on the equal branch. | `[S-32,S)` scratch; destination writes prohibited on the unequal branch, including intermediate writes. Incoming return slot at `S` is protected. | Accepted development case with explicitly recorded integration adaptation. |
| C3 | Compare initial memory, clear `p` unconditionally, then compare current memory. Return 2 on initial mismatch; otherwise 1 if post-clear equality holds, otherwise 0. | `[S-48,S)` scratch, including four saved eight-byte slots. Incoming return at `S` is distinct from nested calls' return at `S-48`. | Original held-out outcome C remains failed; separately budgeted successor is accepted. |

All cases quantify over arbitrary admitted byte contents and `n < 2 EXP 64`; there is no small length cap, equal-input assumption or input alignment premise. Identical and partially overlapping `p`/`q` are admitted. Each case's explicit span, canonicality, image and separation predicates restrict whether an entire machine entry is admissible.

C1 inputs are readable and exclude its eight-byte call slot. C2/C3 require readable inputs and a writable `p` region even when a branch will not write it; both inputs exclude mutable scratch. The cleared region excludes the incoming return slot and, as required by the image permissions/protection clauses, code/GOT. The readable `q` region may overlap the incoming return slot where the frozen predicate permits it. There is no new mutual `p`/`q` separation. These are caller-specific contracts, not hidden generic validity assumptions.

For zero length C1 returns 1 with no input access; C2 returns 1 and invokes zero-length cleanup with no buffer access; C3 returns 1 through two empty comparisons and empty cleanup. Buffer readability/writability is not required in these zero-width spans. Non-buffer entry, stack, image and fetch requirements remain.

The `LITERAL-CONTRACTS-v1.md` equations are controlling over this prose. They expose initial argument registers, memory snapshot, RIP/RSP, canonical return distinct from entry, `S MOD 16 = 8`, nonwrapping restored stack, DF/AC/RF/TF conditions, FS-base canonicality, code/GOT contents, image permissions and each scratch footprint. Admissible-state witness families supplement these universal run theorems; membership is not an execution result, and canonical-top model witnesses are not claims about feasible Linux user mappings.

## Frame and memory-snapshot arguments

C1 derives callee inputs from current memory after its call-slot write and proves that the initial logical inputs remain unchanged because they exclude that slot. Its public return preserves initial memory outside the slot and restores callee-saved registers and RSP through actual `RET`.

C2 stores initial argument/saved-register information in its declared scratch and keeps the equality result across the cleanup call. The false path preserves all non-scratch memory. The true path's permitted write footprint is `p` plus scratch; bytes of `q` inside `p` intentionally have no preservation claim. Its result always concerns the initial snapshot, not the final cleared bytes. Endpoint frames are composed and saved-register modifications canceled after their actual restoration.

C3 must transport four saved slots, incoming return at `S`, and current code/GOT across cleanup before its second handoff. Cleanup's public interface cannot be interpreted as preserving the initial contents of all writable library pages: those pages can already have changed before the call. The successor derives the relevant current byte predicates from the actual intermediate states and the allowed frame. The initial equality remains saved in R13; the second comparison concerns `c3_cleansed_memory m p n`, including any `q` bytes overlapping `p`. The alias-aware snapshot lemma is applied only after proving its actual premises. No assertion that the second call sees original `q` is substituted for this argument.

The original cleanup endpoint failed because a helper discarded a required pointer/scratch premise. The successor retains that premise, uses the u6 GOT fact for the PLT-derived RIP, assembles u7 prefix/register facts, and instantiates accumulated-frame inclusion at actual states. All four suffix paths then execute to actual return, and their entry bundles come from the preceding chain. Review the selected sources through `results/dependency-map-v2.json` under `c3-successor-v1`; its construction-time status field is historical, while the later complete gate supplies acceptance.

## C3 fixed-site MOV qualification and the extension policy

The predeclared `held-out-transfer-v1/layer/CLASS-AND-EXTENSION-POINTS-v1.md` clauses 3 and 4 permit closed actual-site facts and ordinary local proof sequences using frozen rules. They do not permit a new universal integration algorithm, changed callback/search behavior, new normalizer law or ISA definition under a caller filename.

At caller offset 73, actual RIP `0x23001169`, bytes `b8 02 00 00 00` decode to `MOV EAX,2`. The frozen convenience qualifier's rewrite set leaves an existing immediate-operand predicate opaque, and the original search fails. The successor proves a closed statement for that exact site in `c3-successor-v1/proofs/final-mov2-site-v2.ml`: correct literal decode, existing scalar-class membership, five-byte fetch span, and policy under unchanged events. `final-return-site-steps-v7.ml` applies it through existing `GEN_STEP_TAC`, `CLIENT_CHECKED_BASIC_STEP_TAC` and `R1_X86_CONV`; local numeral reduction reconciles `1+6` with 7.

This site proof changes caller construction sources. It does not modify the generic qualifier, dispatch/matching/control flow, callback implementation, normalization algorithm, exported universal statement, model or supplier interface. The classification as permitted caller work is an inspection-based interpretation of the frozen policy, not a formal ML capability guarantee or completed human approval. It proves no automatic integration rule for arbitrary immediate-MOV sites. Review both the exact policy and the actual tactic inputs rather than deciding generality from their directory names.

## Evidence boundaries and review questions

The complete gates require fresh source reconstruction, exact literal/expanded live conclusions, empty hypotheses/free variables, unchanged `INFINITY_AX`, `SELECT_AX`, `ETA_AX`, source/model/artifact closure, extraction/image checks, five disposable-copy integrity controls and a fresh unusable-public-binding construction probe. A pre-root receipt may retain pending/false acceptance fields; the later complete gate is authoritative for that historical package. Successful logs and status fields do not replace theorem reconstruction.

Five controls reject changed executed bytes, modeled GOT, model/contract binding, missing supplier source and missing caller source despite stale success metadata. These are identity/dependency controls. The probe shadows the required public ML binding with `unit` and observes failure at application after fresh supplier reconstruction; the old theorem still exists in the ambient theory. Neither result is a semantic mutation proof or a single-theorem derivation-dependency certificate.

The human review should concentrate on whether the literal domain/post matches the intended behavior, access-event completeness for every reached instruction class, architectural justification for E3/E5/omitted-state clauses, snapshot/frame transport under admitted aliases, source-qualified opacity, the fixed-site extension classification and the theorem-to-final-image correspondence. No blocking finding has been recorded by preparation of this packet. That is not a substitute for this review.
