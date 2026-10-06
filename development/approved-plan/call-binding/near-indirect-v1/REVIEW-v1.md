# Agent semantic review of generic near-indirect candidate 4

Source review result: the candidate has the intended successful-step target,
operand width and complete load/store footprint for the supported long-mode
near-indirect forms. This is an agent review, not human approval or acceptance.
Kernel qualification, independent diagnostics, physical model correspondence,
ABI coverage and caller proof assembly remain gates. The accepted CRYPTO seal
and its original-model sources are unchanged.

Reviewed source hashes:

| Source | SHA-256 |
| --- | --- |
| proofs/model-extension/decode.ml | `ab053d1eca6f67b2257f19db5ca2be0a9c5d3aa7040fa2068efd4be4cc3de15d` |
| third_party/s2n-bignum/x86/proofs/x86.ml | `daa84c1661610a9b95af0b4ad88bf15297fffd22735fd6004c331ed353cfd005` |
| development/approved-plan/call-binding/near-indirect-v1/decode-attempt4.ml | `09bb6414a5eaaf151c2bd795b0746e1973fc1fe0b242cf6d4cfeedacacff93b1` |
| development/approved-plan/call-binding/near-indirect-v1/x86-attempt4.ml | `0e2a9f1076083ce76e3510471eff1bbfd3788af67d3b4b9ece43755fea42d31f` |
| development/approved-plan/abi-qualification/docs/intel-vol2a.pdf | `81a1c07beb20217956b23885193b68a104beaf72fcc85768d8da901991b71ec8` |

The logical decoder changes from the preserved REP RET overlay are confined to
FF/2 and FF/4 width normalization and accepting the 66 operand-size prefix for
those forms. Register targets use Full_64 and memory targets Quadword. The
normalizer preserves register identity and effective-address syntax; it does
not mention a client, PC, symbol or byte whitelist. Other FF forms retain the
old prefix rejection. Candidate 4's additional CPS numeric-equality and
boolean-disjunction handling returns kernel conversion theorems; it does not
supply an instruction-correctness axiom. The final public DECODE_CONV rewrite
must be included in actual-byte qualification, rather than trusting the private
converter's temporarily unnormalized result.

The pinned Intel Volume 2A CALL table and description (text lines 18138–18150
and 18218–18235, PDF pages 248–249) require a 64-bit near target in long mode,
loaded directly into RIP. The description specifies the source stack base
before execution for stack-relative indirect addressing. The near-absolute
pseudocode (text lines 18449–18464, PDF page 253) first saves the destination,
then pushes the next RIP and assigns that destination. The JMP FF/4 table
(text lines 45507–45533) identifies an absolute r/m64 target. These sources
support forced width even without REX.W and with the operand-size prefix.
The model's rejection of unsupported address/segment/REP forms is a declared
support boundary, not a supported no-op.

The executor captures the target and effective address in the postdecode source
state before any stack change. add_load_event only changes the event list.
Consequently RIP-relative addressing uses the advanced RIP, and CALL [RSP+disp]
uses the original source RSP rather than the decremented stack pointer. A
memory-indirect JMP produces an eight-byte load and sets RIP to the full loaded
word; register indirection produces no memory event. JMP preserves stack and
memory. CALL reuses x86_CALL's eight-byte store of postdecode RIP, decrement of
RSP and assignment of the captured target. Immediate CALL/JUMP cases remain
verbatim relative calculations, with their original event behavior.

There is an explicit observation convention to retain. The original x86_CALL
adds EventJump before invoking x86_PUSH, whose event is EventStore. Thus a
memory-indirect CALL's chronological model list is LOAD, JUMP, STORE; its
stored newest-first list is STORE, JUMP, LOAD. This is the original model's
within-instruction event enumeration, **not physical chronological CALL
ordering**. Intel pseudocode pushes before updating RIP. The event footprint
is complete and state effects are correct under the declared successful-step
model, but any future observation claim must identify this convention or use a
separately versioned justified event-order refinement. It has no effect on
accepted CRYPTO observations, whose reached instructions contain no CALL.

Before R1 acceptance:

1. Reconstruct generic memory/register CALL/JMP state and full-width event
   theorems, plus unconditional/conditional relative-case agreement, in a fresh
   model namespace. Include actual final FF25 stubs and variants with absent
   REX.W, REX extension, 66, RIP-relative and RSP-based addressing. Test invalid
   prefixes separately to confirm rejection remains explicit.
2. Independently test the exact reached forms under the declared amd64
   emulation/profile. Tests support qualification; they do not establish
   hardware or emulator fidelity. Preserve cold-load and proof failures and
   require exact live object audits with no added axioms.
3. Derive actual GOT pointer/target and page-permission binding from the frozen
   post-initialization declaration. Prove every eight-byte GOT load and CALL
   stack store/fetch safe at each reached successor, preserve caller input/code
   spans and establish alignment for the newly pushed callee slot. Account for
   target canonicality, stack nonwrap and disabled CET in the declared domain.
4. Extend the generic omitted-state scalar class separately for the documented
   CALL/JMP forms; V4's current class does not qualify CALL automatically. Prove
   reached-site coverage and an all-original-successor product lift. Physical
   effects remain explicit versioned ISA trust, not a ghost equality argument.
5. Replay the affected callee dependencies and final-linked caller compositions
   under the new model pin. Reuse exact public callee interfaces only after
   this model agreement/requalification; do not mix original and revised x86
   constants in one warm namespace. Qualify R1 controls 3/4 against the genuine
   positive package and run a closed fresh aggregate before updating R1 status.

The strongest objection to adopting the candidate now is that source review
alone does not qualify its larger architectural support domain, especially
prefix/addressing forms and CALL's model event convention. Adopt it as
separately frozen development only until those gates pass. No production
counterexample, complete caller proof, whole-core completion or human review is
claimed here.
