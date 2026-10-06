# E2 preserved specification archive

The immutable PROMPT.md and original spec/CONTRACTS.md remain the requirements.
These files are byte-identical archives of the separately frozen pre-search
development statements, now indexed under spec/. This indexing occurred after
construction; their original freeze records supply the actual dates/hashes.
Human review is PENDING. Agent review is not human approval.

CRYPTO_memcmp retains arbitrary input bytes, every machine-representable length
whose exact regions satisfy the explicit permissions/canonical/nonwrap clauses,
misalignment, identical pointers and partial overlaps. Zero length has no buffer
access or buffer-permission premise. Initial ABI/register placement, DF/AC,
actual nonempty RET completion, protected return slot and restored stack are
explicit. The result is initial unsigned-byte equality, without ordering claims.
All accesses are checked over the original machine transitions, independently
of flat model memory. No memory write is permitted. The frame preserves all
callee-saved state, including the separately versioned14-field ABI extension.

The fixed post-initialization whole libcrypto image uses bias0x10000000 and public
entry0x10241840. Three initially nonwritable load segments match the full raw
ELF byte map. The original writable segment (including RELRO and BSS after
initialization) and page padding are explicit stable maps. They contain no
assumption of target behavior. Loader execution, physical ISA correspondence
and actual permission enforcement remain separately declared boundaries.

The architectural observer records every instruction PC/decoded length/opcode,
branch/control observation and each data address/full width/read-write kind,
through the first actual RET. Secret loaded/stored values and returned equality
are excluded. The relational statement has no equality-result, mismatch-position
or trace-length premise, and includes every allowed nondeterministic choice.
It makes no elapsed-time, speculation or microarchitectural claim.

No definition here accepts O1, the core or either entire library by itself.
