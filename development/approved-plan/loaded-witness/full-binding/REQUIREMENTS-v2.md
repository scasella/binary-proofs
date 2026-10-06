# Full image and V4 machine-prestate witness binding V2

Human review **PENDING**. This additive candidate preserves all predecessor
definitions, statements and proof freezes. Its frozen sources are definitions
and statements, with proof recipes separately versioned.

The quantified `file_bytes : num -> byte` denotes the **entire final ELF**
`artifacts/baseline/libcrypto.so.3`, whose SHA-256 is
`76dd3d93e5ee48950a92a58d59b94de8143847f91a80d9682c938767b991577d`.
Its external interpretation maps offsets below the file length to the acquired
byte, and other offsets to zero. The acquisition program checks the digest,
all PT_LOAD headers against the frozen declaration, segment-byte digests and
the exact 95-byte final symbol slice. The parser and interpretation of this
external file map are trusted; there is no theorem that HOL implements ELF
loading or SHA-256. A digest alone is never described as a loading proof.

`fb_full_image` fixes every address in all declared PT_LOAD pages
`[0x10000000,0x1048a000)`. The three initially nonwritable file intervals are
`[0x10000000,0x100c4bd0)`, `[0x100c5000,0x103434c9)`, and
`[0x10344000,0x10421a40)`; each source offset is address minus `0x10000000`.
The fourth segment's mathematical memory interval
`[0x10422e50,0x104895b0)` agrees with a separately supplied public initialized
RW map. This includes relocated file bytes, subsequently RELRO addresses and
initialized BSS. It does not require those bytes to equal raw ELF bytes.
All remaining mapped page padding agrees with an explicit stable public map.
These functions are unconstrained by target behavior.

The deterministic reference construction satisfies exactly this predicate.
File-slice agreement implies actual code-address agreement at `0x10241840`.
The inherited disjoint user overlays preserve the whole predicate, yielding
concrete machine-state pairs for empty, equal, unequal, misaligned,
identical-pointer, overlapping, sixteen-byte, canonical endpoint and ordinary
page-boundary cases. Equal and unequal cases include unsigned bytes 128/255.
Every empty pointer bit pattern is included. Canonical endpoint cases remain
abstract model witnesses; ordinary user-space mapping is not claimed for the
highest addresses.

The initial V4 ABI record has CW `0x37f`, SW zero, full empty tag `0xffff`,
FOP/IP/DP/FCS/FDS zero, eight zero x87 physical data registers, MXCSR `0x1f80`,
FS selector zero and canonical FS base `0x500000`, GS selector/base zero.
The TLS page `[0x500000,0x501000)` is readable ordinary memory. Its presence is
an explicit permission-map clause. Record equations are proved from the
constructor; no preservation, target correctness or opaque valid-state
predicate is assumed. All four endpoint theorems instantiate the same scalar
Pre and the same product-machine semantics already used by V4 qualification.

Logical satisfiability is conditional on exact frozen file-slice agreement,
whose external acquisition check binds it to the complete acquired file.
Physical processor fidelity, loader relocation/initialization, Linux TLS
allocation, page-table enforcement, startup/configuration and concurrent
stability remain the declared environmental and semantic trust boundary.
No routine milestone is accepted by the witness component alone.

V2 preserves the unparseable V1 prestate term and corrects its extra closing
parenthesis before further proof search. Other semantic clauses are identical.
