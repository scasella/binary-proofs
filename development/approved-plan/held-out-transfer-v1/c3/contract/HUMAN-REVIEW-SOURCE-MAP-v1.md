C3 human review remains PENDING. The following map supports review; hashes, parsing and agent inspection do not prove the caller or replace human review.

| Review question | Controlling source |
| --- | --- |
| Exact independently selected behavior and assembler authorship | `c3/artifact/c3.S`, `c3-selection/choice-freeze-v1.json`, `c3/contract/CONTRACT-v1.md` |
| Build identity and supplier byte binding | `c3/artifact/build-v1.sh`, `compiled-v1/compiler.txt`, `compiled-v1/assembler.txt`, `compiled-v1/supplier-binding.txt`, `artifact/freeze-v1.json` |
| Final caller bytes, actual CALL/PLT/GOT relationships and mapped image | `c3/artifact/inventory-v1.json`, `compiled-v1/{disassembly.txt,readelf.txt,gnu-v1}`, `c3/replay/acquisition-discovery-v1.json` |
| Initial versus current memory and overlap | `c3_equal`, `c3_cleansed_memory`, `c3_result`, `c3_scalar_post` in canonical `definitions-v2.ml` |
| Arbitrary contents/lengths and zero-length buffer premises | `c3_pre`, inherited `assurance_span_ok`, `c3_equal`, and `c3w_layout`; witness family does not restrict main precondition |
| Stack, code and GOT protection | `c3_pre`, `c3_scratch`, `c3_allowed_read/write/fetch`; 48-byte scratch includes the nested CALL slot |
| Actual final RET, finite checked progress and ABI frame | `c3_step_policy`, `c3_scalar_post`, `c3_frame`, `c3_checked_statement` |
| Omitted architectural state and E5 RF/TF normal entry | `c3_pre`, `c3_public_post`, the four normal/interface terms in `statements-v1.ml`, inherited E5 definitions |
| First supplier entry derived from real caller execution | `c3_saved_prefix`, `c3_crypto_ready`, `c3_handoff_statement` (an obligation, never an entry assumption) |
| Complete exact target registry | `expected-terms-v1.json`: seven end targets and three separate witness targets |
| Explicit admissible-entry construction data | `witness-definitions-v1.ml`, `witness-statements-v1.ml`; arbitrary external payload and both partial-overlap directions |
| Transfer boundary and permitted caller reasoning | Frozen `layer/CLASS-AND-EXTENSION-POINTS-v1.md`, layer freeze SHA-256 `266f58bbb1883389a74b8ba0986db11d0b0d6f4c03c1d3961d2db04f51d94193` |
| Selector exposure and failures | `c3-selection/preparation-record-v1.json`, `choice-freeze-v1.json`, and append-only `measurements/attempts-v1.jsonl` |

The new experiment is machine-level transfer for an assembler-authored caller assembled and linked by GCC. It does not establish C-language refinement or a result for compiler-generated C output. Clearing p is unconditional. The return keeps the initial equality result across cleanup and another compare, and then combines it with current-memory equality. q changes exactly where it overlaps p; the postcondition deliberately uses the cleared-memory snapshot there.

All new predicates and target terms are definition/specification obligations. No proof solution, reusable composition lemma, new generic automation, execution cache, assumed interface, or theorem object has been supplied by the selector. Source conventions for image predicates, frames, literal terms and explicit membership states came from the authorized old C2 definition/statement and build/extraction metadata only. The old caller proof solutions and supplier recipes were not inspected by the selector.

The v1 definition draft remains available. Canonical v2 adds intended int64 and memory-function types for unused q/m parameters in unconditional write/frame predicates, without changing their meaning. Any later parsing correction must preserve the earlier source and be recorded before final freeze. Any proof-driven domain reduction is prohibited. Final case freeze controls the construction clock and protected literal targets.
