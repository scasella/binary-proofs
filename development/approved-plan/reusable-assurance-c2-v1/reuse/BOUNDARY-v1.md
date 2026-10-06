C2 preconstruction reuse boundary
================================

The classification in `input-classification-v1.json` records exact source
digests. It is an inspection record, not a proof certificate. No C2 proof
construction or proof-checker invocation preceded this record.

The reusable mathematical layer is the accepted, parameterized checked-run
append, postcondition strengthening and policy widening rules, the
three-segment composition rule, the generic span/frame rules, and the E5
normal-entry/RF lifting rules. These rules contain neither C1 addresses nor
an instruction-offset case table. C2 initially attempts their unchanged use.

The supplier surface consists of the unchanged public preconditions,
postconditions, access policies, step counts and theorems
`BP_E3_CRYPTO_PUBLIC_CALLER_POLICY` and
`BP_E3_CLEANSE_PUBLIC_CALLER_POLICY`. Reconstruction of their source proof
chain is required at fresh acceptance. Caller construction may instantiate
these public theorems and their public definitions; it must not symbolically
execute supplier instruction arrays or import their implementation rules.

The original generic checked-step tactic accepts an actual caller execution
rule and a caller policy tactic. The C1 step adapter supplies fixed C1
addresses, argument positions, access-policy predicates and control-flow
facts. The adapter therefore is a C1 recipe, not generic infrastructure.
Likewise, C1 handoff/frame/application facts and C0 cleanse handoff facts
must not be imported as C2 facts. C2 must construct its own instantiations,
permissions, actual linkage steps, branch logic and memory/frame transports.

The address-free policy-inclusion propositions in the C1 application source
are mathematically general, but that source is not part of the pinned generic
loader. Reproving an implication locally for the named C2 supplier-application
obligation is a new proof helper. Promoting it into a new reusable export
would be a generic-layer adaptation and requires a separate version. This
stage must distinguish those actions instead of calling a copied recipe
unchanged generic infrastructure.

The anticipated end-to-end path is initial caller/CALL/PLT/GOT handoff;
public comparison application; result-dependent branch handoff; public
cleanse application only on the equality branch; branch-specific suffix and
actual RET; universal checked-run composition and E5 lift. Each additional
helper must name its obligation on that path. Entry witnesses and helper
audits cannot stand in for the frozen caller end-theorems.

Construction has prior exposure to C0/C1 supplier recipes and has inspected
the public supplier chain. This is not a never-read experiment or an isolated
economics baseline. Explicit source/tactic-input inspection and visible
automation-table comparisons do not provide a kernel derivation dependency
certificate or formal capability isolation. Supplier objects remain ambient
after source reconstruction. The prior inspection-based qualification stays
in force.

No generic modification has yet been made. Anticipated C2 caller-specific
bridges are not checked; their sufficiency remains an experimental question.
