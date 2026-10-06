(* Supplier-only namespace: load after opaque-callee-loader-v3.ml.
   This source deliberately loads no former caller proof or public E5 wrapper.
   Supplier internals remain in the shared top-level; see README-v1.md. *)
if can get_const_type "e5_normal_flags" then
 failwith "RA_GENERIC_REQUIRES_SUPPLIER_ONLY_NAMESPACE_WITHOUT_E5_CONSTANTS";;
let ra_generic_initial_axioms = axioms();;
if ra_generic_initial_axioms <> [INFINITY_AX;SELECT_AX;ETA_AX] then
 failwith "RA_GENERIC_REQUIRES_STANDARD3_AXIOMS";;
needs "/reuse/generic/checked-run-statements-v1.ml";;
needs "/reuse/generic/checked-run-proof-v1.ml";;
needs "/reuse/generic/e5-definitions-v1.ml";;
needs "/reuse/generic/e5-statements-v1.ml";;
needs "/reuse/generic/e5-rf-elementary-v1.ml";;
needs "/reuse/generic/e5-scalar-flags-v1.ml";;
needs "/reuse/generic/e5-qualified-step-v1.ml";;
needs "/reuse/generic/e5-normal-run-v1.ml";;
needs "/reuse/generic/composition-statements-v2.ml";;
needs "/reuse/generic/composition-proof-attempt2.ml";;
needs "/reuse/generic/audit-v1.ml";;
