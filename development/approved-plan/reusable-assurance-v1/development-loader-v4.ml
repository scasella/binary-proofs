(* Selected checked source closure. Supplier bodies are reconstructed by the
   root checker; caller source applies exported interfaces only. *)
needs "/reuse/development-loader-v2.ml";;
needs "/reuse/c1/continuation/frame-widen-v1.ml";;
needs "/reuse/c1/continuation/step-adapter-v1.ml";;
needs "/reuse/c1/continuation/tail-definitions-v1.ml";;
needs "/reuse/c1/continuation/tail-statement-v1.ml";;
needs "/reuse/c1/continuation/rsp-value-statement-v1.ml";;
needs "/reuse/c1/continuation/rsp-value-proof-attempt1.ml";;
needs "/reuse/c1/continuation/tail-proof-attempt10.ml";;
needs "/reuse/c1/continuation/audit-tail-v1.ml";;
needs "/reuse/c1/handoff/slot-disjoint-statements-v1.ml";;
needs "/reuse/c1/handoff/slot-disjoint-proof-attempt1.ml";;
needs "/reuse/c1/handoff/slot-disjoint-audit-v1.ml";;
needs "/reuse/c1/handoff/proof-attempt11.ml";;
needs "/reuse/c1/handoff/audit-v2.ml";;
print_endline "C1_DEVELOPMENT_PREFIX_AND_SUFFIX_RECONSTRUCTED";;
