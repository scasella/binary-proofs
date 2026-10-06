(* Only existing generic span/frame sources from the sealed baseline. *)
needs "/work/development/approved-plan/clients-e3/secret-v1/generic-span-statements-v1.ml";;
needs "/work/development/approved-plan/clients-e3/secret-v1/generic-span-proof-attempt3.ml";;
needs "/work/development/approved-plan/clients-e3/secret-v1/generic-four-frame-statements-v1.ml";;
needs "/work/development/approved-plan/clients-e3/secret-v1/generic-four-frame-proof-attempt1.ml";;
List.iter (fun (name,th,expected) ->
 if hyp th <> [] || frees(concl th) <> [] || not(aconv (concl th) expected)
 then failwith ("RA_GENERIC_SPAN_FRAME_LITERAL:" ^ name))
 [ ("R1_SECRET_SPAN_MONO", R1_SECRET_SPAN_MONO, r1_secret_span_mono_statement);
   ("R1_SECRET_SPAN_SUBSPAN", R1_SECRET_SPAN_SUBSPAN, r1_secret_span_subspan_statement);
   ("R1_SECRET_SPAN_REGION", R1_SECRET_SPAN_REGION, r1_secret_span_region_statement);
   ("R1_SECRET_FOUR_FRAME_PRESERVATION", R1_SECRET_FOUR_FRAME_PRESERVATION,
      bp_public_four_frame_preservation_statement) ];;
if axioms() <> [INFINITY_AX;SELECT_AX;ETA_AX] then
 failwith "RA_GENERIC_SPAN_FRAME_AXIOMS_CHANGED";;
print_endline "RA_GENERIC_SPAN_FRAME_SOURCE_LITERAL_AUDIT_COMPLETE";;
