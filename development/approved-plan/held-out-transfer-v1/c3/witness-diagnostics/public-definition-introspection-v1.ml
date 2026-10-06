(* Diagnostics only: no goals, no proof construction, no caller execution. *)
List.iter (fun (n,t) -> print_endline n; print_thm t; print_newline ())
 ["assurance_span_ok",assurance_span_ok;
  "assurance_region",assurance_region;
  "assurance_canonical48",assurance_canonical48;
  "fb_immutable",fb_immutable;
  "fb_full_image",fb_full_image;
  "fb_reference_image",fb_reference_image;
  "fb_file_code",fb_file_code;
  "clw_file_code",clw_file_code;
  "lw_image_domain",lw_image_domain;
  "lw_execute",lw_execute;
  "lw_image_write",lw_image_write;
  "fb_initial_abi",fb_initial_abi];;
print_endline "C3W_PUBLIC_DEFINITION_INTROSPECTION_V1_COMPLETE";;
