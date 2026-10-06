(* Diagnostic-only exact-tactic core instrumentation. No theorem export. *)
let C3_SECOND_CORE_CAPTURE_TAC label tac goal =
 print_endline ("C3_SECOND_CORE_BEFORE " ^ label);
 print_goal goal;
 try
  let result=tac goal in
  let _,goals,_=result in
  print_endline ("C3_SECOND_CORE_AFTER " ^ label ^ " " ^ string_of_int(length goals));
  List.iter print_goal goals;
  result
 with ex ->
  print_endline ("C3_SECOND_CORE_EXCEPTION " ^ label ^ " " ^ Printexc.to_string ex);
  print_goal goal;
  raise ex;;
let C3_SECOND_ENDPOINT_CORE_DIAGNOSTIC_TAC =
 C3_SECOND_CORE_CAPTURE_TAC "01-subgoal_then"
 (SUBGOAL_THEN `(MAYCHANGE[RIP;RSP;RDX;RSI;RDI] ,, MAYCHANGE SOME_FLAGS ,, MAYCHANGE[memory :> bytes(word_sub(stackpointer:int64)(word 48),8)] ,, MAYCHANGE[events])(returned:x86state)(v5:x86state)` ASSUME_TAC THENL
 [MATCH_MP_TAC(REWRITE_RULE[subsumed](SPEC `stackpointer:int64`C3_SECOND_CONCRETE_FRAME_INCLUDED)) THEN ASM_REWRITE_TAC[];ALL_TAC]) THEN
 C3_SECOND_CORE_CAPTURE_TAC "02-subgoal_then"
 (SUBGOAL_THEN `(MAYCHANGE[RIP;RSP;RDX;RSI;RDI] ,, MAYCHANGE SOME_FLAGS ,, MAYCHANGE[memory :> bytes(word_sub(stackpointer:int64)(word 48),48)] ,, MAYCHANGE[events])(returned:x86state)(v5:x86state)` ASSUME_TAC THENL
 [MATCH_MP_TAC(REWRITE_RULE[subsumed](SPEC `stackpointer:int64`C3_SECOND_FRAME_WIDE_INCLUDED)) THEN ASM_REWRITE_TAC[];ALL_TAC]) THEN
 C3_SECOND_CORE_CAPTURE_TAC "03-mp_tac(ispecl[`lib_file:num->byte`;`lib_rw:int64->byte`;`lib_padding:int64->byte`;`client_file:num->byte`;`client_rw:int64->byte`;`client_padding:int64->byte`;`stackpointer:int64`;`ra:int64`;`p:int64`;`q:int64`;`n:num`;`m:int64->byte`;`rp:num->bool`;`wp:num->bool`;`xp:num->bool`;`ordinary:num->bool`;`initial:x86state`;`a:abi_omitted_state`;`entry:x86state`;`returned:x86state`]c3_cleanse_saved_bindings)"
 (MP_TAC(ISPECL[`lib_file:num->byte`;`lib_rw:int64->byte`;`lib_padding:int64->byte`;`client_file:num->byte`;`client_rw:int64->byte`;`client_padding:int64->byte`;`stackpointer:int64`;`ra:int64`;`p:int64`;`q:int64`;`n:num`;`m:int64->byte`;`rp:num->bool`;`wp:num->bool`;`xp:num->bool`;`ordinary:num->bool`;`initial:x86state`;`a:abi_omitted_state`;`entry:x86state`;`returned:x86state`]C3_CLEANSE_SAVED_BINDINGS)) THEN
 C3_SECOND_CORE_CAPTURE_TAC "04-asm_rewrite_tac[]"
 (ASM_REWRITE_TAC[]) THEN
 C3_SECOND_CORE_CAPTURE_TAC "05-strip_tac"
 (STRIP_TAC) THEN
 C3_SECOND_CORE_CAPTURE_TAC "06-mp_tac(ispecl[`stackpointer:int64`;`returned:x86state`;`v5:x86state`]c3_second_frame_saved)"
 (MP_TAC(ISPECL[`stackpointer:int64`;`returned:x86state`;`v5:x86state`]C3_SECOND_FRAME_SAVED)) THEN
 C3_SECOND_CORE_CAPTURE_TAC "07-asm_rewrite_tac[]"
 (ASM_REWRITE_TAC[]) THEN
 C3_SECOND_CORE_CAPTURE_TAC "08-strip_tac"
 (STRIP_TAC) THEN
 C3_SECOND_CORE_CAPTURE_TAC "09-mp_tac(ispecl[`stackpointer:int64`;`p:int64`;`q:int64`;`n:num`;`m:int64->byte`;`\a:num."
 (MP_TAC(ISPECL[`stackpointer:int64`;`p:int64`;`q:int64`;`n:num`;`m:int64->byte`;`\a:num. rp a /\ ordinary a`;`initial:x86state`;`entry:x86state`;`returned:x86state`]C3_CLEANSE_CURRENT_INPUTS)) THEN
 C3_SECOND_CORE_CAPTURE_TAC "10-asm_rewrite_tac[]"
 (ASM_REWRITE_TAC[]) THEN
 C3_SECOND_CORE_CAPTURE_TAC "11-strip_tac"
 (STRIP_TAC) THEN
 C3_SECOND_CORE_CAPTURE_TAC "12-mp_tac(ispecl[`lib_file:num->byte`;`stackpointer:int64`;`p:int64`;`q:int64`;`n:num`;`m:int64->byte`;`rp:num->bool`;`wp:num->bool`;`xp:num->bool`;`ordinary:num->bool`;`initial:x86state`;`a:abi_omitted_state`;`entry:x86state`;`returned:x86state`]c3_cleanse_return_working_state)"
 (MP_TAC(ISPECL[`lib_file:num->byte`;`stackpointer:int64`;`p:int64`;`q:int64`;`n:num`;`m:int64->byte`;`rp:num->bool`;`wp:num->bool`;`xp:num->bool`;`ordinary:num->bool`;`initial:x86state`;`a:abi_omitted_state`;`entry:x86state`;`returned:x86state`]C3_CLEANSE_RETURN_WORKING_STATE)) THEN
 C3_SECOND_CORE_CAPTURE_TAC "13-asm_rewrite_tac[]"
 (ASM_REWRITE_TAC[]) THEN
 C3_SECOND_CORE_CAPTURE_TAC "14-strip_tac"
 (STRIP_TAC) THEN
 C3_SECOND_CORE_CAPTURE_TAC "15-mp_tac(ispecl[`stackpointer:int64`;`returned:x86state`;`v5:x86state`]c3_second_frame_outside)"
 (MP_TAC(ISPECL[`stackpointer:int64`;`returned:x86state`;`v5:x86state`]C3_SECOND_FRAME_OUTSIDE)) THEN
 C3_SECOND_CORE_CAPTURE_TAC "16-asm_rewrite_tac[]"
 (ASM_REWRITE_TAC[]) THEN
 C3_SECOND_CORE_CAPTURE_TAC "17-strip_tac"
 (STRIP_TAC) THEN
 C3_SECOND_CORE_CAPTURE_TAC "18-subgoal_then"
 (SUBGOAL_THEN `!addr:int64. ~c3_scratch stackpointer(val addr) ==> read memory(v5:x86state)addr=read memory(returned:x86state)addr` ASSUME_TAC THENL
 [REPEAT STRIP_TAC THEN MATCH_MP_TAC(ISPECL[`stackpointer:int64`;`addr:int64`;`returned:x86state`;`v5:x86state`]C3_SECOND_FRAME_WIDE_BYTE) THEN ASM_REWRITE_TAC[];ALL_TAC]) THEN
 C3_SECOND_CORE_CAPTURE_TAC "19-subgoal_then"
 (SUBGOAL_THEN `!i. i<n ==> read memory(v5:x86state)(word_add p(word i))=read memory(returned:x86state)(word_add p(word i))` ASSUME_TAC THENL
 [MATCH_MP_TAC(ISPECL[`\a:num. rp a /\ ordinary a`;`p:int64`;`n:num`;`stackpointer:int64`;`read memory(returned:x86state)`;`v5:x86state`]C3_PREFIX_INPUT_MEMORY) THEN ASM_REWRITE_TAC[];ALL_TAC]) THEN
 C3_SECOND_CORE_CAPTURE_TAC "20-subgoal_then"
 (SUBGOAL_THEN `!i. i<n ==> read memory(v5:x86state)(word_add q(word i))=read memory(returned:x86state)(word_add q(word i))` ASSUME_TAC THENL
 [MATCH_MP_TAC(ISPECL[`\a:num. rp a /\ ordinary a`;`q:int64`;`n:num`;`stackpointer:int64`;`read memory(returned:x86state)`;`v5:x86state`]C3_PREFIX_INPUT_MEMORY) THEN ASM_REWRITE_TAC[];ALL_TAC]) THEN
 C3_SECOND_CORE_CAPTURE_TAC "21-subgoal_then"
 (SUBGOAL_THEN `!i. i<n ==> read memory(v5:x86state)(word_add p(word i))=word 0` ASSUME_TAC THENL
 [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
 (let current=MATCH_MP(SPEC `i:num`(ASSUME `!i. i<n ==> read memory(v5:x86state)(word_add p(word i))=read memory(returned:x86state)(word_add p(word i))`))(ASSUME `i<n`) in
 let zero=MATCH_MP(SPEC `i:num`(ASSUME `!i. i<n ==> read memory(returned:x86state)(word_add p(word i))=word 0`))(ASSUME `i<n`) in
 ACCEPT_TAC(TRANS current zero));ALL_TAC]) THEN
 C3_SECOND_CORE_CAPTURE_TAC "22-subgoal_then"
 (SUBGOAL_THEN `!i. i<n ==> read memory(v5:x86state)(word_add q(word i))=c3_cleansed_memory m p n(word_add q(word i))` ASSUME_TAC THENL
 [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
 (let current=MATCH_MP(SPEC `i:num`(ASSUME `!i. i<n ==> read memory(v5:x86state)(word_add q(word i))=read memory(returned:x86state)(word_add q(word i))`))(ASSUME `i<n`) in
 let cleansed=MATCH_MP(SPEC `i:num`(ASSUME `!i. i<n ==> read memory(returned:x86state)(word_add q(word i))=c3_cleansed_memory m p n(word_add q(word i))`))(ASSUME `i<n`) in
 ACCEPT_TAC(TRANS current cleansed));ALL_TAC]) THEN
 C3_SECOND_CORE_CAPTURE_TAC "23-subgoal_then"
 (SUBGOAL_THEN `!addr:int64. ~(assurance_region p n(val addr) \/ c3_scratch stackpointer(val addr)) ==> read memory(v5:x86state)addr=m addr` ASSUME_TAC THENL
 [X_GEN_TAC `addr:int64` THEN DISCH_TAC THEN
 (let outside=ASSUME `~(assurance_region p n(val(addr:int64)) \/ c3_scratch stackpointer(val addr))` in
 let nonscratch=CONJUNCT2(REWRITE_RULE[DE_MORGAN_THM]outside) in
 let current=MATCH_MP(SPEC `addr:int64`(ASSUME `!addr:int64. ~c3_scratch stackpointer(val addr) ==> read memory(v5:x86state)addr=read memory(returned:x86state)addr`))nonscratch in
 let original=MATCH_MP(SPEC `addr:int64`(ASSUME `!addr:int64. ~(assurance_region p n(val addr) \/ c3_scratch stackpointer(val addr)) ==> read memory(returned:x86state)addr=m addr`))outside in
 ACCEPT_TAC(TRANS current original));ALL_TAC]) THEN
 C3_SECOND_CORE_CAPTURE_TAC "24-subgoal_then"
 (SUBGOAL_THEN `!addr. fb_immutable addr ==> ~c3_scratch stackpointer addr` ASSUME_TAC THENL
 [MATCH_MP_TAC(ISPECL[`stackpointer:int64`;`wp:num->bool`;`ordinary:num->bool`]C3_PREFIX_LIBRARY_SCRATCH_DISJOINT) THEN ASM_REWRITE_TAC[] THEN
 X_GEN_TAC `addr:num` THEN DISCH_TAC THEN
 MP_TAC(MATCH_MP(SPEC `addr:num`(ASSUME `!addr. lw_image_domain addr ==> rp addr /\ ordinary addr /\ (xp addr <=> lw_execute addr) /\ (wp addr <=> lw_image_write addr)`))(ASSUME `lw_image_domain(addr:num)`)) THEN MESON_TAC[];ALL_TAC]) THEN
 C3_SECOND_CORE_CAPTURE_TAC "25-mp_tac(ispecl[`lib_file:num->byte`;`stackpointer:int64`;`p:int64`;`n:num`;`rp:num->bool`;`wp:num->bool`;`xp:num->bool`;`ordinary:num->bool`;`entry:x86state`;`a:abi_omitted_state`;`returned:x86state`]c3_cleanse_library_image)"
 (MP_TAC(ISPECL[`lib_file:num->byte`;`stackpointer:int64`;`p:int64`;`n:num`;`rp:num->bool`;`wp:num->bool`;`xp:num->bool`;`ordinary:num->bool`;`entry:x86state`;`a:abi_omitted_state`;`returned:x86state`]C3_CLEANSE_LIBRARY_IMAGE)) THEN
 C3_SECOND_CORE_CAPTURE_TAC "26-asm_rewrite_tac[]"
 (ASM_REWRITE_TAC[]) THEN
 C3_SECOND_CORE_CAPTURE_TAC "27-disch_tac"
 (DISCH_TAC) THEN
 C3_SECOND_CORE_CAPTURE_TAC "28-subgoal_then"
 (SUBGOAL_THEN `fb_full_image lib_file(read memory(v5:x86state))(read memory v5)(read memory v5)` ASSUME_TAC THENL
 [MATCH_MP_TAC(ISPECL[`lib_file:num->byte`;`read memory(returned:x86state)`;`read memory(returned:x86state)`;`stackpointer:int64`;`read memory(returned:x86state)`;`v5:x86state`]C3_PREFIX_IMAGE_REBIND) THEN ASM_REWRITE_TAC[];ALL_TAC]) THEN
 C3_SECOND_CORE_CAPTURE_TAC "29-mp_tac(match_mp(spec"
 (MP_TAC(MATCH_MP(SPEC `stackpointer:int64`C3_STACK_ALIGNMENT)(CONJ(ASSUME `48<=val(stackpointer:int64)`)(ASSUME `val(stackpointer:int64) MOD 16=8`)))) THEN
 C3_SECOND_CORE_CAPTURE_TAC "30-strip_tac"
 (STRIP_TAC) THEN
 C3_SECOND_CORE_CAPTURE_TAC "31-mp_tac(ispecl[`stackpointer:int64`]c3_prefix_crypto_region_disjoint)"
 (MP_TAC(ISPECL[`stackpointer:int64`]C3_PREFIX_CRYPTO_REGION_DISJOINT)) THEN
 C3_SECOND_CORE_CAPTURE_TAC "32-asm_rewrite_tac[]"
 (ASM_REWRITE_TAC[]) THEN
 C3_SECOND_CORE_CAPTURE_TAC "33-disch_tac"
 (DISCH_TAC) THEN
 C3_SECOND_CORE_CAPTURE_TAC "34-mp_tac(ispecl[`stackpointer:int64`]c3_prefix_slot_crypto_disjoint)"
 (MP_TAC(ISPECL[`stackpointer:int64`]C3_PREFIX_SLOT_CRYPTO_DISJOINT)) THEN
 C3_SECOND_CORE_CAPTURE_TAC "35-asm_rewrite_tac[]"
 (ASM_REWRITE_TAC[]) THEN
 C3_SECOND_CORE_CAPTURE_TAC "36-disch_tac"
 (DISCH_TAC);;
