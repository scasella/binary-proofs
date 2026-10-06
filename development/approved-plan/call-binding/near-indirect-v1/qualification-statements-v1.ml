(* Model qualification only; no target routine/client contract. *)
let R1_NEAR_JMP_MEMORY_STATEMENT =
 `!ea (s:x86state).
    x86_execute (JMP (Memop Quadword ea)) s =
    (let target = read (memory :> bytes64 (bsid_semantics ea s)) s in
     (events := CONS (EventJump(read RIP s,target))
                 (CONS (EventLoad(bsid_semantics ea s,8)) (read events s)) ,,
      RIP := target) s)`;;
let R1_NEAR_CALL_MEMORY_STATEMENT =
 `!ea (s:x86state).
    x86_execute (CALL (Memop Quadword ea)) s =
    (let target = read (memory :> bytes64 (bsid_semantics ea s)) s in
     (events := CONS (EventLoad(bsid_semantics ea s,8)) (read events s) ,,
      x86_CALL target) s)`;;
let R1_RELATIVE_CALL_UNCHANGED_STATEMENT =
 `!off (s:x86state).
    ~r1_indirect_operand off
    ==> x86_execute (CALL off) s =
        (let target = word_add (read RIP s) (read (OPERAND64 off s) s) in
         x86_CALL target s)`;;
let R1_RELATIVE_JUMP_UNCHANGED_STATEMENT =
 `!cc off (s:x86state).
    ~(cc = Unconditional /\ r1_indirect_operand off)
    ==> x86_execute (JUMP cc off) s =
        (events := CONS
          (EventJump(read RIP s,
           if condition_semantics cc s then
             word_add (read RIP s) (read (OPERAND64 off s) s)
           else read RIP s)) (read events s) ,,
         RIP := if condition_semantics cc s then
                  word_add (read RIP s) (read (OPERAND64 off s) s)
                else read RIP s) s`;;
