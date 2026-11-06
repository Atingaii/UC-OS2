(* Independently handwritten expected contracts. These declarations do not
   derive their types from candidate theorem headers. Manual C mapping is
   checked separately; this is not a verified parser/frontend. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import Coq.Lists.List.
Local Open Scope nat_scope.

Definition expected_error_entry table old new p current reserved sr exit :=
  sseq
    (sseq (sifthen (eunop oppsite (ebinop oeq
      (earrayelem (evar table) (evar new)) (ecast enull (Tptr V293_tcb_type))))
      (sseq (scall exit (eaddrof (evar sr)::nil)) (srete (econst32 (Int.repr 40)))))
      (sseq (sifthen (ebinop oeq (ecast (evar old) Tint32) (econst32 (Int.repr 255)))
        (sassign (evar old) (efield (ederef (evar current)) 16%Z)))
        (sseq (sassign (evar p) (earrayelem (evar table) (evar old)))
          (sifthen (ebinop oeq (evar p) (ecast enull (Tptr V293_tcb_type)))
            (sseq (scall exit (eaddrof (evar sr)::nil)) (srete (econst32 (Int.repr 41))))))))
    (sifthen (ebinop oeq (evar p) (ecast (eaddrof (evar reserved)) (Tptr V293_tcb_type)))
      (sseq (scall exit (eaddrof (evar sr)::nil)) (srete (econst32 (Int.repr 67))))).

Definition checked_entry_syntax : forall table old new p current reserved sr exit,
  V293_task_prio_entry_reserved table old new p current reserved sr exit =
  expected_error_entry table old new p current reserved sr exit.
Proof. intros; reflexivity. Qed.

Definition checked_occupied :
  forall P ks ge le M table oldprio newprio ptcb current reserved cpu_sr exit_id
    b bn bs new next,
  new < 12 ->
  get le table = None -> get ge table = Some (b,Tarray (Tptr V293_tcb_type) 13) ->
  get le newprio = Some (bn,Tint8) ->
  load Tint8 M (bn,0%Z) = Some (V293_byteval new) ->
  load (Tptr V293_tcb_type) M (b,(4*Z.of_nat new)%Z) = Some (Vptr next) ->
  get le cpu_sr = Some (bs,Tint32) ->
  cstepstar P
    (curs (expected_error_entry table oldprio newprio ptcb current reserved cpu_sr exit_id),(kenil,ks)) (ge,le,M)
    (curs (sfexec exit_id (Vptr (bs,Int.zero)::nil) (Tptr Tint32::nil)),
      (kenil,kseq (srete (econst32 (Int.repr 40)))
        (kseq (sseq (V293_task_prio_self_read oldprio current)
          (sseq (V293_task_prio_lookup table oldprio ptcb)
            (sifthen (V293_task_prio_null_test (evar ptcb))
              (sseq (scall exit_id (eaddrof (evar cpu_sr)::nil)) (srete (econst32 (Int.repr 41)))))))
          (kseq (V293_task_prio_reserved_guard ptcb reserved cpu_sr exit_id) ks)))) (ge,le,M) :=
  V293_task_prio_occupied_entry_execution.

Definition checked_absent :
  forall P ks ge le M table oldprio newprio ptcb current reserved cpu_sr exit_id
    b bo bn bc bs bcur bct base old new curprio,
  old < 256 -> new < 12 ->
  let resolved := if old =? 255 then curprio else old in
  resolved < 13 ->
  get le table = None -> get ge table = Some (b,Tarray (Tptr V293_tcb_type) 13) ->
  get le oldprio = Some (bo,Tint8) -> get le newprio = Some (bn,Tint8) ->
  get le ptcb = Some (bc,Tptr V293_tcb_type) -> get le cpu_sr = Some (bs,Tint32) ->
  load Tint8 M (bo,0%Z) = Some (V293_byteval old) ->
  load Tint8 M (bn,0%Z) = Some (V293_byteval new) ->
  load (Tptr V293_tcb_type) M (b,(4*Z.of_nat new)%Z) = Some Vnull ->
  load (Tptr V293_tcb_type) M (b,(4*Z.of_nat resolved)%Z) = Some Vnull ->
  b <> bo -> b <> bc -> bo <> bn -> bc <> bn -> bc <> bo ->
  (old = 255 ->
    get le current = None /\ get ge current = Some (bcur,Tptr V293_tcb_type) /\
    load (Tptr V293_tcb_type) M (bcur,0%Z) = Some (Vptr (bct,Int.repr base)) /\
    (0 <= base)%Z /\ (base+50 <= Int.max_unsigned)%Z /\
    load Tint8 M (bct,(base+50)%Z) = Some (V293_byteval curprio) /\
    (exists v, get M (bo,0%Z) = Some (true,v))) ->
  V293_bytes_writable M bc 0%Z 4 ->
  exists Mf,
    cstepstar P (curs (expected_error_entry table oldprio newprio ptcb current reserved cpu_sr exit_id),(kenil,ks)) (ge,le,M)
      (curs (sfexec exit_id (Vptr (bs,Int.zero)::nil) (Tptr Tint32::nil)),
        (kenil,kseq (srete (econst32 (Int.repr 41)))
          (kseq (V293_task_prio_reserved_guard ptcb reserved cpu_sr exit_id) ks))) (ge,le,Mf) /\
    load Tint8 Mf (bo,0%Z) = Some (V293_byteval resolved) /\
    load Tint8 Mf (bn,0%Z) = Some (V293_byteval new) /\
    load (Tptr V293_tcb_type) Mf (bc,0%Z) = Some Vnull /\
    (forall i, i < 13 -> load (Tptr V293_tcb_type) Mf (b,(4*Z.of_nat i)%Z) = load (Tptr V293_tcb_type) M (b,(4*Z.of_nat i)%Z)) /\
    (forall c i, c <> bo -> c <> bc -> get Mf (c,i) = get M (c,i)) :=
  V293_task_prio_absent_entry_execution.

Definition checked_reserved :
  forall P ks ge le M table oldprio newprio ptcb current reserved cpu_sr exit_id
    b bo bn bc bs bcur bct base old new curprio br,
  old < 256 -> new < 12 ->
  let resolved := if old =? 255 then curprio else old in
  resolved < 13 ->
  get le table = None -> get ge table = Some (b,Tarray (Tptr V293_tcb_type) 13) ->
  get le oldprio = Some (bo,Tint8) -> get le newprio = Some (bn,Tint8) ->
  get le ptcb = Some (bc,Tptr V293_tcb_type) -> get le cpu_sr = Some (bs,Tint32) ->
  get le reserved = None -> get ge reserved = Some (br,Tint8) ->
  load Tint8 M (bo,0%Z) = Some (V293_byteval old) ->
  load Tint8 M (bn,0%Z) = Some (V293_byteval new) ->
  load (Tptr V293_tcb_type) M (b,(4*Z.of_nat new)%Z) = Some Vnull ->
  load (Tptr V293_tcb_type) M (b,(4*Z.of_nat resolved)%Z) = Some (Vptr (br,Int.zero)) ->
  b <> bo -> b <> bc -> bo <> bn -> bc <> bn -> bc <> bo ->
  (old = 255 ->
    get le current = None /\ get ge current = Some (bcur,Tptr V293_tcb_type) /\
    load (Tptr V293_tcb_type) M (bcur,0%Z) = Some (Vptr (bct,Int.repr base)) /\
    (0 <= base)%Z /\ (base+50 <= Int.max_unsigned)%Z /\
    load Tint8 M (bct,(base+50)%Z) = Some (V293_byteval curprio) /\
    (exists v, get M (bo,0%Z) = Some (true,v))) ->
  V293_bytes_writable M bc 0%Z 4 ->
  exists Mf,
    resolved <> new /\
    cstepstar P (curs (expected_error_entry table oldprio newprio ptcb current reserved cpu_sr exit_id),(kenil,ks)) (ge,le,M)
      (curs (sfexec exit_id (Vptr (bs,Int.zero)::nil) (Tptr Tint32::nil)),
        (kenil,kseq (srete (econst32 (Int.repr 67))) ks)) (ge,le,Mf) /\
    load Tint8 Mf (bo,0%Z) = Some (V293_byteval resolved) /\
    load Tint8 Mf (bn,0%Z) = Some (V293_byteval new) /\
    load (Tptr V293_tcb_type) Mf (bc,0%Z) = Some (Vptr (br,Int.zero)) /\
    load (Tptr V293_tcb_type) Mf (b,(4*Z.of_nat resolved)%Z) = Some (Vptr (br,Int.zero)) /\
    load (Tptr V293_tcb_type) Mf (b,(4*Z.of_nat new)%Z) = Some Vnull /\
    (forall c i, c <> bo -> c <> bc -> get Mf (c,i) = get M (c,i)) :=
  V293_task_prio_reserved_entry_error_execution.

(* Also check the actual instantiated roots; no claim that their fixture is
   a full allocated/shared/init-reachable OS state. *)
Print Assumptions checked_entry_syntax.
Print Assumptions checked_occupied.
Print Assumptions checked_absent.
Print Assumptions checked_reserved.
Print Assumptions V293_task_prio_absent_same_slot_witness.
Print Assumptions V293_task_prio_reserved_error_witness.
Print Assumptions V293_task_prio_occupied_error_witness.
