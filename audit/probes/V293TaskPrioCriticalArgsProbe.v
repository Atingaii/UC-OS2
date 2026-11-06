(* Handwritten expected interfaces and full error-call syntax.
   Not generated from candidate headers; not a verified C frontend. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import Coq.Lists.List.

Definition expected_error (cpu_sr : var) (exit_id : fid) n :=
  sseq (scall exit_id (eaddrof (evar cpu_sr) :: nil)) (srete (econst32 (Int.repr n))).

Definition checked_call_syntax : forall table oldprio newprio ptcb current cpu_sr exit_id,
  V293_task_prio_entry_lookup table oldprio newprio ptcb current cpu_sr exit_id =
  sseq (sifthen (eunop oppsite (ebinop oeq
    (earrayelem (evar table) (evar newprio)) (ecast enull (Tptr V293_tcb_type))))
    (expected_error cpu_sr exit_id 40))
    (sseq (sifthen (ebinop oeq (ecast (evar oldprio) Tint32) (econst32 (Int.repr 255)))
      (sassign (evar oldprio) (efield (ederef (evar current)) 16%Z)))
      (sseq (sassign (evar ptcb) (earrayelem (evar table) (evar oldprio)))
        (sifthen (ebinop oeq (evar ptcb) (ecast enull (Tptr V293_tcb_type)))
          (expected_error cpu_sr exit_id 41)))) /\
  V293_task_prio_reserved_error cpu_sr exit_id = expected_error cpu_sr exit_id 67.
Proof. intros. split; reflexivity. Qed.

Definition checked_argument_eval : forall ge le M sr b,
  get le sr = Some (b,Tint32) ->
  evaltype (eaddrof (evar sr)) (ge,le,M) = Some (Tptr Tint32) /\
  evalval (eaddrof (evar sr)) (ge,le,M) = Some (Vptr (b,Int.zero)) :=
  V293_cpu_sr_address_eval.

Definition checked_error_execution : forall P ks ge le M sr exit b n,
  get le sr = Some (b,Tint32) ->
  cstepstar P (curs (expected_error sr exit n),(kenil,ks)) (ge,le,M)
    (curs (sfexec exit (Vptr (b,Int.zero) :: nil) (Tptr Tint32 :: nil)),
      (kenil,kseq (srete (econst32 (Int.repr n))) ks)) (ge,le,M) :=
  V293_task_prio_error_call_execution.

Definition checked_actual_branches :
  forall P ks ge le M table old new p cur sr exit b,
  get le sr = Some (b,Tint32) ->
  exists busy absent,
    V293_task_prio_entry_lookup table old new p cur sr exit =
      sseq (sifthen (eunop oppsite (ebinop oeq
        (earrayelem (evar table) (evar new)) (ecast enull (Tptr V293_tcb_type)))) busy)
        (sseq (sifthen (ebinop oeq (ecast (evar old) Tint32) (econst32 (Int.repr 255)))
          (sassign (evar old) (efield (ederef (evar cur)) 16%Z)))
          (sseq (sassign (evar p) (earrayelem (evar table) (evar old)))
            (sifthen (ebinop oeq (evar p) (ecast enull (Tptr V293_tcb_type))) absent))) /\
    cstepstar P (curs busy,(kenil,ks)) (ge,le,M)
      (curs (sfexec exit (Vptr (b,Int.zero) :: nil) (Tptr Tint32 :: nil)),
        (kenil,kseq (srete (econst32 (Int.repr 40))) ks)) (ge,le,M) /\
    cstepstar P (curs absent,(kenil,ks)) (ge,le,M)
      (curs (sfexec exit (Vptr (b,Int.zero) :: nil) (Tptr Tint32 :: nil)),
        (kenil,kseq (srete (econst32 (Int.repr 41))) ks)) (ge,le,M) /\
    cstepstar P (curs (V293_task_prio_reserved_error sr exit),(kenil,ks)) (ge,le,M)
      (curs (sfexec exit (Vptr (b,Int.zero) :: nil) (Tptr Tint32 :: nil)),
        (kenil,kseq (srete (econst32 (Int.repr 67))) ks)) (ge,le,M) :=
  V293_task_prio_error_exit_arguments.

Definition checked_unreadable :
  let le : env := set emp 601%Z (61%positive,Tint32) in
  evalval (evar 601%Z) (emp,le,emp) = None /\
  evaltype (evar 601%Z) (emp,le,emp) = Some Tint32 /\
  evalval (eaddrof (evar 601%Z)) (emp,le,emp) = Some (Vptr (61%positive,Int.zero)) /\
  evaltype (eaddrof (evar 601%Z)) (emp,le,emp) = Some (Tptr Tint32) /\
  forall P ks,
    cstepstar P (curs (V293_task_prio_reserved_error 601%Z 602%Z),(kenil,ks)) (emp,le,emp)
      (curs (sfexec 602%Z (Vptr (61%positive,Int.zero) :: nil) (Tptr Tint32 :: nil)),
        (kenil,kseq (srete (econst32 (Int.repr 67))) ks)) (emp,le,emp) :=
  V293_cpu_sr_unreadable_witness.

Print Assumptions checked_call_syntax.
Print Assumptions checked_argument_eval.
Print Assumptions checked_error_execution.
Print Assumptions checked_actual_branches.
Print Assumptions checked_unreadable.
