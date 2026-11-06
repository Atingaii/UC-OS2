(* Handwritten literal interfaces, NOT generated from candidate headers.
   The macro mapping is explicit and erases CPU_SR memory operations. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import Coq.Lists.List.
Local Open Scope nat_scope.

Definition expected_critical_prefix table oldprio newprio ptcb current reserved :=
  sseq (V293_task_prio_argument_guards oldprio newprio)
    (sseq (sprim encrit)
      (sseq
        (sseq
          (sifthen (eunop oppsite (V293_task_prio_null_test
            (earrayelem (evar table) (evar newprio))))
            (sseq (sprim excrit) (srete (econst32 (Int.repr 40)))))
          (sseq (V293_task_prio_self_read oldprio current)
            (sseq (V293_task_prio_lookup table oldprio ptcb)
              (sifthen (V293_task_prio_null_test (evar ptcb))
                (sseq (sprim excrit) (srete (econst32 (Int.repr 41))))))))
        (sifthen (V293_task_prio_reserved_test ptcb reserved)
          (sseq (sprim excrit) (srete (econst32 (Int.repr 67))))))).

Definition checked_normalize : forall table oldprio newprio ptcb current reserved cpu_sr enter exit,
  enter <> exit ->
  V293_port_normalize enter exit cpu_sr
    (sseq (V293_task_prio_argument_guards oldprio newprio)
      (sseq (scall enter (eaddrof (evar cpu_sr)::nil))
        (V293_task_prio_entry_reserved table oldprio newprio ptcb current reserved cpu_sr exit))) =
  Some (expected_critical_prefix table oldprio newprio ptcb current reserved) :=
  V293_critical_prefix_normalization.

Definition checked_reject : forall enter exit saved other,
  enter <> exit -> other <> saved ->
  V293_port_normalize enter exit saved (scall exit (eaddrof (evar other)::nil)) = None /\
  V293_port_normalize enter exit saved (scall exit (evar saved::nil)) = None /\
  V293_port_normalize enter enter saved (scall enter (eaddrof (evar saved)::nil)) = None :=
  V293_port_rejects_wrong_token.

Definition checked_occupied :
  forall P ks ge le caller M f body next suffix ir enabled si ci
    table oldprio newprio ptcb current reserved cpu_sr b bo bn bs old new target,
  old < 256 -> (old < 12 \/ old = 255) -> new < 12 ->
  get le table = None -> get ge table = Some (b,Tarray (Tptr V293_tcb_type) 13) ->
  get le oldprio = Some (bo,Tint8) -> get le newprio = Some (bn,Tint8) ->
  get le cpu_sr = Some (bs,Tint32) -> bs <> b ->
  load Tint8 M (bo,0%Z) = Some (V293_byteval old) ->
  load Tint8 M (bn,0%Z) = Some (V293_byteval new) ->
  load (Tptr V293_tcb_type) M (b,(4*Z.of_nat new)%Z) = Some (Vptr target) ->
  callcont ks = Some (kcall f body caller next) ->
  NoDup (map fst (getaddr le)) ->
  (forall c t, In (c,t) (getaddr le) -> V293_bytes_writable M c 0%Z (typelen t)) ->
  exists Mf,
    V293_local_steps P
      (curs (sseq (expected_critical_prefix table oldprio newprio ptcb current reserved) suffix),(kenil,ks))
      ((ge,le,M),ir,(enabled,si,ci))
      (curs (sskip (Some (Vint32 (Int.repr 40)))),(kenil,next))
      ((ge,caller,Mf),ir,(enabled,si,ci)) /\
    (forall c i, ~ In c (map fst (getaddr le)) -> get Mf (c,i) = get M (c,i)) /\
    (forall c t k, In (c,t) (getaddr le) -> k < typelen t -> get Mf (c,Z.of_nat k) = None) :=
  V293_occupied_critical_return.

Definition checked_physical : forall P self enabled ir,
  exists Mf,
    V293_local_steps P
      (curs (sseq (expected_critical_prefix 500%Z 501%Z 502%Z 400%Z 750%Z 603%Z)
        (scall 999%Z nil)),(kenil,kcall 700%Z sret emp kstop))
      ((V293_error_fixture_ge,V293_critical_fixture_le,V293_critical_fixture_mem self),ir,(enabled,nil,nil))
      (curs (sskip (Some (Vint32 (Int.repr 40)))),(kenil,kstop))
      ((V293_error_fixture_ge,emp,Mf),ir,(enabled,nil,nil)) /\
    (forall k, k < 4 -> get Mf (61%positive,Z.of_nat k) = None) /\
    get Mf (51%positive,0%Z) = None /\ get Mf (52%positive,0%Z) = None /\
    load (Tptr V293_tcb_type) Mf (50%positive,24%Z) = Some (Vptr (90%positive,Int.zero)) :=
  V293_occupied_critical_witness.

Definition checked_disabled : forall P self ir,
  exists Mf,
    V293_local_steps P
      (curs (sseq (expected_critical_prefix 500%Z 501%Z 502%Z 400%Z 750%Z 603%Z)
        (scall 999%Z nil)),(kenil,kcall 700%Z sret emp kstop))
      ((V293_error_fixture_ge,V293_critical_fixture_le,V293_critical_fixture_mem self),ir,(false,nil,nil))
      (curs (sskip (Some (Vint32 (Int.repr 40)))),(kenil,kstop))
      ((V293_error_fixture_ge,emp,Mf),ir,(false,nil,nil)).
Proof. intros. destruct (V293_occupied_critical_witness P self false ir) as (Mf & E & Rest). eauto. Qed.

Definition checked_raw_missing : forall P exit_id args types ks m ir au,
  P exit_id = None ->
  ~ exists C' state', loststep P (curs (sfexec exit_id args types),(kenil,ks)) (m,ir,au) C' state' :=
  V293_missing_port_has_no_step.

Print Assumptions checked_normalize.
Print Assumptions checked_reject.
Print Assumptions checked_occupied.
Print Assumptions checked_physical.
Print Assumptions checked_disabled.
Print Assumptions checked_raw_missing.
