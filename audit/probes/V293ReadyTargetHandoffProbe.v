(* Literal common-prefix control: only the final pointer assignment differs.
   This is an existence witness, not initialization reachability. *)
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293SharedStateWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCurrent.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTarget.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTargetWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.audit.probes.V293TaskRecordOwnershipProbe.
Require Import CertiOS.certiucos.v293.code.V293ReadyTable.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.auxdef.
Require Import CertiOS.framework.proof.memory_prop.
Require Import CertiOS.framework.proof.lmachLib.
Require Import CertiOS.framework.proof.rulesoundlib.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import Coq.Lists.List Lia.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyTaskInvariant.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.audit.probes.V293TaskRecordInvariantProbe.
Import ListNotations.
Local Open Scope nat_scope.

Require Import CertiOS.certiucos.v293.proofs.V293ReadyTargetHandoff.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewExec.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchState.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.audit.probes.V293ReadyTaskInvariantProbe.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import CertiOS.certiucos.v293.code.V293OSSchedDispatch.
Require Import CertiOS.certiucos.v293.code.V293OSSchedNew.
Local Open Scope nat_scope.
Definition RHge : env := set RTge 106%Z (93%positive,Tptr V293_tcb_type).
Definition RHtarget_cells : list V293_record_cell :=
  [((93%positive,0%Z),Tptr V293_tcb_type,Vptr OwnershipWaiting)].
Definition RHtarget := OwnershipCellsMemory RHtarget_cells.
Definition RHmemory ct := merge (RTexec_memory ct) RHtarget.
Definition RHstate ct M := V293_target_wstate RHge RTle M (RIabstract ct).
Lemma RHbase_entry : forall ct,
  V293_target_wstate RHge RTle (RTexec_memory ct) (RIabstract ct) |=
    (V293_owned_record_cell ((90%positive,0%Z),Tint8,V293_byteval 99) **
     V293_owned_record_cell ((91%positive,0%Z),Tint8,V293_byteval 88)) **
    (SWINVt (V293_ready_inv 80%positive 81%positive 82%positive) ct **
     V293_read_bytes 92%positive 0%Z V293_ready_table).
Proof.
  intro ct.
  assert (Outputs : V293_target_wstate RHge RTle RToutputs emp |=
    V293_owned_record_cell ((90%positive,0%Z),Tint8,V293_byteval 99) **
    V293_owned_record_cell ((91%positive,0%Z),Tint8,V293_byteval 88)).
  { pose proof (OwnershipCellsSpatial RToutput_cells ltac:(vm_compute;repeat split;intros;intuition congruence)
      ltac:(repeat constructor;vm_compute;reflexivity) RHge RTle) as Out.
    cbn [RToutput_cells V293_owned_record_cells] in Out. sep auto. }
  assert (First : V293_target_wstate RHge RTle (RTwith_outputs ct) (RIabstract ct) |=
    SWINVt (V293_ready_inv 80%positive 81%positive 82%positive) ct **
    (V293_owned_record_cell ((90%positive,0%Z),Tint8,V293_byteval 99) **
     V293_owned_record_cell ((91%positive,0%Z),Tint8,V293_byteval 88))).
  { eapply V293_target_wstate_star with (m1:=RTfull ct) (m2:=RToutputs)
      (o1:=RIabstract ct) (o2:=emp).
    - apply RToutputs_join.
    - apply map_join_emp.
    - apply RTenv_spatial. vm_compute;reflexivity.
    - exact Outputs. }
  assert (Raw : V293_target_wstate RHge RTle (RTexec_memory ct) (RIabstract ct) |=
    (SWINVt (V293_ready_inv 80%positive 81%positive 82%positive) ct **
     (V293_owned_record_cell ((90%positive,0%Z),Tint8,V293_byteval 99) **
      V293_owned_record_cell ((91%positive,0%Z),Tint8,V293_byteval 88))) **
    V293_read_bytes 92%positive 0%Z V293_ready_table).
  { eapply V293_target_wstate_star with (m1:=RTwith_outputs ct) (m2:=RTdecoder)
      (o1:=RIabstract ct) (o2:=emp).
    - apply RTdecoder_join.
    - apply map_join_emp.
    - exact First.
    - apply V293_read_bytes_witness. }
  clear First Outputs. sep auto.
Qed.

Lemma RHjoin : forall ct, join (RTexec_memory ct) RHtarget (RHmemory ct).
Proof.
  intro ct. apply map_join_merge;apply map_disjoint;intros [b i].
  destruct (Pos.eq_dec b 93%positive) as [E | N93].
  - subst b. left.
    assert (A : get (RTfull ct) (93%positive,i)=None) by (apply RToutside;discriminate).
    assert (B : get RToutputs (93%positive,i)=None).
    { unfold RToutputs. apply OwnershipCellsOutside. intro H;vm_compute in H;intuition congruence. }
    assert (C : get RTdecoder (93%positive,i)=None).
    { apply V293_encoded_memory_outside. left;discriminate. }
    assert (W : get (RTwith_outputs ct) (93%positive,i)=None).
    { eapply eq_trans; [eapply map_join_get_none; [apply RToutputs_join | exact A] | exact B]. }
    eapply eq_trans; [eapply map_join_get_none; [apply RTdecoder_join | exact W] | exact C].
  - right;left. apply OwnershipCellsOutside. intro H;vm_compute in H;intuition congruence.
Qed.
Lemma RHentry : forall ct,
  RHstate ct (RHmemory ct) |=
    (V293_owned_record_cell ((90%positive,0%Z),Tint8,V293_byteval 99) **
     V293_owned_record_cell ((91%positive,0%Z),Tint8,V293_byteval 88)) **
    (SWINVt (V293_ready_inv 80%positive 81%positive 82%positive) ct **
     (V293_owned_record_cell ((93%positive,0%Z),Tptr V293_tcb_type,Vptr OwnershipWaiting) **
      V293_read_bytes 92%positive 0%Z V293_ready_table)).
Proof.
  intro ct.
  assert (Target : V293_target_wstate RHge RTle RHtarget emp |=
    V293_owned_record_cell ((93%positive,0%Z),Tptr V293_tcb_type,Vptr OwnershipWaiting)).
  { pose proof (OwnershipCellsSpatial RHtarget_cells
      ltac:(vm_compute;repeat split;intros;intuition congruence)
      ltac:(repeat constructor;reflexivity) RHge RTle) as H.
    cbn [RHtarget_cells V293_owned_record_cells] in H. sep auto. }
  assert (Both : RHstate ct (RHmemory ct) |=
    ((V293_owned_record_cell ((90%positive,0%Z),Tint8,V293_byteval 99) **
      V293_owned_record_cell ((91%positive,0%Z),Tint8,V293_byteval 88)) **
     (SWINVt (V293_ready_inv 80%positive 81%positive 82%positive) ct **
      V293_read_bytes 92%positive 0%Z V293_ready_table)) **
     V293_owned_record_cell ((93%positive,0%Z),Tptr V293_tcb_type,Vptr OwnershipWaiting)).
  { eapply V293_target_wstate_star with (m1:=RTexec_memory ct) (m2:=RHtarget)
      (o1:=RIabstract ct) (o2:=emp).
    - apply RHjoin.
    - apply map_join_emp.
    - apply RHbase_entry.
    - exact Target. }
  clear Target. sep auto.
Qed.
Lemma RHlookup : forall ct n, n<256 ->
  load Tint8 (RHmemory ct) (92%positive,Z.of_nat n)=Some (V293_byteval (V293_ready_lookup n)).
Proof.
  intros ct n Bound. eapply load_mem_mono with (M:=RTexec_memory ct).
  - apply RTdecoder_loads;exact Bound.
  - exists RHtarget;apply RHjoin.
Qed.

(* A stale target cannot satisfy SWPRE merely because selection is correct. *)
Lemma RHreject_waiting_target : forall ct M,
  load (Tptr V293_tcb_type) M (93%positive,0%Z)=Some (Vptr OwnershipWaiting) ->
  ~ RHstate ct M |= SWPRE V293_scheduler 106%Z ct.
Proof.
  intros ct M Stale [next Pre].
  assert (Hprio : RHstate ct M |= AHprio V293_scheduler next ** Atrue) by (sep auto).
  assert (TargetHeld : RHstate ct M |= (EX tp : type, GV 106%Z @ (Tptr tp) |-> (Vptr next)) ** Atrue) by (clear Hprio; sep auto).
  apply sat_split in Hprio. destruct Hprio as (m1&m2&o1&o2&JM&JO&[Sched Empty]&Rest).
  destruct Sched as [tasks [Map Highest]].
  assert (FullMap : get (RIabstract ct) abstcblsid=Some (abstcblist tasks)).
  { eapply OSAbstMod.join_get_l; [exact JO | exact Map]. }
  pose proof (RIfixed_tasks ct). assert (tasks=OwnershipTasks) by congruence. subst tasks.
  apply sat_split in TargetHeld. destruct TargetHeld as (m3&m4&o3&o4&JM'&JO'&[tp Cell]&Rest').
  destruct (V293_dispatch_named_cell_parts _ _ _ _ _ _ _ _ _ _ Cell) as (b&GE&Owned&EO).
  change (get RHge 106%Z=Some (b,Tptr tp)) in GE.
  assert (Binding : b=93%positive /\ tp=V293_tcb_type).
  { vm_compute in GE. inversion GE;auto. }
  destruct Binding as [BlockKind TypeKind]. subst b tp.
  assert (Load : load (Tptr V293_tcb_type) m3 (93%positive,0%Z)=Some (Vptr next)).
  { eapply mapstoval_load; [destruct next;reflexivity | exact Owned]. }
  assert (FullLoad : load (Tptr V293_tcb_type) M (93%positive,0%Z)=Some (Vptr next)).
  { eapply load_mem_mono; [exact Load | exists m4;exact JM']. }
  rewrite Stale in FullLoad. inversion FullLoad;subst next.
  destruct Highest as [priority [msg [Ready Minimal]]].
  change (get OwnershipTasks OwnershipWaiting=Some (priority,rdy,msg)) in Ready.
  unfold OwnershipTasks in Ready. rewrite map_get_set in Ready. discriminate.
Qed.

Theorem RHjoint_handoff_and_omission : forall P ks live, exists Mskip Mf,
  cstepstar P
    (curs (V293_OSSchedNew_updates 100%Z 101%Z 102%Z 103%Z 104%Z),
      (kenil,kseq (V293_OSSched_target_update 105%Z 103%Z 106%Z) ks))
    (RHge,RTle,RHmemory (RIcurrent live))
    (curs (sskip None),(kenil,kseq (V293_OSSched_target_update 105%Z 103%Z 106%Z) ks)) (RHge,RTle,Mskip) /\
  cstepstar P
    (curs (sseq (V293_OSSchedNew_updates 100%Z 101%Z 102%Z 103%Z 104%Z)
      (V293_OSSched_target_update 105%Z 103%Z 106%Z)),(kenil,ks))
    (RHge,RTle,RHmemory (RIcurrent live)) (curs (sskip None),(kenil,ks)) (RHge,RTle,Mf) /\
  store (Tptr V293_tcb_type) Mskip (93%positive,0%Z) (Vptr OwnershipReady)=Some Mf /\
  RHstate (RIcurrent live) Mf |= SWPRE V293_scheduler 106%Z (RIcurrent live) /\
  (live=true -> RHstate (RIcurrent live) Mf |= SWPRE_NDEAD V293_scheduler 106%Z (RIcurrent live)) /\
  (live=false -> RHstate (RIcurrent live) Mf |= SWPRE_DEAD V293_scheduler 106%Z (RIcurrent live)) /\
  RHstate (RIcurrent live) Mf |= SWINVt (V293_ready_inv 80%positive 81%positive 82%positive) (RIcurrent live) ** Atrue /\
  load (Tptr V293_tcb_type) Mf (93%positive,0%Z)=Some (Vptr OwnershipReady) /\
  RHstate (RIcurrent live) Mskip |= SWINVt (V293_ready_inv 80%positive 81%positive 82%positive) (RIcurrent live) ** Atrue /\
  load Tint8 Mskip (91%positive,0%Z)=Some (V293_byteval 4) /\
  load (Tptr V293_tcb_type) Mskip (93%positive,0%Z)=Some (Vptr OwnershipWaiting) /\
  ~ RHstate (RIcurrent live) Mskip |= SWPRE V293_scheduler 106%Z (RIcurrent live) /\
  (forall b i, b<>93%positive \/ (i<0)%Z \/ (4<=i)%Z -> get Mf (b,i)=get Mskip (b,i)).
Proof.
  intros P ks live. set (ct:=RIcurrent live).
  destruct (V293_ready_dispatch_updates 80%positive 81%positive 82%positive P ks RHge RTle
    (RHmemory ct) (fun _=>false) (false,nil,nil) (RIabstract ct) (spec_done None)
    ct (V293_read_bytes 92%positive 0%Z V293_ready_table)
    100%Z 101%Z 102%Z 103%Z 104%Z 105%Z 106%Z 92%positive 91%positive 90%positive 93%positive
    (V293_byteval 99) (V293_byteval 88) (Vptr OwnershipWaiting)
    ltac:(repeat split;vm_compute;reflexivity) eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
    ltac:(vm_compute;reflexivity)
    ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
    ltac:(discriminate) ltac:(discriminate) (RHlookup ct) (RHentry ct))
    as (ts&lo&hi&es&next&msg&Mskip&Mf&Map&Rel&Task&Prefix&Skipped&High&Exec&Store&After&Load&Sched&Pre&Member&Dead&Frame).
  pose proof (RIfixed_tasks ct). assert (ts=OwnershipTasks) by congruence. subst ts.
  assert (Bound : V293_ready_select lo hi (V293_ready_group lo hi)<13).
  { apply V293_ready_selection_range; [exact (proj1 Rel) | exact (proj1 (proj2 Rel)) | reflexivity | exact (proj1 (proj2 (proj2 Rel)))]. }
  destruct (RTonly_ready _ _ _ Bound Task) as [Selected [Target Message]]. subst next.
  assert (Stale : load (Tptr V293_tcb_type) Mskip (93%positive,0%Z)=Some (Vptr OwnershipWaiting)).
  { eapply V293_record_star_load_l with (s:=RHstate ct Mskip)
      (P:=V293_owned_record_cell ((93%positive,0%Z),Tptr V293_tcb_type,Vptr OwnershipWaiting)) (Q:=Atrue).
    - intros st CellProof;apply V293_owned_record_cell_load;exact CellProof.
    - sep auto. }
  exists Mskip. exists Mf. split; [exact Prefix | ]. split; [exact Exec | ]. split; [exact Store | ].
  split; [exact Pre | ]. split.
  - intro Live. apply Member. unfold ct,RIcurrent. rewrite Live. exists (Int.repr 6,wait (os_stat_sem (72%positive,Int.repr 5)) Int.one,Vptr (120%positive,Int.repr 7)). vm_compute;reflexivity.
  - split.
    + intro Gone. apply Dead. unfold ct,RIcurrent. rewrite Gone. intros [v V]. vm_compute in V. discriminate.
    + split.
      * clear Skipped Pre. sep auto.
      * split; [exact Load | ]. split.
        -- clear After Pre. sep auto.
        -- split; [rewrite Selected in High;exact High | ]. split; [exact Stale | ]. split.
           ++ apply RHreject_waiting_target;exact Stale.
           ++ intros b i Outside. eapply V293_storebytes_outside; [exact Store | exact Outside].
Qed.
