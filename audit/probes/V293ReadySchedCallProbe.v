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
Require Import CertiOS.audit.probes.V293ReadyTargetHandoffProbe.
Require Import CertiOS.certiucos.v293.proofs.V293ReadySchedCall.

(* A caller-owned canary at its old y binding is not the callee's local. *)
Definition RCframe :=
  V293_owned_record_cell ((90%positive,0%Z),Tint8,V293_byteval 99) **
  V293_read_bytes 92%positive 0%Z V293_ready_table.
Lemma RCread_good : forall vs b off, GoodInvAsrt (V293_read_bytes b off vs).
Proof. induction vs;intros;cbn;auto. Qed.
Lemma RCframe_good : GoodInvAsrt RCframe.
Proof. split;[unfold V293_owned_record_cell;cbn;split;exact I | apply RCread_good]. Qed.
Lemma RCentry : forall ct, RHstate ct (RHmemory ct) |=
  SWINVt (V293_ready_inv 80%positive 81%positive 82%positive) ct **
    (V293_owned_record_cell ((91%positive,0%Z),Tint8,V293_byteval 88) **
      (V293_owned_record_cell ((93%positive,0%Z),Tptr V293_tcb_type,Vptr OwnershipWaiting) ** RCframe)).
Proof. intro ct. pose proof (RHentry ct). unfold RCframe. sep auto. Qed.

Definition RCprogram : progunit := fun f =>
  if Z.eq_dec f 107%Z then Some (V293_OSSchedNew_function 100%Z 101%Z 102%Z 103%Z 104%Z) else None.

Theorem RCjoint_call_handoff_and_omission : forall ks live, exists b Ms Mskip Mf,
  fresh (RHmemory (RIcurrent live)) b /\
  cstepstar RCprogram
    (curs (scall 107%Z nil),(kenil,kseq (V293_OSSched_target_update 105%Z 103%Z 106%Z) ks))
    (RHge,RTle,RHmemory (RIcurrent live))
    (curs (sskip None),(kenil,kseq (V293_OSSched_target_update 105%Z 103%Z 106%Z) ks)) (RHge,RTle,Mskip) /\
  free Tint8 b Ms=Some Mskip /\ get Mskip (b,0%Z)=None /\
  cstepstar RCprogram
    (curs (V293_OSSched_unlocked_prefix 107%Z 105%Z 103%Z 106%Z),(kenil,ks))
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
  load Tint8 Mskip (90%positive,0%Z)=Some (V293_byteval 99) /\
  load Tint8 Mf (90%positive,0%Z)=Some (V293_byteval 99) /\
  (forall c i, (c,i)<>(91%positive,0%Z) -> get Mskip (c,i)=get (RHmemory (RIcurrent live)) (c,i)) /\
  (forall c i, c<>93%positive \/ (i<0)%Z \/ (4<=i)%Z -> get Mf (c,i)=get Mskip (c,i)).
Proof.
  intros ks live. set (ct:=RIcurrent live).
  destruct (V293_ready_dispatch_call 80%positive 81%positive 82%positive RCprogram ks RHge RTle
    (RHmemory ct) (fun _=>false) (false,nil,nil) (RIabstract ct) (spec_done None)
    ct RCframe 107%Z 100%Z 101%Z 102%Z 103%Z 104%Z 105%Z 106%Z 92%positive 91%positive 93%positive
    (V293_byteval 88) (Vptr OwnershipWaiting)
    ltac:(vm_compute;reflexivity)
    ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
    ltac:(discriminate) ltac:(discriminate)
    eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
    RCframe_good (RHlookup ct) (RCentry ct))
    as (ts&lo&hi&es&next&msg&b&Ms&Mskip&Mf&Fresh&Map&Rel&Task&Call&Skipped&Free&Removed&High&Exec&Store&After&Load&Sched&Pre&Member&Dead&CallFrame&Frame).
  pose proof (RIfixed_tasks ct). assert (ts=OwnershipTasks) by congruence. subst ts.
  assert (Bound : V293_ready_select lo hi (V293_ready_group lo hi)<13).
  { apply V293_ready_selection_range; [exact (proj1 Rel) | exact (proj1 (proj2 Rel)) | reflexivity | exact (proj1 (proj2 (proj2 Rel)))]. }
  destruct (RTonly_ready _ _ _ Bound Task) as [Selected [Target Message]]. subst next.
  assert (Stale : load (Tptr V293_tcb_type) Mskip (93%positive,0%Z)=Some (Vptr OwnershipWaiting)).
  { eapply V293_record_star_load_l with (s:=RHstate ct Mskip)
      (P:=V293_owned_record_cell ((93%positive,0%Z),Tptr V293_tcb_type,Vptr OwnershipWaiting)) (Q:=Atrue).
    - intros st CellProof;apply V293_owned_record_cell_load;exact CellProof.
    - sep auto. }
  assert (Canary : load Tint8 Mskip (90%positive,0%Z)=Some (V293_byteval 99)).
  { eapply V293_record_star_load_l with (s:=RHstate ct Mskip)
      (P:=V293_owned_record_cell ((90%positive,0%Z),Tint8,V293_byteval 99)) (Q:=Atrue).
    - intros st CellProof;apply V293_owned_record_cell_load;exact CellProof.
    - unfold RCframe in Skipped. sep auto. }
  assert (CanaryFinal : load Tint8 Mf (90%positive,0%Z)=Some (V293_byteval 99)).
  { eapply V293_record_star_load_l with (s:=RHstate ct Mf)
      (P:=V293_owned_record_cell ((90%positive,0%Z),Tint8,V293_byteval 99)) (Q:=Atrue).
    - intros st CellProof;apply V293_owned_record_cell_load;exact CellProof.
    - unfold RCframe in After. clear Skipped Pre. sep auto. }
  exists b. exists Ms. exists Mskip. exists Mf.
  split;[exact Fresh | ]. split;[exact Call | ]. split;[exact Free | ]. split;[exact Removed | ].
  split;[exact Exec | ]. split;[exact Store | ]. split;[exact Pre | ]. split.
  - intro Live. apply Member. unfold ct,RIcurrent. rewrite Live. exists (Int.repr 6,wait (os_stat_sem (72%positive,Int.repr 5)) Int.one,Vptr (120%positive,Int.repr 7)). vm_compute;reflexivity.
  - split.
    + intro Gone. apply Dead. unfold ct,RIcurrent. rewrite Gone. intros [v V]. vm_compute in V. discriminate.
    + split.
      * clear Skipped Pre. sep auto.
      * split;[exact Load | ]. split.
        -- clear After Pre. sep auto.
        -- split;[rewrite Selected in High;exact High | ]. split;[exact Stale | ]. split.
           ++ apply RHreject_waiting_target;exact Stale.
           ++ split;[exact Canary | ]. split;[exact CanaryFinal | ]. split;assumption.
Qed.

(* Allocation's raw Vundef cannot be smuggled into the typed old-byte API. *)
Theorem RCundef_not_typed_byte : forall s b,
  ~ s |= V293_owned_record_cell ((b,0%Z),Tint8,Vundef).
Proof.
  intros s b Held. unfold V293_owned_record_cell in Held.
  apply astar_l_apure_elim in Held. destruct Held as [Valid Rest]. discriminate.
Qed.
