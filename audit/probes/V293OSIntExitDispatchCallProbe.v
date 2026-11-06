(* Interrupt-exit dispatch witnesses and prospective single-factor controls.
   These are local existence witnesses, not initialization reachability. *)
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

Require Import CertiOS.audit.probes.V293ReadySchedCallProbe.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitDispatchExecution.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitExecution.
Require Import CertiOS.certiucos.v293.code.V293OSIntExit.
Require Import CertiOS.certiucos.v293.code.V293OSSchedChange.
Require Import CertiOS.certiucos.v293.code.V293OSSchedGuards.
Require Import CertiOS.framework.proof.cstepLib.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedChange.
Local Open Scope nat_scope.

Require Import CertiOS.audit.probes.V293OSIntExitDispatchExecutionProbe.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitDispatchCall.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitCallExecution.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyCriticalGlobal.

Definition FXct := OwnershipReady.
Definition FXge : env := set DXge 113%Z(98%positive,Tint8).
Definition FXcaller : env := set(set RTle 601%Z(99%positive,Tint8))113%Z(100%positive,Tint8).
Definition FXbase_state M := V293_target_wstate FXge FXcaller M(RIabstract FXct).
Definition FXextras n nc : list V293_record_cell := DXextras n nc ++
 [((98%positive,0%Z),Tint8,V293_byteval 1);
  ((99%positive,0%Z),Tint8,V293_byteval 23);
  ((100%positive,0%Z),Tint8,V293_byteval 0)].
Definition FXextra n nc := OwnershipCellsMemory(FXextras n nc).
Definition FXmemory n nc := merge(RHmemory FXct)(FXextra n nc).
Definition FXstate M := FXbase_state M.
Definition FXframe := V293_owned_record_cell((97%positive,0%Z),Tint32,Vint32(Int.repr 19)) **
 (RCframe ** (V293_owned_record_cell((99%positive,0%Z),Tint8,V293_byteval 23) **
 V293_owned_record_cell((100%positive,0%Z),Tint8,V293_byteval 0))).
Definition FXentry_frame nc := V293_owned_record_cell((96%positive,0%Z),Tint8,V293_byteval nc) **
 (V293_owned_record_cell((98%positive,0%Z),Tint8,V293_byteval 1) ** FXframe).
Lemma FXbase_entry : forall ct,
  V293_target_wstate FXge FXcaller (RTexec_memory ct) (RIabstract ct) |=
    (V293_owned_record_cell ((90%positive,0%Z),Tint8,V293_byteval 99) **
     V293_owned_record_cell ((91%positive,0%Z),Tint8,V293_byteval 88)) **
    (SWINVt (V293_ready_inv 80%positive 81%positive 82%positive) ct **
     V293_read_bytes 92%positive 0%Z V293_ready_table).
Proof.
  intro ct.
  assert (Outputs : V293_target_wstate FXge FXcaller RToutputs emp |=
    V293_owned_record_cell ((90%positive,0%Z),Tint8,V293_byteval 99) **
    V293_owned_record_cell ((91%positive,0%Z),Tint8,V293_byteval 88)).
  { pose proof (OwnershipCellsSpatial RToutput_cells ltac:(vm_compute;repeat split;intros;intuition congruence)
      ltac:(repeat constructor;vm_compute;reflexivity) FXge FXcaller) as Out.
    cbn [RToutput_cells V293_owned_record_cells] in Out. sep auto. }
  assert (First : V293_target_wstate FXge FXcaller (RTwith_outputs ct) (RIabstract ct) |=
    SWINVt (V293_ready_inv 80%positive 81%positive 82%positive) ct **
    (V293_owned_record_cell ((90%positive,0%Z),Tint8,V293_byteval 99) **
     V293_owned_record_cell ((91%positive,0%Z),Tint8,V293_byteval 88))).
  { eapply V293_target_wstate_star with (m1:=RTfull ct) (m2:=RToutputs)
      (o1:=RIabstract ct) (o2:=emp).
    - apply RToutputs_join.
    - apply map_join_emp.
    - apply RTenv_spatial. vm_compute;reflexivity.
    - exact Outputs. }
  assert (Raw : V293_target_wstate FXge FXcaller (RTexec_memory ct) (RIabstract ct) |=
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

Lemma FXold_entry : forall ct,
  V293_target_wstate FXge FXcaller (RHmemory ct) (RIabstract ct) |=
    (V293_owned_record_cell ((90%positive,0%Z),Tint8,V293_byteval 99) **
     V293_owned_record_cell ((91%positive,0%Z),Tint8,V293_byteval 88)) **
    (SWINVt (V293_ready_inv 80%positive 81%positive 82%positive) ct **
     (V293_owned_record_cell ((93%positive,0%Z),Tptr V293_tcb_type,Vptr OwnershipWaiting) **
      V293_read_bytes 92%positive 0%Z V293_ready_table)).
Proof.
  intro ct.
  assert (Target : V293_target_wstate FXge FXcaller RHtarget emp |=
    V293_owned_record_cell ((93%positive,0%Z),Tptr V293_tcb_type,Vptr OwnershipWaiting)).
  { pose proof (OwnershipCellsSpatial RHtarget_cells
      ltac:(vm_compute;repeat split;intros;intuition congruence)
      ltac:(repeat constructor;reflexivity) FXge FXcaller) as H.
    cbn [RHtarget_cells V293_owned_record_cells] in H. sep auto. }
  assert (Both : V293_target_wstate FXge FXcaller (RHmemory ct) (RIabstract ct) |=
    ((V293_owned_record_cell ((90%positive,0%Z),Tint8,V293_byteval 99) **
      V293_owned_record_cell ((91%positive,0%Z),Tint8,V293_byteval 88)) **
     (SWINVt (V293_ready_inv 80%positive 81%positive 82%positive) ct **
      V293_read_bytes 92%positive 0%Z V293_ready_table)) **
     V293_owned_record_cell ((93%positive,0%Z),Tptr V293_tcb_type,Vptr OwnershipWaiting)).
  { eapply V293_target_wstate_star with (m1:=RTexec_memory ct) (m2:=RHtarget)
      (o1:=RIabstract ct) (o2:=emp).
    - apply RHjoin.
    - apply map_join_emp.
    - apply FXbase_entry.
    - exact Target. }
  clear Target. sep auto.
Qed.
Lemma FXold_outside : forall b i,
 b<>1%positive ->b<>41%positive ->b<>60%positive ->
 b<>80%positive ->b<>81%positive ->b<>82%positive ->
 b<>90%positive ->b<>91%positive ->b<>92%positive ->b<>93%positive ->
 get(RHmemory FXct)(b,i)=None.
Proof.
 intros b i N1 N41 N60 N80 N81 N82 N90 N91 N92 N93.
 unfold RHmemory,RTexec_memory,RTwith_outputs.
 repeat rewrite map_merge_semp by reflexivity.
 rewrite RToutside by assumption.
 unfold RToutputs,RHtarget;repeat rewrite OwnershipCellsOutside by
 (intro H;vm_compute in H;intuition congruence).
 unfold RTdecoder,V293_nat_memory;rewrite V293_encoded_memory_outside by(left;exact N92).
 reflexivity.
Qed.
Lemma FXjoin : forall n nc,join(RHmemory FXct)(FXextra n nc)(FXmemory n nc).
Proof.
 intros n nc;apply map_join_merge;apply map_disjoint;intros[b i].
 destruct(in_dec Pos.eq_dec b [94%positive;95%positive;96%positive;97%positive;98%positive;99%positive;100%positive]) as[Inside |Outside].
 - left;apply FXold_outside;cbn in Inside;intuition congruence.
 - right;left;unfold FXextra;apply OwnershipCellsOutside.
   intro H;vm_compute in H;cbn in Outside;intuition congruence.
Qed.
Lemma FXentry : forall n nc,n<256 ->nc<256 ->
 FXstate(FXmemory n nc)|=SWINVt(V293_ready_inv 80%positive 81%positive 82%positive)FXct **
 (V293_owned_record_cell((91%positive,0%Z),Tint8,V293_byteval 88) **
 (V293_owned_record_cell((93%positive,0%Z),Tptr V293_tcb_type,Vptr OwnershipWaiting) **
 (V293_owned_record_cell((94%positive,0%Z),Tint8,V293_byteval n) **
 (V293_owned_record_cell((95%positive,0%Z),Tint8,V293_byteval 0) ** FXentry_frame nc)))).
Proof.
 intros n nc N C.
 assert(Extra:V293_target_wstate FXge FXcaller(FXextra n nc)emp|=V293_owned_record_cells(FXextras n nc)).
 { apply OwnershipCellsSpatial.
   - vm_compute;repeat split;intros;intuition congruence.
   - repeat constructor;try reflexivity;apply V293_byte_type;assumption. }
 assert(Both:FXstate(FXmemory n nc)|=
 ((V293_owned_record_cell((90%positive,0%Z),Tint8,V293_byteval 99) **
   V293_owned_record_cell((91%positive,0%Z),Tint8,V293_byteval 88)) **
 (SWINVt(V293_ready_inv 80%positive 81%positive 82%positive)FXct **
 (V293_owned_record_cell((93%positive,0%Z),Tptr V293_tcb_type,Vptr OwnershipWaiting) **
 V293_read_bytes 92%positive 0%Z V293_ready_table))) **V293_owned_record_cells(FXextras n nc)).
 { eapply V293_target_wstate_star with(m1:=RHmemory FXct)(m2:=FXextra n nc)
   (o1:=RIabstract FXct)(o2:=emp).
   - apply FXjoin.
   - apply map_join_emp.
   - apply FXold_entry.
   - exact Extra. }
 unfold FXentry_frame,FXframe,RCframe;cbn[FXextras DXextras V293_owned_record_cells app]in Both;clear Extra;sep auto.
Qed.
Lemma FXframe_good : forall nc,GoodInvAsrt(FXentry_frame nc).
Proof. intro;unfold FXentry_frame,FXframe;repeat split;try exact I;exact RCframe_good. Qed.
Lemma FXlookup : forall n nc k,k<256 ->
 load Tint8(FXmemory n nc)(92%positive,Z.of_nat k)=Some(V293_byteval(V293_ready_lookup k)).
Proof. intros;eapply load_mem_mono;[apply RHlookup;assumption |exists(FXextra n nc);apply FXjoin]. Qed.


Definition FXfunction := V293_OSIntExit_abstract_function 113%Z 108%Z 109%Z 601%Z
 105%Z 103%Z 106%Z 110%Z 111%Z 107%Z 112%Z.
Definition FXprogram (fid:fid) := if Z.eq_dec fid 300%Z then Some FXfunction else RCprogram fid.
Definition FXpre := SWINVt(V293_ready_inv 80%positive 81%positive 82%positive)FXct **
 (V293_owned_record_cell((91%positive,0%Z),Tint8,V293_byteval 88) **
 (V293_owned_record_cell((93%positive,0%Z),Tptr V293_tcb_type,Vptr OwnershipWaiting) **
 (V293_owned_record_cell((94%positive,0%Z),Tint8,V293_byteval 1) **
 (V293_owned_record_cell((95%positive,0%Z),Tint8,V293_byteval 0) **FXentry_frame 4)))).
Definition FXpost := SWINVt(V293_ready_inv 80%positive 81%positive 82%positive)FXct **
 (V293_owned_record_cell((91%positive,0%Z),Tint8,V293_byteval 4) **
 (V293_owned_record_cell((93%positive,0%Z),Tptr V293_tcb_type,Vptr OwnershipReady) **
 (V293_owned_record_cell((94%positive,0%Z),Tint8,V293_byteval 0) **
 (V293_owned_record_cell((95%positive,0%Z),Tint8,V293_byteval 0) **FXentry_frame 4)))).
Lemma FXcurrent : V293_current_task OwnershipTasks FXct 4.
Proof. split;[lia|exists rdy;exists Vnull;vm_compute;reflexivity]. Qed.
Lemma FXhighest : V293_highest_ready OwnershipTasks FXct.
Proof.
 destruct RTliteral_rel as(Lo&Hi&Nonempty&Bitmap&Table).
 destruct(V293_ready_selection_task 16 0 RTentries OwnershipTasks Lo Hi Nonempty Bitmap Table)
 as(t&m&Task&Entry&Highest).
 assert(Range:V293_ready_select 16 0(V293_ready_group 16 0)<13).
 { eapply V293_ready_selection_range;[exact Lo|exact Hi|reflexivity|exact Nonempty]. }
 destruct(RTonly_ready _ _ _ Range Task)as(_&T&_);subst t;exact Highest.
Qed.
Lemma FXindependent_entry : forall ci,
 (FXge,FXcaller,FXmemory 1 4,(fun _=>false),(false,nil,ci),RIabstract FXct,spec_done None)|=FXpre.
Proof.
 intro ci;unfold FXpre;apply V293_ready_critical_stack with(ci:=nil).
 - unfold FXentry_frame,FXframe;repeat split;try exact I;exact RCframe_good.
 - exact(FXentry 1 4 ltac:(lia)ltac:(lia)).
Qed.
Theorem FXcomplete_call : forall enabled ci ks,exists bs Mf,
 fresh(FXmemory 1 4)bs /\
 V293_local_steps FXprogram(curs(scall 300%Z nil),(kenil,ks))
 ((FXge,FXcaller,FXmemory 1 4),(fun _=>false),(enabled,nil,ci))
 (curs(sskip None),(kenil,ks))((FXge,FXcaller,Mf),(fun _=>false),(enabled,nil,ci)) /\
 (FXge,FXcaller,Mf,(fun _=>false),(false,nil,ci),RIabstract FXct,spec_done None)|=FXpost /\
 load(Tptr V293_tcb_type)Mf(93%positive,0%Z)=Some(Vptr OwnershipReady) /\
 (forall k,k<4 ->get Mf(bs,Z.of_nat k)=None) /\
 (forall c i,c<>bs ->c<>93%positive ->(c,i)<>(91%positive,0%Z) ->(c,i)<>(94%positive,0%Z) ->
 get Mf(c,i)=get(FXmemory 1 4)(c,i)).
Proof.
 intros enabled ci ks.
 exact(V293_OSIntExit_same_task_call_execution 80%positive 81%positive 82%positive
 FXprogram ks FXge FXcaller(FXmemory 1 4)(fun _=>false)enabled nil ci(RIabstract FXct)(spec_done None)
 FXct FXframe OwnershipTasks 4 300%Z 107%Z 100%Z 101%Z 102%Z 103%Z 104%Z 105%Z 106%Z
 108%Z 109%Z 113%Z 601%Z 110%Z 111%Z 112%Z
 92%positive 91%positive 93%positive 94%positive 95%positive 98%positive 96%positive
 (V293_byteval 88)(Vptr OwnershipWaiting)
 eq_refl eq_refl ltac:(vm_compute;intuition congruence)
 ltac:(discriminate)ltac:(discriminate)ltac:(discriminate)ltac:(discriminate)
 ltac:(discriminate)ltac:(discriminate)ltac:(discriminate)
 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
 (RIfixed_tasks FXct)FXcurrent FXhighest
 ltac:(unfold FXframe;repeat split;try exact I;exact RCframe_good)
 (FXlookup 1 4)(FXindependent_entry ci)).
Qed.

Lemma FXpluck : forall ci tp a v M R,
 (FXge,FXcaller,M,(fun _=>false),(false,nil,ci),RIabstract FXct,spec_done None)|=
 V293_owned_record_cell(a,tp,v)**R ->load tp M a=Some v.
Proof.
 intros;eapply V293_record_star_load_l with
 (s:=(FXge,FXcaller,M,(fun _=>false),(false,nil,ci),RIabstract FXct,spec_done None));
 [intros st Cell;apply V293_owned_record_cell_load;exact Cell|eassumption].
Qed.
Lemma FXpost_loads : forall ci M,
 (FXge,FXcaller,M,(fun _=>false),(false,nil,ci),RIabstract FXct,spec_done None)|=FXpost ->
 load Tint8 M(91%positive,0%Z)=Some(V293_byteval 4) /\
 load Tint8 M(94%positive,0%Z)=Some(V293_byteval 0) /\
 load Tint32 M(97%positive,0%Z)=Some(Vint32(Int.repr 19)) /\
 load Tint8 M(90%positive,0%Z)=Some(V293_byteval 99) /\
 load Tint8 M(99%positive,0%Z)=Some(V293_byteval 23) /\
 load Tint8 M(100%positive,0%Z)=Some(V293_byteval 0).
Proof.
 intros ci M Held;unfold FXpost,FXentry_frame,FXframe,RCframe in Held.
 repeat split;eapply FXpluck with(ci:=ci)(R:=Atrue);sep auto.
Qed.
(* Same program and physical heap; only initial IE differs. Each side runs
   all the way through return/free, not just a guard or rejected entry. *)
Theorem FXboth_IE_complete : forall ci,
 exists b0 M0 b1 M1,
 V293_local_steps FXprogram(curs(scall 300%Z nil),(kenil,kstop))
 ((FXge,FXcaller,FXmemory 1 4),(fun _=>false),(false,nil,ci))
 (curs(sskip None),(kenil,kstop))((FXge,FXcaller,M0),(fun _=>false),(false,nil,ci)) /\
 V293_local_steps FXprogram(curs(scall 300%Z nil),(kenil,kstop))
 ((FXge,FXcaller,FXmemory 1 4),(fun _=>false),(true,nil,ci))
 (curs(sskip None),(kenil,kstop))((FXge,FXcaller,M1),(fun _=>false),(true,nil,ci)) /\
 (forall k,k<4 ->get M0(b0,Z.of_nat k)=None) /\
 (forall k,k<4 ->get M1(b1,Z.of_nat k)=None) /\
 load(Tptr V293_tcb_type)M0(93%positive,0%Z)=Some(Vptr OwnershipReady) /\
 load(Tptr V293_tcb_type)M1(93%positive,0%Z)=Some(Vptr OwnershipReady) /\
 load Tint32 M0(97%positive,0%Z)=Some(Vint32(Int.repr 19)) /\
 load Tint32 M1(97%positive,0%Z)=Some(Vint32(Int.repr 19)) /\
 load Tint8 M0(99%positive,0%Z)=Some(V293_byteval 23) /\
 load Tint8 M1(99%positive,0%Z)=Some(V293_byteval 23) /\
 load Tint8 M0(100%positive,0%Z)=Some(V293_byteval 0) /\
 load Tint8 M1(100%positive,0%Z)=Some(V293_byteval 0).
Proof.
 intro ci.
 destruct(FXcomplete_call false ci kstop)as(b0&M0&Fresh0&Exec0&Post0&Target0&Dead0&Frame0).
 destruct(FXcomplete_call true ci kstop)as(b1&M1&Fresh1&Exec1&Post1&Target1&Dead1&Frame1).
 destruct(FXpost_loads ci M0 Post0)as(High0&Nest0&Count0&Canary0&Saved0&Run0).
 destruct(FXpost_loads ci M1 Post1)as(High1&Nest1&Count1&Canary1&Saved1&Run1).
 exists b0;exists M0;exists b1;exists M1;repeat split;assumption.
Qed.
Theorem FXcaller_shadow :
 get FXcaller 601%Z=Some(99%positive,Tint8) /\
 get FXcaller 113%Z=Some(100%positive,Tint8) /\
 get FXge 113%Z=Some(98%positive,Tint8) /\
 load Tint8(FXmemory 1 4)(98%positive,0%Z)=Some(V293_byteval 1) /\
 load Tint8(FXmemory 1 4)(99%positive,0%Z)=Some(V293_byteval 23) /\
 load Tint8(FXmemory 1 4)(100%positive,0%Z)=Some(V293_byteval 0).
Proof.
 split;[reflexivity| ];split;[reflexivity| ];split;[reflexivity| ].
 pose proof(FXindependent_entry nil)as Held;unfold FXpre,FXentry_frame,FXframe,RCframe in Held.
 repeat split;eapply FXpluck with(ci:=nil)(R:=Atrue);sep auto.
Qed.
Definition FXnoSched (fid:fid) := if Z.eq_dec fid 107%Z then None else FXprogram fid.
Theorem FXonly_callee_deleted : FXnoSched 107%Z=None /\
 (forall f,f<>107%Z ->FXnoSched f=FXprogram f) /\
 FXprogram 107%Z=Some(V293_OSSchedNew_function 100%Z 101%Z 102%Z 103%Z 104%Z).
Proof.
 split;[reflexivity| ];split;[ |reflexivity].
 intros f N;unfold FXnoSched;destruct(Z.eq_dec f 107%Z);congruence.
Qed.
(* Boundary-only rejection; the independent positives above exercise the
   downstream assignment, comparison, critical exit and return/free. *)
Theorem FXmissing_scheduler_no_step : forall ks m ir au,
 ~exists C' st',loststep FXnoSched(curs(sfexec 107%Z nil nil),(kenil,ks))(m,ir,au)C' st'.
Proof. intros;apply V293_missing_port_has_no_step;reflexivity. Qed.
