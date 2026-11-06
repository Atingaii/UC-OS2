(* Joint actual bytes and the exact original priority branch. Fixtures are
   not initialization reachability or a global cache-coherence invariant. *)
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
Require Import CertiOS.certiucos.v293.proofs.V293ReadyTargetHandoff.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewExec.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchState.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.audit.probes.V293ReadyTaskInvariantProbe.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import CertiOS.certiucos.v293.code.V293OSSchedDispatch.
Require Import CertiOS.certiucos.v293.code.V293OSSchedNew.
Require Import CertiOS.audit.probes.V293ReadyTargetHandoffProbe.
Require Import CertiOS.certiucos.v293.proofs.V293ReadySchedCall.
Require Import CertiOS.audit.probes.V293ReadySchedCallProbe.
Require Import CertiOS.certiucos.v293.proofs.V293ReadySwitchStep.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedPointerCompare.
Require Import CertiOS.certiucos.v293.code.V293OSSchedChange.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickCountdown.
Require Import CertiOS.framework.proof.cstepLib.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickLifecycle.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickStorage.
Require Import CertiOS.audit.probes.V293ReadySwitchStepProbe.
Require Import CertiOS.certiucos.v293.proofs.V293ReadySourceTail.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyGlobalTrace.
Require Import CertiOS.audit.probes.V293ReadySourceTailProbe.
Require Import CertiOS.framework.proof.auxdef.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Relations.Operators_Properties.
Import ListNotations.
Local Open Scope nat_scope.
Require Import CertiOS.audit.probes.V293ReadyGlobalTraceProbe.
Require Import CertiOS.certiucos.v293.proofs.V293LocalGlobalTrace.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyCriticalGlobal.
Require Import CertiOS.certiucos.v293.code.V293OSSchedGuards.
Import ListNotations.
Local Open Scope list_scope.

(* Independent actual guard cells; the sole scheduler local is CPU_SR.
   This fixture starts after that local's initialization. *)
Definition CGge := set (set STge 110%Z (96%positive,Tint8)) 111%Z (97%positive,Tint8).
Definition CGle : env := sig 120%Z (98%positive,Tint32).
Definition CGextra ni nl : list V293_record_cell :=
  [((96%positive,0%Z),Tint8,V293_byteval ni);
   ((97%positive,0%Z),Tint8,V293_byteval nl);
   ((98%positive,0%Z),Tint32,Vint32 Int.zero)].
Definition CGcells different ni nl := List.app (STcells different) (CGextra ni nl).
Definition CGoutputs different ni nl := OwnershipCellsMemory (CGcells different ni nl).
Definition CGwith ct different ni nl := merge (RTfull ct) (CGoutputs different ni nl).
Definition CGmemory ct different ni nl := merge (CGwith ct different ni nl) RTdecoder.
Definition CGframe ni nl := V293_owned_record_cells (CGextra ni nl) ** RCframe.
Definition CGstate ct M ci : RstateOP :=
  (CGge,CGle,M,(fun _=>false),(false,nil,ci),RIabstract ct,spec_done None).
Definition CGbody := V293_OSSched_success_body 120%Z 110%Z 111%Z
  107%Z 105%Z 103%Z 106%Z 108%Z 109%Z.
Definition CGpo : progunit := fun f =>
  if Z.eq_dec f 113%Z then Some (V293_OSSched_success_function 120%Z 110%Z 111%Z
    107%Z 105%Z 103%Z 106%Z 108%Z 109%Z) else RCprogram f.
Definition CGempty : progunit := fun _=>None.
Definition CGprogram := pumerge CGpo CGempty.
Definition CGcontrol := V293_sched_control 110%Z 111%Z STbody.
Definition CGouter := kcall 113%Z CGbody CGle kstop.
Definition CGpending := kseq (sseq (sprim excrit) sret) kstop.
Definition CGpost different ni nl :=
  V293_owned_record_cell ((91%positive,0%Z),Tint8,V293_byteval 4) **
  (V293_owned_record_cell ((94%positive,0%Z),Tint8,V293_byteval (STcache different)) **
   (V293_owned_record_cell ((95%positive,0%Z),Tint32,Vint32 (if different then Int.zero else Int.mone)) **
    (V293_owned_record_cell ((93%positive,0%Z),Tptr V293_tcb_type,Vptr OwnershipReady) ** CGframe ni nl))).
Lemma CGframe_good : forall ni nl, GoodInvAsrt (CGframe ni nl).
Proof. intros. split; [apply V293_owned_cells_good | exact RCframe_good]. Qed.
Lemma CGoutputs_join : forall ct different ni nl,
  join (RTfull ct) (CGoutputs different ni nl) (CGwith ct different ni nl).
Proof.
  intros ct different ni nl. apply map_join_merge;apply map_disjoint;intros [b i].
  destruct (Pos.eq_dec b 90%positive) as [E|N90]; [subst b;left;apply RToutside;discriminate | ].
  destruct (Pos.eq_dec b 91%positive) as [E|N91]; [subst b;left;apply RToutside;discriminate | ].
  destruct (Pos.eq_dec b 93%positive) as [E|N93]; [subst b;left;apply RToutside;discriminate | ].
  destruct (Pos.eq_dec b 94%positive) as [E|N94]; [subst b;left;apply RToutside;discriminate | ].
  destruct (Pos.eq_dec b 95%positive) as [E|N95]; [subst b;left;apply RToutside;discriminate | ].
  destruct (Pos.eq_dec b 96%positive) as [E|N96]; [subst b;left;apply RToutside;discriminate | ].
  destruct (Pos.eq_dec b 97%positive) as [E|N97]; [subst b;left;apply RToutside;discriminate | ].
  destruct (Pos.eq_dec b 98%positive) as [E|N98]; [subst b;left;apply RToutside;discriminate | ].
  right;left. unfold CGoutputs. apply OwnershipCellsOutside.
  intro H;destruct different;vm_compute in H;intuition congruence.
Qed.
Lemma CGdecoder_join : forall ct different ni nl,
  join (CGwith ct different ni nl) RTdecoder (CGmemory ct different ni nl).
Proof.
  intros ct different ni nl. apply map_join_merge;apply map_disjoint;intros [b i].
  destruct (Pos.eq_dec b 92%positive) as [E|N92].
  - subst b. left. unfold CGwith;rewrite map_merge_semp by reflexivity.
    rewrite RToutside by discriminate. unfold CGoutputs.
    rewrite OwnershipCellsOutside by (intro H;destruct different;vm_compute in H;intuition congruence).
    reflexivity.
  - right;left. apply V293_encoded_memory_outside. left;exact N92.
Qed.
Lemma CGoutputs_spatial : forall different ni nl, ni<256 -> nl<256 ->
  V293_target_wstate CGge CGle (CGoutputs different ni nl) emp |=
    V293_owned_record_cells (CGcells different ni nl).
Proof.
  intros different ni nl Ni Nl. apply OwnershipCellsSpatial.
  - destruct different;vm_compute;repeat split;intros;intuition congruence.
  - destruct different; cbn [CGcells STcells CGextra app STcache];
      repeat first [apply Forall_cons | apply Forall_nil];
      cbn -[rule_type_val_match]; try reflexivity; apply V293_byte_type; assumption.
Qed.
Lemma CGentry : forall ct different ni nl ci, ni<256 -> nl<256 -> CGstate ct (CGmemory ct different ni nl) ci |=
  SWINVt (V293_ready_inv 80%positive 81%positive 82%positive) ct **
    (V293_owned_record_cell ((91%positive,0%Z),Tint8,V293_byteval 88) **
     (V293_owned_record_cell ((93%positive,0%Z),Tptr V293_tcb_type,Vptr OwnershipWaiting) **
      (V293_owned_record_cell ((94%positive,0%Z),Tint8,V293_byteval (STcache different)) **
       (V293_owned_record_cell ((95%positive,0%Z),Tint32,Vint32 Int.mone) ** CGframe ni nl)))).
Proof.
  intros ct different ni nl ci Ni Nl.
  assert (Core : V293_target_wstate CGge CGle (CGwith ct different ni nl) (RIabstract ct) |=
    SWINVt (V293_ready_inv 80%positive 81%positive 82%positive) ct **
    V293_owned_record_cells (CGcells different ni nl)).
  { eapply V293_target_wstate_star with (m1:=RTfull ct) (m2:=CGoutputs different ni nl)
      (o1:=RIabstract ct) (o2:=emp).
    - apply CGoutputs_join.
    - apply map_join_emp.
    - apply RSenv_spatial with (tp:=V293_tcb_type). vm_compute;reflexivity.
    - apply CGoutputs_spatial; assumption. }
  assert (Both : V293_target_wstate CGge CGle (CGmemory ct different ni nl) (RIabstract ct) |=
    (SWINVt (V293_ready_inv 80%positive 81%positive 82%positive) ct **
      V293_owned_record_cells (CGcells different ni nl)) ** V293_read_bytes 92%positive 0%Z V293_ready_table).
  { eapply V293_target_wstate_star with (m1:=CGwith ct different ni nl) (m2:=RTdecoder)
      (o1:=RIabstract ct) (o2:=emp).
    - apply CGdecoder_join.
    - apply map_join_emp.
    - exact Core.
    - apply V293_read_bytes_witness. }
  unfold CGstate. eapply V293_ready_critical_stack with (ci:=nil).
  - repeat split;exact I.
  - cbn [CGcells STcells CGextra app V293_owned_record_cells] in Both.
    unfold CGframe,RCframe. cbn [CGextra V293_owned_record_cells]. clear Core. sep auto.
Qed.
Lemma CGlookup : forall ct different ni nl n, n<256 ->
  load Tint8 (CGmemory ct different ni nl) (92%positive,Z.of_nat n)=Some (V293_byteval (V293_ready_lookup n)).
Proof.
  intros ct different ni nl n Bound. eapply load_mem_mono with (M:=RTdecoder).
  - assert (RowBound : nth n V293_ready_table 0<256).
    { change (V293_ready_lookup n<256). pose proof (proj1 (V293_ready_row_spec n Bound)). lia. }
    replace (Z.of_nat n) with (0+Z.of_nat n)%Z by lia.
    apply (V293_read_bytes_load V293_ready_table 92%positive 0%Z n Bound RowBound
      (V293_wstate emp emp RTdecoder)). apply V293_read_bytes_witness.
  - exists (CGwith ct different ni nl). apply map_join_comm;apply CGdecoder_join.
Qed.
Lemma CGguard_loads : forall ct different ni nl, ni<256 -> nl<256 ->
  load Tint8 (CGmemory ct different ni nl) (96%positive,0%Z)=Some (V293_byteval ni) /\
  load Tint8 (CGmemory ct different ni nl) (97%positive,0%Z)=Some (V293_byteval nl).
Proof.
  intros ct different ni nl Ni Nl. assert (Loads : forall a tp v, In (a,tp,v) (CGcells different ni nl) ->
    load tp (CGmemory ct different ni nl) a=Some v).
  { intros a tp v Member. eapply load_mem_mono with (M:=CGwith ct different ni nl).
    - eapply load_mem_mono with (M:=CGoutputs different ni nl).
      + change (load tp (getmem (V293_target_wstate CGge CGle (CGoutputs different ni nl) emp)) a=Some v).
        eapply V293_owned_record_cells_load; [exact Member | apply CGoutputs_spatial; assumption].
      + exists (RTfull ct). apply map_join_comm;apply CGoutputs_join.
    - exists RTdecoder. apply CGdecoder_join. }
  split;apply Loads;unfold CGcells,CGextra;apply in_or_app;right;cbn;auto.
Qed.

Theorem CGsource_tail : forall ct different ni nl ci ks, ni<256 -> nl<256 -> exists Mtarget Mtail,
  cstepstar CGprogram (curs STbody,(kenil,ks)) (CGge,CGle,CGmemory ct different ni nl)
    ((if different then curs (sprim (switch 106%Z)) else SKIP),(kenil,ks)) (CGge,CGle,Mtail) /\
  (if different then store Tint32 Mtarget (95%positive,0%Z) (Vint32 Int.zero)=Some Mtail else Mtail=Mtarget) /\
  CGstate ct Mtail ci |= SWINVt (V293_ready_inv 80%positive 81%positive 82%positive) ct **
    (V293_owned_record_cell ((91%positive,0%Z),Tint8,V293_byteval 4) **
     (V293_owned_record_cell ((94%positive,0%Z),Tint8,V293_byteval (STcache different)) **
      (V293_owned_record_cell ((95%positive,0%Z),Tint32,Vint32 (if different then Int.zero else Int.mone)) **
       (V293_owned_record_cell ((93%positive,0%Z),Tptr V293_tcb_type,Vptr OwnershipReady) ** (CGframe ni nl))))) /\
  load (Tptr V293_tcb_type) Mtail (93%positive,0%Z)=Some (Vptr OwnershipReady) /\
  load Tint32 Mtail (95%positive,0%Z)=Some (Vint32 (if different then Int.zero else Int.mone)) /\
  load Tint8 Mtail (94%positive,0%Z)=Some (V293_byteval (STcache different)) /\
  (forall b i, b<>95%positive \/ (i<0)%Z \/ (4<=i)%Z -> get Mtail (b,i)=get Mtarget (b,i)).
Proof.
  intros ct different ni nl ci ks Ni Nl.
  destruct (V293_ready_source_dispatch 80%positive 81%positive 82%positive CGprogram ks CGge CGle
    (CGmemory ct different ni nl) (fun _=>false) (false,nil,ci) (RIabstract ct) (spec_done None) ct (CGframe ni nl)
    107%Z 100%Z 101%Z 102%Z 103%Z 104%Z 105%Z 106%Z 108%Z 109%Z
    92%positive 91%positive 93%positive 94%positive 95%positive (STcache different) Int.mone
    (V293_byteval 88) (Vptr OwnershipWaiting)
    ltac:(vm_compute;reflexivity)
    ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
    ltac:(discriminate) ltac:(discriminate)
    eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
    eq_refl eq_refl eq_refl eq_refl ltac:(destruct different;cbn [STcache];lia)
    (CGframe_good ni nl) (CGlookup ct different ni nl) (CGentry ct different ni nl ci Ni Nl))
    as (tasks & lo & hi & entries & next & message & Mtarget & Mtail & Map & Rel & Task & Exec & Store & After & Target & Counter & Cache & Outside).
  pose proof (RIfixed_tasks ct). assert (tasks=OwnershipTasks) by congruence. subst tasks.
  assert (Range : V293_ready_select lo hi (V293_ready_group lo hi)<13).
  { destruct Rel as [Lo [Hi [Nonempty [Bitmap Table]]]].
    apply V293_ready_selection_range;assumption || reflexivity. }
  destruct (RTonly_ready _ _ _ Range Task) as (Selected & Next & Message). subst next message.
  rewrite Selected in Exec,Store,After,Counter.
  assert (Wrap : Int.add Int.mone Int.one=Int.zero) by (vm_compute;apply Int.mkint_eq;reflexivity).
  rewrite Wrap in Store,After,Counter.
  exists Mtarget. exists Mtail. destruct different;cbn [STcache] in *;
    repeat first [assumption | split].
Qed.


Definition CGat different C M au := V293_local_global_at GSbase GSenvs
  (RSaux (GScurrent different)) (GScurrent different) C ((CGge,CGle,M),(fun _=>false),au).

Theorem CGlocal_ready : forall different enabled ci, exists Mtail,
  V293_local_steps CGprogram (curs CGcontrol,(kenil,kstop))
    ((CGge,CGle,CGmemory (GScurrent different) different 0 0),(fun _=>false),(enabled,nil,ci))
    ((if different then curs (sprim (switch 106%Z)) else SKIP),(kenil,CGpending))
    ((CGge,CGle,Mtail),(fun _=>false),(false,nil,enabled::ci)) /\
  CGstate (GScurrent different) Mtail (enabled::ci) |=
    SWINVt (V293_ready_inv 80%positive 81%positive 82%positive) (GScurrent different) ** CGpost different 0 0 /\
  load (Tptr V293_tcb_type) Mtail (93%positive,0%Z)=Some (Vptr OwnershipReady) /\
  load Tint32 Mtail (95%positive,0%Z)=Some (Vint32 (if different then Int.zero else Int.mone)) /\
  load Tint8 Mtail (94%positive,0%Z)=Some (V293_byteval (STcache different)).
Proof.
  intros different enabled ci.
  destruct (CGsource_tail (GScurrent different) different 0 0 (enabled::ci) CGpending ltac:(lia) ltac:(lia))
    as (Mtarget & Mtail & Tail & Store & Before & Target & Counter & Cache & Outside).
  destruct (CGguard_loads (GScurrent different) different 0 0 ltac:(lia) ltac:(lia)) as [IL LL].
  exists Mtail. split.
  - eapply V293_local_trans.
    + unfold CGcontrol. exact (V293_sched_control_enter CGprogram kstop CGge CGle
        (CGmemory (GScurrent different) different 0 0) (fun _=>false) enabled nil ci
        110%Z 111%Z 96%positive 97%positive 0 0 STbody
        ltac:(lia) ltac:(lia) eq_refl eq_refl eq_refl eq_refl IL LL).
    + apply V293_csteps_local. exact Tail.
  - split; [exact Before | ]. split; [exact Target | ]. split;assumption.
Qed.

Theorem CGglobal_ready : forall different enabled ci ip cst, exists Mtail,
  V293_global_steps (RCprogram,(CGpo,CGempty,ip)) cst
    (CGat different (curs CGcontrol,(kenil,CGouter))
      (CGmemory (GScurrent different) different 0 0) (enabled,nil,ci))
    (CGat different ((if different then curs (sprim (switch 106%Z)) else SKIP),
      (kenil,kseq (sseq (sprim excrit) sret) CGouter)) Mtail (false,nil,enabled::ci)) /\
  CGstate (GScurrent different) Mtail (enabled::ci) |=
    SWINVt (V293_ready_inv 80%positive 81%positive 82%positive) (GScurrent different) ** CGpost different 0 0 /\
  load (Tptr V293_tcb_type) Mtail (93%positive,0%Z)=Some (Vptr OwnershipReady) /\
  load Tint32 Mtail (95%positive,0%Z)=Some (Vint32 (if different then Int.zero else Int.mone)) /\
  load Tint8 Mtail (94%positive,0%Z)=Some (V293_byteval (STcache different)).
Proof.
  intros different enabled ci ip cst.
  destruct (CGlocal_ready different enabled ci) as (Mtail & Trace & Rest).
  exists Mtail. split; [ | exact Rest].
  exact (V293_local_steps_global RCprogram CGpo CGempty ip _ _ _ _ Trace
    113%Z CGbody CGle kstop Tvoid dnil (dcons 120%Z Tint32 dnil)
    GSbase GSenvs (RSaux (GScurrent different)) (GScurrent different) cst eq_refl I).
Qed.

Theorem CGglobal_no_switch_restore : forall enabled ci ip cst, exists Mtail,
  V293_global_steps (RCprogram,(CGpo,CGempty,ip)) cst
    (CGat false (curs CGcontrol,(kenil,CGouter))
      (CGmemory OwnershipReady false 0 0) (enabled,nil,ci))
    (CGat false (curs sret,(kenil,CGouter)) Mtail (enabled,nil,ci)) /\
  load Tint32 Mtail (95%positive,0%Z)=Some (Vint32 Int.mone) /\
  load Tint8 Mtail (94%positive,0%Z)=Some (V293_byteval 4).
Proof.
  intros enabled ci ip cst.
  destruct (CGlocal_ready false enabled ci) as (Mtail & Trace & Before & Target & Counter & Cache).
  exists Mtail. split; [ | split;assumption].
  assert (All : V293_local_steps CGprogram (curs CGcontrol,(kenil,kstop))
    ((CGge,CGle,CGmemory OwnershipReady false 0 0),(fun _=>false),(enabled,nil,ci))
    (curs sret,(kenil,kstop)) ((CGge,CGle,Mtail),(fun _=>false),(enabled,nil,ci))).
  { eapply V293_local_trans; [exact Trace | apply V293_sched_control_exit]. }
  exact (V293_local_steps_global RCprogram CGpo CGempty ip _ _ _ _ All
    113%Z CGbody CGle kstop Tvoid dnil (dcons 120%Z Tint32 dnil)
    GSbase GSenvs (RSaux OwnershipReady) OwnershipReady cst eq_refl I).
Qed.

Theorem CGlocal_blocked : forall ct different ni nl enabled ci,
  ni<256 -> nl<256 -> (Nat.eqb ni 0 && Nat.eqb nl 0)=false ->
  V293_local_steps CGprogram (curs CGcontrol,(kenil,kstop))
    ((CGge,CGle,CGmemory ct different ni nl),(fun _=>false),(enabled,nil,ci))
    (curs sret,(kenil,kstop))
    ((CGge,CGle,CGmemory ct different ni nl),(fun _=>false),(enabled,nil,ci)).
Proof.
  intros ct different ni nl enabled ci Ni Nl Blocked.
  destruct (CGguard_loads ct different ni nl Ni Nl) as [IL LL].
  pose proof (V293_sched_control_enter CGprogram kstop CGge CGle
    (CGmemory ct different ni nl) (fun _=>false) enabled nil ci
    110%Z 111%Z 96%positive 97%positive ni nl STbody
    Ni Nl eq_refl eq_refl eq_refl eq_refl IL LL) as Enter.
  rewrite Blocked in Enter.
  eapply V293_local_trans; [exact Enter | apply V293_sched_control_exit].
Qed.

Theorem CGglobal_independent_guards : forall different enabled ci ip cst,
  (forall ni nl, ni<256 -> nl<256 -> (Nat.eqb ni 0 && Nat.eqb nl 0)=false ->
    V293_global_steps (RCprogram,(CGpo,CGempty,ip)) cst
      (CGat different (curs CGcontrol,(kenil,CGouter))
        (CGmemory (GScurrent different) different ni nl) (enabled,nil,ci))
      (CGat different (curs sret,(kenil,CGouter))
        (CGmemory (GScurrent different) different ni nl) (enabled,nil,ci))) /\
  load Tint8 (CGmemory (GScurrent different) different 1 0) (96%positive,0%Z)=Some (V293_byteval 1) /\
  load Tint8 (CGmemory (GScurrent different) different 1 0) (97%positive,0%Z)=Some (V293_byteval 0) /\
  load Tint8 (CGmemory (GScurrent different) different 0 1) (96%positive,0%Z)=Some (V293_byteval 0) /\
  load Tint8 (CGmemory (GScurrent different) different 0 1) (97%positive,0%Z)=Some (V293_byteval 1).
Proof.
  intros different enabled ci ip cst. split.
  - intros ni nl Ni Nl Blocked.
    pose proof (CGlocal_blocked (GScurrent different) different ni nl enabled ci Ni Nl Blocked) as Trace.
    exact (V293_local_steps_global RCprogram CGpo CGempty ip _ _ _ _ Trace
      113%Z CGbody CGle kstop Tvoid dnil (dcons 120%Z Tint32 dnil)
      GSbase GSenvs (RSaux (GScurrent different)) (GScurrent different) cst eq_refl I).
  - destruct (CGguard_loads (GScurrent different) different 1 0 ltac:(lia) ltac:(lia)).
    destruct (CGguard_loads (GScurrent different) different 0 1 ltac:(lia) ltac:(lia)).
    repeat split;assumption.
Qed.

Definition CGswitch_tasks : tasks := set GSbase OwnershipWaiting
  (curs (sprim (switch 106%Z)),(kenil,kseq (sseq (sprim excrit) sret) CGouter)).
Definition CGswitch_envs : cltenvs := set GSenvs OwnershipWaiting CGle.
Definition CGswitch_aux enabled ci := set (RSaux OwnershipWaiting) OwnershipWaiting (false,nil,enabled::ci).

Theorem CGglobal_switch_pending_exit : forall enabled ci ip cst, exists Mf,
  V293_global_steps (RCprogram,(CGpo,CGempty,ip)) cst
    (CGat true (curs CGcontrol,(kenil,CGouter))
      (CGmemory OwnershipWaiting true 0 0) (enabled,nil,ci))
    (set CGswitch_tasks OwnershipWaiting (SKIP,(kenil,kseq (sseq (sprim excrit) sret) CGouter)),
      (CGge,CGswitch_envs,Mf,(fun _=>false),CGswitch_aux enabled ci),OwnershipReady) /\
  (CGge,CGle,Mf,(fun _=>false),(false,nil,enabled::ci),
    set (RIabstract OwnershipWaiting) curtid (oscurt OwnershipReady),spec_done None) |=
    SWINVt (V293_ready_inv 80%positive 81%positive 82%positive) OwnershipReady ** CGpost true 0 0 /\
  load (Tptr V293_tcb_type) Mf (1%positive,0%Z)=Some (Vptr OwnershipReady) /\
  load Tint32 Mf (95%positive,0%Z)=Some (Vint32 Int.zero) /\
  load Tint8 Mf (94%positive,0%Z)=Some (V293_byteval 6) /\
  ~ V293_current_task OwnershipTasks OwnershipReady 6 /\
  get (CGswitch_aux enabled ci) OwnershipWaiting=Some (false,nil,enabled::ci) /\
  get (CGswitch_aux enabled ci) OwnershipReady=Some (false,nil,nil).
Proof.
  intros enabled ci ip cst.
  destruct (CGglobal_ready true enabled ci ip cst) as (Mtail & Trace & Before & Target & Counter & Cache).
  destruct (V293_ready_switch_step 80%positive 81%positive 82%positive RCprogram CGpo CGempty ip
    CGswitch_tasks cst (kseq (sseq (sprim excrit) sret) CGouter) OwnershipWaiting OwnershipReady
    106%Z 93%positive 1%positive CGge CGle CGswitch_envs Mtail (fun _=>false)
    (false,nil,enabled::ci) (CGswitch_aux enabled ci) (RIabstract OwnershipWaiting)
    (spec_done None) (CGpost true 0 0) V293_tcb_type
    (map_get_set _ _ _) (map_get_set _ _ _) (map_get_set _ _ _) eq_refl Target eq_refl Before)
    as (Mf & Step & Store & After & Current & Skipped & Other & Outside).
  exists Mf. split.
  - apply clos_rt_rt1n. eapply Relation_Operators.rt_trans.
    + apply clos_rt1n_rt. exact Trace.
    + apply Relation_Operators.rt_step. exact Step.
  - split; [exact After | ]. split; [exact Current | ].
    assert (CounterFinal : load Tint32 Mf (95%positive,0%Z)=Some (Vint32 Int.zero)).
    { change (load Tint32 (getmem (CGge,CGle,Mf,(fun _=>false),(false,nil,enabled::ci),
        set (RIabstract OwnershipWaiting) curtid (oscurt OwnershipReady),spec_done None))
        (95%positive,0%Z)=Some (Vint32 Int.zero)).
      eapply V293_record_star_load_r; [ | exact After].
      unfold CGpost. do 2 eapply V293_record_star_load_r.
      eapply V293_record_star_load_l. apply V293_owned_record_cell_load. }
    split; [exact CounterFinal | ].
    assert (CacheFinal : load Tint8 Mf (94%positive,0%Z)=Some (V293_byteval 6)).
    { change (load Tint8 (getmem (CGge,CGle,Mf,(fun _=>false),(false,nil,enabled::ci),
        set (RIabstract OwnershipWaiting) curtid (oscurt OwnershipReady),spec_done None))
        (94%positive,0%Z)=Some (V293_byteval 6)).
      eapply V293_record_star_load_r; [ | exact After]. unfold CGpost.
      eapply V293_record_star_load_r. eapply V293_record_star_load_l.
      apply V293_owned_record_cell_load. }
    split; [exact CacheFinal | ]. split.
    + intros [Range [status [message Task]]].
      change (Some (Int.repr 4,rdy,Vnull)=Some (Int.repr 6,status,message)) in Task.
      vm_compute in Task. discriminate.
    + split; [apply map_get_set | ]. unfold CGswitch_aux.
      rewrite map_get_set' by (vm_compute;discriminate). reflexivity.
Qed.

Definition CGdeleted := sseq (V293_OSSched_guards 110%Z 111%Z STbody) (sseq (sprim excrit) sret).
Lemma CGdeleted_to_skip : forall ct different enabled ci,
  V293_local_steps CGprogram (curs CGdeleted,(kenil,kstop))
    ((CGge,CGle,CGmemory ct different 1 0),(fun _=>false),(enabled,nil,ci))
    (SKIP,(kenil,CGpending))
    ((CGge,CGle,CGmemory ct different 1 0),(fun _=>false),(enabled,nil,ci)).
Proof.
  intros ct different enabled ci.
  destruct (CGguard_loads ct different 1 0 ltac:(lia) ltac:(lia)) as [IL LL].
  pose proof (V293_success_global_byte_eq CGge CGle (CGmemory ct different 1 0)
    110%Z 96%positive 1 0 ltac:(lia) ltac:(lia) eq_refl eq_refl IL) as EI.
  unfold CGdeleted,V293_OSSched_guards.
  eapply V293_local_cons. { apply ostc_step. eapply stmt_step; [reflexivity | apply sseq_step]. }
  apply V293_csteps_local.
  exact (V293_entry_if_select CGprogram CGpending CGge CGle (CGmemory ct different 1 0)
    (V293_OSSched_zero 110%Z) (sifthen (V293_OSSched_zero 111%Z) STbody) false EI).
Qed.

(* Same memory/guards/tail/initial aux. Delete only encrit; for BOTH IE
   values a genuine execution now pops the pre-existing outer frame. *)
Theorem CGonly_enter_ablation : forall ct different enabled ci,
  CGcontrol=sseq (sprim encrit) CGdeleted /\
  V293_local_steps CGprogram (curs CGcontrol,(kenil,kstop))
    ((CGge,CGle,CGmemory ct different 1 0),(fun _=>false),(enabled,nil,negb enabled::ci))
    (curs sret,(kenil,kstop))
    ((CGge,CGle,CGmemory ct different 1 0),(fun _=>false),(enabled,nil,negb enabled::ci)) /\
  V293_local_steps CGprogram (curs CGdeleted,(kenil,kstop))
    ((CGge,CGle,CGmemory ct different 1 0),(fun _=>false),(enabled,nil,negb enabled::ci))
    (curs sret,(kenil,kstop))
    ((CGge,CGle,CGmemory ct different 1 0),(fun _=>false),(negb enabled,nil,ci)) /\
  (negb enabled,(nil:is),ci)<>(enabled,nil,negb enabled::ci).
Proof.
  intros. split; [reflexivity | ]. split.
  - apply CGlocal_blocked;vm_compute;reflexivity || lia.
  - split.
    + eapply V293_local_trans; [apply CGdeleted_to_skip | apply V293_sched_control_exit].
    + destruct enabled;intro Equal;discriminate Equal.
Qed.

Theorem CGdeleted_empty_stack_boundary : forall ct different enabled,
  V293_local_steps CGprogram (curs CGdeleted,(kenil,kstop))
    ((CGge,CGle,CGmemory ct different 1 0),(fun _=>false),(enabled,nil,nil))
    (curs (sprim excrit),(kenil,kseq sret kstop))
    ((CGge,CGle,CGmemory ct different 1 0),(fun _=>false),(enabled,nil,nil)) /\
  ~ (exists C' st', loststep CGprogram (curs (sprim excrit),(kenil,kseq sret kstop))
    ((CGge,CGle,CGmemory ct different 1 0),(fun _=>false),(enabled,nil,nil)) C' st').
Proof.
  intros. split.
  - eapply V293_local_trans; [apply CGdeleted_to_skip | ].
    eapply V293_local_cons. { apply ostc_step. eapply stmt_step; [reflexivity | apply sskip_step]. }
    eapply V293_local_cons. { apply ostc_step. eapply stmt_step; [reflexivity | apply sseq_step]. }
    apply V293_local_refl.
  - exact (proj2 (proj2 (V293_missing_enter_control CGprogram (kseq sret kstop)
      (CGge,CGle,CGmemory ct different 1 0) (fun _=>false) enabled true nil nil))).
Qed.

Lemma CGexact_existing_body : CGbody=sseq (sassign (evar 120%Z) (econst32 Int.zero)) CGcontrol.
Proof. reflexivity. Qed.

Theorem CGinterrupt_only_byte : forall ct different a, a<>(96%positive,0%Z) ->
  get (CGmemory ct different 1 0) a=get (CGmemory ct different 0 0) a.
Proof.
  intros ct different [b i] Apart.
  assert (Outside : b<>96%positive \/ (i<0)%Z \/ (1<=i)%Z).
  { destruct (Pos.eq_dec b 96%positive) as [E|N]; [subst b;right | left;exact N].
    assert (i<>0%Z) by (intro E;apply Apart;congruence). lia. }
  assert (Leaf : get (OwnershipCellMemory ((96%positive,0%Z),Tint8,V293_byteval 1)) (b,i)=
    get (OwnershipCellMemory ((96%positive,0%Z),Tint8,V293_byteval 0)) (b,i)).
  { unfold OwnershipCellMemory.
    rewrite !V293_encoded_memory_outside; [reflexivity | exact Outside | exact Outside]. }
  unfold CGmemory,CGwith,CGoutputs,CGcells,STcells,CGextra.
  cbn [OwnershipCellsMemory app]. rewrite !map_merge_semp by reflexivity.
  rewrite Leaf. reflexivity.
Qed.

Theorem CGlock_only_byte : forall ct different a, a<>(97%positive,0%Z) ->
  get (CGmemory ct different 0 1) a=get (CGmemory ct different 0 0) a.
Proof.
  intros ct different [b i] Apart.
  assert (Outside : b<>97%positive \/ (i<0)%Z \/ (1<=i)%Z).
  { destruct (Pos.eq_dec b 97%positive) as [E|N]; [subst b;right | left;exact N].
    assert (i<>0%Z) by (intro E;apply Apart;congruence). lia. }
  assert (Leaf : get (OwnershipCellMemory ((97%positive,0%Z),Tint8,V293_byteval 1)) (b,i)=
    get (OwnershipCellMemory ((97%positive,0%Z),Tint8,V293_byteval 0)) (b,i)).
  { unfold OwnershipCellMemory.
    rewrite !V293_encoded_memory_outside; [reflexivity | exact Outside | exact Outside]. }
  unfold CGmemory,CGwith,CGoutputs,CGcells,STcells,CGextra.
  cbn [OwnershipCellsMemory app]. rewrite !map_merge_semp by reflexivity.
  rewrite Leaf. reflexivity.
Qed.
