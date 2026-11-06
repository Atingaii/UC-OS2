(* Independent typed TCB, ready, lookup and control bytes; no boot claim. *)
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitChangedBody.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitDispatchHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitSamePriority.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TimeAccess.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitBody.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickDelayHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedStoragePrefix.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedStorageTail.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchStorage.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedSwitch.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import CertiOS.tactics.sepauto.sep_combine_lemmas.
Require Import Coq.Lists.List Lia.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitHandoffHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitBoundarySwitch.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchState.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedShared.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedChange.
Require Import CertiOS.certiucos.v293.code.V293OSSchedChange.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCritical.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedPrefix.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedISRContext.
Require Import CertiOS.certiucos.v293.code.V293OSIntExit.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitNondispatch.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitDispatch.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntEnterInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedGuards.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedStoragePrefixWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedPrefixWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTargetWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCurrentWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedChangeWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedSwitchWitness.
Require Import CertiOS.certiucos.v293.proofs.V293SharedStateWitness.
Require Import CertiOS.certiucos.v293.code.V293ReadyTable.
Require Import CertiOS.audit.probes.V293OSIntExitBoundarySwitchProbe.
Require Import CertiOS.framework.proof.auxdef.
Require Import CertiOS.audit.probes.V293OSIntExitDispatchHoareProbe.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitChangedBody.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitReadyDispatch.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitReadyHandoff.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyStorageInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyTaskInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import CertiOS.tactics.sepauto.sep_combine_lemmas.
Require Import Coq.Lists.List Lia.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitDispatchHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitSamePriority.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TimeAccess.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitBody.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickDelayHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedStoragePrefix.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedStorageTail.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchStorage.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedSwitch.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import CertiOS.tactics.sepauto.sep_combine_lemmas.
Require Import Coq.Lists.List Lia.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitHandoffHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitBoundarySwitch.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchState.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedShared.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedChange.
Require Import CertiOS.certiucos.v293.code.V293OSSchedChange.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCritical.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedPrefix.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedISRContext.
Require Import CertiOS.certiucos.v293.code.V293OSIntExit.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitNondispatch.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitDispatch.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntEnterInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedGuards.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.code.V293ReadyTable.
Require Import CertiOS.audit.probes.V293TaskRecordOwnershipProbe.
Require Import CertiOS.audit.probes.V293ReadyTaskInvariantProbe.
Require Import CertiOS.audit.probes.V293TaskRecordInvariantProbe.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitReadyBody.
Require Import CertiOS.audit.probes.V293OSIntExitReadyHandoffProbe.

Require Import CertiOS.framework.proof.rulesoundlib.
Require Import CertiOS.framework.proof.lmachLib.
Require Import CertiOS.framework.proof.invariant_prop.
Import ListNotations.
Local Open Scope nat_scope.
Definition JBge : env :=
 set(set(set(set(set(set(set(set(set(set(set(set(emp:env)
 OSTCBCur(1%positive,Tptr V293_tcb_type))
 100%Z(92%positive,Tarray Tint8 256))101%Z(81%positive,Tint8))
 102%Z(80%positive,Tarray Tint8 2))103%Z(91%positive,Tint8))
 105%Z(82%positive,Tarray(Tptr V293_tcb_type)13))106%Z(93%positive,Tptr V293_tcb_type))
 108%Z(94%positive,Tint8))109%Z(95%positive,Tint32))110%Z(96%positive,Tint8))
 111%Z(97%positive,Tint8))112%Z(99%positive,Tint8).
Definition JBle:env:=sig 120%Z(98%positive,Tint32).
Definition JBcontrols nest c old : list V293_record_cell :=
 [((1%positive,0%Z),Tptr V293_tcb_type,Vptr OwnershipWaiting);
 ((93%positive,0%Z),Tptr V293_tcb_type,Vptr OwnershipWaiting);
 ((91%positive,0%Z),Tint8,V293_byteval 88);
 ((94%positive,0%Z),Tint8,V293_byteval 6);
 ((95%positive,0%Z),Tint32,Vint32 c);
 ((99%positive,0%Z),Tint8,V293_byteval 1);
 ((96%positive,0%Z),Tint8,V293_byteval nest);
 ((97%positive,0%Z),Tint8,V293_byteval 0);
 ((98%positive,0%Z),Tint32,Vint32 old)].
Definition JBinner nest c old:=merge OwnershipMemory(OwnershipCellsMemory(JBcontrols nest c old)).
Definition JBready nest c old:=merge RTmemory(JBinner nest c old).
Definition JBlookup:=V293_full_array_memory 92%positive 0 Tint8(map V293_byteval V293_ready_table).
Definition JBmemory nest c old:=merge JBlookup(JBready nest c old).
Definition JBstate M ci op:RstateOP:=(JBge,JBle,M,(fun _=>false),(false,nil,ci),RIabstract OwnershipWaiting,op).
Definition JBdata nest c old:=
 V293_exit_ready_body_data 100%Z 101%Z 102%Z 103%Z 105%Z 106%Z 108%Z 109%Z
 112%Z 110%Z 111%Z 120%Z 92%positive 81%positive 80%positive 91%positive
 82%positive 93%positive 94%positive 95%positive 99%positive 96%positive 97%positive 98%positive
 16 0 6 RTentries nil OwnershipWaiting OwnershipTasks (emp:EcbMod.map) Int.zero Aemp
 nest(V293_byteval 88)(Vptr OwnershipWaiting)c(Vint32 old).
Ltac JBoutside :=
 unfold JBinner,OwnershipMemory,RTmemory;
 repeat rewrite map_merge_semp by reflexivity;
 repeat rewrite OwnershipCellsOutside by
 (let h := fresh "Outside" in intro h;vm_compute in h;intuition congruence);reflexivity.
Lemma JBinner_join : forall nest c old,
 join OwnershipMemory(OwnershipCellsMemory(JBcontrols nest c old))(JBinner nest c old).
Proof.
 intros;apply map_join_merge;apply map_disjoint;intros[b i].
 destruct(Pos.eq_dec b 41%positive);[subst b;right;left;JBoutside| ].
 destruct(Pos.eq_dec b 60%positive);[subst b;right;left;JBoutside| ].
 left;JBoutside.
Qed.
Lemma JBready_join : forall nest c old,
 join RTmemory(JBinner nest c old)(JBready nest c old).
Proof.
 intros;apply map_join_merge;apply map_disjoint;intros[b i].
 destruct(Pos.eq_dec b 80%positive);[subst b;right;left;JBoutside| ].
 destruct(Pos.eq_dec b 81%positive);[subst b;right;left;JBoutside| ].
 destruct(Pos.eq_dec b 82%positive);[subst b;right;left;JBoutside| ].
 left;JBoutside.
Qed.
Lemma JBlookup_join : forall nest c old,
 join JBlookup(JBready nest c old)(JBmemory nest c old).
Proof.
 intros;apply map_join_merge;apply map_disjoint;intros[b i].
 destruct(Pos.eq_dec b 92%positive).
 - subst b;right;left;unfold JBready;rewrite map_merge_semp by reflexivity;JBoutside.
 - left;unfold JBlookup;apply V293_full_array_outside;left;assumption.
Qed.
Lemma JBcontrols_spatial : forall nest c old,nest<256 ->
 V293_wstate JBge JBle(OwnershipCellsMemory(JBcontrols nest c old)) |=
 V293_owned_record_cells(JBcontrols nest c old).
Proof.
 intros;apply OwnershipCellsSpatial.
 - unfold JBcontrols;vm_compute;repeat split;intros;intuition congruence.
 - unfold JBcontrols;repeat constructor;try reflexivity;apply V293_byte_type;lia.
Qed.
Definition JBcontrol_owned nest c old:=
 (GV OSTCBCur@(Tptr V293_tcb_type)|->Vptr OwnershipWaiting) **
 ((GV 106%Z@(Tptr V293_tcb_type)|->Vptr OwnershipWaiting) **
 V293_owned_record_cells(skipn 2(JBcontrols nest c old))).
Lemma JBpointer : forall x b v M O,
 get JBge x=Some(b,Tptr V293_tcb_type) ->
 V293_target_wstate JBge JBle M O |=V293_owned_record_cell((b,0%Z),Tptr V293_tcb_type,v) ->
 V293_target_wstate JBge JBle M O |=GV x@(Tptr V293_tcb_type)|->v.
Proof.
 intros x b v M O G H;unfold V293_owned_record_cell in H.
 apply astar_l_apure_elim in H as[Typed H].
 pose proof(@astar_l_agvarenv_intro _ x(Tptr V293_tcb_type)(b,0%Z)_ H(conj eq_refl G))as B.
 unfold Agvarmapsto;exists b;clear H;sep auto.
Qed.
Lemma JBcontrol_open : forall nest c old M O,
 V293_target_wstate JBge JBle M O |=V293_owned_record_cells(JBcontrols nest c old) ->
 V293_target_wstate JBge JBle M O |=JBcontrol_owned nest c old.
Proof.
 intros nest c old M O H;change(V293_target_wstate JBge JBle M O |=
 V293_owned_record_cell((1%positive,0%Z),Tptr V293_tcb_type,Vptr OwnershipWaiting) **
 (V293_owned_record_cell((93%positive,0%Z),Tptr V293_tcb_type,Vptr OwnershipWaiting) **
 V293_owned_record_cells(skipn 2(JBcontrols nest c old))))in H.
 apply sat_split in H;destruct H as(m1&m2&o1&o2&JM&JO&H1&H2).
 unfold JBcontrol_owned;eapply V293_target_wstate_star;[exact JM|exact JO| | ].
 - apply JBpointer with(b:=1%positive);[vm_compute;reflexivity|exact H1].
 - apply sat_split in H2;destruct H2 as(m3&m4&o3&o4&JM2&JO2&H3&H4).
   eapply V293_target_wstate_star;[exact JM2|exact JO2| |exact H4].
   apply JBpointer with(b:=93%positive);[vm_compute;reflexivity|exact H3].
Qed.
Lemma JBcontrol_frame : forall nest c old,GoodFrm(JBcontrol_owned nest c old).
Proof.
 intros;unfold JBcontrol_owned,Agvarmapsto,Agvarenv',Aptrmapsto;
 cbn[GoodFrm];repeat split;try exact I;try(intros;repeat split;exact I);apply V293_owned_cells_frame.
Qed.
Lemma JBphysical : forall nest c old,nest<256 ->
 V293_wstate JBge JBle(JBmemory nest c old) |=
 V293_array true 92%positive 0 1 Tint8(map V293_byteval V293_ready_table) **
 (V293_owned_record_cells RTcells **
 (V293_owned_task_records OwnershipTasks ** JBcontrol_owned nest c old)).
Proof.
 intros nest c old Bound;eapply V293_wstate_star;[apply JBlookup_join|apply V293_full_array_witness| ].
 eapply V293_wstate_star;[apply JBready_join| | ].
 - eapply V293_owned_cells_context;exact RTliteral_cells.
 - eapply V293_wstate_star;[apply JBinner_join| |apply JBcontrol_open;apply JBcontrols_spatial;exact Bound].
   eapply V293_task_list_context;exact OwnershipLiteralSpatial.
Qed.
Lemma JBpriority_array : forall b off es,
 V293_owned_record_cells(V293_priority_cells b off es) ==>
 V293_array true b off 4(Tptr V293_tcb_type)es.
Proof.
 intros b off es;revert off;induction es as[ |v es IH];intros off st H;[exact H| ].
 cbn[V293_priority_cells V293_owned_record_cells V293_array]in *.
 eapply astar_mono;[ |apply IH|exact H].
 intros s S;unfold V293_owned_record_cell in S;sep auto.
Qed.
Definition JBenv:=
 V293_sched_globals 100%Z 101%Z 102%Z 103%Z 92%positive 81%positive 80%positive 91%positive **
 (V293_prefix_bindings 105%Z 103%Z 106%Z V293_tcb_type 82%positive 93%positive **
 (V293_handoff_binding 103%Z 91%positive **
 (V293_exit_ready_body_bindings 110%Z 111%Z 96%positive 97%positive **
 (V293_handoff_binding 112%Z 99%positive **
 (V293_handoff_binding 108%Z 94%positive **
 (V293_counter_bindings 109%Z 95%positive **
 (Alvarenv 120%Z Tint32(98%positive,0%Z) **
 (Agvarenv OSTCBCur(Tptr V293_tcb_type)(1%positive,0%Z) **
 Agvarenv 106%Z(Tptr V293_tcb_type)(93%positive,0%Z))))))))).
Lemma JBstar : forall ci aop m1 m2 m o1 o2 o p q,
 join m1 m2 m ->join o1 o2 o ->
 (JBge,JBle,m1,(fun _:hid=>false),(false,nil,ci),o1,aop)|=p ->
 (JBge,JBle,m2,(fun _:hid=>false),(false,nil,ci),o2,aop)|=q ->
 (JBge,JBle,m,(fun _:hid=>false),(false,nil,ci),o,aop)|=p ** q.
Proof.
 intros;apply sat_split';exists m1;exists m2;exists o1;exists o2;tauto.
Qed.
Lemma JBenv_owned : forall ci aop,
 (JBge,JBle,(emp:mem),(fun _:hid=>false),(false,nil,ci),(emp:osabst),aop)|=JBenv.
Proof.
 intros;unfold JBenv,V293_exit_ready_body_bindings,V293_handoff_binding,V293_counter_bindings.
 repeat(eapply JBstar with(m1:=emp)(m2:=emp)(o1:=emp)(o2:=emp);
 [apply map_join_emp|apply map_join_emp| | ]).
 { unfold V293_sched_globals;repeat split;
   (eexists;split;[vm_compute;reflexivity|repeat split;reflexivity]). }
 { unfold V293_prefix_bindings;repeat split.
   + exists 82%positive;split;[vm_compute;reflexivity|repeat split;reflexivity].
   + exists 93%positive;split;[vm_compute;reflexivity|repeat split;reflexivity].
   + intros[v H];vm_compute in H;discriminate.
   + intros[v H];vm_compute in H;discriminate.
   + intros[v H];vm_compute in H;discriminate. }
 all: repeat split;first [solve[eexists;split;[vm_compute;reflexivity|repeat split;reflexivity]] |
 solve[intros[v H];vm_compute in H;discriminate]].
Qed.
Lemma JBentry : forall nest c old ci aop,nest<256 ->
 JBstate(JBmemory nest c old)ci(sched;;aop) |=
 <||sched;;aop||> ** OS[(fun _:hid=>false),false,nil,ci] ** JBdata nest c old.
Proof.
 intros nest c old ci aop Bound.
 pose proof(JBphysical nest c old Bound)as Physical.
 assert(Raw:JBstate(JBmemory nest c old)ci(sched;;aop) |=
 (V293_array true 92%positive 0 1 Tint8(map V293_byteval V293_ready_table) **
 (V293_owned_record_cells RTcells **
 (V293_owned_task_records OwnershipTasks ** JBcontrol_owned nest c old))) **
 V293_shared_fields OwnershipWaiting OwnershipTasks(emp:EcbMod.map)Int.zero).
 { apply sat_split';exists(JBmemory nest c old);exists(emp:mem);exists(emp:osabst);exists(RIabstract OwnershipWaiting).
   split;[apply map_join_emp| ];split;[apply map_join_comm;apply map_join_emp| ];split.
   - unfold V293_wstate in Physical.
     eapply goodfrm_prop;[ |exact Physical].
     split;[apply V293_array_good|split;[apply V293_owned_cells_frame|split;[apply V293_owned_tasks_frame|apply JBcontrol_frame]]].
   - pose proof(V293_shared_fixture_fields OwnershipWaiting OwnershipTasks(emp:EcbMod.map)Int.zero)as F.
     exact F. }
 assert(Reordered:JBstate(JBmemory nest c old)ci(sched;;aop) |=
 V293_owned_record_cells(V293_priority_cells 82%positive 0 RTentries) **
 (V293_array true 92%positive 0 1 Tint8(map V293_byteval V293_ready_table) **
 (V293_owned_task_records OwnershipTasks **
 (JBcontrol_owned nest c old **
 (Amapsto(80%positive,0%Z)Tint8 true(V293_byteval 16) **
 (Amapsto(80%positive,1%Z)Tint8 true(V293_byteval 0) **
 (Amapsto(81%positive,0%Z)Tint8 true(V293_byteval(V293_ready_group 16 0)) **
 V293_shared_fields OwnershipWaiting OwnershipTasks(emp:EcbMod.map)Int.zero))))))).
 { unfold RTcells,V293_ready_cells in Raw;cbn[app V293_owned_record_cells V293_owned_record_cell]in Raw.
   clear Physical;sep auto. }
 eapply astar_mono in Reordered;[ |apply JBpriority_array|intros st H;exact H].
 assert(Resources:JBstate(JBmemory nest c old)ci(sched;;aop)|=JBenv **
 (V293_array true 82%positive 0 4(Tptr V293_tcb_type)RTentries **
 (V293_array true 92%positive 0 1 Tint8(map V293_byteval V293_ready_table) **
 (V293_owned_task_records OwnershipTasks **
 (JBcontrol_owned nest c old **
 (Amapsto(80%positive,0%Z)Tint8 true(V293_byteval 16) **
 (Amapsto(80%positive,1%Z)Tint8 true(V293_byteval 0) **
 (Amapsto(81%positive,0%Z)Tint8 true(V293_byteval(V293_ready_group 16 0)) **
 V293_shared_fields OwnershipWaiting OwnershipTasks(emp:EcbMod.map)Int.zero)))))))).
 { apply sat_split';exists(emp:mem);exists(JBmemory nest c old);exists(emp:osabst);exists(RIabstract OwnershipWaiting).
   split;[apply map_join_comm;apply map_join_emp| ];split;[apply map_join_comm;apply map_join_emp| ];split.
   - apply JBenv_owned.
   - exact Reordered. }
 apply astar_l_aop'_intro with(aop:=sched;;aop);[ |reflexivity].
 pose proof(@astar_l_aisr_intro _(fun _:hid=>false)_ Resources eq_refl)as R0.
 pose proof(@astar_l_aie_intro _ false _ R0 eq_refl)as R1.
 pose proof(@astar_l_ais_intro _ nil _ R1 eq_refl)as R2.
 pose proof(@astar_l_acs_intro _ ci _ R2 eq_refl)as R3.
 unfold JBdata,V293_exit_ready_body_data,V293_exit_ready_body_core,JBenv,
 V293_exit_ready_body_bindings,V293_handoff_byte,V293_time_cell,V293_time_binding,
 V293_counter_cell,JBcontrol_owned,V293_exit_cells,V293_interrupt_cells in *.
 cbn[V293_owned_record_cells V293_owned_record_cell skipn JBcontrols V293_rdy_raw_cells V293_storage]in *.
 assert(RowOpen:V293_array true 80%positive 0 1 Tint8(map V293_byteval [16;0]) =
 (Amapsto(80%positive,0%Z)Tint8 true(V293_byteval 16) **
 (Amapsto(80%positive,1%Z)Tint8 true(V293_byteval 0) ** Aemp)))by reflexivity.
 unfold V293_inputs_full;rewrite RowOpen;clear -R3;sep auto.
Qed.

Theorem JBentry_nonempty : forall nest c old ci aop,nest<=1 ->exists s,
 s|=<||sched;;aop||> ** OS[(fun _:hid=>false),false,nil,ci] ** JBdata nest c old /\
 V293_highest_ready OwnershipTasks OwnershipReady /\ OwnershipReady<>OwnershipWaiting.
Proof.
 intros;exists(JBstate(JBmemory nest c old)ci(sched;;aop));split;[apply JBentry;lia| ].
 split;[ |vm_compute;discriminate].
 destruct RTliteral_rel as[Low[High[Ready[Bitmap Table]]]].
 destruct(V293_ready_selection_task 16 0 RTentries OwnershipTasks Low High Ready Bitmap Table)
 as(t&m&Get&Entry&Highest).
 change(Vptr OwnershipReady=Vptr t)in Entry.
 inversion Entry;subst;exact Highest.
Qed.
Definition JBcells:=((95%positive,0%Z),Tint32)::((91%positive,0%Z),Tint8)::
 ((94%positive,0%Z),Tint8)::(V293_array_cells 92%positive 0 1 Tint8(length V293_ready_table)++
 [((99%positive,0%Z),Tint8);((96%positive,0%Z),Tint8);((97%positive,0%Z),Tint8)]).
Definition JBpost aop ci:=V293_exit_ready_body_resumed
 100%Z 101%Z 102%Z 103%Z 105%Z 106%Z 108%Z 109%Z 112%Z 110%Z 111%Z 120%Z
 92%positive 81%positive 80%positive 91%positive 82%positive 93%positive 94%positive 95%positive
 99%positive 96%positive 97%positive 98%positive nil OwnershipWaiting aop nil Aemp ci.
Theorem JBactual_body : forall Spec sched_id nest c old ci aop,
 nest<=1 ->Spec sched_id=Some
 (V293_critical_fpre 100%Z 101%Z 102%Z 103%Z 92%positive 81%positive 80%positive 91%positive
 V293_shared_li V293_opened_inv V293_switch_li_good,
 V293_critical_fpost 100%Z 101%Z 102%Z 103%Z 92%positive 81%positive 80%positive 91%positive
 V293_shared_li V293_opened_inv V293_switch_li_good,(Tvoid,nil)) ->
 InfRules Spec V293_scheduler V293_shared_li
 (V293_ready_storage_inv 80%positive 81%positive 82%positive 106%Z V293_tcb_type JBcells)
 (fun v=>[|v=None|] ** JBpost aop ci)Afalse
 (<||sched;;aop||> ** OS[(fun _:hid=>false),false,nil,ci] ** JBdata nest c old)
 (V293_exit_boundary_body 112%Z 110%Z 111%Z 120%Z 105%Z 103%Z 106%Z 108%Z 109%Z sched_id
 (V293_interrupt_handoff 103%Z 108%Z 106%Z))Afalse OwnershipWaiting.
Proof.
 intros;unfold JBcells,JBpost,JBdata;apply V293_OSIntExit_ready_body;try lia.
 - exists 4;vm_compute;intuition lia.
 - vm_compute;discriminate.
 - exact(proj1(proj2(proj2(proj2 RTliteral_rel)))).
 - exact(proj2(proj2(proj2(proj2 RTliteral_rel)))).
 - vm_compute;repeat constructor.
 - exists(Int.repr 6,wait(os_stat_sem(72%positive,Int.repr 5))Int.one,Vptr(120%positive,Int.repr 7));vm_compute;reflexivity.
 - exact I.
 - assumption.
Qed.
(* Neutralize only the final primitive. Both states keep identical physical
   memory and abstract resources. This is not two complete body traces. *)
Theorem JBexcrit_control : forall P ks ge le M ir O si ci aop,
 loststep P(curs(sprim excrit),(kenil,ks))((ge,le,M),ir,(false,si,false::ci))
 (curs(sskip None),(kenil,ks))((ge,le,M),ir,(false,si,ci)) /\
 ~((ge,le,M,ir,(false,si,false::ci),O,aop)|=Acs ci ** Atrue).
Proof.
 intros;split;[apply excrit_step;reflexivity| ].
 intro H;apply astar_l_acs_elim in H as[E _].
 change(false::ci=ci)in E;apply(f_equal(@length bool))in E;cbn in E;lia.
Qed.
