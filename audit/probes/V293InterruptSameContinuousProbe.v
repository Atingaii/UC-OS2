Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTargetWitness.
Require Import CertiOS.audit.probes.V293InterruptReadyEnvironmentProbe.
(* A typed physical fixture for the same full ready/TCB/storage invariant. *)
Require Import CertiOS.certiucos.v293.proofs.V293InterruptQuietContinuous.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntEnterOpenExact.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitAllExactDynamic.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptReadyLocal.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptSourceRoundtrip.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitUnifiedInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitNondispatch.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedExactLocal.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchState.
Require Import CertiOS.tactics.sepauto.sep_combine_lemmas.
Require Import CertiOS.certiucos.v293.code.V293ReadyTable.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickDelayHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitReadyBody.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitHandoffHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedChange.
Require Import CertiOS.certiucos.v293.proofs.V293TimeAccess.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptReadyEnvironment.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptReadyEnter.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitReadyDynamic.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitReadyDispatch.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyStorageInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyTaskInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedStoragePrefix.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedSwitch.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntEnterInternal.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchStorage.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.code.V293OSIntEnter.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.audit.probes.V293OSIntExitReadyDynamicProbe.
Require Import CertiOS.audit.probes.V293OSIntExitReadyBodyProbe.
Require Import CertiOS.audit.probes.V293ReadyTaskInvariantProbe.
Require Import CertiOS.audit.probes.V293TaskRecordOwnershipProbe.
Require Import CertiOS.audit.probes.V293TaskRecordInvariantProbe.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.framework.proof.rulesoundlib.
Require Import CertiOS.framework.proof.toptheorem.
Require Import CertiOS.tactics.basetac.join_lib.
Require Import CertiOS.tactics.basetac.join_general.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.
Require Import CertiOS.audit.probes.V293InterruptQuietContinuousProbe.
Require Import CertiOS.audit.probes.V293OSIntExitReadyInternalProbe.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptChangedContinuous.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitReadyInternal.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitBuilders.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewInternal.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptSameContinuous.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitSameInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitResourceCodec.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedStoragePrefixWitness.
Require Import CertiOS.certiucos.v293.proofs.V293SharedStateWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedPrefix.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyTaskInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Definition SCcontrols nest c old : list V293_record_cell :=
 [((1%positive,0%Z),Tptr V293_tcb_type,Vptr OwnershipReady);
 ((93%positive,0%Z),Tptr V293_tcb_type,Vptr OwnershipReady);
 ((91%positive,0%Z),Tint8,V293_byteval 88);
 ((94%positive,0%Z),Tint8,V293_byteval 4);
 ((95%positive,0%Z),Tint32,Vint32 c);
 ((99%positive,0%Z),Tint8,V293_byteval 1);
 ((96%positive,0%Z),Tint8,V293_byteval nest);
 ((97%positive,0%Z),Tint8,V293_byteval 0);
 ((98%positive,0%Z),Tint32,Vint32 old)].
Definition SCinner nest c old:=merge OwnershipMemory(OwnershipCellsMemory(SCcontrols nest c old)).
Definition SCready nest c old:=merge RTmemory(SCinner nest c old).
Definition SClookup:=V293_full_array_memory 92%positive 0 Tint8(map V293_byteval V293_ready_table).
Definition SCmemory nest c old:=merge SClookup(SCready nest c old).
Definition SCstate M ci op:RstateOP:=(JBge,JBle,M,(fun _=>false),(false,nil,ci),RIabstract OwnershipReady,op).
Definition SCdata nest c old:=
 V293_exit_ready_body_data 100%Z 101%Z 102%Z 103%Z 105%Z 106%Z 108%Z 109%Z
 112%Z 110%Z 111%Z 120%Z 92%positive 81%positive 80%positive 91%positive
 82%positive 93%positive 94%positive 95%positive 99%positive 96%positive 97%positive 98%positive
 16 0 4 RTentries nil OwnershipReady OwnershipTasks (emp:EcbMod.map) Int.zero Aemp
 nest(V293_byteval 88)(Vptr OwnershipReady)c(Vint32 old).
Ltac SCoutside :=
 unfold SCinner,OwnershipMemory,RTmemory;
 repeat rewrite map_merge_semp by reflexivity;
 repeat rewrite OwnershipCellsOutside by
 (let h := fresh "Outside" in intro h;vm_compute in h;intuition congruence);reflexivity.
Lemma SCinner_join : forall nest c old,
 join OwnershipMemory(OwnershipCellsMemory(SCcontrols nest c old))(SCinner nest c old).
Proof.
 intros;apply map_join_merge;apply map_disjoint;intros[b i].
 destruct(Pos.eq_dec b 41%positive);[subst b;right;left;SCoutside| ].
 destruct(Pos.eq_dec b 60%positive);[subst b;right;left;SCoutside| ].
 left;SCoutside.
Qed.
Lemma SCready_join : forall nest c old,
 join RTmemory(SCinner nest c old)(SCready nest c old).
Proof.
 intros;apply map_join_merge;apply map_disjoint;intros[b i].
 destruct(Pos.eq_dec b 80%positive);[subst b;right;left;SCoutside| ].
 destruct(Pos.eq_dec b 81%positive);[subst b;right;left;SCoutside| ].
 destruct(Pos.eq_dec b 82%positive);[subst b;right;left;SCoutside| ].
 left;SCoutside.
Qed.
Lemma SClookup_join : forall nest c old,
 join SClookup(SCready nest c old)(SCmemory nest c old).
Proof.
 intros;apply map_join_merge;apply map_disjoint;intros[b i].
 destruct(Pos.eq_dec b 92%positive).
 - subst b;right;left;unfold SCready;rewrite map_merge_semp by reflexivity;SCoutside.
 - left;unfold SClookup;apply V293_full_array_outside;left;assumption.
Qed.
Lemma SCcontrols_spatial : forall nest c old,nest<256 ->
 V293_wstate JBge JBle(OwnershipCellsMemory(SCcontrols nest c old)) |=
 V293_owned_record_cells(SCcontrols nest c old).
Proof.
 intros;apply OwnershipCellsSpatial.
 - unfold SCcontrols;vm_compute;repeat split;intros;intuition congruence.
 - unfold SCcontrols;repeat constructor;try reflexivity.
   apply V293_byte_type;lia.
Qed.
Definition SCcontrol_owned nest c old:=
 (GV OSTCBCur@(Tptr V293_tcb_type)|->Vptr OwnershipReady) **
 ((GV 106%Z@(Tptr V293_tcb_type)|->Vptr OwnershipReady) **
 V293_owned_record_cells(skipn 2(SCcontrols nest c old))).
Lemma SCcontrol_open : forall nest c old M O,
 V293_target_wstate JBge JBle M O |=V293_owned_record_cells(SCcontrols nest c old) ->
 V293_target_wstate JBge JBle M O |=SCcontrol_owned nest c old.
Proof.
 intros nest c old M O H;change(V293_target_wstate JBge JBle M O |=
 V293_owned_record_cell((1%positive,0%Z),Tptr V293_tcb_type,Vptr OwnershipReady) **
 (V293_owned_record_cell((93%positive,0%Z),Tptr V293_tcb_type,Vptr OwnershipReady) **
 V293_owned_record_cells(skipn 2(SCcontrols nest c old))))in H.
 apply sat_split in H;destruct H as(m1&m2&o1&o2&JM&JO&H1&H2).
 unfold SCcontrol_owned;eapply V293_target_wstate_star;[exact JM|exact JO| | ].
 - apply JBpointer with(b:=1%positive);[vm_compute;reflexivity|exact H1].
 - apply sat_split in H2;destruct H2 as(m3&m4&o3&o4&JM2&JO2&H3&H4).
   eapply V293_target_wstate_star;[exact JM2|exact JO2| |exact H4].
   apply JBpointer with(b:=93%positive);[vm_compute;reflexivity|exact H3].
Qed.
Lemma SCcontrol_frame : forall nest c old,GoodFrm(SCcontrol_owned nest c old).
Proof.
 intros;unfold SCcontrol_owned,Agvarmapsto,Agvarenv',Aptrmapsto;
 cbn[GoodFrm];repeat split;try exact I;try(intros;repeat split;exact I);apply V293_owned_cells_frame.
Qed.
Lemma SCphysical : forall nest c old,nest<256 ->
 V293_wstate JBge JBle(SCmemory nest c old) |=
 V293_array true 92%positive 0 1 Tint8(map V293_byteval V293_ready_table) **
 (V293_owned_record_cells RTcells **
 (V293_owned_task_records OwnershipTasks ** SCcontrol_owned nest c old)).
Proof.
 intros nest c old Bound;eapply V293_wstate_star;[apply SClookup_join|apply V293_full_array_witness| ].
 eapply V293_wstate_star;[apply SCready_join| | ].
 - eapply V293_owned_cells_context;exact RTliteral_cells.
 - eapply V293_wstate_star;[apply SCinner_join| |apply SCcontrol_open;apply SCcontrols_spatial;exact Bound].
   eapply V293_task_list_context;exact OwnershipLiteralSpatial.
Qed.
Lemma SCheap_data : forall nest c old ci aop,nest<256 ->
 SCstate(SCmemory nest c old)ci(aop) |=
 <||aop||> ** OS[(fun _:hid=>false),false,nil,ci] ** SCdata nest c old.
Proof.
 intros nest c old ci aop Bound.
 pose proof(SCphysical nest c old Bound)as Physical.
 assert(Raw:SCstate(SCmemory nest c old)ci(aop) |=
 (V293_array true 92%positive 0 1 Tint8(map V293_byteval V293_ready_table) **
 (V293_owned_record_cells RTcells **
 (V293_owned_task_records OwnershipTasks ** SCcontrol_owned nest c old))) **
 V293_shared_fields OwnershipReady OwnershipTasks(emp:EcbMod.map)Int.zero).
 { apply sat_split';exists(SCmemory nest c old);exists(emp:mem);exists(emp:osabst);exists(RIabstract OwnershipReady).
   split;[apply map_join_emp| ];split;[apply map_join_comm;apply map_join_emp| ];split.
   - unfold V293_wstate in Physical.
     eapply goodfrm_prop;[ |exact Physical].
     split;[apply V293_array_good|split;[apply V293_owned_cells_frame|split;[apply V293_owned_tasks_frame|apply SCcontrol_frame]]].
   - pose proof(V293_shared_fixture_fields OwnershipReady OwnershipTasks(emp:EcbMod.map)Int.zero)as F.
     exact F. }
 assert(Reordered:SCstate(SCmemory nest c old)ci(aop) |=
 V293_owned_record_cells(V293_priority_cells 82%positive 0 RTentries) **
 (V293_array true 92%positive 0 1 Tint8(map V293_byteval V293_ready_table) **
 (V293_owned_task_records OwnershipTasks **
 (SCcontrol_owned nest c old **
 (Amapsto(80%positive,0%Z)Tint8 true(V293_byteval 16) **
 (Amapsto(80%positive,1%Z)Tint8 true(V293_byteval 0) **
 (Amapsto(81%positive,0%Z)Tint8 true(V293_byteval(V293_ready_group 16 0)) **
 V293_shared_fields OwnershipReady OwnershipTasks(emp:EcbMod.map)Int.zero))))))).
 { unfold RTcells,V293_ready_cells in Raw;cbn[app V293_owned_record_cells V293_owned_record_cell]in Raw.
   clear Physical;sep auto. }
 eapply astar_mono in Reordered;[ |apply JBpriority_array|intros st H;exact H].
 assert(Resources:SCstate(SCmemory nest c old)ci(aop)|=JBenv **
 (V293_array true 82%positive 0 4(Tptr V293_tcb_type)RTentries **
 (V293_array true 92%positive 0 1 Tint8(map V293_byteval V293_ready_table) **
 (V293_owned_task_records OwnershipTasks **
 (SCcontrol_owned nest c old **
 (Amapsto(80%positive,0%Z)Tint8 true(V293_byteval 16) **
 (Amapsto(80%positive,1%Z)Tint8 true(V293_byteval 0) **
 (Amapsto(81%positive,0%Z)Tint8 true(V293_byteval(V293_ready_group 16 0)) **
 V293_shared_fields OwnershipReady OwnershipTasks(emp:EcbMod.map)Int.zero)))))))).
 { apply sat_split';exists(emp:mem);exists(SCmemory nest c old);exists(emp:osabst);exists(RIabstract OwnershipReady).
   split;[apply map_join_comm;apply map_join_emp| ];split;[apply map_join_comm;apply map_join_emp| ];split.
   - apply JBenv_owned.
   - exact Reordered. }
 apply astar_l_aop'_intro with(aop:=aop);[ |reflexivity].
 pose proof(@astar_l_aisr_intro _(fun _:hid=>false)_ Resources eq_refl)as R0.
 pose proof(@astar_l_aie_intro _ false _ R0 eq_refl)as R1.
 pose proof(@astar_l_ais_intro _ nil _ R1 eq_refl)as R2.
 pose proof(@astar_l_acs_intro _ ci _ R2 eq_refl)as R3.
 unfold SCdata,V293_exit_ready_body_data,V293_exit_ready_body_core,JBenv,
 V293_exit_ready_body_bindings,V293_handoff_byte,V293_time_cell,V293_time_binding,
 V293_counter_cell,SCcontrol_owned,V293_exit_cells,V293_interrupt_cells in *.
 cbn[V293_owned_record_cells V293_owned_record_cell skipn SCcontrols V293_rdy_raw_cells V293_storage]in *.
 assert(RowOpen:V293_array true 80%positive 0 1 Tint8(map V293_byteval [16;0]) =
 (Amapsto(80%positive,0%Z)Tint8 true(V293_byteval 16) **
 (Amapsto(80%positive,1%Z)Tint8 true(V293_byteval 0) ** Aemp)))by reflexivity.
 unfold V293_inputs_full;rewrite RowOpen;clear -R3;sep auto.
Qed.


Definition SCkept:=
 V293_shared_fields OwnershipReady OwnershipTasks(emp:EcbMod.map)Int.zero **
 (V293_prefix_output V293_tcb_type 93%positive(Vptr OwnershipReady) **
 (PV(91%positive,Int.zero)@Tint8|->V293_byteval 88 **
 (PV(95%positive,Int.zero)@Tint32|->Vint32 Int.zero **
 (V293_owned_task_records OwnershipTasks **
 (V293_storage nil **
 (V293_sched_globals 100%Z 101%Z 102%Z 103%Z 92%positive 81%positive 80%positive 91%positive ** RBglobals)))))).
Definition SCraw:=
 GV OSTCBCur@(Tptr V293_tcb_type)|->Vptr OwnershipReady **
 (SCkept **
 (V293_same_irq_read_full 92%positive 81%positive 80%positive 82%positive 94%positive 99%positive 16 0 4 RTentries **
 (Amapsto(96%positive,0%Z)Tint8 true(V293_byteval 0) **
 Amapsto(97%positive,0%Z)Tint8 true(V293_byteval 0)))).
Definition SCentry:=V293_same_irq_snapshot
 100%Z 101%Z 102%Z 103%Z 105%Z 106%Z 108%Z 109%Z 112%Z 110%Z 111%Z
 92%positive 81%positive 80%positive 91%positive 82%positive 93%positive 94%positive 95%positive
 99%positive 96%positive 97%positive nil 16 0 4 RTentries OwnershipTasks emp Int.zero
 (V293_byteval 88)(Vptr OwnershipReady)Int.zero 0(spec_done None)
 (isrupd(fun _:hid=>false)0 true)[0]OwnershipReady.
Definition SCirq_state M O:RstateOP:=(JBge,emp,M,isrupd(fun _:hid=>false)0 true,
 (false,[0],nil),O,spec_done None).
Lemma SCraw_good : GoodInvAsrt SCraw /\ GoodFrm SCraw.
Proof.
 assert(A:GoodInvAsrt(V293_array true 82%positive 0 4(Tptr V293_tcb_type)RTentries)).
 { unfold RTentries;cbn[V293_array GoodInvAsrt];tauto. }
 assert(F:GoodFrm(V293_array true 82%positive 0 4(Tptr V293_tcb_type)RTentries))by(apply V293_array_good).
 assert(O:GoodInvAsrt(V293_owned_task_records OwnershipTasks)).
 { unfold V293_owned_task_records;apply V293_task_list_good. }
 assert(OF:GoodFrm(V293_owned_task_records OwnershipTasks))by(apply V293_owned_tasks_frame).
 unfold SCraw,SCkept,RBglobals,V293_same_irq_read_full,V293_prefix_output,
 V293_shared_fields,V293_inputs_full,V293_exit_builder_globals,V293_sched_globals,
 Agvarmapsto,Agvarenv',Aptrmapsto.
 split;[cbn[GoodInvAsrt]|cbn[GoodFrm]];repeat split;try exact Logic.I;assumption.
Qed.
Lemma SCraw_heap : SCstate(SCmemory 0 Int.zero Int.zero)nil(spec_done None)|=SCraw ** Atrue.
Proof.
 pose proof(SCheap_data 0 Int.zero Int.zero nil(spec_done None)ltac:(lia))as Entry.
 assert(H:SCstate(SCmemory 0 Int.zero Int.zero)nil(spec_done None)|=RBglobals **
 (<||spec_done None||> ** OS[(fun _:hid=>false),false,nil,nil] ** SCdata 0 Int.zero Int.zero)).
 { unfold SCstate;eapply JBstar with(m1:=emp)(o1:=emp).
   - apply map_join_comm;apply map_join_emp.
   - apply map_join_comm;apply map_join_emp.
   - apply RBglobals_owned.
   - exact Entry. }
 unfold SCraw,SCkept,SCdata,RBglobals,V293_exit_ready_body_data,V293_exit_ready_body_core,
 V293_handoff_byte,V293_counter_cell,V293_time_cell,V293_time_binding,
 V293_exit_ready_body_bindings,V293_exit_builder_globals,V293_prefix_bindings,
 V293_prefix_output,V293_handoff_binding,V293_counter_bindings,Agvarmapsto,Agvarenv',Aptrmapsto,
 V293OSIntExitHoare.V293_exit_cells,V293OSIntEnterInternal.V293_interrupt_cells,
 V293_same_irq_read_full in *;cbn[V293_rdy_raw_cells addrval_to_addr]in *.
 clear Entry;sep normal in H;destruct H as[bcur[btarget H]].
 assert(bcur=1%positive /\ btarget=93%positive).
 { assert(B:SCstate(SCmemory 0 Int.zero Int.zero)nil(spec_done None)|=
   Agvarenv OSTCBCur(Tptr V293_tcb_type)(bcur,0%Z) **
   (Agvarenv 106%Z(Tptr V293_tcb_type)(btarget,0%Z) ** Atrue)).
   { rewrite Int.unsigned_zero in H;sep auto. }
   apply astar_l_agvarenv_elim in B;destruct B as[BC B].
   apply astar_l_agvarenv_elim in B;destruct B as[BT B].
   vm_compute in BC,BT;destruct BC as[_ BC];destruct BT as[_ BT];split;congruence. }
 destruct H0;subst;sep auto.

Qed.
Theorem SCentry_nonempty : exists M Mf O Of,
 join M Mf(SCmemory 0 Int.zero Int.zero) /\ join O Of(RIabstract OwnershipReady) /\
 SCirq_state M O|=SCentry.
Proof.
 pose proof SCraw_heap as H;unfold SCstate in H.
 assert(Moved:(JBge,emp,SCmemory 0 Int.zero Int.zero,(fun _:hid=>false),
 (false,nil,nil),RIabstract OwnershipReady,spec_done None)|=SCraw ** Atrue).
 { eapply good_inv_prop;[split;[exact(proj1 SCraw_good)|exact Logic.I]|exact H]. }
 assert(New:SCirq_state(SCmemory 0 Int.zero Int.zero)(RIabstract OwnershipReady)|=SCraw ** Atrue).
 { unfold SCirq_state;eapply goodfrm_prop;[split;[exact(proj2 SCraw_good)|exact Logic.I]|exact Moved]. }
 apply sat_split in New;destruct New as(M&Mf&O&Of&JM&JO&Owned&Extra).
 exists M;exists Mf;exists O;exists Of;split;[exact JM| ];split;[exact JO| ].
 unfold SCraw in Owned;eapply astar_mono in Owned;[ |apply GV_separate_rw|intros s K;exact K].
 apply astar_l_adomlenv_intro with(d:=nil)in Owned.
 2:{ intros x tau;split;[contradiction|intros[l E];discriminate]. }
 apply astar_l_aisr_intro with(i:=isrupd(fun _:hid=>false)0 true)in Owned;[ |reflexivity].
 apply astar_l_aie_intro with(i:=false)in Owned;[ |reflexivity].
 apply astar_l_ais_intro with(i:=[0])in Owned;[ |reflexivity].
 apply astar_l_acs_intro with(i:=nil)in Owned;[ |reflexivity].
 apply astar_l_aop'_intro with(aop:=spec_done None)in Owned;[ |reflexivity].
 unfold SCentry,V293_same_irq_snapshot,V293_same_irq_physical,V293_same_irq_payload,
 SCkept,p_local,LINV,V293_shared_li,CurTid in *;clear H Moved Extra;sep auto;
 apply V293_switch_li_good.
Qed.
Theorem SCvalid : V293_same_exit_valid (0::nil)
 (V293_same_irq_index 16 0 4 RTentries OwnershipTasks(Vptr OwnershipReady)Int.zero(spec_done None)).
Proof.
 destruct RTliteral_rel as[Lo[Hi[Ready[Bitmap Table]]]].
 unfold V293_same_exit_valid,V293_same_irq_index,V293_exit_snapshot_bounded.
 cbn[V293_xlo V293_xhi V293_xcurrent V293_xnest V293_xlocked V293_xcounter V293_xold V293_xentries V293_xtasks V293_xaop].
 split;[unfold gettopis,INUM;cbn;lia| ].
 split;[repeat split;lia| ];split;[lia| ];split;[reflexivity| ].
 split;[exact Ready| ];split;[exact Bitmap| ];split;[exact Table|reflexivity].
Qed.
Theorem SCenvironment : GoodI RDinv V293_scheduler V293_shared_li /\
 WFFunEnv RDprogram QCspec V293_scheduler V293_shared_li RDinv /\
 WFIFun RDprogram QCspec V293_scheduler RDinv V293_shared_li.
Proof. exact QCenvironment. Qed.
Theorem SCactual_wrapper : forall ret,
 Some ret=BuildintRet 0 QCintspec(fun _:hid=>false)nil RDinv V293_shared_li OwnershipReady nil ->
 InfRules QCspec V293_scheduler V293_shared_li RDinv arfalse ret
 SCentry(V293_irq_source_wrapper 301%Z 300%Z Int.zero)Afalse OwnershipReady.
Proof.
 intros ret Ret;unfold SCentry;apply(V293_interrupt_same_continuous
 100%Z 101%Z 102%Z 103%Z 105%Z 106%Z 108%Z 109%Z 112%Z 110%Z 111%Z
 92%positive 81%positive 80%positive 91%positive 82%positive 93%positive 94%positive 95%positive
 99%positive 96%positive 97%positive nil 16 0 4 RTentries OwnershipTasks emp Int.zero
 (V293_byteval 88)(Vptr OwnershipReady)Int.zero QCspec 301%Z 300%Z QCintspec 0(fun _:hid=>false)nil
 OwnershipReady ret Int.zero);try assumption;try reflexivity;
 try(unfold QCspec,V293_open_exact_irq_spec;reflexivity).
 - exact SCvalid.
 - vm_compute;repeat constructor.
 - unfold INUM;rewrite Int.unsigned_zero;cbn;lia.
Qed.
Theorem SCreturn_builder_exists : exists ret,
 Some ret=BuildintRet 0 QCintspec(fun _:hid=>false)nil RDinv V293_shared_li OwnershipReady nil.
Proof. eexists;reflexivity. Qed.
