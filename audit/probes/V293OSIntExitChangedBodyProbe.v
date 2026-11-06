(* Concrete full-body entry from independent bytes; no initialization claim. *)
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
Import ListNotations.
Local Open Scope nat_scope.
Definition CXge:=set(set(set DXge 114%Z(13%positive,Tint8))115%Z(14%positive,Tint8))116%Z(15%positive,Tint8).
Definition CXle:=set emp 117%Z(16%positive,Tint32).
Lemma CXprefix_inputs : forall ge le,
  V293_wstate ge le V293_storage_prefix_inputs_memory |=
    V293_inputs_full 1%positive 2%positive 3%positive 0 16.
Proof.
  intros ge le. assert (HS : V293_wstate ge le V293_storage_prefix_inputs_memory |=
    V293_array true 1%positive 0 1 Tint8 (map V293_byteval V293_ready_table) **
      (V293_array true 3%positive 0 1 Tint8 (map V293_byteval [0;16]) **
        Amapsto (2%positive, 0%Z) Tint8 true (V293_byteval 2))).
  { eapply V293_wstate_star.
    - apply map_join_merge. apply map_disjoint. intros [b i].
      destruct (Pos.eq_dec b 1%positive); [subst b; right; left | left]; V293_storage_prefix_outside.
    - apply V293_full_array_witness.
    - eapply V293_wstate_star.
      + apply map_join_merge. apply map_disjoint. intros [b i].
        destruct (Pos.eq_dec b 3%positive); [subst b; right; left | left]; V293_storage_prefix_outside.
      + apply V293_full_array_witness.
      + split; [apply V293_encoded_memory_mapsto | reflexivity]. }
  unfold V293_inputs_full. change (V293_ready_group 0 16) with 2. sep auto.
Qed.
Lemma CXprefix_local : forall ge le different,
  V293_wstate ge le (V293_storage_prefix_local_memory different) |=
    (PV (4%positive, Int.zero) @ Tint8 |-> (V293_byteval 0)) **
      V293_array true 8%positive 0 4 (Tptr Tvoid) (V293_current_mode_entries different).
Proof.
  intros ge le different. eapply V293_wstate_star.
  - apply map_join_merge. apply map_disjoint. intros [b i].
    destruct (Pos.eq_dec b 4%positive); [subst b; right; left | left]; V293_storage_prefix_outside.
  - split; [apply V293_encoded_memory_mapsto | reflexivity].
  - apply V293_full_array_witness.
Qed.
Lemma CXprefix_pointer : forall ge le x b t,
  get ge x = Some (b, Tptr Tvoid) ->
  V293_wstate ge le
    (V293_encoded_memory b 0 true (encode_val (Tptr Tvoid) (Vptr t))) |=
    GV x @ (Tptr Tvoid) |-> (Vptr t).
Proof.
  intros ge le x b t HG. exists b. eapply V293_wstate_star with (m1 := emp).
  - apply map_join_comm. apply map_join_emp.
  - exists b. split; [exact HG | ]. repeat split; reflexivity.
  - split; [apply V293_encoded_memory_mapsto | reflexivity].
Qed.
Lemma CXprefix_shared : forall ge le,
  get ge OSTCBCur = Some (6%positive, Tptr Tvoid) ->
  get ge 107%Z = Some (10%positive, Tptr Tvoid) ->
  V293_wstate ge le V293_storage_prefix_shared_memory |=
    (GV OSTCBCur @ (Tptr Tvoid) |-> (Vptr V293_idle_tid)) **
      (GV 107%Z @ (Tptr Tvoid) |-> (Vptr V293_idle_tid)).
Proof.
  intros ge le Hcur Htarget. eapply V293_wstate_star.
  - apply map_join_merge. apply map_disjoint. intros [b i].
    destruct (Pos.eq_dec b 6%positive); [subst b; right; left | left]; V293_storage_prefix_outside.
  - apply CXprefix_pointer; assumption.
  - apply CXprefix_pointer; assumption.
Qed.
Lemma CXprefix_physical : forall ge le different,
  get ge OSTCBCur = Some (6%positive, Tptr Tvoid) ->
  get ge 107%Z = Some (10%positive, Tptr Tvoid) ->
  V293_wstate ge le (V293_storage_prefix_memory different) |=
    V293_inputs_full 1%positive 2%positive 3%positive 0 16 **
      (((PV (4%positive, Int.zero) @ Tint8 |-> (V293_byteval 0)) **
        V293_array true 8%positive 0 4 (Tptr Tvoid) (V293_current_mode_entries different)) **
        ((GV OSTCBCur @ (Tptr Tvoid) |-> (Vptr V293_idle_tid)) **
          (GV 107%Z @ (Tptr Tvoid) |-> (Vptr V293_idle_tid)))).
Proof.
  intros ge le different Hcur Htarget. eapply V293_wstate_star.
  - apply map_join_merge. apply map_disjoint. intros [b i].
    destruct (Pos.eq_dec b 1%positive); [subst b; right; left; V293_storage_prefix_outside | ].
    destruct (Pos.eq_dec b 2%positive); [subst b; right; left; V293_storage_prefix_outside | ].
    destruct (Pos.eq_dec b 3%positive); [subst b; right; left; V293_storage_prefix_outside | ].
    left. V293_storage_prefix_outside.
  - apply CXprefix_inputs.
  - eapply V293_wstate_star.
    + apply map_join_merge. apply map_disjoint. intros [b i].
      destruct (Pos.eq_dec b 4%positive); [subst b; right; left; V293_storage_prefix_outside | ].
      destruct (Pos.eq_dec b 8%positive); [subst b; right; left; V293_storage_prefix_outside | ].
      left. V293_storage_prefix_outside.
    + apply CXprefix_local.
    + apply CXprefix_shared; assumption.
Qed.

Lemma CXbyte_owned : forall n,
 V293_wstate CXge CXle(DXbyte n)|=V293_handoff_byte 113%Z 11%positive n.
Proof.
 intro n;unfold V293_handoff_byte,V293_handoff_binding.
 eapply V293_wstate_star with(m1:=emp).
 - apply map_join_comm;apply map_join_emp.
 - split.
   + exists 11%positive;split;[vm_compute;reflexivity|repeat split;reflexivity].
   + split;[intros[v E];discriminate|repeat split;reflexivity].
 - split;[apply V293_encoded_memory_mapsto|reflexivity].
Qed.
Lemma CXextra_owned : forall n c,V293_wstate CXge CXle(DXextra n c)|=DXowned n c.
Proof.
 intros n c;eapply V293_wstate_star.
 - apply map_join_merge;apply map_disjoint;intros[b i].
   destruct(Pos.eq_dec b 11%positive)as[E|E].
   + subst b;right;left;apply V293_encoded_memory_outside;left;discriminate.
   + left;apply V293_encoded_memory_outside;left;exact E.
 - apply CXbyte_owned.
 - unfold V293_counter_cell,V293_counter_bindings.
   eapply V293_wstate_star with(m1:=emp).
   + apply map_join_comm;apply map_join_emp.
   + split.
     * exists 12%positive;split;[vm_compute;reflexivity|repeat split;reflexivity].
     * split;[intros[v E];vm_compute in E;discriminate|repeat split;reflexivity].
   + split;[apply V293_encoded_memory_mapsto|reflexivity].
Qed.
Lemma CXphysical_owned : forall n c,
 V293_wstate CXge CXle(DXmemory n c)|=DXphysical ** DXowned n c.
Proof.
 intros n c;eapply V293_wstate_star.
 - apply map_join_merge;apply map_disjoint;intros[b i].
   destruct(Pos.eq_dec b 11%positive)as[E|E].
   + subst b;left;unfold V293_storage_prefix_memory;V293_storage_prefix_outside.
   + destruct(Pos.eq_dec b 12%positive)as[F|F].
     * subst b;left;unfold V293_storage_prefix_memory;V293_storage_prefix_outside.
     * right;left;unfold DXextra,DXbyte,V293_counter_memory.
       rewrite map_merge_semp by reflexivity.
       repeat rewrite V293_encoded_memory_outside by(left;congruence);reflexivity.
 - apply CXprefix_physical;vm_compute;reflexivity.
 - apply CXextra_owned.
Qed.
Definition CXcontrols nest old:=
 merge(V293_encoded_memory 13%positive 0 true(encode_val Tint8(V293_byteval 1)))
 (merge(V293_encoded_memory 14%positive 0 true(encode_val Tint8(V293_byteval nest)))
 (merge(V293_encoded_memory 15%positive 0 true(encode_val Tint8(V293_byteval 0)))
 (V293_counter_memory 16%positive old))).
Definition CXcontrol_owned nest old:=
 Amapsto(13%positive,0%Z)Tint8 true(V293_byteval 1) **
 (Amapsto(14%positive,0%Z)Tint8 true(V293_byteval nest) **
 (Amapsto(15%positive,0%Z)Tint8 true(V293_byteval 0) **
 (PV(16%positive,Int.zero)@Tint32|->Vint32 old))).
Ltac CXcontrols_outside:=unfold CXcontrols,V293_counter_memory;
 repeat rewrite map_merge_semp by reflexivity;
 repeat rewrite V293_encoded_memory_outside by(left;congruence);reflexivity.
Lemma CXcontrols_witness : forall nest old,
 V293_wstate CXge CXle(CXcontrols nest old)|=CXcontrol_owned nest old.
Proof.
 intros;unfold CXcontrol_owned,CXcontrols.
 eapply V293_wstate_star.
 - apply map_join_merge;apply map_disjoint;intros[b i].
   destruct(Pos.eq_dec b 13%positive);[subst b;right;left|left];CXcontrols_outside.
 - split;[apply V293_encoded_memory_mapsto|reflexivity].
 - eapply V293_wstate_star.
   + apply map_join_merge;apply map_disjoint;intros[b i].
     destruct(Pos.eq_dec b 14%positive);[subst b;right;left|left];CXcontrols_outside.
   + split;[apply V293_encoded_memory_mapsto|reflexivity].
   + eapply V293_wstate_star.
     * apply map_join_merge;apply map_disjoint;intros[b i].
       destruct(Pos.eq_dec b 15%positive);[subst b;right;left|left];CXcontrols_outside.
     * split;[apply V293_encoded_memory_mapsto|reflexivity].
     * split;[apply V293_encoded_memory_mapsto|reflexivity].
Qed.
Definition CXmemory nest c old:=merge(DXmemory 4 c)(CXcontrols nest old).
Lemma CXphysical_all : forall nest c old,
 V293_wstate CXge CXle(CXmemory nest c old)|=
 (DXphysical ** DXowned 4 c) ** CXcontrol_owned nest old.
Proof.
 intros;eapply V293_wstate_star.
 - apply map_join_merge;apply map_disjoint;intros[b i].
   destruct(Pos.eq_dec b 13%positive)as[E|E];[subst b;left;unfold DXmemory,DXextra,DXbyte,V293_counter_memory;
    repeat rewrite map_merge_semp by reflexivity;unfold V293_storage_prefix_memory;
    V293_storage_prefix_outside| ].
   destruct(Pos.eq_dec b 14%positive)as[F|F];[subst b;left;unfold DXmemory,DXextra,DXbyte,V293_counter_memory;
    repeat rewrite map_merge_semp by reflexivity;unfold V293_storage_prefix_memory;
    V293_storage_prefix_outside| ].
   destruct(Pos.eq_dec b 15%positive)as[G|G];[subst b;left;unfold DXmemory,DXextra,DXbyte,V293_counter_memory;
    repeat rewrite map_merge_semp by reflexivity;unfold V293_storage_prefix_memory;
    V293_storage_prefix_outside| ].
   destruct(Pos.eq_dec b 16%positive)as[J|J];[subst b;left;unfold DXmemory,DXextra,DXbyte,V293_counter_memory;
    repeat rewrite map_merge_semp by reflexivity;unfold V293_storage_prefix_memory;
    V293_storage_prefix_outside| ].
   right;left;CXcontrols_outside.
 - apply CXphysical_owned.
 - apply CXcontrols_witness.
Qed.
Definition CXenv:=
 V293_sched_globals 100%Z 101%Z 102%Z 103%Z 1%positive 2%positive 3%positive 4%positive **
 (V293_prefix_bindings 106%Z 103%Z 107%Z Tvoid 8%positive 10%positive **
 (V293_handoff_binding 103%Z 4%positive **
 (V293_exit_changed_bindings 115%Z 116%Z 14%positive 15%positive **
 (V293_handoff_binding 114%Z 13%positive ** Alvarenv 117%Z Tint32(16%positive,0%Z))))).
Lemma CXenv_owned : V293_target_wstate CXge CXle emp emp|=CXenv.
Proof.
 unfold CXenv,V293_exit_changed_bindings.
 repeat(eapply V293_target_wstate_star with(m1:=emp)(m2:=emp)(o1:=emp)(o2:=emp);
 [apply map_join_emp|apply map_join_emp| | ]).
 - unfold V293_sched_globals;repeat split.
   + exists 1%positive;split;[vm_compute;reflexivity|repeat split;reflexivity].
   + exists 2%positive;split;[vm_compute;reflexivity|repeat split;reflexivity].
   + exists 3%positive;split;[vm_compute;reflexivity|repeat split;reflexivity].
   + exists 4%positive;split;[vm_compute;reflexivity|repeat split;reflexivity].
 - unfold V293_prefix_bindings;repeat split.
   + exists 8%positive;split;[vm_compute;reflexivity|repeat split;reflexivity].
   + exists 10%positive;split;[vm_compute;reflexivity|repeat split;reflexivity].
   + intros[v H];vm_compute in H;discriminate.
   + intros[v H];vm_compute in H;discriminate.
   + intros[v H];vm_compute in H;discriminate.
 - unfold V293_handoff_binding;split.
   + exists 4%positive;split;[vm_compute;reflexivity|repeat split;reflexivity].
   + split;[intros[v H];vm_compute in H;discriminate|repeat split;reflexivity].
 - unfold V293_handoff_binding;split.
   + exists 14%positive;split;[vm_compute;reflexivity|repeat split;reflexivity].
   + split;[intros[v H];vm_compute in H;discriminate|repeat split;reflexivity].
 - unfold V293_handoff_binding;split.
   + exists 15%positive;split;[vm_compute;reflexivity|repeat split;reflexivity].
   + split;[intros[v H];vm_compute in H;discriminate|repeat split;reflexivity].
 - unfold V293_handoff_binding;split.
   + exists 13%positive;split;[vm_compute;reflexivity|repeat split;reflexivity].
   + split;[intros[v H];vm_compute in H;discriminate|repeat split;reflexivity].
 - exists 16%positive;split;[vm_compute;reflexivity|repeat split;reflexivity].
Qed.
Definition CXdata nest c old:=V293_exit_changed_data
 100%Z 101%Z 102%Z 103%Z 106%Z 107%Z 113%Z 111%Z 114%Z 115%Z 116%Z 117%Z
 1%positive 2%positive 3%positive 4%positive 8%positive 10%positive 11%positive 12%positive
 13%positive 14%positive 15%positive 16%positive Tvoid 0 16 4(V293_current_mode_entries true)nil
 V293_idle_tid(V293_current_mode_tasks true)emp Int.zero Aemp nest(V293_byteval 0)(Vptr V293_idle_tid)c(Vint32 old).
Definition CXresources nest c old:=CXenv **
 (((DXphysical ** DXowned 4 c) ** CXcontrol_owned nest old) **
 V293_shared_fields V293_idle_tid(V293_current_mode_tasks true)emp Int.zero).
Lemma CXresources_owned : forall nest c old,
 V293_target_wstate CXge CXle(CXmemory nest c old)
 (V293_shared_fixture_abs V293_idle_tid(V293_current_mode_tasks true)emp Int.zero)|=CXresources nest c old.
Proof.
 intros;unfold CXresources.
 eapply V293_target_wstate_star with(m1:=emp)(o1:=emp).
 - apply map_join_comm;apply map_join_emp.
 - apply map_join_comm;apply map_join_emp.
 - apply CXenv_owned.
 - eapply V293_target_wstate_star with(m2:=emp)(o1:=emp).
   + apply map_join_emp.
   + apply map_join_comm;apply map_join_emp.
   + apply CXphysical_all.
   + unfold V293_shared_fixture_abs,V293_shared_fields.
     repeat(eapply V293_target_wstate_star;[apply map_join_emp|apply map_join_merge;
      apply map_disjoint;intros key;destruct key;simpl;auto|split;reflexivity| ]).
     split;reflexivity.
Qed.
Lemma CXresources_aop_free : forall nest c old,can_change_aop(CXresources nest c old).
Proof.
 intros;unfold CXresources,CXenv,DXphysical,DXowned,CXcontrol_owned,
 V293_exit_changed_bindings,V293_handoff_byte,V293_handoff_binding,V293_counter_cell,
 V293_counter_bindings,V293_sched_globals,V293_prefix_bindings,V293_shared_fields,
 V293_inputs_full,Agvarmapsto,Aptrmapsto.
 cbn[can_change_aop];repeat split;try exact I;apply V293_array_aop_independent.
Qed.
Definition CXstate nest c old aop:RstateOP:=
 (CXge,CXle,CXmemory nest c old,(fun _:hid=>false),(false,nil,nil),
 V293_shared_fixture_abs V293_idle_tid(V293_current_mode_tasks true)emp Int.zero,sched;;aop).
Definition CXpre nest c old aop:=<||sched;;aop||> **
 OS[(fun _:hid=>false),false,nil,nil] ** CXdata nest c old.
Lemma CXpre_owned : forall nest c old aop,CXstate nest c old aop|=CXpre nest c old aop.
Proof.
 intros;pose proof(CXresources_owned nest c old)as H.
 pose proof(@change_aop_rule _ _ _(sched;;aop)_ H(CXresources_aop_free nest c old))as Held.
 change(CXstate nest c old aop|=CXresources nest c old)in Held.
 unfold CXpre;apply astar_l_aop'_intro with(aop:=sched;;aop);[ |reflexivity].
 assert(C:CXstate nest c old aop|=Aisr(fun _:hid=>false) **
 (Aie false ** (Ais nil ** (Acs nil ** CXresources nest c old)))).
 { apply astar_l_aisr_intro;[apply astar_l_aie_intro;[apply astar_l_ais_intro;
   [apply astar_l_acs_intro;[exact Held|reflexivity]|reflexivity]|reflexivity]|reflexivity]. }
 unfold CXdata,V293_exit_changed_data,V293_exit_changed_core,V293_exit_changed_bindings,
 V293_time_cell,V293_time_binding,CXresources,CXenv,DXphysical,DXowned,CXcontrol_owned,
 V293_handoff_byte,V293_exit_cells,V293_interrupt_cells in *;
 cbn[V293_rdy_raw_cells V293_storage]in *;unfold V293_exit_changed_bindings in *;clear -C;sep auto.
Qed.
Theorem CXentry_nonempty : forall c old aop,exists s,
 s|=CXpre 1 c old aop /\
 V293_highest_ready(V293_current_mode_tasks true)(V293_switch_target true) /\
 V293_switch_target true<>V293_idle_tid.
Proof.
 intros;exists(CXstate 1 c old aop);split;[apply CXpre_owned| ].
 split;[exact(V293_shared_case_highest true)|vm_compute;discriminate].
Qed.
Theorem CXzero_max_entry : forall old aop,exists s,
 s|=CXpre 0(Int.repr Int.max_unsigned)old aop.
Proof. intros;exists(CXstate 0(Int.repr Int.max_unsigned)old aop);apply CXpre_owned. Qed.
Definition CXcells:=((12%positive,0%Z),Tint32)::((4%positive,0%Z),Tint8)::
 ((11%positive,0%Z),Tint8)::(V293_input_cells 1%positive 2%positive 3%positive ++
 V293_array_cells 8%positive 0 4(Tptr Tvoid)(length(V293_current_mode_entries true)) ++
 [((13%positive,0%Z),Tint8);((14%positive,0%Z),Tint8);((15%positive,0%Z),Tint8)]).
Definition CXpost aop:=V293_exit_changed_resumed
 100%Z 101%Z 102%Z 103%Z 106%Z 107%Z 113%Z 111%Z 114%Z 115%Z 116%Z 117%Z
 1%positive 2%positive 3%positive 4%positive 8%positive 10%positive 11%positive 12%positive
 13%positive 14%positive 15%positive 16%positive Tvoid(V293_current_mode_entries true)nil
 V293_idle_tid aop nil Aemp nil.
Theorem CXactual_body : forall Spec sched_id nest c old aop,
 nest<=1 ->Spec sched_id=Some
 (V293_critical_fpre 100%Z 101%Z 102%Z 103%Z 1%positive 2%positive 3%positive 4%positive
 V293_shared_li V293_opened_inv V293_switch_li_good,
 V293_critical_fpost 100%Z 101%Z 102%Z 103%Z 1%positive 2%positive 3%positive 4%positive
 V293_shared_li V293_opened_inv V293_switch_li_good,(Tvoid,nil)) ->
 InfRules Spec V293_scheduler V293_shared_li(V293_storage_inv CXcells 107%Z Tvoid)
 (fun v=>[|v=None|] ** CXpost aop)Afalse(CXpre nest c old aop)
 (V293_exit_boundary_body 114%Z 115%Z 116%Z 117%Z 106%Z 103%Z 107%Z 113%Z 111%Z sched_id
 (V293_interrupt_handoff 103%Z 113%Z 107%Z))Afalse V293_idle_tid.
Proof.
 intros;unfold CXcells,CXpost,CXpre,CXdata;apply V293_OSIntExit_changed_body;try lia.
 - exists 12;vm_compute;intuition lia.
 - vm_compute;discriminate.
 - exact(proj1(V293_current_mode_relations true)).
 - exact(proj1(proj2(V293_current_mode_relations true))).
 - vm_compute;repeat constructor.
 - exists(Int.repr 4,wait os_stat_time Int.one,Vnull);vm_compute;reflexivity.
 - exact I.
 - assumption.
Qed.
(* Only the final excrit is neutralized; this is a primitive-tail control,
   not two complete scheduler/function executions. *)
Theorem CXexcrit_control : forall P ks ge le M ir si ci aop,
 loststep P(curs(sprim excrit),(kenil,ks))((ge,le,M),ir,(false,si,false::ci))
 (curs(sskip None),(kenil,ks))((ge,le,M),ir,(false,si,ci)) /\
 ~((ge,le,M,ir,(false,si,false::ci),emp,aop)|=Acs ci ** Atrue).
Proof.
 intros;split;[apply excrit_step;reflexivity| ].
 intro H;apply astar_l_acs_elim in H as[E _].
 change(false::ci=ci)in E;apply(f_equal(@length bool))in E;cbn in E;lia.
Qed.
