(* Independent bytes plus shared tables for the actual dispatch entry.
   This is not initialization reachability or a resumption execution trace. *)
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitDispatchHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitHandoffHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitBoundarySwitch.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedStoragePrefix.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedStoragePrefixWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedStorageTail.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedPrefix.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedPrefixWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTargetWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCurrentWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedChangeWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedChange.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedSwitch.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedSwitchWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCritical.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedShared.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293SharedStateWitness.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchStorage.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchState.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.certiucos.v293.code.V293ReadyTable.
Require Import CertiOS.certiucos.v293.code.V293OSSchedChange.
Require Import CertiOS.audit.probes.V293OSIntExitBoundarySwitchProbe.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.auxdef.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.sep_combine_lemmas.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.
Definition DXge:=set(set V293_prefix_fixture_ge 113%Z(11%positive,Tint8))111%Z(12%positive,Tint32).
Definition DXbyte n:=V293_encoded_memory 11%positive 0 true(encode_val Tint8(V293_byteval n)).
Definition DXextra n c:=merge(DXbyte n)(V293_counter_memory 12%positive c).
Definition DXowned n c:=V293_handoff_byte 113%Z 11%positive n ** V293_counter_cell 111%Z 12%positive c.
Definition DXphysical:=V293_inputs_full 1%positive 2%positive 3%positive 0 16 **
 (((PV(4%positive,Int.zero)@Tint8|->V293_byteval 0) **
 V293_array true 8%positive 0 4(Tptr Tvoid)(V293_current_mode_entries true)) **
 ((GV OSTCBCur@(Tptr Tvoid)|->Vptr V293_idle_tid) **
 (GV 107%Z@(Tptr Tvoid)|->Vptr V293_idle_tid))).
Definition DXempty:=V293_shared_flags ** ((Ais nil ** Acs nil) **
 ((V293_sched_globals 100%Z 101%Z 102%Z 103%Z 1%positive 2%positive 3%positive 4%positive **
 V293_prefix_bindings 106%Z 103%Z 107%Z Tvoid 8%positive 10%positive) **
 (V293_handoff_binding 103%Z 4%positive ** Aemp))).
Definition DXmemory n c:=merge(V293_storage_prefix_memory true)(DXextra n c).
Definition DXresources n c events now:=DXempty **
 (DXphysical ** (DXowned n c ** V293_shared_fields V293_idle_tid(V293_current_mode_tasks true)events now)).
Definition DXentry c events now aop:=
 V293_exit_dispatch_entry 100%Z 101%Z 102%Z 103%Z 106%Z 107%Z 113%Z 111%Z
 1%positive 2%positive 3%positive 4%positive 8%positive 10%positive 11%positive 12%positive
 Tvoid 0 16 4(V293_current_mode_entries true)nil V293_idle_tid(V293_current_mode_tasks true)
 events now aop nil nil Aemp(Vptr V293_idle_tid)c.
Lemma DXbyte_owned : forall n,
 V293_wstate DXge emp(DXbyte n)|=V293_handoff_byte 113%Z 11%positive n.
Proof.
 intro n;unfold V293_handoff_byte,V293_handoff_binding.
 eapply V293_wstate_star with(m1:=emp).
 - apply map_join_comm;apply map_join_emp.
 - split.
   + exists 11%positive;split;[vm_compute;reflexivity|repeat split;reflexivity].
   + split;[intros[v E];discriminate|repeat split;reflexivity].
 - split;[apply V293_encoded_memory_mapsto|reflexivity].
Qed.
Lemma DXextra_owned : forall n c,V293_wstate DXge emp(DXextra n c)|=DXowned n c.
Proof.
 intros n c;eapply V293_wstate_star.
 - apply map_join_merge;apply map_disjoint;intros[b i].
   destruct(Pos.eq_dec b 11%positive)as[E|E].
   + subst b;right;left;apply V293_encoded_memory_outside;left;discriminate.
   + left;apply V293_encoded_memory_outside;left;exact E.
 - apply DXbyte_owned.
 - apply V293_counter_cell_witness;vm_compute;reflexivity.
Qed.
Lemma DXphysical_owned : forall n c,
 V293_wstate DXge emp(DXmemory n c)|=DXphysical ** DXowned n c.
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
 - apply V293_storage_prefix_physical_witness;vm_compute;reflexivity.
 - apply DXextra_owned.
Qed.
Lemma DXempty_owned : V293_target_wstate DXge emp emp emp|=DXempty.
Proof.
 unfold DXempty,V293_shared_flags.
 repeat(eapply V293_target_wstate_star with(m1:=emp)(m2:=emp)(o1:=emp)(o2:=emp);
 [apply map_join_emp|apply map_join_emp| | ]).
 - exists(fun _:hid=>false);split;repeat split;reflexivity.
 - repeat split;reflexivity.
 - exists INUM;repeat split;reflexivity.
 - repeat split;reflexivity.
 - repeat split;reflexivity.
 - apply V293_prefix_fixture_globals;vm_compute;reflexivity.
 - unfold V293_prefix_bindings;repeat split.
   + exists 8%positive;split;[vm_compute;reflexivity|repeat split;reflexivity].
   + exists 10%positive;split;[vm_compute;reflexivity|repeat split;reflexivity].
   + intros[v H];discriminate.
   + intros[v H];discriminate.
   + intros[v H];discriminate.
 - unfold V293_handoff_binding;repeat split.
   + exists 4%positive;split;[vm_compute;reflexivity|repeat split;reflexivity].
   + intros[v H];discriminate.
 - split;reflexivity.
Qed.
Lemma DXresources_owned : forall n c events now,
 V293_target_wstate DXge emp(DXmemory n c)
 (V293_shared_fixture_abs V293_idle_tid(V293_current_mode_tasks true)events now)|=DXresources n c events now.
Proof.
 intros n c events now;unfold DXresources.
 eapply V293_target_wstate_star with(m1:=emp)(o1:=emp).
 - apply map_join_comm;apply map_join_emp.
 - apply map_join_comm;apply map_join_emp.
 - apply DXempty_owned.
 - assert(P:V293_target_wstate DXge emp(DXmemory n c)
   (V293_shared_fixture_abs V293_idle_tid(V293_current_mode_tasks true)events now)|=
   (DXphysical ** DXowned n c) ** V293_shared_fields V293_idle_tid(V293_current_mode_tasks true)events now).
   { eapply V293_target_wstate_star with(m2:=emp)(o1:=emp).
     - apply map_join_emp.
     - apply map_join_comm;apply map_join_emp.
     - apply DXphysical_owned.
     - unfold V293_shared_fixture_abs,V293_shared_fields.
       repeat(eapply V293_target_wstate_star;[apply map_join_emp|apply map_join_merge;
       apply map_disjoint;intros key;destruct key;simpl;auto|split;reflexivity| ]).
       split;reflexivity. }
   clear -P;sep auto.
Qed.
Lemma DXresources_action_free : forall n c events now,can_change_aop(DXresources n c events now).
Proof.
 intros;unfold DXresources,DXempty,DXphysical,DXowned,V293_handoff_byte,V293_handoff_binding,
 V293_counter_cell,V293_counter_bindings,V293_shared_flags,V293_sched_globals,V293_prefix_bindings,
 V293_shared_fields,V293_inputs_full,Agvarmapsto,Aptrmapsto.
 cbn[can_change_aop];repeat split;try exact I;intros;repeat split;try exact I;
 apply V293_array_aop_independent.
Qed.
Definition DXstate c events now aop : RstateOP:=
 (DXge,emp,DXmemory 4 c,(fun _:hid=>false),(false,nil,nil),
 V293_shared_fixture_abs V293_idle_tid(V293_current_mode_tasks true)events now,sched;;aop).
Lemma DXentry_owned : forall c events now aop,DXstate c events now aop|=DXentry c events now aop.
Proof.
 intros c events now aop.
 set(O:=V293_shared_fixture_abs V293_idle_tid(V293_current_mode_tasks true)events now).
 set(s:=DXstate c events now aop).
 pose proof(DXresources_owned 4 c events now)as H.
 pose proof(@change_aop_rule _ _ _(sched;;aop)_ H(DXresources_action_free 4 c events now))as Held.
 fold O in Held;change(s|=DXresources 4 c events now)in Held.
 assert(Halves:s|=(CurTid V293_idle_tid ** CurTid V293_idle_tid) **
 (DXempty ** ((V293_inputs_full 1%positive 2%positive 3%positive 0 16 **
 ((PV(4%positive,Int.zero)@Tint8|->V293_byteval 0) **
 V293_array true 8%positive 0 4(Tptr Tvoid)(V293_current_mode_entries true))) **
 ((GV 107%Z@(Tptr Tvoid)|->Vptr V293_idle_tid) **
 (DXowned 4 c ** V293_shared_fields V293_idle_tid(V293_current_mode_tasks true)events now))))).
 { eapply astar_mono with(P:=GV OSTCBCur@(Tptr Tvoid)|->Vptr V293_idle_tid).
   - intros st HC;apply GV_separate_rw in HC;unfold CurTid;sep auto.
   - intros st HC;exact HC.
   - unfold DXresources,DXphysical in Held;clear -Held;sep auto. }
 unfold DXentry,V293_exit_dispatch_entry.
 apply V293_retained_storage_prefix_lend_value with(hv:=V293_byteval 0);try lia.
 - exists 12;vm_compute;intuition lia.
 - apply astar_l_aop'_intro with(aop:=sched;;aop);[ |reflexivity].
   unfold V293_retained_prefix_entry_heap,V293_storage_open,DXempty,DXowned in *.
   cbn[V293_storage];clear -Halves;sep auto.
Qed.
Theorem DXentry_nonempty : forall c events now aop,exists s,
 V293_bitmap_tasks 0 16(V293_current_mode_tasks true) /\
 V293_priority_table(V293_current_mode_entries true)(V293_current_mode_tasks true) /\
 indom(V293_current_mode_tasks true)V293_idle_tid /\
 V293_highest_ready(V293_current_mode_tasks true)(V293_switch_target true) /\
 V293_switch_target true<>V293_idle_tid /\s|=DXentry c events now aop.
Proof.
 intros c events now aop;exists(DXstate c events now aop).
 destruct(V293_current_mode_relations true)as[B[T C]].
 split;[exact B| ];split;[exact T| ].
 split;[exists(Int.repr 4,wait os_stat_time Int.one,Vnull);vm_compute;reflexivity| ].
 split;[exact(V293_shared_case_highest true)| ].
 split;[vm_compute;discriminate|apply DXentry_owned].
Qed.
Theorem DXmax_entry_nonempty : forall events now aop,
 exists s,s|=DXentry(Int.repr Int.max_unsigned)events now aop.
Proof.
 intros events now aop;destruct(DXentry_nonempty(Int.repr Int.max_unsigned)events now aop)
 as(s & B & T & M & H & D & Held);exists s;exact Held.
Qed.
(* A comparison control on the same concrete memory, changing ONLY the high
   expression's identifier. This observes the guard, not two body executions. *)
Theorem DXcomparison_control : forall c events now aop,
 exists s,
 (s|=DXentry c events now aop) /\
 evalval(V293_OSSched_different 103%Z 113%Z)(getsmem s)=Some(Vint32 Int.one) /\
 evalval(V293_OSSched_different 113%Z 113%Z)(getsmem s)=Some(Vint32 Int.zero).
Proof.
 intros c events now aop;set(s:=DXstate c events now aop);exists s.
 split;[apply DXentry_owned| ].
 pose proof(DXresources_owned 4 c events now)as H.
 pose proof(@change_aop_rule _ _ _(sched;;aop)_ H(DXresources_action_free 4 c events now))as Held.
 change(s|=DXresources 4 c events now)in Held.
 assert(HC:s|=V293_handoff_byte 113%Z 11%positive 4 ** Atrue).
 { unfold DXresources,DXowned in Held;clear -Held;sep auto. }
 assert(HH:s|=V293_handoff_byte 103%Z 4%positive 0 ** Atrue).
 { unfold DXresources,DXempty,DXphysical,V293_handoff_byte in *;clear -Held;sep auto. }
 destruct(V293_handoff_cast 113%Z 11%positive 4 Atrue s ltac:(lia) HC)as[EC TC].
 destruct(V293_handoff_cast 103%Z 4%positive 0 Atrue s ltac:(lia) HH)as[EH TH].
 unfold V293_OSSched_different;destruct s as[[[[[[ge le]m]ir]aux]o]op].
 cbn[getsmem get_smem evalval evaltype]in EC,TC,EH,TH|-*.
 rewrite EC,TC,EH,TH;split;reflexivity.
Qed.
(* Frozen BX copy-deletion executions remain a separate fixture. *)
Check BXcopy_ablation.

(* This instantiates the same entry and the same outer Inv; it still requires
   the real callee contract, and does not assert a full function execution. *)
Definition DXinv:=V293_storage_inv
 (((12%positive,0%Z),Tint32)::((4%positive,0%Z),Tint8)::((11%positive,0%Z),Tint8)::
 (V293_input_cells 1%positive 2%positive 3%positive ++
 V293_array_cells 8%positive 0 4(Tptr Tvoid)(length(V293_current_mode_entries true)) ++ nil))
 107%Z Tvoid.
Definition DXpost aop:=V293_exit_dispatch_resumed
 100%Z 101%Z 102%Z 103%Z 106%Z 107%Z 113%Z 111%Z
 1%positive 2%positive 3%positive 4%positive 8%positive 10%positive 11%positive 12%positive
 Tvoid(V293_current_mode_entries true)nil V293_idle_tid aop nil nil Aemp.
Theorem DXactual_dispatch : forall Spec r ri sched_id events now aop c,
 Spec sched_id=Some
 (V293_critical_fpre 100%Z 101%Z 102%Z 103%Z 1%positive 2%positive 3%positive 4%positive
 V293_shared_li V293_opened_inv V293_switch_li_good,
 V293_critical_fpost 100%Z 101%Z 102%Z 103%Z 1%positive 2%positive 3%positive 4%positive
 V293_shared_li V293_opened_inv V293_switch_li_good,(Tvoid,nil)) ->
 InfRules Spec V293_scheduler V293_shared_li DXinv r ri(DXentry c events now aop)
 (V293_exit_boundary_dispatch 106%Z 103%Z 107%Z 113%Z 111%Z sched_id
 (V293_interrupt_handoff 103%Z 113%Z 107%Z))(DXpost aop)V293_idle_tid.
Proof.
 intros Spec r ri sched_id events now aop c Callee.
 unfold DXinv,DXentry,DXpost;apply V293_OSIntExit_changed_dispatch;try lia.
 - exists 12;vm_compute;intuition lia.
 - vm_compute;discriminate.
 - exact(proj1(V293_current_mode_relations true)).
 - exact(proj1(proj2(V293_current_mode_relations true))).
 - vm_compute;repeat constructor.
 - exists(Int.repr 4,wait os_stat_time Int.one,Vnull);vm_compute;reflexivity.
 - exact I.
 - intros s H;pose proof(V293_switch_local_empty V293_idle_tid nil s H)as L;
   clear -L;sep auto.
 - exact Callee.
Qed.
