Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitSameInternal.
Require Import CertiOS.framework.proof.toptheorem.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptReadyEnvironment.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitUnifiedInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedSwitch.
(* Typed dynamic same Exit entry with exact local resources. *)
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitNondispatch.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedChange.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedPrefix.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitBoundarySwitch.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitResourceBridge.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitResourceCodec.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntEnterInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTargetWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedGuards.
Require Import CertiOS.certiucos.v293.proofs.V293TimeAccess.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.audit.probes.V293OSIntExitResourceCodecProbe.
Require Import CertiOS.audit.probes.V293OSIntExitBuildersProbe.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.rulesoundlib.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.

Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitSamePriority.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedISRContext.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.certiucos.v293.code.V293OSIntExit.
Require Import CertiOS.audit.probes.V293OSSchedISRContextProbe.

Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitBody.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitCriticalCalls.
Require Import CertiOS.certiucos.v293.code.V293OSIntEnter.
Require Import CertiOS.framework.proof.auxdef.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedGuardsWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedPrefixWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTarget.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitDispatch.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedChangeWitness.
Require Import CertiOS.certiucos.v293.code.V293OSSchedChange.
Require Import CertiOS.certiucos.v293.code.V293OSSchedGuards.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitBuilders.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitSameExact.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedISRExact.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedExactLocal.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedExactPrefix.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitQuietExact.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293SharedStateWitness.
Require Import CertiOS.audit.probes.V293InterruptReadyEnvironmentProbe.
Require Import CertiOS.audit.probes.V293InterruptReadyLocalProbe.
Require Import CertiOS.audit.probes.V293TaskRecordOwnershipProbe.

Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitAllExactDynamic.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitSameExactInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedAllExactJoint.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitReadyDynamic.
Require Import CertiOS.audit.probes.V293OSIntExitSameInternalProbe.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.
Local Open Scope list_scope.

Lemma SEpointer_bytes : forall entries tp b offset,
 V293_pointer_memory tp b offset entries=V293_pointer_memory Tvoid b offset entries.
Proof. induction entries;intros;cbn[V293_pointer_memory];[reflexivity|rewrite IHentries;reflexivity]. Qed.
Definition SEge:=set(set BLge 106%Z(8%positive,Tarray(Tptr V293_tcb_type)13))107%Z(10%positive,Tptr V293_tcb_type).
Definition SEbase M:=V293_target_wstate SEge emp M V293_target_fixture_abs.
Definition SEbigstate nc nest c run value:=V293_target_wstate SEge BLle(RCbigmemory nc nest c run value)V293_target_fixture_abs.
Definition SEbindings:=V293_exit_caller_bindings 103%Z 106%Z 107%Z V293_tcb_type
 8%positive 10%positive 110%Z 111%Z 108%Z 109%Z 13%positive 14%positive 11%positive 12%positive.
Lemma SEnames_owned : V293_wstate SEge emp emp |= BLnames.
Proof.
 unfold BLnames. eapply V293_wstate_star with(m1:=emp)(m2:=emp);[apply map_join_emp| | ];
 split;[eexists;split;[vm_compute;reflexivity|repeat split;reflexivity]|
 split;[intros[v H];discriminate|split;reflexivity]|
 eexists;split;[vm_compute;reflexivity|repeat split;reflexivity]|
 split;[intros[v H];discriminate|split;reflexivity]].
Qed.
Lemma SEcaller_owned : forall out,
 V293_target_wstate SEge emp(BLcaller out)V293_target_fixture_abs |=
 V293_prefix_frame 106%Z 103%Z 107%Z V293_tcb_type 8%positive 10%positive V293_idle_entries V293_idle_tasks Aemp **
 V293_prefix_output V293_tcb_type 10%positive out.
Proof.
 intro out. unfold BLcaller.
 eapply V293_target_wstate_star;[BLjoin 8%positive|apply map_join_emp| | ].
 - apply astar_r_aemp_intro.
   eapply V293_target_wstate_star with(m1:=emp)(m2:=V293_target_fixture_table)
    (o1:=emp)(o2:=V293_target_fixture_abs).
   + apply map_join_comm;apply map_join_emp.
   + apply map_join_comm;apply map_join_emp.
   + unfold V293_prefix_bindings. repeat split.
     * eexists;split;[vm_compute;reflexivity|repeat split;reflexivity].
     * eexists;split;[vm_compute;reflexivity|repeat split;reflexivity].
     * intros[v H];discriminate.
     * intros[v H];discriminate.
     * intros[v H];discriminate.
   + eapply V293_target_wstate_star with(m1:=V293_target_fixture_table)(m2:=emp)
      (o1:=emp)(o2:=V293_target_fixture_abs).
     * apply map_join_emp.
     * apply map_join_comm;apply map_join_emp.
     * unfold V293_target_fixture_table. rewrite <-SEpointer_bytes with(tp:=V293_tcb_type). apply V293_read_pointers_witness.
     * split;reflexivity.
 - split;[apply V293_encoded_memory_mapsto|reflexivity].
Qed.
Lemma SEextra_owned : forall nest locked nc c,
 V293_wstate SEge emp(BLextra nest locked nc c) |=
 V293_rdy_raw_cells(V293_exit_cells 11%positive 12%positive nest locked)BLnames **
 (V293_guard_cell 110%Z 13%positive nc ** V293_counter_cell 111%Z 14%positive c).
Proof.
 intros. unfold V293_exit_cells,V293_interrupt_cells;cbn[V293_rdy_raw_cells].
 assert(H:V293_wstate SEge emp(BLextra nest locked nc c) |=
  PV(11%positive,Int.zero)@Tint8|->(V293_byteval nest) **
  (PV(12%positive,Int.zero)@Tint8|->(V293_byteval locked) **
  (V293_guard_cell 110%Z 13%positive nc ** V293_counter_cell 111%Z 14%positive c))).
 { unfold BLextra. eapply V293_wstate_star;[BLjoin 11%positive| | ].
   - split;[apply V293_encoded_memory_mapsto|reflexivity].
   - eapply V293_wstate_star;[BLjoin 12%positive| | ].
     + split;[apply V293_encoded_memory_mapsto|reflexivity].
     + unfold V293_change_extra. eapply V293_wstate_star.
       * apply map_join_merge. apply map_disjoint. intros[b i].
         destruct(Pos.eq_dec b 13%positive);[subst b;right;left|left];
         apply V293_encoded_memory_outside;left;congruence.
       * apply V293_guard_cell_witness;vm_compute;reflexivity.
       * apply V293_counter_cell_witness;vm_compute;reflexivity. }
 assert(H':V293_wstate SEge emp(BLextra nest locked nc c) |= BLnames **
  (PV(11%positive,Int.zero)@Tint8|->(V293_byteval nest) **
  (PV(12%positive,Int.zero)@Tint8|->(V293_byteval locked) **
  (V293_guard_cell 110%Z 13%positive nc ** V293_counter_cell 111%Z 14%positive c)))).
 { eapply V293_wstate_star with(m1:=emp)(m2:=BLextra nest locked nc c).
   - apply map_join_comm;apply map_join_emp.
   - apply SEnames_owned.
   - exact H. }
 clear H. sep auto.
Qed.
Lemma SEbindings_empty : SEbindings ==> Aemp.
Proof.
 assert(S:forall p q,(p ==> Aemp)->(q ==> Aemp)->p ** q ==> Aemp).
 { intros p q P Q s H. apply astar_l_aemp_elim.
   eapply astar_mono;[exact P|exact Q|exact H]. }
 unfold SEbindings,V293_exit_caller_bindings,V293_prefix_bindings,V293_counter_bindings,V293_exit_guard_bindings.
 repeat apply S;intros s H;destruct H as[G _];
 apply agvarenv_elim in G;exact(proj2 G).
Qed.
Lemma SEcaller_names : V293_wstate SEge BLle emp |=
 Alvarenv 120%Z Tint32(15%positive,0%Z) ** (SEbindings ** Aemp).
Proof.
 unfold SEbindings,V293_exit_caller_bindings,V293_prefix_bindings,V293_counter_bindings,V293_exit_guard_bindings.
 repeat(eapply V293_wstate_star with(m1:=emp)(m2:=emp);[apply map_join_emp| | ]).
 all:repeat split;try(intros[v H];vm_compute in H;discriminate);
 try(eexists;split;[vm_compute;reflexivity|repeat split;reflexivity]);try reflexivity.
Qed.
Lemma SErun_owned : forall run,
 V293_wstate SEge BLle(BLrun run) |= V293_guard_cell 112%Z 16%positive run.
Proof.
 intro run. unfold V293_guard_cell. eapply V293_wstate_star with(m1:=emp)(m2:=BLrun run).
 - apply map_join_comm;apply map_join_emp.
 - split.
   + eexists;split;[vm_compute;reflexivity|repeat split;reflexivity].
   + split;[intros[v H];vm_compute in H;discriminate|split;reflexivity].
 - split;[apply V293_encoded_memory_mapsto|reflexivity].
Qed.
Lemma SEcurrent : V293_wstate SEge emp V293_witness_current |=
 p_local V293_shared_li V293_idle_tid nil.
Proof.
 unfold p_local; eapply V293_wstate_star with(m1:=V293_witness_current)(m2:=emp).
 - apply map_join_emp.
 - exists Tvoid;exists 6%positive.
   eapply V293_wstate_star with(m1:=emp)(m2:=V293_witness_current).
   + apply map_join_comm;apply map_join_emp.
   + exists 6%positive;split;[vm_compute;reflexivity| ];split;[reflexivity|split;reflexivity].
   + split;[apply V293_encoded_memory_mapsto|reflexivity].
 - unfold LINV,V293_shared_li; eapply V293_wstate_star with(m1:=emp)(m2:=emp).
   + apply map_join_emp.
   + split;reflexivity.
   + split;[apply V293_switch_li_good|split;reflexivity].
Qed.

Lemma SEinternal_owned : forall hv,
 V293_wstate SEge emp(BLinternal hv) |=
 <||spec_done None||> ** V293_sched_exact_resource
 100%Z 101%Z 102%Z 103%Z 1%positive 2%positive 3%positive 4%positive 0 16
 V293_shared_li V293_idle_tid(V293_byteval hv).
Proof.
 intro hv. apply astar_l_aop'_intro;[ |reflexivity].
 unfold V293_sched_exact_resource.
 eapply V293_wstate_star;[BLjoin 4%positive| | ].
 - eapply V293_wstate_star;[BLjoin 6%positive| | ].
   + eapply V293_wstate_star with(m1:=emp)(m2:=V293_witness_inputs).
     * apply map_join_comm;apply map_join_emp.
     * apply V293_prefix_fixture_globals;vm_compute;reflexivity.
     * apply V293_prefix_fixture_inputs.
   + apply astar_comm. apply astar_l_aie_intro;[ |reflexivity].
     apply SEcurrent.
 - split;[apply V293_encoded_memory_mapsto|reflexivity].
Qed.
Lemma SEjoint_owned : forall hv out nest locked nc c,
 SEbase(BLmemory hv out nest locked nc c) |=
 ((<||spec_done None||> ** V293_sched_exact_resource
 100%Z 101%Z 102%Z 103%Z 1%positive 2%positive 3%positive 4%positive 0 16
 V293_shared_li V293_idle_tid(V293_byteval hv)) **
 (V293_prefix_frame 106%Z 103%Z 107%Z V293_tcb_type 8%positive 10%positive V293_idle_entries V293_idle_tasks Aemp **
 V293_prefix_output V293_tcb_type 10%positive out)) **
 (V293_rdy_raw_cells(V293_exit_cells 11%positive 12%positive nest locked)BLnames **
 (V293_guard_cell 110%Z 13%positive nc ** V293_counter_cell 111%Z 14%positive c)).
Proof.
 intros. eapply V293_target_wstate_star with(o1:=V293_target_fixture_abs)(o2:=emp).
 - apply map_join_merge;apply map_disjoint;intros[b i].
   destruct(Pos.eq_dec b 11%positive);[subst b;left;BLoutside| ].
   destruct(Pos.eq_dec b 12%positive);[subst b;left;BLoutside| ].
   destruct(Pos.eq_dec b 13%positive);[subst b;left;BLoutside| ].
   destruct(Pos.eq_dec b 14%positive);[subst b;left;BLoutside| ]. right;left;BLoutside.
 - apply map_join_emp.
 - eapply V293_target_wstate_star with(o1:=emp)(o2:=V293_target_fixture_abs).
   + apply map_join_merge;apply map_disjoint;intros[b i].
     destruct(Pos.eq_dec b 8%positive);[subst b;left;BLoutside| ].
     destruct(Pos.eq_dec b 10%positive);[subst b;left;BLoutside| ]. right;left;BLoutside.
   + apply map_join_comm;apply map_join_emp.
   + apply SEinternal_owned.
   + apply SEcaller_owned.
 - apply SEextra_owned.
Qed.
Definition SEready nc nest locked out c := V293_exit_ready_exact_pre
 100%Z 101%Z 102%Z 103%Z 1%positive 2%positive 3%positive 4%positive 0 16
 V293_shared_li V293_idle_tid(spec_done None)106%Z 107%Z V293_tcb_type 8%positive 10%positive
 V293_idle_entries V293_idle_tasks 110%Z 111%Z 13%positive 14%positive 11%positive 12%positive
 nc BLnames nest locked out c.
Theorem SEready_owned : forall hv out nest locked nc c,
 SEbase(BLmemory hv out nest locked nc c) |= SEready nc nest locked out c.
Proof.
 intros. pose proof(SEjoint_owned hv out nest locked nc c)as Hs.
 unfold SEready,V293_exit_ready_exact_pre,V293_sched_exact_pre. sep normal. exists(V293_byteval hv).
 assert(B:0<256 /\ 16<256 /\ exists p,V293_bitmap_ready 0 16 p).
 { split;[lia| ]. split;[lia| ]. exists 12;vm_compute;intuition lia. }
 unfold V293_prefix_frame in *;sep auto;assumption.
Qed.

Definition SEphysical nc nest c :=
 V293_sched_exact_pre 100%Z 101%Z 102%Z 103%Z
 1%positive 2%positive 3%positive 4%positive 0 16 V293_shared_li V293_idle_tid(spec_done None) **
 ((V293_read_pointers V293_tcb_type 8%positive 0 V293_idle_entries ** Aabsdata abstcblsid(abstcblist V293_idle_tasks)) **
 (Amapsto(13%positive,0%Z)Tint8 false(V293_byteval nc) **
  V293_rdy_raw_cells(V293_exit_cells 11%positive 12%positive nest 0)Aemp)) **
 (V293_prefix_output V293_tcb_type 10%positive Vnull ** PV(14%positive,Int.zero)@Tint32|->Vint32 c).
Lemma SEphysical_good : forall nc nest c,GoodFunAsrt(SEphysical nc nest c).
Proof.
 intros. unfold SEphysical. split.
 - apply V293_sched_exact_pre_good;apply V293_switch_li_good.
 - unfold V293_prefix_output,V293_exit_cells,V293_interrupt_cells.
   cbn[V293_rdy_raw_cells Aptrmapsto GoodFunAsrt]. repeat split;try exact I.
Qed.
Lemma SEphysical_owned : forall nc nest c,
 SEbase(BLmemory 0 Vnull nest 0 nc c) |= SEphysical nc nest c.
Proof.
 intros. pose proof(SEready_owned 0 Vnull nest 0 nc c)as H.
 assert(U:SEbase(BLmemory 0 Vnull nest 0 nc c) |= SEphysical nc nest c ** (SEbindings ** Aemp)).
 { unfold SEready,V293_exit_ready_exact_pre,SEphysical,SEbindings,
   V293_exit_caller_bindings,V293_prefix_frame,V293_guard_cell,V293_counter_cell,
   V293_exit_guard_bindings,BLnames,V293_exit_cells,V293_interrupt_cells in *.
   cbn[V293_rdy_raw_cells]in *;clear -H;sep auto. }
 apply astar_r_aemp_elim. eapply astar_mono;[intros st Hst;exact Hst| |exact U].
 intros st Hst. apply astar_r_aemp_elim in Hst. apply SEbindings_empty;exact Hst.
Qed.
Lemma SEbig_owned : forall nc nest c run value, SEbigstate nc nest c run value |=
 ((SEphysical nc nest c) ** PV(15%positive,Int.zero)@Tint32|->value) **
 (V293_guard_cell 112%Z 16%positive run **
  (Alvarenv 120%Z Tint32(15%positive,0%Z) ** (SEbindings ** Aemp))).
Proof.
 intros.
 assert(H:SEbigstate nc nest c run value |=
  (((SEphysical nc nest c) ** PV(15%positive,Int.zero)@Tint32|->value) **
   V293_guard_cell 112%Z 16%positive run) **
  (Alvarenv 120%Z Tint32(15%positive,0%Z) ** (SEbindings ** Aemp))).
 { unfold SEbigstate. eapply V293_target_wstate_star with
 (m1:=RCbigmemory nc nest c run value)(m2:=emp)(o1:=V293_target_fixture_abs)(o2:=emp);try apply map_join_emp.
 - eapply V293_target_wstate_star with(m1:=RCbigjoined nc nest c value)(m2:=BLrun run)
   (o1:=V293_target_fixture_abs)(o2:=emp).
   + apply RCbig_run_join.
   + apply map_join_emp.
   + eapply V293_target_wstate_star with(m1:=BLmemory 0 Vnull nest 0 nc c)(m2:=BLsaved value)
     (o1:=V293_target_fixture_abs)(o2:=emp).
     * apply RCbig_saved_join.
     * apply map_join_emp.
     * eapply good_fun_asrt_absop with(p:=(SEphysical nc nest c))(le:=emp).
       -- apply SEphysical_good.
       -- apply SEphysical_owned.
     * split;[apply V293_encoded_memory_mapsto|reflexivity].
   + apply SErun_owned.
 - apply SEcaller_names. }
 clear -H;sep auto.
Qed.
Definition SEdata := V293_exit_same_exact_data
 100%Z 101%Z 102%Z 103%Z 1%positive 2%positive 3%positive 4%positive 0 16
 V293_shared_li V293_idle_tid 106%Z 107%Z V293_tcb_type 8%positive 10%positive
 V293_idle_entries V293_idle_tasks 110%Z 111%Z 112%Z 120%Z
 13%positive 14%positive 16%positive 11%positive 12%positive 15%positive 12 BLnames.
Definition SEout := V293_exit_same_exact_result
 100%Z 101%Z 102%Z 103%Z 1%positive 2%positive 3%positive 4%positive 0 16
 V293_shared_li V293_idle_tid 106%Z 107%Z V293_tcb_type 8%positive 10%positive
 V293_idle_entries V293_idle_tasks 110%Z 111%Z 112%Z 120%Z
 13%positive 14%positive 16%positive 11%positive 12%positive 15%positive 12 BLnames.
Definition SEstate enabled si ci nest c old : RstateOP :=
 (SEge,BLle,RCbigmemory 12 nest c 1 old,(fun _=>false),
  (enabled,si,ci),V293_target_fixture_abs,spec_done None).
Definition SEpre enabled si ci nest c old :=
 EX hv:val,<||spec_done None||> ** OS[(fun _=>false),enabled,si,ci] **
 SEdata nest hv Vnull c old.
Lemma SEdata_owned : forall nest c old,
 SEbigstate 12 nest c 1 old |= EX hv:val,SEdata nest hv Vnull c old.
Proof.
 intros nest c old. pose proof(SEbig_owned 12 nest c 1 old)as Held.
 unfold SEphysical,V293_sched_exact_pre,V293_sched_exact_resource in Held.
 unfold SEdata,V293_exit_same_exact_data,V293_exit_same_exact_core,BLnames,SEbindings,
 V293_exit_caller_bindings,V293_exit_guard_bindings,V293_prefix_frame in *.
 unfold V293_exit_cells,V293_interrupt_cells in *.
 cbn [RCsnapshot V293_xlo V293_xhi V293_xnest V293_xlocked V293_xold
 V293_xcounter V293_xcurrent V293_xentries V293_xtasks V293_xaop V293_rdy_raw_cells] in *.
 unfold V293_time_cell,V293_time_binding,V293_guard_cell,V293_counter_cell,
 V293_counter_bindings in *.
 sep normal in Held. destruct Held as[hv Held]. exists hv.
 sep lift 6 in Held;apply astar_l_aop'_elim in Held as[_ Held].
 sep lift 9 in Held;apply astar_l_aie_elim in Held as[_ Held].
 ssplit_apure_in Held;sclearemp_in Held.
 sep rearr in Held with (1::2::4::5::3::19::17::18::6::7::8::9::20::10::11::12::13::14::15::16::nil).
 sep normal. exact Held.
Qed.
Theorem SEpre_nonempty : forall enabled si ci nest c old,
 SEstate enabled si ci nest c old |= SEpre enabled si ci nest c old.
Proof.
 intros enabled si ci nest c old.
 assert(Data:SEstate enabled si ci nest c old |= EX hv:val,SEdata nest hv Vnull c old).
 { eapply goodfrm_prop.
   - intro hv;unfold SEdata. apply V293_exit_same_exact_data_good;[apply V293_switch_li_good|apply QSframe_good].
   - exact(SEdata_owned nest c old). }
 destruct Data as[hv Data]. unfold SEpre. exists hv. apply astar_l_aop'_intro;[ |reflexivity].
 apply astar_l_aie_intro with(i:=enabled)in Data;[ |reflexivity].
 apply astar_l_ais_intro with(i:=si)in Data;[ |reflexivity].
 apply astar_l_aisr_intro with(i:=fun _=>false)in Data;[ |reflexivity].
 apply astar_l_acs_intro with(i:=ci)in Data;[ |reflexivity].
 clear -Data;sep auto.
Qed.
Definition SEfp:=V293_all_exact_dynamic_fpre 100%Z 101%Z 102%Z 103%Z 106%Z 107%Z 110%Z 111%Z 112%Z 108%Z 109%Z 1%positive 2%positive 3%positive 4%positive 8%positive 10%positive 13%positive 14%positive 16%positive 11%positive 12%positive nil Aemp I.
Definition SEfq:=V293_all_exact_dynamic_fpost 100%Z 101%Z 102%Z 103%Z 106%Z 107%Z 110%Z 111%Z 112%Z 108%Z 109%Z 1%positive 2%positive 3%positive 4%positive 8%positive 10%positive 13%positive 14%positive 16%positive 11%positive 12%positive nil Aemp I.
Definition SEspec:=V293_all_exact_dynamic_spec 100%Z 101%Z 102%Z 103%Z 106%Z 107%Z 110%Z 111%Z 112%Z 108%Z 109%Z 1%positive 2%positive 3%positive 4%positive 8%positive 10%positive 13%positive 14%positive 16%positive 11%positive 12%positive nil Aemp I 300%Z 301%Z 200%Z.
Definition SEprogram:=V293_ready_irq_unit 100%Z 101%Z 102%Z 103%Z 106%Z 107%Z 110%Z 111%Z 112%Z 108%Z 109%Z 120%Z 300%Z 301%Z 200%Z 104%Z.
Definition SEinv:=V293_ready_dynamic_exit_inv 107%Z 1%positive 2%positive 3%positive 4%positive
 8%positive 13%positive 14%positive 16%positive 11%positive 12%positive nil.
Definition SElg enabled:=logic_ie false::logic_ie false::BIlogic enabled.
Definition SEbuilderpre enabled:=V293_exit_builder_cells 120%Z **
 getasrt(SEfp nil(SElg enabled)V293_idle_tid) ** V293_exit_builder_domain 120%Z.
Definition SEbuilderpost enabled result:=V293_exit_builder_cells 120%Z **
 getasrt(SEfq nil result(SElg enabled)V293_idle_tid) ** V293_exit_builder_domain 120%Z.
Lemma SEbuilders : forall enabled,
 BuildPreI SEprogram 300%Z nil(SElg enabled)SEfp V293_idle_tid=Some(SEbuilderpre enabled) /\
 BuildRetI SEprogram 300%Z nil(SElg enabled)SEfq V293_idle_tid=Some(SEbuilderpost enabled).
Proof. intro;split;reflexivity. Qed.
Theorem SEenvironment : WFFunEnv SEprogram SEspec V293_scheduler V293_shared_li SEinv /\
 WFIFun SEprogram SEspec V293_scheduler SEinv V293_shared_li.
Proof. split;unfold SEprogram,SEspec;
 [apply V293_all_exact_dynamic_WFFunEnv|apply V293_all_exact_dynamic_WFIFun];try discriminate;exact I. Qed.
Definition SEmemory := V293_same_exact_exit_memory
 100%Z 101%Z 102%Z 103%Z 1%positive 2%positive 3%positive 4%positive
 8%positive 10%positive 13%positive 14%positive 11%positive 12%positive V293_tcb_type V293_shared_li.
Definition SEglobals := V293_exit_builder_globals
 106%Z 107%Z 110%Z 111%Z 108%Z 109%Z 112%Z V293_tcb_type
 8%positive 10%positive 13%positive 14%positive 11%positive 12%positive 16%positive.
Lemma SEowned : forall enabled si ci nest c old,
 SEstate enabled si ci nest c old |=
 EX hv:val,V293_exit_builder_cells 120%Z **
 (<||spec_done None||> ** OS[(fun _=>false),enabled,si,ci] **
 (SEmemory 0 16 V293_idle_entries V293_idle_tasks 12 nest hv Vnull c V293_idle_tid **
 (SEglobals ** (Amapsto(16%positive,0%Z)Tint8 false(V293_byteval 1) ** Aemp)))) **
 V293_exit_builder_domain 120%Z.
Proof.
 intros enabled si ci nest c old.
 pose proof(SEpre_nonempty enabled si ci nest c old)as Held.
 unfold SEpre in Held;destruct Held as[hv Held];exists hv.
 apply astar_l_adomlenv_intro with(d:=cons(120%Z,Tint32)nil)in Held;
 [ |exact BLdomain].
 assert(U:SEstate enabled si ci nest c old |=
 (SEbindings ** (Agvarenv 112%Z Tint8(16%positive,0%Z) //\\ A_notin_lenv 112%Z)) **
 (V293_exit_builder_cells 120%Z ** <||spec_done None||> ** OS[(fun _=>false),enabled,si,ci] **
 (SEmemory 0 16 V293_idle_entries V293_idle_tasks 12 nest hv Vnull c V293_idle_tid **
 (Amapsto(16%positive,0%Z)Tint8 false(V293_byteval 1) ** V293_exit_builder_domain 120%Z)))).
 { unfold SEdata,V293_exit_same_exact_data,V293_exit_same_exact_core,SEmemory,V293_same_exact_exit_memory,
   V293_time_cell,V293_time_binding,V293_guard_cell,V293_counter_cell,V293_prefix_frame,
   V293_exit_builder_cells,Alvarmapsto,Alvarenv',Aptrmapsto in *.
   unfold V293_exit_cells,V293_interrupt_cells in *;cbn[V293_rdy_raw_cells]in *.
   unfold SEbindings,V293_exit_caller_bindings,BLnames,V293_exit_guard_bindings in *.
   sep normal in Held. sep normal. exists old;exists 15%positive.
   unfold V293_exit_builder_domain in *;cbn[addrval_to_addr]in *.
   sep rearr in Held with(2::3::4::1::11::12::18::25::6::7::8::9::10::14::15::16::17::19::20::21::22::23::24::26::13::5::nil).
   exact Held. }
 eapply astar_mono in U.
 2:{ apply V293_exit_builder_forget_names. }
 2:{ intros st Hst;exact Hst. }
 unfold SEglobals. clear -U;sep auto.
Qed.
Theorem SEentry_nonempty : forall enabled,
 SEstate enabled(cons 0 nil)(cons false nil)1 Int.one(Vint32 Int.one) |=
 SEbuilderpre enabled.
Proof.
 intro enabled. pose proof(SEowned enabled(cons 0 nil)(cons false nil)1 Int.one(Vint32 Int.one))as Held.
 destruct Held as[hv Held].
 unfold SEbuilderpre,SEfp,SElg,V293_all_exact_dynamic_fpre,V293_exit_path,V293_same_exact_exit_fpre,getasrt,V293_same_exact_exit_pre.
 rewrite BIdecode. cbn[V293_xlo V293_xhi V293_xcurrent V293_xnest V293_xold
 V293_xcounter V293_xentries V293_xtasks V293_xaop RCsnapshot].
 assert(U:SEstate enabled(cons 0 nil)(cons false nil)1 Int.one(Vint32 Int.one) |=
 V293_exit_builder_cells 120%Z **
 (EX v:val,V293_same_exact_exit_external
 100%Z 101%Z 102%Z 103%Z 106%Z 107%Z 110%Z 111%Z 108%Z 109%Z 112%Z
 1%positive 2%positive 3%positive 4%positive 8%positive 10%positive
 13%positive 14%positive 11%positive 12%positive 16%positive V293_tcb_type V293_shared_li Aemp
 enabled(fun _=>false)(cons 0 nil)(cons false nil)0 16 V293_idle_entries V293_idle_tasks
 12 1 v Vnull Int.one(spec_done None)V293_idle_tid) ** V293_exit_builder_domain 120%Z).
 { unfold V293_same_exact_exit_external,SEglobals,SEmemory in *;clear -Held;sep auto. }
 assert(Valid:V293_same_exit_valid(cons 0 nil)(RCsnapshot 12 1 Int.one))by exact BIvalid.
 clear -U Valid;sep auto.
Qed.

Definition SEexternal enabled nest hv out := V293_same_exact_exit_external
 100%Z 101%Z 102%Z 103%Z 106%Z 107%Z 110%Z 111%Z 108%Z 109%Z 112%Z
 1%positive 2%positive 3%positive 4%positive 8%positive 10%positive
 13%positive 14%positive 11%positive 12%positive 16%positive V293_tcb_type V293_shared_li Aemp
 enabled(fun _=>false)(cons 0 nil)(cons false nil)0 16 V293_idle_entries V293_idle_tasks
 12 nest hv out Int.one(spec_done None)V293_idle_tid.
Lemma SEliteral : forall enabled,
 getasrt(SEfp nil(SElg enabled)V293_idle_tid)=
 [|V293_same_exit_valid(cons 0 nil)(RCsnapshot 12 1 Int.one)|] **
 (EX hv:val,SEexternal enabled 1 hv Vnull) /\
 (forall result,getasrt(SEfq nil result(SElg enabled)V293_idle_tid)=
 [|result=None|] **
 (EX selected:Modules.tid,[|V293_highest_ready V293_idle_tasks selected|] **
 SEexternal enabled 0(V293_byteval(V293_ready_select 0 16(V293_ready_group 0 16)))(Vptr selected))).
Proof.
 intro enabled;split;[ |intro result];unfold SEfp,SEfq,SElg,
 V293_all_exact_dynamic_fpre,V293_all_exact_dynamic_fpost,V293_exit_path,
 V293_same_exact_exit_fpre,V293_same_exact_exit_fpost,getasrt,
 V293_same_exact_exit_pre,V293_same_exact_exit_post;
 rewrite BIdecode;reflexivity.
Qed.
Theorem SEactual_contract : forall enabled,
 InfRules SEspec V293_scheduler V293_shared_li SEinv(SEbuilderpost enabled) Afalse(SEbuilderpre enabled)
 (V293_exit_boundary_body 112%Z 108%Z 109%Z 120%Z 106%Z 103%Z 107%Z 110%Z 111%Z
 200%Z(V293_interrupt_handoff 103%Z 110%Z 107%Z)) Afalse V293_idle_tid.
Proof.
 intro enabled.
 eapply(V293_OSIntExit_all_exact_dynamic_contract
 100%Z 101%Z 102%Z 103%Z 106%Z 107%Z 110%Z 111%Z 112%Z 108%Z 109%Z 120%Z
 1%positive 2%positive 3%positive 4%positive 8%positive 10%positive
 13%positive 14%positive 16%positive 11%positive 12%positive nil Aemp I
 SEprogram 300%Z SEspec 200%Z nil(SElg enabled)V293_idle_tid(SEbuilderpre enabled)(SEbuilderpost enabled));
 try discriminate;try reflexivity;exact I.
Qed.
Theorem SEactual_call : forall RI enabled,
 InfRules SEspec V293_scheduler V293_shared_li RI(SEbuilderpost enabled) Afalse
 (getasrt(SEfp nil(SElg enabled)V293_idle_tid) **
 (V293_exit_builder_cells 120%Z ** V293_exit_builder_domain 120%Z))
 (scall 300%Z nil)
 (EX result:option val,getasrt(SEfq nil result(SElg enabled)V293_idle_tid) **
 (V293_exit_builder_cells 120%Z ** V293_exit_builder_domain 120%Z)) V293_idle_tid.
Proof.
 intros RI enabled;unfold SElg,BIlogic,SEfp,SEfq,SEspec.
 apply V293_OSIntExit_all_exact_dynamic_same_call;try reflexivity.
 - exact(proj1(proj2 BIvalid)).
 - unfold V293_exit_builder_cells,V293_exit_builder_domain,Alvarmapsto,Alvarenv',Aptrmapsto;
   cbn[GoodFrm];repeat split;try exact I;intros;repeat split;exact I.
Qed.
Theorem SEcall_entry_nonempty : forall enabled,
 SEstate enabled(cons 0 nil)(cons false nil)1 Int.one(Vint32 Int.one) |=
 getasrt(SEfp nil(SElg enabled)V293_idle_tid) **
 (V293_exit_builder_cells 120%Z ** V293_exit_builder_domain 120%Z).
Proof. intro enabled;pose proof(SEentry_nonempty enabled)as H;unfold SEbuilderpre in H;clear -H;sep auto. Qed.
(* One fixed physical state; only the logical IE argument changes. *)
Theorem SEie_control :
 (SEstate true(cons 0 nil)(cons false nil)1 Int.one(Vint32 Int.one) |=SEbuilderpre true) /\
 ~(SEstate true(cons 0 nil)(cons false nil)1 Int.one(Vint32 Int.one) |=SEbuilderpre false).
Proof.
 split;[apply SEentry_nonempty| ]. intro Bad.
 unfold SEbuilderpre in Bad;rewrite(proj1(SEliteral false))in Bad.
 assert(IE:SEstate true(cons 0 nil)(cons false nil)1 Int.one(Vint32 Int.one) |=Aie false ** Atrue).
 { unfold SEexternal,V293_same_exact_exit_external in Bad;clear -Bad;sep auto. }
 apply astar_l_aie_elim in IE as[E _];discriminate.
Qed.
(* Separate fixed-state local assertion boundary, not an execution ablation. *)
Theorem SElocal_control : REstate |=CurLINV V293_shared_li OwnershipWaiting /\
 ~REstate |=p_local V293_shared_li OwnershipWaiting nil.
Proof. apply RLlocal_exactness_control. Qed.
Theorem SEarity_control : forall lg t,
 BuildPreI SEprogram 300%Z(cons(Vint32 Int.zero)nil)lg SEfp t=None.
Proof. intros;reflexivity. Qed.
(* Return construction does not check the formal argument count. *)
Lemma SEreturn_arity_observation : forall lg t,
 BuildRetI SEprogram 300%Z(cons(Vint32 Int.zero)nil)lg SEfq t=
 Some(fun result=>V293_exit_builder_cells 120%Z ** getasrt(SEfq(cons(Vint32 Int.zero)nil)result lg t) **
 V293_exit_builder_domain 120%Z).
Proof. intros;reflexivity. Qed.
