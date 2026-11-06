(* Independent nonempty full-body entry and an assignment-boundary control. *)
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
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitSamePriority.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedISRContext.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.certiucos.v293.code.V293OSIntExit.
Require Import CertiOS.audit.probes.V293OSSchedISRContextProbe.

Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitResourceBridge.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitBody.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitCriticalCalls.
Require Import CertiOS.certiucos.v293.proofs.V293TimeAccess.
Require Import CertiOS.certiucos.v293.code.V293OSIntEnter.
Require Import CertiOS.framework.proof.rulesoundlib.
Require Import CertiOS.framework.proof.auxdef.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedChange.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedGuards.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedGuardsWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedPrefix.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedPrefixWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTargetWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTarget.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List Lia.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitDispatch.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntEnterInternal.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedChangeWitness.
Require Import CertiOS.certiucos.v293.code.V293OSIntExit.
Require Import CertiOS.certiucos.v293.code.V293OSSchedChange.
Require Import CertiOS.certiucos.v293.code.V293OSSchedGuards.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
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

Lemma QEcurrent : V293_wstate BLge emp V293_witness_current |=
 p_local V293_witness_li V293_idle_tid nil.
Proof.
 unfold p_local; eapply V293_wstate_star with(m1:=V293_witness_current)(m2:=emp).
 - apply map_join_emp.
 - exists Tvoid;exists 6%positive.
   eapply V293_wstate_star with(m1:=emp)(m2:=V293_witness_current).
   + apply map_join_comm;apply map_join_emp.
   + exists 6%positive;split;[vm_compute;reflexivity| ];split;[reflexivity|split;reflexivity].
   + split;[apply V293_encoded_memory_mapsto|reflexivity].
 - unfold LINV,V293_witness_li; eapply V293_wstate_star with(m1:=emp)(m2:=emp).
   + apply map_join_emp.
   + split;reflexivity.
   + split;[apply V293_witness_li_good|split;reflexivity].
Qed.

Lemma QEinternal_owned : forall hv,
 V293_wstate BLge emp(BLinternal hv) |=
 <||spec_done None||> ** V293_sched_exact_resource
 100%Z 101%Z 102%Z 103%Z 1%positive 2%positive 3%positive 4%positive 0 16
 V293_witness_li V293_idle_tid(V293_byteval hv).
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
     apply QEcurrent.
 - split;[apply V293_encoded_memory_mapsto|reflexivity].
Qed.
Lemma QEjoint_owned : forall hv out nest locked nc c,
 BLstate(BLmemory hv out nest locked nc c) |=
 ((<||spec_done None||> ** V293_sched_exact_resource
 100%Z 101%Z 102%Z 103%Z 1%positive 2%positive 3%positive 4%positive 0 16
 V293_witness_li V293_idle_tid(V293_byteval hv)) **
 (V293_prefix_frame 106%Z 103%Z 107%Z Tvoid 8%positive 10%positive V293_idle_entries V293_idle_tasks Aemp **
 V293_prefix_output Tvoid 10%positive out)) **
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
   + apply QEinternal_owned.
   + apply BLcaller_owned.
 - apply BLextra_owned.
Qed.
Definition QEready nc nest locked out c := V293_exit_ready_exact_pre
 100%Z 101%Z 102%Z 103%Z 1%positive 2%positive 3%positive 4%positive 0 16
 V293_witness_li V293_idle_tid(spec_done None)106%Z 107%Z Tvoid 8%positive 10%positive
 V293_idle_entries V293_idle_tasks 110%Z 111%Z 13%positive 14%positive 11%positive 12%positive
 nc BLnames nest locked out c.
Theorem QEready_owned : forall hv out nest locked nc c,
 BLstate(BLmemory hv out nest locked nc c) |= QEready nc nest locked out c.
Proof.
 intros. pose proof(QEjoint_owned hv out nest locked nc c)as Hs.
 unfold QEready,V293_exit_ready_exact_pre,V293_sched_exact_pre. sep normal. exists(V293_byteval hv).
 assert(B:0<256 /\ 16<256 /\ exists p,V293_bitmap_ready 0 16 p).
 { split;[lia| ]. split;[lia| ]. exists 12;vm_compute;intuition lia. }
 unfold V293_prefix_frame in *;sep auto;assumption.
Qed.

Definition QEphysical nc nest c :=
 V293_sched_exact_pre 100%Z 101%Z 102%Z 103%Z
 1%positive 2%positive 3%positive 4%positive 0 16 V293_witness_li V293_idle_tid(spec_done None) **
 ((V293_read_pointers Tvoid 8%positive 0 V293_idle_entries ** Aabsdata abstcblsid(abstcblist V293_idle_tasks)) **
 (Amapsto(13%positive,0%Z)Tint8 false(V293_byteval nc) **
  V293_rdy_raw_cells(V293_exit_cells 11%positive 12%positive nest 0)Aemp)) **
 (V293_prefix_output Tvoid 10%positive Vnull ** PV(14%positive,Int.zero)@Tint32|->Vint32 c).
Lemma QEphysical_good : forall nc nest c,GoodFunAsrt(QEphysical nc nest c).
Proof.
 intros. unfold QEphysical. split.
 - apply V293_sched_exact_pre_good;apply V293_witness_li_good.
 - unfold V293_prefix_output,V293_exit_cells,V293_interrupt_cells.
   cbn[V293_rdy_raw_cells Aptrmapsto GoodFunAsrt]. repeat split;try exact I.
Qed.
Lemma QEphysical_owned : forall nc nest c,
 BLstate(BLmemory 0 Vnull nest 0 nc c) |= QEphysical nc nest c.
Proof.
 intros. pose proof(QEready_owned 0 Vnull nest 0 nc c)as H.
 assert(U:BLstate(BLmemory 0 Vnull nest 0 nc c) |= QEphysical nc nest c ** (BLbindings ** Aemp)).
 { unfold QEready,V293_exit_ready_exact_pre,QEphysical,BLbindings,
   V293_exit_caller_bindings,V293_prefix_frame,V293_guard_cell,V293_counter_cell,
   V293_exit_guard_bindings,BLnames,V293_exit_cells,V293_interrupt_cells in *.
   cbn[V293_rdy_raw_cells]in *;clear -H;sep auto. }
 apply astar_r_aemp_elim. eapply astar_mono;[intros st Hst;exact Hst| |exact U].
 intros st Hst. apply astar_r_aemp_elim in Hst. apply BLbindings_empty;exact Hst.
Qed.
Lemma QEbig_owned : forall nc nest c run value, RCbigstate nc nest c run value |=
 ((QEphysical nc nest c) ** PV(15%positive,Int.zero)@Tint32|->value) **
 (V293_guard_cell 112%Z 16%positive run **
  (Alvarenv 120%Z Tint32(15%positive,0%Z) ** (BLbindings ** Aemp))).
Proof.
 intros.
 assert(H:RCbigstate nc nest c run value |=
  (((QEphysical nc nest c) ** PV(15%positive,Int.zero)@Tint32|->value) **
   V293_guard_cell 112%Z 16%positive run) **
  (Alvarenv 120%Z Tint32(15%positive,0%Z) ** (BLbindings ** Aemp))).
 { unfold RCbigstate. eapply V293_target_wstate_star with
 (m1:=RCbigmemory nc nest c run value)(m2:=emp)(o1:=V293_target_fixture_abs)(o2:=emp);try apply map_join_emp.
 - eapply V293_target_wstate_star with(m1:=RCbigjoined nc nest c value)(m2:=BLrun run)
   (o1:=V293_target_fixture_abs)(o2:=emp).
   + apply RCbig_run_join.
   + apply map_join_emp.
   + eapply V293_target_wstate_star with(m1:=BLmemory 0 Vnull nest 0 nc c)(m2:=BLsaved value)
     (o1:=V293_target_fixture_abs)(o2:=emp).
     * apply RCbig_saved_join.
     * apply map_join_emp.
     * eapply good_fun_asrt_absop with(p:=(QEphysical nc nest c))(le:=emp).
       -- apply QEphysical_good.
       -- apply QEphysical_owned.
     * split;[apply V293_encoded_memory_mapsto|reflexivity].
   + apply BLrun_owned.
 - apply BLcaller_names. }
 clear -H;sep auto.
Qed.
Definition QEspec I := V293_ISR_exact_sched_spec 200%Z 100%Z 101%Z 102%Z 103%Z
 1%positive 2%positive 3%positive 4%positive V293_witness_li I V293_witness_li_good.
Definition QEdata := V293_exit_same_exact_data
 100%Z 101%Z 102%Z 103%Z 1%positive 2%positive 3%positive 4%positive 0 16
 V293_witness_li V293_idle_tid 106%Z 107%Z Tvoid 8%positive 10%positive
 V293_idle_entries V293_idle_tasks 110%Z 111%Z 112%Z 120%Z
 13%positive 14%positive 16%positive 11%positive 12%positive 15%positive 12 BLnames.
Definition QEout := V293_exit_same_exact_result
 100%Z 101%Z 102%Z 103%Z 1%positive 2%positive 3%positive 4%positive 0 16
 V293_witness_li V293_idle_tid 106%Z 107%Z Tvoid 8%positive 10%positive
 V293_idle_entries V293_idle_tasks 110%Z 111%Z 112%Z 120%Z
 13%positive 14%positive 16%positive 11%positive 12%positive 15%positive 12 BLnames.
Definition QEstate enabled si ci nest c old : RstateOP :=
 (BLge,BLle,RCbigmemory 12 nest c 1 old,(fun _=>false),
  (enabled,si,ci),V293_target_fixture_abs,spec_done None).
Definition QEpre enabled si ci nest c old :=
 EX hv:val,<||spec_done None||> ** OS[(fun _=>false),enabled,si,ci] **
 QEdata nest hv Vnull c old.
Lemma QEdata_owned : forall nest c old,
 RCbigstate 12 nest c 1 old |= EX hv:val,QEdata nest hv Vnull c old.
Proof.
 intros nest c old. pose proof(QEbig_owned 12 nest c 1 old)as Held.
 unfold QEphysical,V293_sched_exact_pre,V293_sched_exact_resource in Held.
 unfold QEdata,V293_exit_same_exact_data,V293_exit_same_exact_core,BLnames,BLbindings,
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
Theorem QEpre_nonempty : forall enabled si ci nest c old,
 QEstate enabled si ci nest c old |= QEpre enabled si ci nest c old.
Proof.
 intros enabled si ci nest c old.
 assert(Data:QEstate enabled si ci nest c old |= EX hv:val,QEdata nest hv Vnull c old).
 { eapply goodfrm_prop.
   - intro hv;unfold QEdata. apply V293_exit_same_exact_data_good;[apply V293_witness_li_good|apply QSframe_good].
   - exact(QEdata_owned nest c old). }
 destruct Data as[hv Data]. unfold QEpre. exists hv. apply astar_l_aop'_intro;[ |reflexivity].
 apply astar_l_aie_intro with(i:=enabled)in Data;[ |reflexivity].
 apply astar_l_ais_intro with(i:=si)in Data;[ |reflexivity].
 apply astar_l_aisr_intro with(i:=fun _=>false)in Data;[ |reflexivity].
 apply astar_l_acs_intro with(i:=ci)in Data;[ |reflexivity].
 clear -Data;sep auto.
Qed.
Theorem QEbody : forall sd I enabled si ci nest c old,
 (gettopis si<=INUM)%nat -> nest<=1 ->
 InfRules(QEspec I)sd V293_witness_li I
 (fun result=>[|result=None|] **
 (<||spec_done None||> ** OS[(fun _=>false),enabled,si,ci] ** QEout c(Vint32 Int.zero))) Afalse
 (QEpre enabled si ci nest c old)
 (V293_exit_boundary_body 112%Z 108%Z 109%Z 120%Z 106%Z 103%Z 107%Z 110%Z
 111%Z 200%Z(V293_interrupt_handoff 103%Z 110%Z 107%Z)) Afalse V293_idle_tid.
Proof.
 intros. unfold QEpre,QEdata,QEout. apply ex_intro_rule;intro hv.
 apply V293_OSIntExit_same_exact_priority_body with(Hli:=V293_witness_li_good);
 try assumption;try lia;try reflexivity.
 - exists 12;vm_compute;repeat split;lia.
 - exact(proj1 V293_idle_relations).
 - exact(proj2 V293_idle_relations).
 - exact QSframe_good.
 - exact BLenv.
Qed.
Theorem QEboth_ie_and_nonempty_stacks :
 QEstate true (cons 0 nil)(cons false nil) 1 Int.one(Vint32 Int.one) |=
  QEpre true (cons 0 nil)(cons false nil) 1 Int.one(Vint32 Int.one) /\
 QEstate false (cons 0 nil)(cons false nil) 1 Int.one(Vint32 Int.one) |=
  QEpre false (cons 0 nil)(cons false nil) 1 Int.one(Vint32 Int.one).
Proof. split;apply QEpre_nonempty. Qed.

(* This pair checks the saved assignment only, not two full executions. *)
Theorem QEzero : forall Spec sd I r ri old,
 InfRules Spec sd V293_witness_li I r ri
 (<||spec_done None||> ** (V293_time_cell true 120%Z 15%positive old **
 CurLINV V293_witness_li V293_idle_tid))
 (sassign(evar 120%Z)(econst32 Int.zero))
 (<||spec_done None||> ** (V293_time_cell true 120%Z 15%positive(Vint32 Int.zero) **
 CurLINV V293_witness_li V293_idle_tid)) V293_idle_tid.
Proof. intros;apply V293_time_zero;intros s H;exact H. Qed.
Lemma QEsaved_read : forall enabled si ci nest c v s,
 s |= QEpre enabled si ci nest c(Vint32 v) ->
 evalval(evar 120%Z)(getsmem s)=Some(Vint32 v).
Proof.
 intros enabled si ci nest c v s [hv H].
 assert(C:s |= V293_time_cell true 120%Z 15%positive(Vint32 v) ** Atrue).
 { unfold QEdata,V293_exit_same_exact_data in H;clear -H;sep auto. }
 exact(proj1(V293_time_cell_read true 120%Z 15%positive v Atrue s C)).
Qed.
Theorem QEwithout_zero : forall enabled si ci nest c,
 ~(QEstate enabled si ci nest c(Vint32 Int.one) |=
 QEpre enabled si ci nest c(Vint32 Int.zero)).
Proof.
 intros enabled si ci nest c Bad.
 pose proof(QEsaved_read _ _ _ _ _ _ _ Bad)as Wrong.
 pose proof(QEsaved_read _ _ _ _ _ _ _(QEpre_nonempty enabled si ci nest c(Vint32 Int.one)))as Actual.
 rewrite Actual in Wrong;discriminate.
Qed.

Theorem QEscheduler_environment : forall resourceI RI sd,
 WFFunEnv(V293_OSSchedNew_internal_unit 200%Z 100%Z 101%Z 102%Z 103%Z 104%Z)
 (QEspec resourceI)sd V293_witness_li RI.
Proof. intros;apply V293_OSSchedNew_ISR_exact_WFFunEnv;discriminate. Qed.
(* Only the local assertion changes, on one fixed preexisting state. *)
Theorem QElocal_control : REstate |=CurLINV V293_shared_li OwnershipWaiting /\
 ~REstate |=p_local V293_shared_li OwnershipWaiting nil.
Proof. apply RLlocal_exactness_control. Qed.

Definition QEcallee (I:Inv) :=
 V293_sched_exact_pre 100%Z 101%Z 102%Z 103%Z
 1%positive 2%positive 3%positive 4%positive 0 16 V293_witness_li V293_idle_tid(spec_done None) **
 V293_sched_ISR_context I false (fun _=>false) nil nil.
Theorem QEcallee_nonempty : forall I hv out nc nest c,
 BLstate(BLmemory hv out nest 0 nc c) |= QEcallee I ** Atrue.
Proof.
 intros Inv hv out nc nest c. pose proof(QEready_owned hv out nest 0 nc c)as H.
 apply astar_l_aie_intro with(i:=false)in H;[ |reflexivity].
 apply astar_l_aisr_intro with(i:=fun _=>false)in H;[ |reflexivity].
 apply astar_l_ais_intro with(i:=nil)in H;[ |reflexivity].
 apply astar_l_acs_intro with(i:=nil)in H;[ |reflexivity].
 unfold QEcallee,QEready,V293_sched_ISR_context,V293_exit_ready_exact_pre in *.
 unfold V293_prefix_frame,V293_exit_cells,V293_interrupt_cells in *.
 cbn[V293_rdy_raw_cells]in *;clear -H;sep auto.
Qed.
Theorem QEactual_scheduler_call : forall I RI sd r ri,
 InfRules(QEspec I)sd V293_witness_li RI r ri
 (QEcallee I ** Atrue)(scall 200%Z nil)
 (EX result:option val,
 (V293_sched_exact_post 100%Z 101%Z 102%Z 103%Z
 1%positive 2%positive 3%positive 4%positive 0 16 V293_witness_li V293_idle_tid(spec_done None) result **
 V293_sched_ISR_context I false (fun _=>false) nil nil) ** Atrue)V293_idle_tid.
Proof.
 intros. unfold QEcallee,QEspec.
 apply V293_OSSchedNew_ISR_exact_call with(Hli:=V293_witness_li_good);try lia;try exact Logic.I.
 reflexivity.
Qed.
