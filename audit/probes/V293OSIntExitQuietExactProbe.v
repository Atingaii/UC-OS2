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
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitReadyDispatch.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitReadyHandoff.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyStorageInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyTaskInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.audit.probes.V293TaskRecordOwnershipProbe.
Require Import CertiOS.audit.probes.V293ReadyTaskInvariantProbe.
Require Import CertiOS.audit.probes.V293TaskRecordInvariantProbe.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitReadyBody.
Require Import CertiOS.audit.probes.V293OSIntExitReadyHandoffProbe.

Require Import CertiOS.framework.proof.rulesoundlib.
Require Import CertiOS.framework.proof.lmachLib.
Require Import CertiOS.framework.proof.invariant_prop.
Import ListNotations.
Local Open Scope nat_scope.

Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitBuilders.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitResourceBridge.

Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitChangedInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitReadyInternal.
Require Import CertiOS.audit.probes.V293OSIntExitReadyBodyProbe.

Require Import CertiOS.audit.probes.V293OSIntExitReadyInternalProbe.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitReadyDynamic.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitDynamic.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitUnifiedInternal.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptExitEnvironment.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCall.
Require Import CertiOS.framework.proof.toptheorem.

Require Import CertiOS.audit.probes.V293OSIntExitReadyDynamicProbe.
Require Import CertiOS.audit.probes.V293OSIntExitExactInternalProbe.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitExactDynamic.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedExactJoint.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptReadyLocal.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptReadyEnvironment.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitQuietExact.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitQuietExactDynamic.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedExactLocal.
Require Import CertiOS.audit.probes.V293InterruptReadyLocalProbe.
Require Import CertiOS.audit.probes.V293InterruptReadyEnvironmentProbe.
Definition Qfp:=V293_quiet_exact_dynamic_fpre
 100%Z 101%Z 102%Z 103%Z 105%Z 106%Z 108%Z 109%Z 112%Z 110%Z 111%Z
 92%positive 81%positive 80%positive 91%positive 82%positive 93%positive 94%positive 95%positive
 99%positive 96%positive 97%positive nil Aemp I.
Definition Qfq:=V293_quiet_exact_dynamic_fpost
 100%Z 101%Z 102%Z 103%Z 105%Z 106%Z 108%Z 109%Z 112%Z 110%Z 111%Z
 92%positive 81%positive 80%positive 91%positive 82%positive 93%positive 94%positive 95%positive
 99%positive 96%positive 97%positive nil Aemp I.
Definition Qspec:=V293_quiet_exact_dynamic_spec
 100%Z 101%Z 102%Z 103%Z 105%Z 106%Z 108%Z 109%Z 112%Z 110%Z 111%Z
 92%positive 81%positive 80%positive 91%positive 82%positive 93%positive 94%positive 95%positive
 99%positive 96%positive 97%positive nil Aemp I 300%Z 301%Z 200%Z.
Definition Qlg:=logic_ie false::logic_ie true::V293_quiet_exit_args
 1 2 0(spec_done None)false(fun _:hid=>false)nil nil.
Definition Qpre:=V293_exit_builder_cells 120%Z **
 getasrt(Qfp nil Qlg OwnershipWaiting) ** V293_exit_builder_domain 120%Z.
Definition Qpost result:=V293_exit_builder_cells 120%Z **
 getasrt(Qfq nil result Qlg OwnershipWaiting) ** V293_exit_builder_domain 120%Z.
Definition Qexternal nest:=<||spec_done None||> ** OS[(fun _:hid=>false),false,nil,nil] **
 (V293_quiet_globals 112%Z 110%Z 111%Z 99%positive 96%positive 97%positive **
 (Amapsto(99%positive,0%Z)Tint8 false(V293_byteval 1) **
 V293_rdy_raw_cells(V293_exit_cells 96%positive 97%positive nest 0)
 (p_local V293_shared_li OwnershipWaiting nil ** Aemp))).
Lemma Qliteral :
 getasrt(Qfp nil Qlg OwnershipWaiting)=[|V293_quiet_exit_valid 1 2 0 nil|] ** Qexternal 2 /\
 (forall result,getasrt(Qfq nil result Qlg OwnershipWaiting)=[|result=None|] ** Qexternal 1).
Proof. split;[ |intro result];reflexivity. Qed.
Lemma Qbuilders : BuildPreI RDprogram 300%Z nil Qlg Qfp OwnershipWaiting=Some Qpre /\
 BuildRetI RDprogram 300%Z nil Qlg Qfq OwnershipWaiting=Some Qpost.
Proof. split;reflexivity. Qed.
Theorem Qenvironment :
 WFFunEnv RDprogram Qspec V293_scheduler V293_shared_li RDinv /\
 WFIFun RDprogram Qspec V293_scheduler RDinv V293_shared_li.
Proof. split;unfold RDprogram,Qspec;
 [apply V293_quiet_exact_dynamic_WFFunEnv|apply V293_quiet_exact_dynamic_WFIFun];try discriminate;exact I. Qed.
(* Five actual disjoint cells. This is satisfiability, not boot reachability. *)
Definition Qcell b tp permission v:=V293_encoded_memory b 0 permission(encode_val tp v).
Definition Qcurrent:=Qcell 1%positive(Tptr V293_tcb_type)false(Vptr OwnershipWaiting).
Definition Qmemory:=merge(Qcell 98%positive Tint32 true(Vint32 Int.one))
 (merge(Qcell 99%positive Tint8 false(V293_byteval 1))
 (merge(Qcell 96%positive Tint8 true(V293_byteval 2))
 (merge(Qcell 97%positive Tint8 true(V293_byteval 0))Qcurrent))).
Definition Qstate M:=V293_wstate JBge JBle M.
Ltac Qapart b :=
 apply map_join_merge;apply map_disjoint;intros[other offset];
 destruct(Pos.eq_dec other b);[subst other;right;left|left];
 unfold Qcurrent,Qcell;
 repeat first[rewrite map_merge_semp by reflexivity|
 rewrite V293_encoded_memory_outside by(left;congruence)];reflexivity.
Lemma Qcurrent_owned : Qstate Qcurrent |=p_local V293_shared_li OwnershipWaiting nil.
Proof.
 assert(C:Qstate Qcurrent |=CurTid OwnershipWaiting).
 { exists V293_tcb_type;exists 1%positive.
   eapply V293_wstate_star with(m1:=emp)(m2:=Qcurrent).
   - apply map_join_comm;apply map_join_emp.
   - exists 1%positive;split;[vm_compute;reflexivity|repeat split;reflexivity].
   - split;[apply V293_encoded_memory_mapsto|reflexivity]. }
 unfold p_local,LINV,V293_shared_li;clear -C;sep auto;apply V293_switch_li_good.
Qed.
Lemma Qspatial : Qstate Qmemory |=
 Amapsto(98%positive,0%Z)Tint32 true(Vint32 Int.one) **
 (Amapsto(99%positive,0%Z)Tint8 false(V293_byteval 1) **
 (Amapsto(96%positive,0%Z)Tint8 true(V293_byteval 2) **
 (Amapsto(97%positive,0%Z)Tint8 true(V293_byteval 0) ** p_local V293_shared_li OwnershipWaiting nil))).
Proof.
 unfold Qstate,Qmemory.
 eapply V293_wstate_star;[Qapart 98%positive|split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
 eapply V293_wstate_star;[Qapart 99%positive|split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
 eapply V293_wstate_star;[Qapart 96%positive|split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
 eapply V293_wstate_star;[Qapart 97%positive|split;[apply V293_encoded_memory_mapsto|reflexivity]|apply Qcurrent_owned].
Qed.
Lemma Qnames : Qstate emp |=
 V293_quiet_globals 112%Z 110%Z 111%Z 99%positive 96%positive 97%positive **
 Alvarenv 120%Z Tint32(98%positive,0%Z).
Proof.
 apply V293_exit_empty_star;[split;reflexivity| | ].
 - unfold V293_quiet_globals;repeat split;
   (eexists;split;[vm_compute;reflexivity|repeat split;reflexivity]).
 - exists 98%positive;split;[vm_compute;reflexivity|repeat split;reflexivity].
Qed.
Theorem Qentry_nonempty : Qstate Qmemory |=Qpre.
Proof.
 assert(H:Qstate Qmemory |=
 (V293_quiet_globals 112%Z 110%Z 111%Z 99%positive 96%positive 97%positive **
 Alvarenv 120%Z Tint32(98%positive,0%Z)) **
 (Amapsto(98%positive,0%Z)Tint32 true(Vint32 Int.one) **
 (Amapsto(99%positive,0%Z)Tint8 false(V293_byteval 1) **
 (Amapsto(96%positive,0%Z)Tint8 true(V293_byteval 2) **
 (Amapsto(97%positive,0%Z)Tint8 true(V293_byteval 0) ** p_local V293_shared_li OwnershipWaiting nil))))).
 { eapply V293_wstate_star with(m1:=emp)(m2:=Qmemory).
   - apply map_join_comm;apply map_join_emp.
   - exact Qnames.
   - exact Qspatial. }
 apply astar_l_adomlenv_intro with(d:=[(120%Z,Tint32)])in H.
 2:{ change(eq_dom_env(RBle 120%Z)[(120%Z,Tint32)]);apply RBsingle_domain. }
 apply astar_l_aisr_intro with(i:=fun _:hid=>false)in H;[ |reflexivity].
 apply astar_l_aie_intro with(i:=false)in H;[ |reflexivity].
 apply astar_l_ais_intro with(i:=nil)in H;[ |reflexivity].
 apply astar_l_acs_intro with(i:=nil)in H;[ |reflexivity].
 apply astar_l_aop'_intro with(aop:=spec_done None)in H;[ |reflexivity].
 unfold Qpre;rewrite(proj1 Qliteral).
 assert(V:V293_quiet_exit_valid 1 2 0 nil)by(unfold V293_quiet_exit_valid;cbn;lia).
 unfold Qexternal,V293_exit_builder_cells,V293_exit_builder_domain,Alvarmapsto,Alvarenv',Aptrmapsto,
 V293_exit_cells,V293_interrupt_cells in *;cbn[V293_rdy_raw_cells addrval_to_addr]in *.
 clear -H V;sep normal;exists(Vint32 Int.one);exists 98%positive;sep auto.
Qed.
Theorem Qactual_contract :
 InfRules Qspec V293_scheduler V293_shared_li RDinv Qpost Afalse Qpre
 (V293_exit_boundary_body 112%Z 110%Z 111%Z 120%Z 105%Z 103%Z 106%Z 108%Z 109%Z
 200%Z(V293_interrupt_handoff 103%Z 108%Z 106%Z))Afalse OwnershipWaiting.
Proof.
 eapply(V293_OSIntExit_quiet_exact_dynamic_contract
 100%Z 101%Z 102%Z 103%Z 105%Z 106%Z 108%Z 109%Z 112%Z 110%Z 111%Z 120%Z
 92%positive 81%positive 80%positive 91%positive 82%positive 93%positive 94%positive 95%positive
 99%positive 96%positive 97%positive nil Aemp I RDprogram 300%Z Qspec 200%Z nil Qlg OwnershipWaiting Qpre Qpost);
 try discriminate;try reflexivity;exact I.
Qed.
Theorem Qactual_call : forall RI,
 InfRules Qspec V293_scheduler V293_shared_li RI Qpost Afalse
 (getasrt(Qfp nil Qlg OwnershipWaiting) **
 (V293_exit_builder_cells 120%Z ** V293_exit_builder_domain 120%Z))
 (scall 300%Z nil)
 (EX result:option val,getasrt(Qfq nil result Qlg OwnershipWaiting) **
 (V293_exit_builder_cells 120%Z ** V293_exit_builder_domain 120%Z))OwnershipWaiting.
Proof.
 intro;unfold Qlg,Qfp,Qfq,Qspec.
 apply V293_OSIntExit_quiet_exact_dynamic_call;try reflexivity;try lia.
 unfold V293_exit_builder_cells,V293_exit_builder_domain,Alvarmapsto,Alvarenv',Aptrmapsto;
 cbn[GoodFrm];repeat split;try exact I;intros;repeat split;exact I.
Qed.
Theorem Qcall_entry_nonempty : Qstate Qmemory |=
 getasrt(Qfp nil Qlg OwnershipWaiting) **
 (V293_exit_builder_cells 120%Z ** V293_exit_builder_domain 120%Z).
Proof. pose proof Qentry_nonempty as H;unfold Qpre in H;clear -H;sep auto. Qed.
(* Only the local assertion changes on one fixed preexisting state. *)
Theorem Qlocal_control : REstate |=CurLINV V293_shared_li OwnershipWaiting /\
 ~REstate |=p_local V293_shared_li OwnershipWaiting nil.
Proof. apply RLlocal_exactness_control. Qed.
