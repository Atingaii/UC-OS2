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

Definition RBfp nest c aop ci:=V293_ready_builder_fpre
 100%Z 101%Z 102%Z 103%Z 105%Z 106%Z 108%Z 109%Z 112%Z 110%Z 111%Z
 92%positive 81%positive 80%positive 91%positive 82%positive 93%positive 94%positive 95%positive
 99%positive 96%positive 97%positive 16 0 6 nest RTentries nil OwnershipTasks emp Int.zero
 (V293_byteval 88)(Vptr OwnershipWaiting)c aop nil ci Aemp I.
Definition RBfq aop ci:=V293_ready_builder_fpost
 100%Z 101%Z 102%Z 103%Z 105%Z 106%Z 108%Z 109%Z 112%Z 110%Z 111%Z
 92%positive 81%positive 80%positive 91%positive 82%positive 93%positive 94%positive 95%positive
 99%positive 96%positive 97%positive nil aop nil ci Aemp I.
Definition RBprogram saved sched_id:fid->option function:=
 fun f=>if Z.eq_dec f 300%Z then Some(V293_exit_boundary_function 112%Z 110%Z 111%Z saved
 105%Z 103%Z 106%Z 108%Z 109%Z sched_id(V293_interrupt_handoff 103%Z 108%Z 106%Z))else None.
Definition RBpre saved nest c aop ci:=V293_exit_builder_cells saved **
 getasrt(RBfp nest c aop ci nil nil OwnershipWaiting) ** V293_exit_builder_domain saved.
Definition RBpost saved aop ci result:=V293_exit_builder_cells saved **
 getasrt(RBfq aop ci nil result nil OwnershipWaiting) ** V293_exit_builder_domain saved.
Lemma RBbuilders : forall saved sched_id nest c aop ci,
 BuildPreI(RBprogram saved sched_id)300%Z nil nil(RBfp nest c aop ci)OwnershipWaiting=Some(RBpre saved nest c aop ci) /\
 BuildRetI(RBprogram saved sched_id)300%Z nil nil(RBfq aop ci)OwnershipWaiting=Some(RBpost saved aop ci).
Proof. intros;split;reflexivity. Qed.
Definition RBglobals:=V293_exit_builder_globals 105%Z 106%Z 108%Z 109%Z 110%Z 111%Z 112%Z
 V293_tcb_type 82%positive 93%positive 94%positive 95%positive 96%positive 97%positive 99%positive.
Lemma RBglobals_owned : forall ci aop,
 (JBge,JBle,(emp:mem),(fun _:hid=>false),(false,nil,ci),(emp:osabst),aop)|=RBglobals.
Proof.
 intros;unfold RBglobals,V293_exit_builder_globals;repeat split;
 (eexists;split;[vm_compute;reflexivity|repeat split;reflexivity]).
Qed.
Definition RBle(saved:var):=set emp saved(98%positive,Tint32).
Lemma RBsingle_domain : forall saved,eq_dom_env(RBle saved)((saved,Tint32)::nil).
Proof.
 intros saved x t;split.
 - intros[H|H];[inversion H;subst;eexists;unfold RBle;apply map_get_set|contradiction].
 - intros[b H];destruct(Z.eq_dec x saved);[subst;unfold RBle in H;rewrite map_get_set in H;inversion H;left;reflexivity| ].
   unfold RBle in H;rewrite map_get_set' in H by congruence;vm_compute in H;discriminate.
Qed.
Lemma RBvalid : forall nest,nest<=1 ->
 V293_changed_builder_valid V293_tcb_type 16 0 6 nest RTentries OwnershipTasks OwnershipWaiting.
Proof.
 intros nest N;unfold V293_changed_builder_valid.
 destruct RTliteral_rel as[Low[High[Ready[Bitmap Table]]]].
 split;[exact Low| ];split;[exact High| ];split;[exact Ready| ].
 split;[lia| ];split;[exact N| ];split;[vm_compute;discriminate| ].
 split;[exact Bitmap| ];split;[exact Table| ];split;[vm_compute;repeat constructor| ].
 exists(Int.repr 6,wait(os_stat_sem(72%positive,Int.repr 5))Int.one,Vptr(120%positive,Int.repr 7));vm_compute;reflexivity.
Qed.
Theorem RBpre_owned : forall nest c old ci aop,nest<=1 ->
 JBstate(JBmemory nest c old)ci(sched;;aop)|=RBpre 120%Z nest c aop ci.
Proof.
 intros nest c old ci aop Nest.
 pose proof(JBentry nest c old ci aop ltac:(lia))as Entry.
 assert(WithGlobals:JBstate(JBmemory nest c old)ci(sched;;aop)|=RBglobals **
 (<||sched;;aop||> ** OS[(fun _:hid=>false),false,nil,ci] ** JBdata nest c old)).
 { unfold JBstate;eapply JBstar with(m1:=emp)(o1:=emp).
   - apply map_join_comm;apply map_join_emp.
   - apply map_join_comm;apply map_join_emp.
   - apply RBglobals_owned.
   - exact Entry. }
 apply astar_l_adomlenv_intro with(d:=((120%Z,Tint32)::nil))in WithGlobals.
 2:{ change(eq_dom_env(RBle 120%Z)((120%Z,Tint32)::nil));apply RBsingle_domain. }
 assert(Valid:V293_changed_builder_valid V293_tcb_type 16 0 6 nest RTentries OwnershipTasks OwnershipWaiting)
 by(apply RBvalid;assumption).
 unfold RBpre,RBfp,V293_ready_builder_fpre,getasrt,V293_ready_builder_pre,
 V293_ready_builder_external,V293_ready_builder_memory,RBglobals,JBdata,
 V293_exit_ready_body_data,V293_exit_ready_body_core,
 V293_exit_ready_body_bindings,V293_handoff_byte,V293_counter_cell,
 V293_counter_bindings,V293_handoff_binding,V293_time_cell,V293_time_binding,
 V293_exit_builder_cells,V293_exit_builder_domain,Alvarmapsto,Alvarenv',Aptrmapsto,
 V293_exit_cells,V293_interrupt_cells in *.
 cbn[V293_rdy_raw_cells V293_storage addrval_to_addr]in *.
 clear -WithGlobals Valid;sep normal in WithGlobals;sep normal;
 exists(Vint32 old);exists 98%positive;sep auto.
 do 6 (eapply astar_mono in WithGlobals;
 [apply astar_l_aemp_elim in WithGlobals|intros s[G _];apply agvarenv_elim in G;exact(proj2 G)|intros s HS;exact HS]).
 destruct WithGlobals as[G _];apply agvarenv_elim in G;exact(proj2 G).
Qed.
Theorem RBentry_nonempty : forall nest c(old:int32)ci aop,nest<=1 ->exists st,
 st|=RBpre 120%Z nest c aop ci /\
 V293_highest_ready OwnershipTasks OwnershipReady /\ OwnershipReady<>OwnershipWaiting.
Proof.
 intros nest c old ci aop N;exists(JBstate(JBmemory nest c old)ci(sched;;aop));split.
 - apply RBpre_owned;exact N.
 - destruct(JBentry_nonempty nest c old ci aop N)as(s&S&Highest&Different);tauto.
Qed.
Theorem RBzero_max_entry : forall(old:int32)ci aop,exists st,
 st|=RBpre 120%Z 0(Int.repr Int.max_unsigned)aop ci.
Proof. intros;exists(JBstate(JBmemory 0(Int.repr Int.max_unsigned)old)ci(sched;;aop));apply RBpre_owned;lia. Qed.
Theorem RBactual_contract : forall Spec sched_id nest c ci aop,
 Spec sched_id=Some
 (V293_critical_fpre 100%Z 101%Z 102%Z 103%Z 92%positive 81%positive 80%positive 91%positive
 V293_shared_li V293_opened_inv V293_switch_li_good,
 V293_critical_fpost 100%Z 101%Z 102%Z 103%Z 92%positive 81%positive 80%positive 91%positive
 V293_shared_li V293_opened_inv V293_switch_li_good,(Tvoid,nil)) ->
 InfRules Spec V293_scheduler V293_shared_li
 (V293_ready_storage_inv 80%positive 81%positive 82%positive 106%Z V293_tcb_type JBcells)
 (RBpost 120%Z aop ci)Afalse(RBpre 120%Z nest c aop ci)
 (V293_exit_boundary_body 112%Z 110%Z 111%Z 120%Z 105%Z 103%Z 106%Z 108%Z 109%Z sched_id
 (V293_interrupt_handoff 103%Z 108%Z 106%Z))Afalse OwnershipWaiting.
Proof.
 intros. eapply V293_OSIntExit_ready_builder_contract with
 (P:=RBprogram 120%Z sched_id)(f:=300%Z)(vl:=nil)(lg:=nil)
 (unmap:=100%Z)(group:=101%Z)(rows:=102%Z)
 (bo:=93%positive)(lo:=16)(hi:=0)(nc:=6)(nest:=nest)
 (entries:=RTentries)(tasks:=OwnershipTasks)(events:=emp)(now:=Int.zero)
 (hv:=V293_byteval 88)(out:=Vptr OwnershipWaiting)(c:=c)(aop:=aop)
 (si:=nil)(ci:=ci)(extra:=Aemp)(EG:=I);
 try discriminate;try exact I;try eassumption.
 - reflexivity.
 - reflexivity.
 - reflexivity.
Qed.
Theorem RBarity_control : forall saved sched_id nest c aop ci,
 BuildPreI(RBprogram saved sched_id)300%Z[Vint32 Int.zero]nil(RBfp nest c aop ci)OwnershipWaiting=None.
Proof. intros;reflexivity. Qed.
Lemma RBreturn_arity_observation : forall saved sched_id aop ci,
 BuildRetI(RBprogram saved sched_id)300%Z[Vint32 Int.zero]nil(RBfq aop ci)OwnershipWaiting=Some(RBpost saved aop ci).
Proof. intros;reflexivity. Qed.

(* Only the local name and binding change; no physical byte changes.
   This checks the builder/name boundary, not two complete executions. *)
Definition RBrenamed_state saved nest c old aop:RstateOP:=
 (JBge,RBle saved,JBmemory nest c old,(fun _:hid=>false),(false,nil,nil),
 RIabstract OwnershipWaiting,sched;;aop).
Lemma RBrenamed_pre : forall saved nest c old aop,nest<=1 ->
 RBrenamed_state saved nest c old aop|=RBpre saved nest c aop nil.
Proof.
 intros saved nest c old aop N;pose proof(RBpre_owned nest c old nil aop N)as H.
 assert(U:JBstate(JBmemory nest c old)nil(sched;;aop)|=V293_exit_builder_domain 120%Z **
 (V293_exit_builder_cells 120%Z ** getasrt(RBfp nest c aop nil nil nil OwnershipWaiting))).
 { unfold RBpre in H;clear -H;sep auto. }
 unfold V293_exit_builder_domain in U;apply astar_l_adomlenv_elim in U as[_ U].
 unfold V293_exit_builder_cells,Alvarmapsto,Alvarenv',Aptrmapsto in U;
 cbn[addrval_to_addr]in U;sep normal in U;destruct U as[value[bs U]].
 apply astar_l_alvarenv_elim in U as[Bind U].
 destruct Bind as[_ Bind];change(get JBle 120%Z=Some(bs,Tint32))in Bind.
 vm_compute in Bind;inversion Bind;subst bs.
 assert(V:RBrenamed_state saved nest c old aop|=
 Amapsto(98%positive,Int.unsigned Int.zero)Tint32 true value **
 getasrt(RBfp nest c aop nil nil nil OwnershipWaiting)).
 { unfold RBrenamed_state;unfold JBstate in U.
   eapply good_fun_asrt_absop;[split;[exact I|exact(getprop(RBfp nest c aop nil nil nil OwnershipWaiting))]|exact U]. }
 apply astar_l_alvarenv_intro with(x:=saved)(t:=Tint32)(l:=(98%positive,Int.unsigned Int.zero))in V.
 2:{ split;[reflexivity|change(get(RBle saved)saved=Some(98%positive,Tint32));unfold RBle;apply map_get_set]. }
 apply astar_l_adomlenv_intro with(d:=((saved,Tint32)::nil))in V.
 2:{ apply RBsingle_domain. }
 unfold RBpre,V293_exit_builder_cells,V293_exit_builder_domain,Alvarmapsto,Alvarenv',Aptrmapsto;
 cbn[addrval_to_addr];clear -V;sep normal;exists value;exists 98%positive;sep auto.
Qed.
Theorem RBshadow_control : forall sched_id nest c old aop,nest<=1 ->
 BuildPreI(RBprogram 112%Z sched_id)300%Z nil nil(RBfp nest c aop nil)OwnershipWaiting=Some(RBpre 112%Z nest c aop nil) /\
 JBstate(JBmemory nest c old)nil(sched;;aop)|=RBpre 120%Z nest c aop nil /\
 RBrenamed_state 112%Z nest c old aop|=RBpre 112%Z nest c aop nil /\
 getmem(JBstate(JBmemory nest c old)nil(sched;;aop))=getmem(RBrenamed_state 112%Z nest c old aop) /\
 get(getgenv(RBrenamed_state 112%Z nest c old aop))112%Z=Some(99%positive,Tint8) /\
 get(getlenv(JBstate(JBmemory nest c old)nil(sched;;aop)))112%Z=None /\
 get(getlenv(RBrenamed_state 112%Z nest c old aop))112%Z=Some(98%positive,Tint32) /\
 ~(RBrenamed_state 112%Z nest c old aop|=V293_handoff_binding 112%Z 99%positive ** Atrue).
Proof.
 intros sched_id nest c old aop N.
 split;[reflexivity| ];split;[apply RBpre_owned;assumption| ];
 split;[apply RBrenamed_pre;assumption| ];split;[reflexivity| ];
 split;[vm_compute;reflexivity| ];split;[vm_compute;reflexivity| ];
 split;[vm_compute;reflexivity| ].
 intro H;assert(E:get(getlenv(RBrenamed_state 112%Z nest c old aop))112%Z=None).
 { eapply V293_star_env_l with(E:=fun ge le=>get le 112%Z=None);[ |exact H].
   intros s HS;exact(proj2(V293_handoff_binding_env _ _ _ HS)). }
 vm_compute in E;discriminate.
Qed.
