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
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitChangedInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitBuilders.
Require Import CertiOS.audit.probes.V293OSIntExitChangedBodyProbe.

Definition CBfp nest c aop:=V293_changed_builder_fpre
 100%Z 101%Z 102%Z 103%Z 106%Z 107%Z 113%Z 111%Z 114%Z 115%Z 116%Z
 1%positive 2%positive 3%positive 4%positive 8%positive 10%positive 11%positive 12%positive
 13%positive 14%positive 15%positive Tvoid 0 16 4 nest(V293_current_mode_entries true)nil
 (V293_current_mode_tasks true)emp Int.zero(V293_byteval 0)(Vptr V293_idle_tid)c aop nil nil Aemp I.
Definition CBfq aop:=V293_changed_builder_fpost
 100%Z 101%Z 102%Z 103%Z 106%Z 107%Z 113%Z 111%Z 114%Z 115%Z 116%Z
 1%positive 2%positive 3%positive 4%positive 8%positive 10%positive 11%positive 12%positive
 13%positive 14%positive 15%positive Tvoid(V293_current_mode_entries true)nil aop nil nil Aemp I.
Definition CBprogram saved sched_id:fid->option function:=
 fun f=>if Z.eq_dec f 300%Z then Some(V293_exit_boundary_function 114%Z 115%Z 116%Z saved
 106%Z 103%Z 107%Z 113%Z 111%Z sched_id(V293_interrupt_handoff 103%Z 113%Z 107%Z))else None.
Definition CBpre saved nest c aop:=V293_exit_builder_cells saved **
 getasrt(CBfp nest c aop nil nil V293_idle_tid) ** V293_exit_builder_domain saved.
Definition CBpost saved aop result:=V293_exit_builder_cells saved **
 getasrt(CBfq aop nil result nil V293_idle_tid) ** V293_exit_builder_domain saved.
Lemma CBbuilders : forall saved sched_id nest c aop,
 BuildPreI(CBprogram saved sched_id)300%Z nil nil(CBfp nest c aop)V293_idle_tid=Some(CBpre saved nest c aop) /\
 BuildRetI(CBprogram saved sched_id)300%Z nil nil(CBfq aop)V293_idle_tid=Some(CBpost saved aop).
Proof. intros;split;reflexivity. Qed.
Definition CBglobals:=V293_exit_builder_globals 106%Z 107%Z 113%Z 111%Z 115%Z 116%Z 114%Z
 Tvoid 8%positive 10%positive 11%positive 12%positive 14%positive 15%positive 13%positive.
Definition CBenv:=CBglobals **
 (V293_sched_globals 100%Z 101%Z 102%Z 103%Z 1%positive 2%positive 3%positive 4%positive **
 (Alvarenv 117%Z Tint32(16%positive,0%Z) ** V293_exit_builder_domain 117%Z)).
Lemma CBenv_owned : V293_target_wstate CXge CXle emp emp|=CBenv.
Proof.
 unfold CBenv.
 repeat(eapply V293_target_wstate_star with(m1:=emp)(m2:=emp)(o1:=emp)(o2:=emp);
 [apply map_join_emp|apply map_join_emp| | ]).
 - unfold CBglobals,V293_exit_builder_globals;repeat split;
   (eexists;split;[vm_compute;reflexivity|repeat split;reflexivity]).
 - unfold V293_sched_globals;repeat split;
   (eexists;split;[vm_compute;reflexivity|repeat split;reflexivity]).
 - exists 16%positive;split;[vm_compute;reflexivity|repeat split;reflexivity].
 - unfold V293_exit_builder_domain;split;[ |repeat split;reflexivity].
   intros x t;split.
   + intros[H|H];[inversion H;subst;eexists;vm_compute;reflexivity|contradiction].
   + intros[b H];change(get CXle x=Some(b,t))in H;destruct(Z.eq_dec x 117%Z);[subst;vm_compute in H;inversion H;left;reflexivity| ].
     unfold CXle in H;rewrite map_get_set' in H by congruence;vm_compute in H;discriminate.
Qed.
Definition CBresources nest c old:=CBenv **
 (((DXphysical ** DXowned 4 c) ** CXcontrol_owned nest old) **
 V293_shared_fields V293_idle_tid(V293_current_mode_tasks true)emp Int.zero).
Lemma CBresources_owned : forall nest c old,
 V293_target_wstate CXge CXle(CXmemory nest c old)
 (V293_shared_fixture_abs V293_idle_tid(V293_current_mode_tasks true)emp Int.zero)|=CBresources nest c old.
Proof.
 intros;unfold CBresources.
 eapply V293_target_wstate_star with(m1:=emp)(o1:=emp).
 - apply map_join_comm;apply map_join_emp.
 - apply map_join_comm;apply map_join_emp.
 - apply CBenv_owned.
 - eapply V293_target_wstate_star with(m2:=emp)(o1:=emp).
   + apply map_join_emp.
   + apply map_join_comm;apply map_join_emp.
   + apply CXphysical_all.
   + unfold V293_shared_fixture_abs,V293_shared_fields.
     repeat(eapply V293_target_wstate_star;[apply map_join_emp|apply map_join_merge;
      apply map_disjoint;intros key;destruct key;simpl;auto|split;reflexivity| ]).
     split;reflexivity.
Qed.
Lemma CBresources_aop_free : forall nest c old,can_change_aop(CBresources nest c old).
Proof.
 intros;unfold CBresources,CBenv,CBglobals,V293_exit_builder_globals,V293_exit_builder_domain,
 DXphysical,DXowned,CXcontrol_owned,V293_handoff_byte,V293_handoff_binding,V293_counter_cell,
 V293_counter_bindings,V293_sched_globals,V293_shared_fields,V293_inputs_full,Agvarmapsto,Aptrmapsto.
 cbn[can_change_aop];repeat split;try exact I;apply V293_array_aop_independent.
Qed.
Lemma CBvalid : forall nest,nest<=1 ->
 V293_changed_builder_valid Tvoid 0 16 4 nest(V293_current_mode_entries true)
 (V293_current_mode_tasks true)V293_idle_tid.
Proof.
 intros nest N;unfold V293_changed_builder_valid.
 split;[lia| ];split;[lia| ];split.
 - exists 12;vm_compute;intuition lia.
 - split;[lia| ];split;[exact N| ];split;[vm_compute;discriminate| ].
   split;[exact(proj1(V293_current_mode_relations true))| ].
   split;[exact(proj1(proj2(V293_current_mode_relations true)))| ].
   split;[vm_compute;repeat constructor| ].
   exists(Int.repr 4,wait os_stat_time Int.one,Vnull);vm_compute;reflexivity.
Qed.
Theorem CBpre_owned : forall nest c old aop,nest<=1 ->
 CXstate nest c old aop|=CBpre 117%Z nest c aop.
Proof.
 intros nest c old aop Nest;pose proof(CBresources_owned nest c old)as H.
 pose proof(@change_aop_rule _ _ _(sched;;aop)_ H(CBresources_aop_free nest c old))as Held.
 change(CXstate nest c old aop|=CBresources nest c old)in Held.
 apply astar_l_aop'_intro with(aop:=sched;;aop)in Held;[ |reflexivity].
 assert(C:CXstate nest c old aop|=Aisr(fun _:hid=>false) **
 (Aie false ** (Ais nil ** (Acs nil ** (<||sched;;aop||> ** CBresources nest c old))))).
 { apply astar_l_aisr_intro;[apply astar_l_aie_intro;[apply astar_l_ais_intro;
   [apply astar_l_acs_intro;[exact Held|reflexivity]|reflexivity]|reflexivity]|reflexivity]. }
 assert(V:V293_changed_builder_valid Tvoid 0 16 4 nest(V293_current_mode_entries true)
 (V293_current_mode_tasks true)V293_idle_tid)by(apply CBvalid;assumption).
 unfold CBpre,CBfp,V293_changed_builder_fpre,getasrt,V293_changed_builder_pre,
 V293_changed_builder_external,V293_changed_builder_memory,CBresources,CBenv,CBglobals,
 V293_exit_builder_cells,Alvarmapsto,Alvarenv',Aptrmapsto,V293_handoff_byte,V293_counter_cell,
 V293_time_cell,V293_time_binding,DXphysical,DXowned,CXcontrol_owned,
 V293_exit_cells,V293_interrupt_cells in *;
 unfold V293_handoff_byte,V293_counter_cell,V293_handoff_binding,V293_counter_bindings,Aptrmapsto in *;
 cbn[V293_rdy_raw_cells V293_storage addrval_to_addr]in *;clear -C V;
 sep normal in C;sep normal;exists(Vint32 old);exists 16%positive;sep auto.
 do 2 (eapply astar_mono in C;
 [apply astar_l_aemp_elim in C|intros s[G _];apply agvarenv_elim in G;exact(proj2 G)|intros s HS;exact HS]).
 exact C.
Qed.


Theorem CBentry_nonempty : forall c(old:int32)aop,exists st,
 st|=CBpre 117%Z 1 c aop /\
 V293_highest_ready(V293_current_mode_tasks true)(V293_switch_target true) /\
 V293_switch_target true<>V293_idle_tid.
Proof.
 intros;exists(CXstate 1 c old aop);split;[apply CBpre_owned;lia| ].
 split;[exact(V293_shared_case_highest true)|vm_compute;discriminate].
Qed.
Theorem CBzero_max_entry : forall(old:int32)aop,exists st,
 st|=CBpre 117%Z 0(Int.repr Int.max_unsigned)aop.
Proof. intros;exists(CXstate 0(Int.repr Int.max_unsigned)old aop);apply CBpre_owned;lia. Qed.
Theorem CBactual_contract : forall Spec sched_id nest c aop,
 Spec sched_id=Some
 (V293_critical_fpre 100%Z 101%Z 102%Z 103%Z 1%positive 2%positive 3%positive 4%positive
 V293_shared_li V293_opened_inv V293_switch_li_good,
 V293_critical_fpost 100%Z 101%Z 102%Z 103%Z 1%positive 2%positive 3%positive 4%positive
 V293_shared_li V293_opened_inv V293_switch_li_good,(Tvoid,nil)) ->
 InfRules Spec V293_scheduler V293_shared_li(V293_storage_inv CXcells 107%Z Tvoid)
 (CBpost 117%Z aop)Afalse(CBpre 117%Z nest c aop)
 (V293_exit_boundary_body 114%Z 115%Z 116%Z 117%Z 106%Z 103%Z 107%Z 113%Z 111%Z sched_id
 (V293_interrupt_handoff 103%Z 113%Z 107%Z))Afalse V293_idle_tid.
Proof.
 intros. eapply V293_OSIntExit_changed_builder_contract with
 (P:=CBprogram 117%Z sched_id)(f:=300%Z)(vl:=nil)(lg:=nil)
 (unmap:=100%Z)(group:=101%Z)(rows:=102%Z)
 (bo:=10%positive)(lo:=0)(hi:=16)(nc:=4)(nest:=nest)
 (tasks:=V293_current_mode_tasks true)(events:=emp)(now:=Int.zero)
 (hv:=V293_byteval 0)(out:=Vptr V293_idle_tid)(c:=c)(aop:=aop)
 (si:=nil)(ci:=nil)(extra:=Aemp)(EG:=I);
 try discriminate;try exact I;try eassumption.
 - reflexivity.
 - reflexivity.
 - reflexivity.
Qed.
Theorem CBarity_control : forall saved sched_id nest c aop,
 BuildPreI(CBprogram saved sched_id)300%Z[Vint32 Int.zero]nil(CBfp nest c aop)V293_idle_tid=None.
Proof. intros;reflexivity. Qed.
Lemma CBreturn_arity_observation : forall saved sched_id aop,
 BuildRetI(CBprogram saved sched_id)300%Z[Vint32 Int.zero]nil(CBfq aop)V293_idle_tid=Some(CBpost saved aop).
Proof. intros;reflexivity. Qed.

Require Import CertiOS.framework.proof.rulesoundlib.
(* Only the declared local identifier and its binding change; all bytes stay fixed.
   This is a builder/name-separation control, not two function executions. *)
Definition CBle(saved:var):=set emp saved(16%positive,Tint32).
Definition CBrenamed_state saved nest c old aop:RstateOP:=
 (CXge,CBle saved,CXmemory nest c old,(fun _:hid=>false),(false,nil,nil),
 V293_shared_fixture_abs V293_idle_tid(V293_current_mode_tasks true)emp Int.zero,sched;;aop).
Lemma CBsingle_domain : forall saved,eq_dom_env(CBle saved)((saved,Tint32)::nil).
Proof.
 intros saved x t;split.
 - intros[H|H];[inversion H;subst;eexists;unfold CBle;apply map_get_set|contradiction].
 - intros[b H];destruct(Z.eq_dec x saved);[subst;unfold CBle in H;rewrite map_get_set in H;inversion H;left;reflexivity| ].
   unfold CBle in H;rewrite map_get_set' in H by congruence;vm_compute in H;discriminate.
Qed.
Lemma CBrenamed_pre : forall saved nest c old aop,nest<=1 ->
 CBrenamed_state saved nest c old aop|=CBpre saved nest c aop.
Proof.
 intros saved nest c old aop N;pose proof(CBpre_owned nest c old aop N)as H.
 assert(U:CXstate nest c old aop|=V293_exit_builder_domain 117%Z **
 (V293_exit_builder_cells 117%Z ** getasrt(CBfp nest c aop nil nil V293_idle_tid))).
 { unfold CBpre in H;clear -H;sep auto. }
 unfold V293_exit_builder_domain in U;apply astar_l_adomlenv_elim in U as[_ U].
 unfold V293_exit_builder_cells,Alvarmapsto,Alvarenv',Aptrmapsto in U;
 cbn[addrval_to_addr]in U;sep normal in U;destruct U as[value[bs U]].
 apply astar_l_alvarenv_elim in U as[Bind U].
 destruct Bind as[_ Bind];change(get CXle 117%Z=Some(bs,Tint32))in Bind.
 vm_compute in Bind;inversion Bind;subst bs.
 assert(V:CBrenamed_state saved nest c old aop|=
 Amapsto(16%positive,Int.unsigned Int.zero)Tint32 true value **
 getasrt(CBfp nest c aop nil nil V293_idle_tid)).
 { unfold CBrenamed_state;unfold CXstate in U.
   eapply good_fun_asrt_absop;[split;[exact I|exact(getprop(CBfp nest c aop nil nil V293_idle_tid))]|exact U]. }
 apply astar_l_alvarenv_intro with(x:=saved)(t:=Tint32)(l:=(16%positive,Int.unsigned Int.zero))in V.
 2:{ split;[reflexivity|change(get(CBle saved)saved=Some(16%positive,Tint32));unfold CBle;apply map_get_set]. }
 apply astar_l_adomlenv_intro with(d:=((saved,Tint32)::nil))in V.
 2:{ apply CBsingle_domain. }
 unfold CBpre,V293_exit_builder_cells,V293_exit_builder_domain,Alvarmapsto,Alvarenv',Aptrmapsto;
 cbn[addrval_to_addr];clear -V;sep normal;exists value;exists 16%positive;sep auto.
Qed.
Theorem CBshadow_control : forall sched_id nest c old aop,nest<=1 ->
 BuildPreI(CBprogram 114%Z sched_id)300%Z nil nil(CBfp nest c aop)V293_idle_tid=Some(CBpre 114%Z nest c aop) /\
 CXstate nest c old aop|=CBpre 117%Z nest c aop /\
 CBrenamed_state 114%Z nest c old aop|=CBpre 114%Z nest c aop /\
 getmem(CXstate nest c old aop)=getmem(CBrenamed_state 114%Z nest c old aop) /\
 get(getgenv(CBrenamed_state 114%Z nest c old aop))114%Z=Some(13%positive,Tint8) /\
 get(getlenv(CXstate nest c old aop))114%Z=None /\
 get(getlenv(CBrenamed_state 114%Z nest c old aop))114%Z=Some(16%positive,Tint32) /\
 ~(CBrenamed_state 114%Z nest c old aop|=V293_handoff_binding 114%Z 13%positive ** Atrue).
Proof.
 intros sched_id nest c old aop N.
 split;[reflexivity| ];split;[apply CBpre_owned;assumption| ];
 split;[apply CBrenamed_pre;assumption| ];split;[reflexivity| ];
 split;[vm_compute;reflexivity| ];split;[vm_compute;reflexivity| ];
 split;[vm_compute;reflexivity| ].
 intro H;assert(E:get(getlenv(CBrenamed_state 114%Z nest c old aop))114%Z=None).
 { eapply V293_star_env_l with(E:=fun ge le=>get le 114%Z=None);[ |exact H].
   intros s HS;exact(proj2(V293_handoff_binding_env _ _ _ HS)). }
 vm_compute in E;discriminate.
Qed.
