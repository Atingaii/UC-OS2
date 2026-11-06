(* Reuse actual typed TCB/lookup/control memory, not boot reachability. *)
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
Definition REspec:=V293_ready_irq_spec
 100%Z 101%Z 102%Z 103%Z 105%Z 106%Z 108%Z 109%Z 112%Z 110%Z 111%Z
 92%positive 81%positive 80%positive 91%positive 82%positive 93%positive 94%positive 95%positive
 99%positive 96%positive 97%positive nil Aemp I 300%Z 301%Z 200%Z.
Definition REprefix:=V293_ready_irq_prefix 92%positive 91%positive 94%positive 95%positive.
Definition REsuffix:=V293_ready_irq_suffix 97%positive nil.
Definition REboundary:=V293_enter_ready_boundary 80%positive 81%positive 82%positive
 99%positive 96%positive 112%Z 110%Z 106%Z V293_tcb_type REprefix REsuffix
 (spec_done None)[0]nil OwnershipWaiting.
Definition REfp:=V293_enter_ready_fpre 80%positive 81%positive 82%positive
 99%positive 96%positive 112%Z 110%Z 106%Z V293_tcb_type REprefix REsuffix.
Definition REfq:=V293_enter_ready_fpost 80%positive 81%positive 82%positive
 99%positive 96%positive 112%Z 110%Z 106%Z V293_tcb_type REprefix REsuffix.
Definition RElg:=V293_enter_ready_call_lg(spec_done None)[0]nil.
Definition REstate:RstateOP:=(JBge,emp,JBmemory 0 Int.zero Int.zero,
 (fun _:hid=>false),(false,[0],nil),RIabstract OwnershipWaiting,spec_done None).
Theorem REenvironment :
 GoodI RDinv V293_scheduler V293_shared_li /\
 WFFunEnv RDprogram REspec V293_scheduler V293_shared_li RDinv /\
 WFIFun RDprogram REspec V293_scheduler RDinv V293_shared_li.
Proof.
 split;[apply V293_ready_storage_good| ];split;
 change RDprogram with(V293_ready_irq_unit
 100%Z 101%Z 102%Z 103%Z 105%Z 106%Z 108%Z 109%Z 112%Z 110%Z 111%Z 120%Z
 300%Z 301%Z 200%Z 104%Z);unfold REspec.
 - apply V293_ready_irq_WFFunEnv;try discriminate;exact I.
 - apply V293_ready_irq_WFIFun;try discriminate;exact I.
Qed.
Lemma REbuilder :
 BuildPreI RDprogram 301%Z nil RElg REfp OwnershipWaiting=
 Some(Aemp ** (REboundary ** A_dom_lenv nil)) /\
 BuildRetI RDprogram 301%Z nil RElg REfq OwnershipWaiting=
 Some(fun result=>Aemp ** (([|result=None|] ** REboundary) ** A_dom_lenv nil)).
Proof. split;reflexivity. Qed.
Lemma REheap : REstate |=
 (V293_ready_storage_core 80%positive 81%positive 82%positive 106%Z V293_tcb_type JBcells **
 CurTid OwnershipWaiting) ** Atrue.
Proof.
 pose proof(JBentry 0 Int.zero Int.zero nil(spec_done None)ltac:(lia))as Entry.
 assert(Pack:JBstate(JBmemory 0 Int.zero Int.zero)nil(sched;;spec_done None)|=
 (V293_inputs_full 92%positive 81%positive 80%positive 16 0 **
 (V293_array true 82%positive 0 4(Tptr V293_tcb_type)RTentries **
 (V293_owned_task_records OwnershipTasks ** V293_storage(
 [((99%positive,0%Z),Tint8);((96%positive,0%Z),Tint8);((97%positive,0%Z),Tint8)])))) **
 ((GV OSTCBCur@(Tptr V293_tcb_type)|->Vptr OwnershipWaiting) **
 (V293_shared_fields OwnershipWaiting OwnershipTasks(emp:EcbMod.map)Int.zero **
 ((GV 106%Z@(Tptr V293_tcb_type)|->Vptr OwnershipWaiting) **
 (PV(91%positive,Int.zero)@Tint8|->V293_byteval 88 **
 (Amapsto(94%positive,0%Z)Tint8 true(V293_byteval 6) **
 (PV(95%positive,Int.zero)@Tint32|->Vint32 Int.zero ** Atrue))))))).
 { unfold JBdata,V293_exit_ready_body_data,V293_exit_ready_body_core,
 V293_handoff_byte,V293_counter_cell,V293_time_cell,V293_exit_cells,V293_interrupt_cells in Entry;
 cbn[V293_rdy_raw_cells V293_storage]in *;unfold V293_storage_cell;sep auto;apply V293_byte_type;lia. }
 eapply astar_mono in Pack.
 2:{ apply V293_retained_arrays_ready;[exact RTliteral_rel|vm_compute;repeat constructor]. }
 2:{ intros s H;exact H. }
 assert(Storage:JBstate(JBmemory 0 Int.zero Int.zero)nil(sched;;spec_done None)|=
 V293_storage JBcells **
 ((GV OSTCBCur@(Tptr V293_tcb_type)|->Vptr OwnershipWaiting) **
 (V293_shared_fields OwnershipWaiting OwnershipTasks(emp:EcbMod.map)Int.zero **
 ((GV 106%Z@(Tptr V293_tcb_type)|->Vptr OwnershipWaiting) **
 (V293_ready_payload 80%positive 81%positive 82%positive OwnershipTasks ** Atrue))))).
 { change(JBstate(JBmemory 0 Int.zero Int.zero)nil(sched;;spec_done None)|=
 (V293_storage_cell(95%positive,0%Z)Tint32 **
 (V293_storage_cell(91%positive,0%Z)Tint8 **
 (V293_storage_cell(94%positive,0%Z)Tint8 **
 V293_storage(V293_array_cells 92%positive 0 1 Tint8(length V293_ready_table)++
 [((99%positive,0%Z),Tint8);((96%positive,0%Z),Tint8);((97%positive,0%Z),Tint8)])))) **
 ((GV OSTCBCur@(Tptr V293_tcb_type)|->Vptr OwnershipWaiting) **
 (V293_shared_fields OwnershipWaiting OwnershipTasks(emp:EcbMod.map)Int.zero **
 ((GV 106%Z@(Tptr V293_tcb_type)|->Vptr OwnershipWaiting) **
 (V293_ready_payload 80%positive 81%positive 82%positive OwnershipTasks ** Atrue))))).
 unfold V293_storage_cell;clear Entry;sep auto;try(apply V293_byte_type;lia). }
 eapply astar_mono in Storage;[ |intros st K;exact K|apply astar_mono;[apply GV_separate_rw|intros st K;exact K]].
 assert(Core:JBstate(JBmemory 0 Int.zero Int.zero)nil(sched;;spec_done None)|=
 (V293_ready_storage_core 80%positive 81%positive 82%positive 106%Z V293_tcb_type JBcells **
 CurTid OwnershipWaiting) ** Atrue).
 { unfold V293_ready_storage_core,V293ReadyTaskInvariant.V293_ready_core,
 V293_shared_ready_records,V293_ready_storage_extra,V293_dispatch_cell,
 CurTid in *;clear Entry Pack;sep auto;reflexivity. }
 unfold JBstate in Core.
 assert(Good:GoodInvAsrt((V293_ready_storage_core 80%positive 81%positive 82%positive 106%Z V293_tcb_type JBcells **
 CurTid OwnershipWaiting) ** Atrue)).
 { split;[split;[apply V293_ready_storage_core_good|unfold CurTid;intro tp;unfold Agvarmapsto,Agvarenv',Aptrmapsto;cbn[GoodInvAsrt];auto]|exact I]. }
 assert(Empty:(JBge,emp,JBmemory 0 Int.zero Int.zero,(fun _:hid=>false),
 (false,nil,nil),RIabstract OwnershipWaiting,spec_done None)|=
 V293_ready_storage_core 80%positive 81%positive 82%positive 106%Z V293_tcb_type JBcells **
 (CurTid OwnershipWaiting ** Atrue)).
 { assert(E:(JBge,emp,JBmemory 0 Int.zero Int.zero,(fun _:hid=>false),
 (false,nil,nil),RIabstract OwnershipWaiting,spec_done None)|=
 (V293_ready_storage_core 80%positive 81%positive 82%positive 106%Z V293_tcb_type JBcells **
 CurTid OwnershipWaiting) ** Atrue)by(eapply good_inv_prop;[exact Good|exact Core]).
 clear -E;sep auto. }
 apply sat_split in Empty;destruct Empty as(m1&m2&o1&o2&JM&JO&Shared&Private).
 assert(New:REstate|=
 V293_ready_storage_core 80%positive 81%positive 82%positive 106%Z V293_tcb_type JBcells **
 (CurTid OwnershipWaiting ** Atrue)).
 { unfold REstate;apply sat_split';exists m1;exists m2;exists o1;exists o2.
 split;[exact JM| ];split;[exact JO| ];split.
 - eapply V293_ready_storage_core_aux;exact Shared.
 - exact Private. }
 clear -New;sep auto.
Qed.
Theorem REentry_nonempty : REstate |=REboundary ** A_dom_lenv nil.
Proof.
 pose proof REheap as H.
 apply astar_l_aisr_intro with(i:=fun _:hid=>false)in H;[ |reflexivity].
 apply astar_l_aie_intro with(i:=false)in H;[ |reflexivity].
 apply astar_l_atopis_intro with(i:=0)in H;[ |reflexivity].
 assert(Flags:REstate |= (V293_shared_flags **
 V293_ready_storage_core 80%positive 81%positive 82%positive 106%Z V293_tcb_type JBcells) **
 (CurTid OwnershipWaiting ** Atrue)).
 { assert(C:Aisr(fun _:hid=>false) ==>isrclr).
   { intros st K;unfold isrclr;exists(fun _:hid=>false);split;[exact K|split;[auto|exact(proj2 K)]]. }
 eapply astar_mono in H;[ |intros st K;exact K|apply astar_mono;
 [intros st K;exact K|apply astar_mono;[exact C|intros st K;exact K]]].
 unfold V293_shared_flags;clear -H;sep normal;exists 0;sep auto. }
 eapply astar_mono in Flags;[ |apply V293_ready_storage_switch_close|intros s K;exact K].
 apply astar_l_ais_intro with(i:=[0])in Flags;[ |reflexivity].
 apply astar_l_acs_intro with(i:=nil)in Flags;[ |reflexivity].
 apply astar_l_adomlenv_intro with(d:=nil)in Flags.
 2:{ intros x t;split;[contradiction|intros[l E];discriminate]. }
 apply astar_l_aop'_intro with(aop:=spec_done None)in Flags;[ |reflexivity].
 assert(G:(JBge,emp,empmem,(fun _:hid=>false),(false,[0],nil),empabst,spec_done None)|=
 V293_interrupt_globals 112%Z 110%Z 99%positive 96%positive).
 { unfold V293_interrupt_globals;split;apply agvarenv_intro;
 [split;reflexivity|split;reflexivity|split;reflexivity|split;reflexivity]. }
 assert(Pack:REstate|=V293_interrupt_globals 112%Z 110%Z 99%positive 96%positive **
 (<||spec_done None||> ** (A_dom_lenv nil ** (Acs nil ** (Ais (0::nil) **
 (SWINV RDinv ** (CurTid OwnershipWaiting ** Atrue))))))).
 { unfold REstate;apply sat_split';exists empmem;exists(JBmemory 0 Int.zero Int.zero);
 exists empabst;exists(RIabstract OwnershipWaiting).
 split;[apply join_emp| ];split;[apply join_emp| ];split;[exact G|exact Flags]. }
 unfold REboundary,V293_enter_ready_boundary,REprefix,REsuffix,V293_ready_irq_prefix,V293_ready_irq_suffix.
 assert(Local:GoodLInvAsrt V293_shared_li)by apply V293_switch_li_good.
 unfold CurLINV,LINV,V293_shared_li.
 clear -Pack Local;sep normal;exists(@nil logicvar);sep auto.
Qed.
(* Fixed state, logic arguments and program; only the Enter spec entry changes.
   Old decoding rejects this new context encoding. This is not two executions. *)
Theorem REsingle_entry_control :
 REstate |=Aemp ** (REboundary ** A_dom_lenv nil) /\
 (forall st pre,Some pre=BuildPreI RDprogram 301%Z nil RElg
 (V293_interrupt_fpre 112%Z 110%Z 99%positive 96%positive V293_shared_li V293_switch_li_good)OwnershipWaiting ->
 ~st|=pre) /\
 (forall f,f<>301%Z ->REspec f=RDspec f).
Proof.
 split;[pose proof REentry_nonempty;sep auto| ];split.
 - intros st pre E;change(Some pre=Some(Aemp ** (Afalse ** A_dom_lenv nil)))in E.
   inversion E;subst pre;intro H;apply astar_l_aemp_elim in H;apply astar_l_afalse_elim in H;exact H.
 - intros f Apart;unfold REspec,RDspec,V293_ready_irq_spec,V293_ready_dynamic_exit_env_spec;
 repeat destruct Z.eq_dec;try congruence;reflexivity.
Qed.
Theorem REactual_call : forall r ri,
 InfRules REspec V293_scheduler V293_shared_li RDinv r ri
 (REboundary ** A_dom_lenv nil)(scall 301%Z nil)
 (REboundary ** A_dom_lenv nil)OwnershipWaiting.
Proof.
 intros;unfold REspec,REboundary,REprefix,REsuffix;
 apply V293_ready_irq_Enter_call;discriminate.
Qed.
Theorem REexit_nonempty : forall nest c old aop ci,nest<=1 ->
 JBstate(JBmemory nest c old)ci(sched;;aop)|=RDpre(RDlg nest c aop ci) /\
 REspec 300%Z=Some(RDfp,RDfq,(Tvoid,nil)).
Proof. intros;split;[apply RDchanged_nonempty;assumption|reflexivity]. Qed.
