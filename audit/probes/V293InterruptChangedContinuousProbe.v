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
Definition CCmemory:=V293_ready_builder_memory 100%Z 101%Z 102%Z 103%Z 106%Z
 92%positive 81%positive 80%positive 91%positive 82%positive 94%positive 95%positive
 16 0 6 RTentries nil OwnershipTasks emp Int.zero(V293_byteval 88)(Vptr OwnershipWaiting)Int.zero Aemp OwnershipWaiting.
Definition CCraw:=CCmemory ** (RBglobals **
 (Amapsto(99%positive,0%Z)Tint8 true(V293_byteval 1) **
 (Amapsto(96%positive,0%Z)Tint8 true(V293_byteval 0) **
 Amapsto(97%positive,0%Z)Tint8 true(V293_byteval 0)))).
Definition CCentry:=V293_changed_irq_snapshot
 100%Z 101%Z 102%Z 103%Z 105%Z 106%Z 108%Z 109%Z 112%Z 110%Z 111%Z
 92%positive 81%positive 80%positive 91%positive 82%positive 93%positive 94%positive 95%positive
 99%positive 96%positive 97%positive nil 16 0 6 RTentries OwnershipTasks emp Int.zero
 (V293_byteval 88)(Vptr OwnershipWaiting)Int.zero 0(spec_done None)
 (isrupd(fun _:hid=>false)0 true)[0]OwnershipWaiting.
Definition CCstate M O:RstateOP:=(JBge,emp,M,isrupd(fun _:hid=>false)0 true,
 (false,[0],nil),O,sched;;spec_done None).
Lemma CCraw_good : GoodInvAsrt CCraw /\ GoodFrm CCraw.
Proof.
 assert(A:GoodInvAsrt(V293_array true 82%positive 0 4(Tptr V293_tcb_type)RTentries)).
 { unfold RTentries;cbn[V293_array GoodInvAsrt];tauto. }
 assert(F:GoodFrm(V293_array true 82%positive 0 4(Tptr V293_tcb_type)RTentries)).
 { unfold RTentries;cbn[V293_array GoodFrm];tauto. }
 assert(O:GoodInvAsrt(V293_owned_task_records OwnershipTasks)).
 { unfold V293_owned_task_records;apply V293_task_list_good. }
 assert(OF:GoodFrm(V293_owned_task_records OwnershipTasks))by(apply V293_owned_tasks_frame).
 unfold CCraw,CCmemory,RBglobals,V293_ready_builder_memory,V293_shared_fields,V293_inputs_full,
 V293_exit_builder_globals,V293_sched_globals,Agvarmapsto,Agvarenv',Aptrmapsto.
 split;[cbn[GoodInvAsrt]|cbn[GoodFrm]];repeat split;try exact Logic.I;assumption.
Qed.
Lemma CCraw_heap : JBstate(JBmemory 0 Int.zero Int.zero)nil(sched;;spec_done None)|=CCraw ** Atrue.
Proof.
 pose proof(RBpre_owned 0 Int.zero Int.zero nil(spec_done None)ltac:(lia))as Entry.
 unfold RBpre,RBfp,V293_ready_builder_fpre in Entry;cbn[getasrt]in Entry.
 unfold CCraw,CCmemory,RBglobals,V293_ready_builder_pre,V293_ready_builder_external,
 V293OSIntExitHoare.V293_exit_cells,V293OSIntEnterInternal.V293_interrupt_cells in *;
 cbn[V293_rdy_raw_cells]in *;sep auto.
Qed.
Theorem CCentry_nonempty : exists M Mf O Of,
 join M Mf(JBmemory 0 Int.zero Int.zero) /\ join O Of(RIabstract OwnershipWaiting) /\
 CCstate M O|=CCentry.
Proof.
 pose proof CCraw_heap as H;unfold JBstate in H.
 assert(Moved:(JBge,emp,JBmemory 0 Int.zero Int.zero,(fun _:hid=>false),
 (false,nil,nil),RIabstract OwnershipWaiting,sched;;spec_done None)|=CCraw ** Atrue).
 { eapply good_inv_prop;[split;[exact(proj1 CCraw_good)|exact Logic.I]|exact H]. }
 assert(New:CCstate(JBmemory 0 Int.zero Int.zero)(RIabstract OwnershipWaiting)|=CCraw ** Atrue).
 { unfold CCstate;eapply goodfrm_prop;[split;[exact(proj2 CCraw_good)|exact Logic.I]|exact Moved]. }
 apply sat_split in New;destruct New as(M&Mf&O&Of&JM&JO&Owned&Extra).
 exists M;exists Mf;exists O;exists Of;split;[exact JM| ];split;[exact JO| ].
 apply astar_l_adomlenv_intro with(d:=nil)in Owned.
 2:{ intros x tau;split;[contradiction|intros[l E];discriminate]. }
 apply astar_l_aisr_intro with(i:=isrupd(fun _:hid=>false)0 true)in Owned;[ |reflexivity].
 apply astar_l_aie_intro with(i:=false)in Owned;[ |reflexivity].
 apply astar_l_ais_intro with(i:=[0])in Owned;[ |reflexivity].
 apply astar_l_acs_intro with(i:=nil)in Owned;[ |reflexivity].
 apply astar_l_aop'_intro with(aop:=sched;;spec_done None)in Owned;[ |reflexivity].
 unfold CCentry,V293_changed_irq_snapshot,V293_changed_irq_physical,CCraw,CCmemory,RBglobals in *;
 clear H Moved Extra;sep auto.
Qed.
Theorem CCenvironment : GoodI RDinv V293_scheduler V293_shared_li /\
 WFFunEnv RDprogram QCspec V293_scheduler V293_shared_li RDinv /\
 WFIFun RDprogram QCspec V293_scheduler RDinv V293_shared_li.
Proof. exact QCenvironment. Qed.
Theorem CCactual_wrapper : forall ret,
 Some ret=BuildintRet 0 QCintspec(fun _:hid=>false)nil RDinv V293_shared_li OwnershipWaiting nil ->
 InfRules QCspec V293_scheduler V293_shared_li RDinv arfalse ret
 CCentry(V293_irq_source_wrapper 301%Z 300%Z Int.zero)Afalse OwnershipWaiting.
Proof.
 intros ret Ret;unfold CCentry;apply(V293_interrupt_changed_continuous
 100%Z 101%Z 102%Z 103%Z 105%Z 106%Z 108%Z 109%Z 112%Z 110%Z 111%Z
 92%positive 81%positive 80%positive 91%positive 82%positive 93%positive 94%positive 95%positive
 99%positive 96%positive 97%positive nil 16 0 6 RTentries OwnershipTasks emp Int.zero
 (V293_byteval 88)(Vptr OwnershipWaiting)Int.zero QCspec 301%Z 300%Z QCintspec 0(fun _:hid=>false)nil
 OwnershipWaiting ret Int.zero);try assumption;try reflexivity;
 try(unfold QCspec,V293_open_exact_irq_spec;reflexivity).
 - apply RBvalid;lia.
 - unfold INUM;rewrite Int.unsigned_zero;cbn;lia.
Qed.
Theorem CCreturn_builder_exists : exists ret,
 Some ret=BuildintRet 0 QCintspec(fun _:hid=>false)nil RDinv V293_shared_li OwnershipWaiting nil.
Proof. exact QCreturn_builder_exists. Qed.
