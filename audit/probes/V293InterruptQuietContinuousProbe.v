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
Definition QCspec:=V293_open_exact_irq_spec
 100%Z 101%Z 102%Z 103%Z 105%Z 106%Z 108%Z 109%Z 112%Z 110%Z 111%Z
 92%positive 81%positive 80%positive 91%positive 82%positive 93%positive 94%positive 95%positive
 99%positive 96%positive 97%positive nil Aemp Logic.I 300%Z 301%Z 200%Z.
Definition QCkept:=V293_quiet_irq_kept 106%Z 92%positive 81%positive 80%positive 91%positive 82%positive
 94%positive 95%positive nil.
Definition QCentry:=V293_quiet_irq_snapshot 106%Z 112%Z 110%Z 111%Z 92%positive 81%positive 80%positive 91%positive 82%positive
 94%positive 95%positive 99%positive 96%positive 97%positive nil
 1 1 0(spec_done None)false(isrupd(fun _:hid=>false)0 true)[0]nil OwnershipWaiting.
Definition QCstate M O:RstateOP:=(JBge,emp,M,isrupd(fun _:hid=>false)0 true,
 (false,[0],nil),O,spec_done None).
Definition QCraw:=
 Amapsto(99%positive,0%Z)Tint8 true(V293_byteval 1) **
 (Amapsto(96%positive,0%Z)Tint8 true(V293_byteval 1) **
 (Amapsto(97%positive,0%Z)Tint8 true(V293_byteval 0) **
 (CurTid OwnershipWaiting ** QCkept))).
Lemma QCraw_good : GoodInvAsrt QCraw /\ GoodFrm QCraw.
Proof.
 unfold QCraw;split.
 - split;[exact Logic.I| ];split;[exact Logic.I| ];split;[exact Logic.I| ];split.
   + unfold CurTid;intro tq;unfold Agvarmapsto,Agvarenv',Aptrmapsto;cbn[GoodInvAsrt];auto.
   + unfold QCkept,V293_quiet_irq_kept;split;[apply V293_ready_core_good| ];split.
     * unfold V293_dispatch_cell;intro v;cbn[GoodInvAsrt];split;[exact Logic.I| ];
     unfold Agvarmapsto,Agvarenv',Aptrmapsto;cbn[GoodInvAsrt];auto.
     * split;apply V293_storage_good.
 - split;[exact Logic.I| ];split;[exact Logic.I| ];split;[exact Logic.I| ];split.
   + unfold CurTid;intro tq;unfold Agvarmapsto,Agvarenv',Aptrmapsto;cbn[GoodFrm];auto.
   + apply V293_quiet_irq_kept_good.
Qed.
Lemma QCraw_heap : JBstate(JBmemory 1 Int.zero Int.zero)nil(sched;;spec_done None)|=QCraw ** Atrue.
Proof.
 pose proof(JBentry 1 Int.zero Int.zero nil(spec_done None)ltac:(lia))as Entry.
 assert(Pack:JBstate(JBmemory 1 Int.zero Int.zero)nil(sched;;spec_done None)|=
 (V293_inputs_full 92%positive 81%positive 80%positive 16 0 **
 (V293_array true 82%positive 0 4(Tptr V293_tcb_type)RTentries **
 (V293_owned_task_records OwnershipTasks ** V293_storage nil))) **
 ((GV OSTCBCur@(Tptr V293_tcb_type)|->Vptr OwnershipWaiting) **
 (V293_shared_fields OwnershipWaiting OwnershipTasks(emp:EcbMod.map)Int.zero **
 ((GV 106%Z@(Tptr V293_tcb_type)|->Vptr OwnershipWaiting) **
 (PV(91%positive,Int.zero)@Tint8|->V293_byteval 88 **
 (Amapsto(94%positive,0%Z)Tint8 true(V293_byteval 6) **
 (PV(95%positive,Int.zero)@Tint32|->Vint32 Int.zero **
 (Amapsto(99%positive,0%Z)Tint8 true(V293_byteval 1) **
 (Amapsto(96%positive,0%Z)Tint8 true(V293_byteval 1) **
 (Amapsto(97%positive,0%Z)Tint8 true(V293_byteval 0) ** Atrue)))))))))).
 { unfold JBdata,V293_exit_ready_body_data,V293_exit_ready_body_core,
 V293_handoff_byte,V293_counter_cell,V293_time_cell,V293_exit_cells,V293_interrupt_cells in Entry;
 cbn[V293_rdy_raw_cells V293_storage]in *;sep auto. }
 eapply astar_mono in Pack;[ |apply V293_retained_arrays_ready;[exact RTliteral_rel|vm_compute;repeat constructor]|intros s H;exact H].
 assert(Storage:JBstate(JBmemory 1 Int.zero Int.zero)nil(sched;;spec_done None)|=
 V293_storage REprefix **
 ((GV OSTCBCur@(Tptr V293_tcb_type)|->Vptr OwnershipWaiting) **
 (V293_shared_fields OwnershipWaiting OwnershipTasks(emp:EcbMod.map)Int.zero **
 ((GV 106%Z@(Tptr V293_tcb_type)|->Vptr OwnershipWaiting) **
 (V293_ready_payload 80%positive 81%positive 82%positive OwnershipTasks **
 (Amapsto(99%positive,0%Z)Tint8 true(V293_byteval 1) **
 (Amapsto(96%positive,0%Z)Tint8 true(V293_byteval 1) **
 (Amapsto(97%positive,0%Z)Tint8 true(V293_byteval 0) ** Atrue)))))))).
 { unfold REprefix,V293_ready_irq_prefix;cbn[V293_storage];unfold V293_storage_cell;
 clear Entry;sep auto;try(apply V293_byte_type;lia). }
 eapply astar_mono in Storage;[ |intros s H;exact H|apply astar_mono;[apply GV_separate_rw|intros s H;exact H]].
 unfold QCraw,QCkept,V293_quiet_irq_kept,V293ReadyTaskInvariant.V293_ready_core,V293_shared_ready_records,
 V293_dispatch_cell,CurTid;cbn[V293_storage];clear Entry Pack;sep auto.
 all:reflexivity.
Qed.
Theorem QCentry_nonempty : exists M Mf O Of,
 join M Mf(JBmemory 1 Int.zero Int.zero) /\ join O Of(RIabstract OwnershipWaiting) /\
 QCstate M O|=QCentry.
Proof.
 pose proof QCraw_heap as H;unfold JBstate in H.
 assert(Moved:(JBge,emp,JBmemory 1 Int.zero Int.zero,(fun _:hid=>false),
 (false,nil,nil),RIabstract OwnershipWaiting,spec_done None)|=QCraw ** Atrue).
 { eapply good_inv_prop;[split;[exact(proj1 QCraw_good)|exact Logic.I]|exact H]. }
 assert(New:QCstate(JBmemory 1 Int.zero Int.zero)(RIabstract OwnershipWaiting)|=QCraw ** Atrue).
 { unfold QCstate;eapply goodfrm_prop;[split;[exact(proj2 QCraw_good)|exact Logic.I]|exact Moved]. }
 apply sat_split in New;destruct New as(M&Mf&O&Of&JM&JO&Owned&Extra).
 exists M;exists Mf;exists O;exists Of;split;[exact JM| ];split;[exact JO| ].
 assert(G:(JBge,emp,empmem,isrupd(fun _:hid=>false)0 true,(false,[0],nil),empabst,spec_done None)|=
 V293_quiet_globals 112%Z 110%Z 111%Z 99%positive 96%positive 97%positive).
 { unfold V293_quiet_globals;repeat split;apply agvarenv_intro;
 split;reflexivity. }
 assert(Pack:QCstate M O|=V293_quiet_globals 112%Z 110%Z 111%Z 99%positive 96%positive 97%positive ** QCraw).
 { unfold QCstate;apply sat_split';exists empmem;exists M;exists empabst;exists O.
 split;[apply join_emp| ];split;[apply join_emp| ];split;assumption. }
 apply astar_l_adomlenv_intro with(d:=nil)in Pack.
 2:{ intros x tau;split;[contradiction|intros[l E];discriminate]. }
 apply astar_l_aisr_intro with(i:=isrupd(fun _:hid=>false)0 true)in Pack;[ |reflexivity].
 apply astar_l_aie_intro with(i:=false)in Pack;[ |reflexivity].
 apply astar_l_ais_intro with(i:=[0])in Pack;[ |reflexivity].
 apply astar_l_acs_intro with(i:=nil)in Pack;[ |reflexivity].
 apply astar_l_aop'_intro with(aop:=spec_done None)in Pack;[ |reflexivity].
 unfold QCentry,V293_quiet_irq_snapshot,V293_enter_open_external,QCraw,QCkept,
 p_local,LINV,V293_shared_li in *;clear H Moved Owned Extra;sep auto;apply V293_switch_li_good.
Qed.
Theorem QCenvironment : GoodI RDinv V293_scheduler V293_shared_li /\
 WFFunEnv RDprogram QCspec V293_scheduler V293_shared_li RDinv /\
 WFIFun RDprogram QCspec V293_scheduler RDinv V293_shared_li.
Proof.
 split;[apply V293_ready_storage_good| ];split;unfold QCspec;
 change RDprogram with(V293_ready_irq_unit
 100%Z 101%Z 102%Z 103%Z 105%Z 106%Z 108%Z 109%Z 112%Z 110%Z 111%Z 120%Z
 300%Z 301%Z 200%Z 104%Z).
 - apply V293_open_exact_irq_WFFunEnv;try discriminate;exact Logic.I.
 - apply V293_open_exact_irq_WFIFun;try discriminate;exact Logic.I.
Qed.
Definition QCintspec:osintspec:=fun k=>if Nat.eq_dec k 0 then Some(spec_done None)else None.
Theorem QCactual_wrapper : forall ret,
 Some ret=BuildintRet 0 QCintspec(fun _:hid=>false)nil RDinv V293_shared_li OwnershipWaiting nil ->
 InfRules QCspec V293_scheduler V293_shared_li RDinv arfalse ret
 QCentry(V293_irq_source_wrapper 301%Z 300%Z Int.zero)Afalse OwnershipWaiting.
Proof.
 intros ret Ret;unfold QCentry;apply(V293_interrupt_quiet_continuous
 100%Z 101%Z 102%Z 103%Z 105%Z 106%Z 108%Z 109%Z 112%Z 110%Z 111%Z
 92%positive 81%positive 80%positive 91%positive 82%positive 93%positive 94%positive 95%positive
 99%positive 96%positive 97%positive nil QCspec 301%Z 300%Z QCintspec 0(fun _:hid=>false)nil
 OwnershipWaiting ret Int.zero 1 1 0);try assumption;try reflexivity;try(unfold QCspec,V293_open_exact_irq_spec;reflexivity);try (cbn;lia).
 all: unfold gettopis,INUM;rewrite ?Int.unsigned_zero;cbn;lia.
Qed.
Theorem QCreturn_builder_exists : exists ret,
 Some ret=BuildintRet 0 QCintspec(fun _:hid=>false)nil RDinv V293_shared_li OwnershipWaiting nil.
Proof. eexists;reflexivity. Qed.
Theorem QCdispatch_entry_not_quiet : ~V293_quiet_exit_valid 1(V293_interrupt_nest_after 1 0)0 [0].
Proof. unfold V293_quiet_exit_valid,V293_interrupt_nest_after;simpl;intros(_&_&_&_&H);specialize(H eq_refl);lia. Qed.
