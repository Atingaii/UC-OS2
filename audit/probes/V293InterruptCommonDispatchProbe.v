Require Import CertiOS.certiucos.v293.proofs.V293InterruptSourceRoundtrip.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptReadyBoundary.
Require Import CertiOS.audit.probes.V293InterruptBoundDispatchContinuousProbe.
Require Import CertiOS.audit.probes.V293InterruptChangedContinuousProbe.
Require Import CertiOS.audit.probes.V293InterruptSameContinuousProbe.
Require Import CertiOS.audit.probes.V293InterruptQuietContinuousProbe.
Require Import CertiOS.audit.probes.V293OSIntExitReadyDynamicProbe.
Require Import CertiOS.audit.probes.V293OSIntExitReadyBodyProbe.
Require Import CertiOS.audit.probes.V293OSIntExitLocalDispatchProbe.
Require Import CertiOS.audit.probes.V293OSIntExitBoundDynamicProbe.
Require Import CertiOS.audit.probes.V293ReadyTaskInvariantProbe.
Require Import CertiOS.audit.probes.V293TaskRecordOwnershipProbe.
Require Import CertiOS.audit.probes.V293TaskRecordInvariantProbe.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptBoundEntry.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.toptheorem.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptCommonDispatch.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptSameContinuous.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitChangedInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCurrent.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedDispatchFinish.
Require Import CertiOS.certiucos.v293.proofs.V293SharedStateWitness.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptBoundEntry.
Require Import CertiOS.audit.probes.V293InterruptBoundEntryProbe.
Require Import CertiOS.audit.probes.V293OSIntExitReadyInternalProbe.

Definition CDchanged:=V293_common_dispatch_entry 100%Z 101%Z 102%Z 103%Z 105%Z 106%Z 108%Z 109%Z 112%Z 110%Z 111%Z
 92%positive 81%positive 80%positive 91%positive 82%positive 93%positive 94%positive 95%positive
 99%positive 96%positive 97%positive nil 16 0 6 RTentries OwnershipTasks emp Int.zero
 (V293_byteval 88)(Vptr OwnershipWaiting)Int.zero 0 nil OwnershipWaiting.
Definition CDsame:=V293_common_dispatch_entry 100%Z 101%Z 102%Z 103%Z 105%Z 106%Z 108%Z 109%Z 112%Z 110%Z 111%Z
 92%positive 81%positive 80%positive 91%positive 82%positive 93%positive 94%positive 95%positive
 99%positive 96%positive 97%positive nil 16 0 4 RTentries OwnershipTasks emp Int.zero
 (V293_byteval 88)(Vptr OwnershipReady)Int.zero 0 nil OwnershipReady.
Definition CDpre:=ipreasrt' 0(fun _:hid=>false)nil(sched;;spec_done None)RDinv **p_local LDli OwnershipReady nil.
Definition CDstate M O:RstateOP:=(JBge,emp,M,isrupd(fun _:hid=>false)0 true,
 (false,[0],nil),O,sched;;spec_done None).
Lemma CDcurrent : V293_current_task OwnershipTasks OwnershipReady 4.
Proof. split;[lia|exists rdy;exists Vnull;vm_compute;reflexivity]. Qed.
Theorem CDbuilders :
 Some CDpre=BuildintPre 0 BCintspec(fun _:hid=>false)nil RDinv LDli OwnershipReady nil /\
 Some BSret=BuildintRet 0 BCintspec(fun _:hid=>false)nil RDinv LDli OwnershipReady nil /\
 Some BCpre=BuildintPre 0 BCintspec(fun _:hid=>false)nil RDinv LDli OwnershipWaiting nil /\
 Some BCret=BuildintRet 0 BCintspec(fun _:hid=>false)nil RDinv LDli OwnershipWaiting nil.
Proof. repeat split;reflexivity. Qed.
Lemma CDsame_lift : forall M O,SCirq_state M O|=SCentry ->CDstate M O|=CDsame.
Proof.
 intros M O H;unfold SCentry,V293_same_irq_snapshot in H.
 apply astar_l_aop'_elim in H;destruct H as[_ H].
 unfold CDsame,V293_common_dispatch_entry;right.
 apply astar_comm;apply astar_l_apure_intro;[ |split;[exact SCvalid|exact CDcurrent]].
 unfold V293_same_irq_snapshot;apply astar_l_aop'_intro;[ |reflexivity].
 unfold CDstate,SCirq_state in *;eapply change_aop_rule;[exact H| ].
 split;[cbn[can_change_aop];tauto| ].
 apply V293_good_frame_action_free;apply V293_same_irq_physical_good.
Qed.
Lemma CDchanged_lift : forall M O,CCstate M O|=CCentry ->CCstate M O|=CDchanged.
Proof.
 intros M O H;unfold CDchanged,V293_common_dispatch_entry;left.
 apply astar_comm;apply astar_l_apure_intro;[exact H|apply RBvalid;lia].
Qed.
Lemma CDchanged_builder : forall M O,CCstate M O|=CDchanged ->CCstate M O|=BCpre.
Proof.
 intros M O H;apply(V293_common_dispatch_BuildintPre 100%Z 101%Z 102%Z 103%Z 105%Z 106%Z 108%Z 109%Z 112%Z 110%Z 111%Z
 92%positive 81%positive 80%positive 91%positive 82%positive 93%positive 94%positive 95%positive
 99%positive 96%positive 97%positive nil 16 0 6 RTentries OwnershipTasks emp Int.zero
 (V293_byteval 88)(Vptr OwnershipWaiting)Int.zero nil OwnershipWaiting BCintspec BCpre);try reflexivity;try lia.
 - exact RTliteral_rel.
 - vm_compute;repeat constructor.
 - exact H.
Qed.
Theorem CDchanged_wrapper :
 InfRules BDspec V293_scheduler LDli RDinv arfalse BCret
 CDchanged(V293_irq_source_wrapper 301%Z 300%Z Int.zero)Afalse OwnershipWaiting.
Proof.
 unfold CDchanged;apply(V293_interrupt_common_dispatch_continuous 100%Z 101%Z 102%Z 103%Z 105%Z 106%Z 108%Z 109%Z 112%Z 110%Z 111%Z
 92%positive 81%positive 80%positive 91%positive 82%positive 93%positive 94%positive 95%positive
 99%positive 96%positive 97%positive nil 16 0 6 RTentries OwnershipTasks emp Int.zero
 (V293_byteval 88)(Vptr OwnershipWaiting)Int.zero BDspec 301%Z 300%Z BCintspec 0 nil OwnershipWaiting BCret Int.zero);try reflexivity.
 - vm_compute;repeat constructor.
 - unfold INUM;rewrite Int.unsigned_zero;cbn;lia.
Qed.
Theorem CDchanged_nonempty : exists M Mf O Of,
 join M Mf(JBmemory 0 Int.zero Int.zero) /\join O Of(RIabstract OwnershipWaiting) /\
 CCstate M O|=CDchanged /\CCstate M O|=BCpre.
Proof.
 destruct BCtyped_entry_nonempty as(M&Mf&O&Of&JM&JO&H).
 apply CDchanged_lift in H.
 exists M;exists Mf;exists O;exists Of;split;[exact JM| ];split;[exact JO| ];split;[exact H| ].
 apply CDchanged_builder;exact H.
Qed.
Lemma CDsame_builder : forall M O,CDstate M O|=CDsame ->CDstate M O|=CDpre.
Proof.
 intros M O H;apply(V293_common_dispatch_BuildintPre 100%Z 101%Z 102%Z 103%Z 105%Z 106%Z 108%Z 109%Z 112%Z 110%Z 111%Z
 92%positive 81%positive 80%positive 91%positive 82%positive 93%positive 94%positive 95%positive
 99%positive 96%positive 97%positive nil 16 0 4 RTentries OwnershipTasks emp Int.zero
 (V293_byteval 88)(Vptr OwnershipReady)Int.zero nil OwnershipReady BCintspec CDpre);try reflexivity;try lia.
 - exact RTliteral_rel.
 - vm_compute;repeat constructor.
 - exact H.
Qed.
Theorem CDsame_wrapper :
 InfRules BDspec V293_scheduler LDli RDinv arfalse BSret
 CDsame(V293_irq_source_wrapper 301%Z 300%Z Int.zero)Afalse OwnershipReady.
Proof.
 unfold CDsame;apply(V293_interrupt_common_dispatch_continuous 100%Z 101%Z 102%Z 103%Z 105%Z 106%Z 108%Z 109%Z 112%Z 110%Z 111%Z
 92%positive 81%positive 80%positive 91%positive 82%positive 93%positive 94%positive 95%positive
 99%positive 96%positive 97%positive nil 16 0 4 RTentries OwnershipTasks emp Int.zero
 (V293_byteval 88)(Vptr OwnershipReady)Int.zero BDspec 301%Z 300%Z BCintspec 0 nil OwnershipReady BSret Int.zero);try reflexivity.
 - vm_compute;repeat constructor.
 - unfold INUM;rewrite Int.unsigned_zero;cbn;lia.
Qed.
Theorem CDsame_nonempty : exists M Mf O Of,
 join M Mf(SCmemory 0 Int.zero Int.zero) /\join O Of(RIabstract OwnershipReady) /\
 CDstate M O|=CDsame /\CDstate M O|=CDpre.
Proof.
 destruct BStyped_entry_nonempty as(M&Mf&O&Of&JM&JO&H).
 apply CDsame_lift in H.
 exists M;exists Mf;exists O;exists Of;split;[exact JM| ];split;[exact JO| ];split;[exact H| ].
 apply CDsame_builder;exact H.
Qed.
Theorem CDcurrent_ablation :
 sched_self V293_scheduler(RIabstract OwnershipReady) /\
 ~sched_self V293_scheduler(RIabstract OwnershipWaiting).
Proof.
 split.
 - exists OwnershipReady;split;[reflexivity|exists OwnershipTasks;split;[reflexivity| ]].
   apply(V293_equal_current_highest 16 0 RTentries OwnershipTasks OwnershipReady 4);
   try exact RTliteral_rel;try exact CDcurrent;reflexivity.
 - intros[t[C[ts[T[pr[msg[Ready Minimal]]]]]]].
   change(Some(oscurt OwnershipWaiting)=Some(oscurt t))in C;inversion C;subst t.
   change(Some(abstcblist OwnershipTasks)=Some(abstcblist ts))in T;inversion T;subst ts.
   vm_compute in Ready;discriminate.
Qed.

Theorem CDenvironment : GoodI RDinv V293_scheduler LDli /\ WFFunEnv RDprogram BDspec V293_scheduler LDli RDinv /\
 WFIFun RDprogram BDspec V293_scheduler RDinv LDli.
Proof. exact BCenvironment. Qed.
Theorem CDcurrent_only : forall key,key<>curtid ->
 get(RIabstract OwnershipReady)key=get(RIabstract OwnershipWaiting)key.
Proof. intros key K;destruct key;try reflexivity;contradiction. Qed.
Theorem CDsame_abstract_steps :
 spec_stepstar V293_scheduler(sched;;spec_done None)(RIabstract OwnershipReady)
 (spec_done None)(RIabstract OwnershipReady).
Proof.
 destruct(proj1 CDcurrent_ablation)as[t[Current Highest]].
 eapply spec_stepS.
 - apply spec_seq_step2;eapply spec_sched_step;[exact Current|exact Highest|apply map_join_emp].
 - eapply spec_stepS;[apply spec_seq_step1|apply spec_stepO].
Qed.
