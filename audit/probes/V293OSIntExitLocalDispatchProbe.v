(* A typed nonempty changed dispatch under the same bound LI as Enter. *)
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitExact.
Require Import CertiOS.audit.probes.V293OSIntExitReadyBodyProbe.
Require Import CertiOS.audit.probes.V293TaskRecordOwnershipProbe.
Require Import CertiOS.audit.probes.V293ReadyTaskInvariantProbe.
Require Import CertiOS.audit.probes.V293OSIntExitReadyHandoffProbe.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitHandoffHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitBoundarySwitch.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedStoragePrefix.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedStorageTail.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchStorage.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchState.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedShared.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedChange.
Require Import CertiOS.certiucos.v293.code.V293OSSchedChange.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCritical.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedPrefix.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedSwitch.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.sep_combine_lemmas.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import Coq.Lists.List Lia.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitDispatchHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitReadyHandoff.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyTaskInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyStorageInvariant.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.code.V293ReadyTable.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitReadyDispatch.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedExactPrefix.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedExactLocal.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitReadyBody.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitChangedBody.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntEnterInternal.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitBody.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitNondispatch.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitDispatch.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedGuards.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TimeAccess.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickDelayHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitLocalDispatch.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptBindings.
Require Import CertiOS.audit.probes.V293InterruptBindingsProbe.
Require Import CertiOS.audit.probes.V293OSIntExitExactProbe.
Import ListNotations.
Local Open Scope nat_scope.
Definition LDli:=V293_irq_bound_li 112%Z 110%Z 111%Z 99%positive 96%positive 97%positive.
Definition LDgood:=V293_irq_bound_good 112%Z 110%Z 111%Z 99%positive 96%positive 97%positive.
Definition LDspec:=V293_sched_exact_spec 200%Z 100%Z 101%Z 102%Z 103%Z
 92%positive 81%positive 80%positive 91%positive LDli V293_opened_inv LDgood.
Definition LDprogram:=V293_OSSchedNew_internal_unit 200%Z 100%Z 101%Z 102%Z 103%Z 104%Z.
Definition LDpre c aop ci:=V293_exit_bound_dispatch_entry
 100%Z 101%Z 102%Z 103%Z 105%Z 106%Z 108%Z 109%Z 112%Z 110%Z 111%Z 120%Z
 92%positive 81%positive 80%positive 91%positive 82%positive 93%positive 94%positive 95%positive
 99%positive 96%positive 97%positive 98%positive
 16 0 6 RTentries nil OwnershipWaiting OwnershipTasks (emp:EcbMod.map) Int.zero aop nil ci Aemp
 (Vptr OwnershipWaiting)c.
Definition LDpost aop ci:=
 <||aop||> ** SWINVt(V293_ready_storage_inv 80%positive 81%positive 82%positive
 106%Z V293_tcb_type JBcells)OwnershipWaiting ** Ais nil ** Acs ci **
 (V293_counter_bindings 109%Z 95%positive **
 ((V293_handoff_binding 103%Z 91%positive ** V293_handoff_binding 108%Z 94%positive) **
 ((V293_sched_globals 100%Z 101%Z 102%Z 103%Z 92%positive 81%positive 80%positive 91%positive **
 V293_prefix_bindings 105%Z 103%Z 106%Z V293_tcb_type 82%positive 93%positive) **
 ((V293_exit_ready_body_bindings 110%Z 111%Z 96%positive 97%positive) **
 (V293_handoff_binding 112%Z 99%positive **
 (V293_time_cell true 120%Z 98%positive(Vint32 Int.zero) ** Aemp)))))).
Lemma LDsame_local_invariant : LDli=EBli.
Proof. reflexivity. Qed.
Lemma LDsame_scheduler_body : LDprogram 200%Z=XEprogram 200%Z.
Proof. reflexivity. Qed.
Theorem LDscheduler_environment : forall sd RI,
 WFFunEnv LDprogram LDspec sd LDli RI.
Proof. intros;apply V293_OSSchedNew_exact_WFFunEnv;discriminate. Qed.
Lemma LDbody_lend : forall c aop ci,
 <||sched;;aop||> ** OS[(fun _:hid=>false),false,nil,ci] ** JBdata 0 c Int.zero ==>
 LDpre c aop ci.
Proof.
 intros;unfold LDpre,JBdata;apply V293_exit_bound_body_lend with(hv:=V293_byteval 88);try lia.
 exists 4;vm_compute;intuition lia.
 all: assumption.
Qed.
Theorem LDnonempty : forall c aop ci,exists s,
 (s|=<||sched;;aop||> ** OS[(fun _:hid=>false),false,nil,ci] ** JBdata 0 c Int.zero) /\
 (s|=LDpre c aop ci) /\ V293_highest_ready OwnershipTasks OwnershipReady /\
 OwnershipReady<>OwnershipWaiting.
Proof.
 intros;destruct(JBentry_nonempty 0 c Int.zero ci aop)as[s[H[Highest Different]]];[lia| ].
 exists s;split;[exact H| ];split;[apply LDbody_lend;exact H|tauto].
Qed.
Theorem LDactual_dispatch : forall c aop ci r ri,
 InfRules LDspec V293_scheduler LDli
 (V293_ready_storage_inv 80%positive 81%positive 82%positive 106%Z V293_tcb_type JBcells)r ri
 (LDpre c aop ci)
 (V293_exit_boundary_dispatch 105%Z 103%Z 106%Z 108%Z 109%Z 200%Z
 (V293_interrupt_handoff 103%Z 108%Z 106%Z))(LDpost aop ci)OwnershipWaiting.
Proof.
 intros;unfold LDpre,LDpost,JBcells.
 apply V293_OSIntExit_bound_dispatch;try lia.
 - exists 4;vm_compute;intuition lia.
 - vm_compute;discriminate.
 - exact(proj1(proj2(proj2(proj2 RTliteral_rel)))).
 - exact(proj2(proj2(proj2(proj2 RTliteral_rel)))).
 - vm_compute;repeat constructor.
 - exists(Int.repr 6,wait(os_stat_sem(72%positive,Int.repr 5))Int.one,Vptr(120%positive,Int.repr 7));vm_compute;reflexivity.
 - exact I.
 - reflexivity.
Qed.
Lemma LDresumed_local : forall aop ci,LDpost aop ci ==>CurLINV LDli OwnershipWaiting.
Proof.
 intros aop ci st H;unfold LDpost,LDli,JBcells in *.
 eapply V293_exit_bound_dispatch_current;exact H.
Qed.
