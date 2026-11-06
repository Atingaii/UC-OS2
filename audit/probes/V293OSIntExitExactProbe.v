(* The same typed-TCB full-lookup witness meets the new exact body entry.
   This is mathematical satisfiability, not initialization reachability. *)
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
Import ListNotations.
Local Open Scope nat_scope.

Definition XEprogram:=V293_OSSchedNew_internal_unit 200%Z 100%Z 101%Z 102%Z 103%Z 104%Z.
Definition XEspec:=V293_sched_exact_spec 200%Z 100%Z 101%Z 102%Z 103%Z
 92%positive 81%positive 80%positive 91%positive V293_shared_li V293_opened_inv V293_switch_li_good.
(* Literal output interface, not inferred by printing a candidate theorem. *)
Definition XEpost aop ci:=
 <||aop||> **
 ((SWINV(V293_ready_storage_inv 80%positive 81%positive 82%positive 106%Z V293_tcb_type JBcells) **
   p_local V293_shared_li OwnershipWaiting nil) **
 ((Ais nil ** Acs ci) **
 (V293_counter_bindings 109%Z 95%positive **
 ((V293_handoff_binding 103%Z 91%positive ** V293_handoff_binding 108%Z 94%positive) **
 ((V293_sched_globals 100%Z 101%Z 102%Z 103%Z 92%positive 81%positive 80%positive 91%positive **
   V293_prefix_bindings 105%Z 103%Z 106%Z V293_tcb_type 82%positive 93%positive) **
 ((V293_handoff_binding 110%Z 96%positive ** V293_handoff_binding 111%Z 97%positive) **
 (V293_handoff_binding 112%Z 99%positive **
 (V293_time_cell true 120%Z 98%positive(Vint32 Int.zero) ** Aemp)))))))).

Theorem XEenvironment : forall sd RI,
 WFFunEnv XEprogram XEspec sd V293_shared_li RI.
Proof. intros;apply V293_OSSchedNew_exact_WFFunEnv;discriminate. Qed.

Theorem XEnonempty : forall nest c old ci aop,nest<=1 ->
 exists s,
 (s |= <||sched;;aop||> ** OS[(fun _:hid=>false),false,nil,ci] ** JBdata nest c old) /\ V293_highest_ready OwnershipTasks OwnershipReady /\ OwnershipReady<>OwnershipWaiting.
Proof. intros;apply JBentry_nonempty;assumption. Qed.

Theorem XEactual_body : forall nest c old ci aop,nest<=1 ->
 InfRules XEspec V293_scheduler V293_shared_li
 (V293_ready_storage_inv 80%positive 81%positive 82%positive 106%Z V293_tcb_type JBcells)
 (fun v=>[|v=None|] ** XEpost aop ci)Afalse
 (<||sched;;aop||> ** OS[(fun _:hid=>false),false,nil,ci] ** JBdata nest c old)
 (V293_exit_boundary_body 112%Z 110%Z 111%Z 120%Z 105%Z 103%Z 106%Z 108%Z 109%Z 200%Z
 (V293_interrupt_handoff 103%Z 108%Z 106%Z))Afalse OwnershipWaiting.
Proof.
 intros;unfold JBcells,XEpost,JBdata;apply V293_OSIntExit_exact_body;try lia.
 - exists 4;vm_compute;intuition lia.
 - vm_compute;discriminate.
 - exact(proj1(proj2(proj2(proj2 RTliteral_rel)))).
 - exact(proj2(proj2(proj2(proj2 RTliteral_rel)))).
 - vm_compute;repeat constructor.
 - exists(Int.repr 6,wait(os_stat_sem(72%positive,Int.repr 5))Int.one,Vptr(120%positive,Int.repr 7));vm_compute;reflexivity.
 - exact I.
 - reflexivity.
Qed.
