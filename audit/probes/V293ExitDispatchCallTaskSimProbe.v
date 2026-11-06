(* One low program and one sched API, with independently constructed EC/AC heaps. *)
Require Import CertiOS.audit.probes.V293ExitActiveCallTaskSimProbe.
Require Import CertiOS.audit.probes.V293ExitGuardHelperProbe.
Require Import CertiOS.audit.probes.V293ReadySchedCallProbe.
Require Import CertiOS.audit.probes.V293ReadyCriticalGlobalProbe.
Require Import CertiOS.audit.probes.V293TaskRecordInvariantProbe.
Require Import CertiOS.audit.probes.V293TaskRecordOwnershipProbe.
Require Import CertiOS.certiucos.v293.proofs.V293ExitClientCallTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyStorageInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.simulation.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.
Require Import CertiOS.audit.probes.V293ExitEqualCallTaskSimProbe.
Require Import CertiOS.audit.probes.V293ExitClientCallTaskSimProbe.
Require Import CertiOS.certiucos.v293.proofs.V293ExitDispatchCallTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293SharedStateWitness.
Theorem DCsame_nonempty_client_call : forall n ip,
 n<=1 ->
 TaskSim(RCprogram,(ACpo,CGempty,ip))(curs(scall 114%Z nil),(kenil,kstop))
 (ECge,ECle,ECmemory n,(fun _=>false),(false,nil,nil))
 (RCprogram,CCspec)(curs(scall 114%Z nil),(kenil,kstop))
 (RIabstract OwnershipReady)V293_shared_li ECinv
 (fun st=>satp(fst st)(snd st)(RDYINV ECinv OwnershipReady **LINV V293_shared_li OwnershipReady nil))OwnershipReady.
Proof.
 intros n ip Bound;unfold ECinv,ECrest,ECle.
 eapply V293_exit_dispatch_client_call_TaskSim with(nc:=4)(bc:=94%positive)(bo:=93%positive)
 (oldtarget:=Vptr OwnershipWaiting)(c:=Int.mone)(oldhigh:=V293_byteval 88)
 (tasks:=OwnershipTasks)(rest:=nil)(saved:=120%Z)(helper:=107%Z)
 (running:=132%Z)(nesting:=130%Z)(lock:=131%Z)
 (unmap:=100%Z)(group:=101%Z)(rows:=102%Z)(y:=104%Z).
 - reflexivity.
 - vm_compute;reflexivity.
 - vm_compute;reflexivity.
 - right;right;reflexivity.
 - vm_compute;reflexivity.
 - discriminate.
 - discriminate.
 - discriminate.
 - discriminate.
 - reflexivity.
 - reflexivity.
 - reflexivity.
 - reflexivity.
 - discriminate.
 - discriminate.
 - discriminate.
 - discriminate.
 - discriminate.
 - reflexivity.
 - reflexivity.
 - reflexivity.
 - reflexivity.
 - exact(RIfixed_tasks OwnershipReady).
 - split;[lia|exists rdy;exists Vnull;reflexivity].
 - exact Bound.
 - discriminate.
 - discriminate.
 - discriminate.
 - reflexivity.
 - reflexivity.
 - reflexivity.
 - reflexivity.
 - apply ECbase;lia.
Qed.


Theorem DCchanged_nonempty_client_call : forall n ip,
 n<=1 ->
 TaskSim(RCprogram,(ACpo,CGempty,ip))(curs(scall 114%Z nil),(kenil,kstop))
 (ACge,ACle,ACmemory n,(fun _=>false),(false,nil,nil))
 (RCprogram,CCspec)(curs(scall 114%Z nil),(kenil,kstop))
 (RIabstract OwnershipWaiting)V293_shared_li ACinv
 (fun st=>satp(fst st)(snd st)(RDYINV ACinv OwnershipWaiting **LINV V293_shared_li OwnershipWaiting nil))OwnershipWaiting.
Proof.
 intros n ip Bound;unfold ACinv,ACrest,ACle.
 eapply V293_exit_dispatch_client_call_TaskSim with(nc:=6)(bc:=94%positive)(bo:=93%positive)
 (oldtarget:=Vptr OwnershipWaiting)(c:=Int.mone)(oldhigh:=V293_byteval 88)
 (tasks:=OwnershipTasks)(rest:=nil)(saved:=120%Z)(helper:=107%Z)
 (running:=132%Z)(nesting:=130%Z)(lock:=131%Z)
 (unmap:=100%Z)(group:=101%Z)(rows:=102%Z)(y:=104%Z).
 - reflexivity.
 - vm_compute;reflexivity.
 - vm_compute;reflexivity.
 - right;right;reflexivity.
 - vm_compute;reflexivity.
 - discriminate.
 - discriminate.
 - discriminate.
 - discriminate.
 - reflexivity.
 - reflexivity.
 - reflexivity.
 - reflexivity.
 - discriminate.
 - discriminate.
 - discriminate.
 - discriminate.
 - discriminate.
 - reflexivity.
 - reflexivity.
 - reflexivity.
 - reflexivity.
 - exact(RIfixed_tasks OwnershipWaiting).
 - split;[lia|exists(wait(os_stat_sem(72%positive,Int.repr 5))Int.one);exists(Vptr(120%positive,Int.repr 7));reflexivity].
 - exact Bound.
 - discriminate.
 - discriminate.
 - discriminate.
 - reflexivity.
 - reflexivity.
 - reflexivity.
 - reflexivity.
 - apply ACbase;lia.
Qed.

Lemma DCcurrent_single_factor :
 get(RIabstract OwnershipReady)curtid=Some(oscurt OwnershipReady) /\
 get(RIabstract OwnershipWaiting)curtid=Some(oscurt OwnershipWaiting) /\
 (forall id,id<>curtid ->
  get(RIabstract OwnershipReady)id=get(RIabstract OwnershipWaiting)id).
Proof. repeat split;try reflexivity;intros id NE;destruct id;try reflexivity;contradiction. Qed.

Lemma DCself_sched_step :
 spec_step V293_scheduler sched(RIabstract OwnershipReady)
 (spec_done None)(RIabstract OwnershipReady).
Proof.
 eapply spec_sched_step with(O:=RIabstract OwnershipReady)(Of:=emp)(t:=OwnershipReady).
 - reflexivity.
 - exists OwnershipTasks;split;[apply RIfixed_tasks|exact RIhighest].
 - apply map_join_emp.
Qed.

Lemma DCself_sched_requires_highest : forall ct,
 spec_step V293_scheduler sched(RIabstract ct)(spec_done None)(RIabstract ct) ->
 V293_highest_ready OwnershipTasks ct.
Proof.
 intros ct Step;inversion Step;subst.
 match goal with
 | C:get ?O curtid=Some(oscurt ?t),S:V293_scheduler ?O ?t,
   J:join ?O ?Of(RIabstract ct) |- _ =>
  assert(Full:get(RIabstract ct)curtid=Some(oscurt t))by(eapply OSAbstMod.join_get_l;[exact J|exact C]);
  assert(Selected:V293_scheduler(RIabstract ct)t)by(eapply(proj1 V293_scheduler_good);[exact J|exact S])
 end.
 assert(Current:get(RIabstract ct)curtid=Some(oscurt ct))by reflexivity.
 rewrite Current in Full;injection Full as E;rewrite E in Selected.
 destruct Selected as(tasks&Map&Highest).
 change(get(RIabstract ct)abstcblsid=Some(abstcblist tasks))in Map.
 pose proof(RIfixed_tasks ct)as Fixed;rewrite Fixed in Map;inversion Map;subst;exact Highest.
Qed.

Theorem DCwaiting_no_self_sched :
 ~spec_step V293_scheduler sched(RIabstract OwnershipWaiting)
 (spec_done None)(RIabstract OwnershipWaiting).
Proof.
 intro Step;apply DCself_sched_requires_highest in Step.
 destruct Step as(p&m&Task&Minimum);vm_compute in Task;discriminate.
Qed.

Lemma DCself_sched_skip_with_frame : forall pc ks cst Of OO,
 join(RIabstract OwnershipReady)Of OO ->
 htstepstar(pc,CCspec)OwnershipReady
 (curs(hapi_code(spec_seq sched(spec_done None))),(kenil,ks))cst OO
 (SKIP,(kenil,ks))cst OO.
Proof.
 intros pc ks cst Of OO Join.
 eapply V293_self_sched_skip with(O:=RIabstract OwnershipReady)(Of:=Of).
 - reflexivity.
 - reflexivity.
 - exists OwnershipTasks;split;[apply RIfixed_tasks|exact RIhighest].
 - exact Join.
Qed.
