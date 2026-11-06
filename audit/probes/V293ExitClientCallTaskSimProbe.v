(* Same client call on both levels; vary only the abstract API binding. *)
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
Definition CCspec:osspec:=((fun f=>if Z.eq_dec f 114%Z then
 Some((fun _:vallist=>spec_seq sched(spec_done None)),(Tvoid,nil))else None),
 (fun _=>None),V293_scheduler).
Theorem CCnonempty_client_call : forall n ip,
 n<=1 ->
 TaskSim(RCprogram,(ACpo,CGempty,ip))(curs(scall 114%Z nil),(kenil,kstop))
 (ACge,ACle,ACmemory n,(fun _=>false),(false,nil,nil))
 (RCprogram,CCspec)(curs(scall 114%Z nil),(kenil,kstop))
 (RIabstract OwnershipWaiting)V293_shared_li ACinv
 (fun st=>satp(fst st)(snd st)(RDYINV ACinv OwnershipWaiting **LINV V293_shared_li OwnershipWaiting nil))OwnershipWaiting.
Proof.
 intros n ip Bound;unfold ACinv,ACrest,ACle.
 eapply V293_exit_client_call_TaskSim with(nc:=6)(bc:=94%positive)(bo:=93%positive)
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
 - intros(p&m&Task&Minimum);vm_compute in Task;discriminate.
 - exact Bound.
 - discriminate.
 - discriminate.
 - discriminate.
 - reflexivity.
 - reflexivity.
 - reflexivity.
 - apply ACbase;lia.
Qed.

Lemma CCbinding_single_factor :
 fst(fst CCspec)114%Z=Some((fun _:vallist=>spec_seq sched(spec_done None)),(Tvoid,nil)) /\ fst(fst GHspec)114%Z=None /\ snd CCspec=snd GHspec /\snd(fst CCspec)=snd(fst GHspec) /\ (forall f,f<>114%Z ->fst(fst CCspec)f=fst(fst GHspec)f).
Proof. repeat split;try reflexivity;intros f NE;
 change((if Z.eq_dec f 114%Z then Some((fun _:vallist=>spec_seq sched(spec_done None)),(Tvoid,@nil type))else None)=None);
 destruct(Z.eq_dec f 114%Z);congruence. Qed.

Lemma CCabstract_entry : forall t cst O,
 htstep(RCprogram,CCspec)t(curs(sfexec 114%Z nil nil),(kenil,kstop))cst O
 (curs(hapi_code(spec_seq sched(spec_done None))),(kenil,kstop))cst O.
Proof. intros;apply V293_client_nil_api_enter;vm_compute;reflexivity. Qed.

Theorem CCmissing_binding_no_high_step : forall t cst O Cf cst' O',
 ~htstep(RCprogram,GHspec)t(curs(sfexec 114%Z nil nil),(kenil,kstop))cst O Cf cst' O'.
Proof.
 intros t cst O Cf cst' O' Step;inversion Step;subst;
 repeat match goal with E:(_,_) = (_,_) |- _=>inversion E;clear E;subst end.
 - match goal with H:cstep _ _ _ _ _ |- _=>inversion H;subst end;
   match goal with
   | H:estep _ _ _ _ _ _ |- _=>inversion H;subst;discriminate
   | H:sstep _ _ _ _ _ _ _ |- _=>inversion H;subst;try discriminate
   end.
   repeat match goal with E:(_,_) = (_,_) |- _=>inversion E;clear E;subst end.
   match goal with H:RCprogram 114%Z=Some _ |- _=>vm_compute in H;discriminate H end.
 - match goal with H:hapistep _ _ _ _ _ |- _=>inversion H;subst;try discriminate end.
   repeat match goal with E:(_,_) = (_,_) |- _=>inversion E;clear E;subst end.
   match goal with E:GHspec=(?B,_,_),H:?B 114%Z=Some _ |- _=>
     pose proof(f_equal(fun A=>fst(fst A)114%Z)E)as Empty;
     change(None=B 114%Z)in Empty;rewrite <-Empty in H;discriminate H end.
Qed.

(* Removing the high API binding cannot change this concrete client step. *)
Lemma CCclient_step_unchanged : forall n,
 cstep(pumerge RCprogram ACpo)(curs(scall 114%Z nil),(kenil,kstop))
 (ACge,ACle,ACmemory n)(curs(sfexec 114%Z nil nil),(kenil,kstop))
 (ACge,ACle,ACmemory n).
Proof. intro n;eapply stmt_step;[reflexivity|apply snpcall_step]. Qed.

Definition CCclient : clientst :=
 (ACge,set(emp:cltenvs)OwnershipWaiting ACle,(emp:mem)).
Lemma CCactual_client_low_step : forall n ip,exists cst',
 ltstep(RCprogram,(ACpo,CGempty,ip))OwnershipWaiting
 (curs(scall 114%Z nil),(kenil,kstop))CCclient
 (ACge,ACle,ACmemory n,(fun _=>false),(false,nil,nil))
 (curs(sfexec 114%Z nil nil),(kenil,kstop))cst'
 (ACge,ACle,ACmemory n,(fun _=>false),(false,nil,nil)).
Proof.
 intros n ip;unfold CCclient;
 exists(ACge,set(set(emp:cltenvs)OwnershipWaiting ACle)OwnershipWaiting ACle,(emp:mem)).
 eapply clt_step with(m:=(ACge,ACle,(emp:mem)))(m':=(ACge,ACle,(emp:mem)));
 try reflexivity.
 - eapply stmt_step;[reflexivity|apply snpcall_step].
 - apply ACclient_call_not_OS.
 - apply map_get_set.
Qed.
