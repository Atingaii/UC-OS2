(* Original AC heap, changing only the lock byte; both calls retain ACinv.
   CCspec and QCspec are different: this is not yet one uniform high program. *)
Require Import CertiOS.audit.probes.V293ExitNoDispatchCallTaskSimProbe.
Require Import CertiOS.audit.probes.V293ExitDispatchCallTaskSimProbe.
Require Import CertiOS.audit.probes.V293ExitActiveCallTaskSimProbe.
Require Import CertiOS.audit.probes.V293ExitClientCallTaskSimProbe.
Require Import CertiOS.audit.probes.V293ExitQuietCallTaskSimProbe.
Require Import CertiOS.audit.probes.V293ReadyTaskInvariantProbe.
Require Import CertiOS.audit.probes.V293TaskRecordInvariantProbe.
Require Import CertiOS.audit.probes.V293TaskRecordOwnershipProbe.
Require Import CertiOS.audit.probes.V293ReadyCriticalGlobalProbe.
Require Import CertiOS.audit.probes.V293ReadySchedCallProbe.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptControlRetention.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptQuietBuilder.
Require Import CertiOS.certiucos.v293.proofs.V293ExitActiveCallTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293ExitCriticalPrefixTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTargetWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitHoare.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.certiucos.v293.code.V293OSSchedGuards.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.simulation.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Definition CRcall M A ip :=
 TaskSim(RCprogram,(ACpo,CGempty,ip))(curs(scall 114%Z nil),(kenil,kstop))
 (ACge,ACle,M,(fun _=>false),(false,nil,nil))
 (RCprogram,A)(curs(scall 114%Z nil),(kenil,kstop))
 (RIabstract OwnershipWaiting)V293_shared_li ACinv
 (fun st=>satp(fst st)(snd st)
  (RDYINV ACinv OwnershipWaiting **LINV V293_shared_li OwnershipWaiting nil))OwnershipWaiting.

Lemma CRoriginal_controls : forall n,n<256 ->
 V293_target_wstate ACge ACle(ACmemory n)(RIabstract OwnershipWaiting)|=
 V293_irq_controls 152%positive 150%positive 151%positive 1 n 0.
Proof.
 intros n Bound;pose proof(ACbase n Bound)as Held.
 unfold ACresource,V293_exit_active_resource,V293_exit_guard_resource in Held.
 unfold V293_irq_controls,V293_owned_record_cell in *;cbn zeta in *;sep auto.
Qed.

Theorem CRlock_only_pair : forall n ip,n<=1 ->exists Ml,
 store Tint8(ACmemory n)(151%positive,0%Z)(V293_byteval 1)=Some Ml /\
 (forall b i,(b,i)<>(151%positive,0%Z) ->get Ml(b,i)=get(ACmemory n)(b,i)) /\
 V293_control_read 152%positive 150%positive 151%positive(ACmemory n)=Some(V293_control 1 n 0) /\
 V293_control_read 152%positive 150%positive 151%positive Ml=Some(V293_control 1 n 1) /\
 V293_exit_depth n=0 /\
 evalval(V293_OSSched_zero 131%Z)(ACge,ACle,ACmemory n)=Some(Vint32 Int.one) /\
 evalval(V293_OSSched_zero 131%Z)(ACge,ACle,Ml)=Some(Vint32 Int.zero) /\
 V293_control_exit_code(V293_control 1 n 0)=sched;;spec_done None /\
 V293_control_exit_code(V293_control 1 n 1)=spec_done None /\
 CRcall(ACmemory n)CCspec ip /\ CRcall Ml QCspec ip.
Proof.
 intros n ip Bound.
 destruct(NDlock_single_factor_complete_call n 1 ip ltac:(lia)ltac:(lia)ltac:(lia))
 as[Ml[Old[Store[New[Outside[Yes[No Call]]]]]]].
 destruct(V293_irq_controls_load 152%positive 150%positive 151%positive 1 n 0
 _ ltac:(lia)ltac:(lia)ltac:(lia)(CRoriginal_controls n ltac:(lia)))as[Run[Nest Lock]].
 change(load Tint8(ACmemory n)(152%positive,0%Z)=Some(V293_byteval 1))in Run.
 change(load Tint8(ACmemory n)(150%positive,0%Z)=Some(V293_byteval n))in Nest.
 change(load Tint8(ACmemory n)(151%positive,0%Z)=Some(V293_byteval 0))in Lock.
 assert(Run':load Tint8 Ml(152%positive,0%Z)=Some(V293_byteval 1)).
 { transitivity(load Tint8(ACmemory n)(152%positive,0%Z));[ |exact Run].
   apply V293_load_block_frame;intros j;apply Outside;congruence. }
 assert(Nest':load Tint8 Ml(150%positive,0%Z)=Some(V293_byteval n)).
 { transitivity(load Tint8(ACmemory n)(150%positive,0%Z));[ |exact Nest].
   apply V293_load_block_frame;intros j;apply Outside;congruence. }
 assert(Enabled:V293_control_dispatch(V293_control 1 n 0)=true).
 { apply V293_control_dispatch_iff;auto. }
 assert(Disabled:V293_control_dispatch(V293_control 1 n 1)=false).
 { unfold V293_control_dispatch,V293_exit_enabled;cbn.
   rewrite Bool.andb_false_r;reflexivity. }
 exists Ml;split;[exact Store| ];split;[exact Outside| ];split.
 - eapply V293_control_read_exact;try eassumption;lia.
 - split.
   + eapply V293_control_read_exact;try eassumption;lia.
   + split;[unfold V293_exit_depth;lia| ];split;[exact Yes| ];split;[exact No| ];split.
     * apply V293_control_enabled_code;exact Enabled.
     * split;[apply V293_control_quiet_code;exact Disabled| ];split.
       -- apply DCchanged_nonempty_client_call;exact Bound.
       -- exact Call.
Qed.

Theorem CRboth_outer_paths : forall ip,
 (exists Ml,CRcall(ACmemory 0)CCspec ip /\ CRcall Ml QCspec ip) /\
 (exists Ml,CRcall(ACmemory 1)CCspec ip /\ CRcall Ml QCspec ip).
Proof.
 intro ip;split.
 - destruct(CRlock_only_pair 0 ip ltac:(lia))as[Ml[_[_[_[_[_[_[_[_[_ Calls]]]]]]]]]].
   exists Ml;exact Calls.
 - destruct(CRlock_only_pair 1 ip ltac:(lia))as[Ml[_[_[_[_[_[_[_[_[_ Calls]]]]]]]]]].
   exists Ml;exact Calls.
Qed.

(* The current invariant admits this input; initialized reachability and the
   stronger current-is-running invariant are deliberately not asserted. *)
Theorem CRerasure_actual_heap : forall ip,exists Ml,
 CRcall(ACmemory 1)CCspec ip /\ CRcall Ml QCspec ip /\
 ~(@ex (osabst->bool)(fun classify =>
 classify(RIabstract OwnershipWaiting)=V293_control_dispatch(V293_control 1 1 0) /\
 classify(RIabstract OwnershipWaiting)=V293_control_dispatch(V293_control 1 1 1))).
Proof.
 intro ip;destruct(CRlock_only_pair 1 ip ltac:(lia))as[Ml[_[_[_[_[_[_[_[_[_[Enabled Disabled]]]]]]]]]]].
 exists Ml;split;[exact Enabled| ];split;[exact Disabled| ].
 exact(V293_control_erasure_obstruction(RIabstract OwnershipWaiting)).
Qed.

Theorem CRquiet_nonhighest :
 ~spec_step V293_scheduler sched(RIabstract OwnershipWaiting)
 (spec_done None)(RIabstract OwnershipWaiting) /\
 V293_control_state_code(RIabstract OwnershipWaiting,V293_control 1 1 1)=spec_done None.
Proof. split;[exact DCwaiting_no_self_sched|reflexivity]. Qed.

Theorem CRboundaries :
 V293_control_exit_code(V293_control 0 0 0)=spec_done None /\
 V293_control_exit_code(V293_control 2 0 0)=spec_done None /\
 V293_control_exit_code(V293_control 1 0 0)=sched;;spec_done None /\
 V293_control_exit_code(V293_control 1 1 0)=sched;;spec_done None /\
 V293_control_exit_code(V293_control 1 2 0)=spec_done None /\
 V293_control_exit_code(V293_control 1 255 0)=spec_done None /\
 V293_control_exit_code(V293_control 1 0 255)=spec_done None /\
 V293_control_exit(V293_control_enter(V293_control 1 255 0))=V293_control 1 254 0.
Proof. repeat split;reflexivity. Qed.
