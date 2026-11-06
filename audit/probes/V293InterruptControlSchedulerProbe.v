(* Same fixed handler and scheduler; physical execution stops before raw port112.
   The global step below is the existing HIGH-level rule, not raw-port execution. *)
Require Import CertiOS.certiucos.v293.proofs.V293InterruptControlScheduler.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptFixedControlSpec.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptControlRetention.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptQuietBuilder.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.audit.probes.V293OSIntExitSwitchEntryProbe.
Require Import CertiOS.audit.probes.V293OSIntExitDispatchCallProbe.
Require Import CertiOS.audit.probes.V293TaskRecordOwnershipProbe.
Require Import CertiOS.audit.probes.V293TaskRecordInvariantProbe.
Require Import CertiOS.audit.probes.V293InterruptBuilderQuietExecutionProbe.
Require Import CertiOS.audit.probes.V293InterruptQuietContinuousProbe.
Require Import CertiOS.audit.probes.V293InterruptQuietISRReturnProbe.
Require Import CertiOS.audit.probes.V293InterruptBoundQuietContinuousProbe.
Require Import CertiOS.audit.probes.V293InterruptBuilderNestedReturnProbe.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyFullCall.
Require Import CertiOS.audit.probes.V293OSIntExitReadyBodyProbe.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.auxdef.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Definition CSO:=RIabstract OwnershipWaiting.
Definition CSc:=V293_control 1 0 0.
Definition CSnext:=set CSO curtid(oscurt OwnershipReady).
Definition CSke:=keop1 negation Tint32 kenil.
Definition CSks:=kseq(sskip None)kstop.
Definition CSbefore:code:=(curs(hapi_code(sched;;spec_done None)),(CSke,CSks)).
Definition CSafter:code:=(curs(hapi_code(spec_done None)),(CSke,CSks)).
Definition CSready:code:=(cure(econst32(Int.repr 7)),(CSke,CSks)).
Definition CST:tasks:=set(set emp OwnershipReady CSready)OwnershipWaiting CSbefore.
Definition CSTnext:=set CST OwnershipWaiting CSafter.
Definition CSprog:hprog:=(SXprogram,((fun _=>None),(fun _=>None),V293_scheduler)).
Definition CSsource_run enabled ci bs Mf:=
 V293_local_steps SXprogram(curs(scall 300%Z nil),(kenil,kstop))
 ((SXge,SXcaller,SXmemory 1 6),(fun _=>false),(enabled,nil,ci))
 (curs(sfexec 112%Z nil nil),(kenil,SXK kstop))
 ((SXge,V293_cpu_lenv 601%Z bs,Mf),(fun _=>false),(false,nil,cons enabled ci)).

Lemma CSchosen : V293_scheduler CSO OwnershipReady.
Proof. exists OwnershipTasks;split;[apply RIfixed_tasks|exact FXhighest]. Qed.

Lemma CSsource_capture : forall enabled ci bs Mf,
 (SXge,V293_cpu_lenv 601%Z bs,Mf,(fun _=>false),(false,nil,cons enabled ci),CSO,spec_done None)|=SXpost bs ->
 V293_control_capture 98%positive 94%positive 95%positive
 (SXge,V293_cpu_lenv 601%Z bs,Mf,(fun _=>false),(false,nil,cons enabled ci),CSO,spec_done None)=Some(CSO,CSc).
Proof.
 intros enabled ci bs Mf Held.
 assert(Controls:(SXge,V293_cpu_lenv 601%Z bs,Mf,(fun _=>false),(false,nil,cons enabled ci),CSO,spec_done None)|=
 V293_irq_controls 98%positive 94%positive 95%positive 1 0 0).
 { unfold SXpost,SXframe,SXentry_frame,V293_owned_record_cell,V293_irq_controls in *;sep auto. }
 apply V293_control_capture_owned;try lia;exact Controls.
Qed.

(* Actual source prefix and readback are acquired first. The exact same O and
   selected pointer then support the labelled step and original hswi_step.
   This deliberately does not assert a low/high simulation relation. *)
Theorem CScompleted_coupling : forall enabled ci cst,exists bs Mf,
 CSsource_run enabled ci bs Mf /\
 load(Tptr V293_tcb_type)Mf(93%positive,0%Z)=Some(Vptr OwnershipReady) /\
 load Tint32 Mf(97%positive,0%Z)=Some(Vint32(Int.repr 20)) /\
 V293_control_capture 98%positive 94%positive 95%positive
 (SXge,V293_cpu_lenv 601%Z bs,Mf,(fun _=>false),(false,nil,cons enabled ci),CSO,spec_done None)=Some(CSO,CSc) /\
 V293_control_run V293_scheduler V293_control_Exit(CSO,V293_control 1 1 0)
 [(OwnershipWaiting,OwnershipReady)](V293_control_Core(spec_done None))(CSnext,CSc) /\
 hpstep CSprog CST cst CSO CSTnext cst CSnext /\
 get CSnext curtid=Some(oscurt OwnershipReady) /\
 get CSTnext OwnershipWaiting=Some CSafter /\
 get CSTnext OwnershipReady=Some CSready /\
 (forall key,key<>curtid ->get CSnext key=get CSO key).
Proof.
 intros enabled ci cst.
 destruct(SXcomplete_prefix enabled ci kstop)
 as(bs&Mf&Fresh&Exec&Post&Target&Counter&Cache&Alive&Frame).
 assert(Captured:V293_control_capture 98%positive 94%positive 95%positive
 (SXge,V293_cpu_lenv 601%Z bs,Mf,(fun _=>false),(false,nil,cons enabled ci),CSO,spec_done None)=Some(CSO,CSc)).
 { eapply CSsource_capture;exact Post. }
 assert(Switch:V293_control_run_step V293_scheduler
 (V293_control_Core(sched;;spec_done None))(CSO,CSc)(Some(OwnershipWaiting,OwnershipReady))
 (V293_control_Core(spec_done None))(CSnext,CSc)).
 { constructor;[reflexivity|exact CSchosen]. }
 assert(Code:get CST OwnershipWaiting=Some CSbefore)by(apply map_get_set).
 destruct(V293_control_switch_hpstep SXprogram (fun _=>None)(fun _=>None)V293_scheduler
 CST cst CSke CSks(sched;;spec_done None)CSO CSc OwnershipWaiting OwnershipReady
 (spec_done None)CSnext CSc Switch Code)as[Global[Kept[Observed[Outside TasksOutside]]]].
 exists bs;exists Mf;split;[exact Exec| ];split;[exact Target| ];split;[exact Counter| ];split;[exact Captured| ].
 split.
 - change(V293_control_run V293_scheduler V293_control_Exit(CSO,V293_control 1 1 0)
 (V293_control_emit None[(OwnershipWaiting,OwnershipReady)])(V293_control_Core(spec_done None))(CSnext,CSc)).
   eapply V293_control_run_cons.
   + apply V293_control_run_local;apply V293_control_exit_step;repeat split;cbn;lia.
   + change(V293_control_run V293_scheduler(V293_control_Core(sched;;spec_done None))(CSO,CSc)
     (V293_control_emit(Some(OwnershipWaiting,OwnershipReady))[])(V293_control_Core(spec_done None))(CSnext,CSc)).
     eapply V293_control_run_cons;[exact Switch|constructor].
 - split;[exact Global| ];split;[exact Observed| ];split;[apply map_get_set| ];split;[ |exact Outside].
   unfold CSTnext,CST;rewrite !map_get_set' by discriminate;apply map_get_set.
Qed.

(* Full high-level handler, not a claim that the SX fixture executed Enter. *)
Theorem CSsame_handler_branches :
 V293_control_run V293_scheduler V293_fixed_control_handler(CSO,V293_control 1 0 1)[]
 (V293_control_Core(spec_done None))(CSO,V293_control 1 0 1) /\
 V293_control_run V293_scheduler V293_fixed_control_handler(CSO,CSc)
 [(OwnershipWaiting,OwnershipReady)](V293_control_Core(spec_done None))(CSnext,CSc) /\
 V293_control_run V293_scheduler V293_fixed_control_handler(RIabstract OwnershipReady,CSc)[]
 (V293_control_Core(spec_done None))(RIabstract OwnershipReady,CSc).
Proof.
 split.
 - apply V293_control_handler_quiet;[repeat split;cbn;lia|reflexivity].
 - split.
   + apply V293_control_handler_switch;[repeat split;cbn;lia|reflexivity|reflexivity|exact CSchosen].
   + apply V293_control_handler_self with(current:=OwnershipReady).
     * repeat split;cbn;lia.
     * reflexivity.
     * reflexivity.
     * exists OwnershipTasks;split;[apply RIfixed_tasks|exact FXhighest].
Qed.

Theorem CSwithout_switch_cannot_complete :
 ~V293_control_run V293_scheduler V293_fixed_control_handler(CSO,CSc)[]
 (V293_control_Core(spec_done None))(CSnext,CSc).
Proof.
 intro Run;pose proof(V293_control_without_switch_current _ _ _ _ _ _ _ Run)as Same.
 change(Some(oscurt OwnershipWaiting)=get CSnext curtid)in Same.
 unfold CSnext in Same;rewrite map_get_set in Same;discriminate.
Qed.

Theorem CSwrong_target_rejected :
 ~V293_control_run_step V293_scheduler(V293_control_Core(sched;;spec_done None))(CSO,CSc)
 (Some(OwnershipWaiting,OwnershipWaiting))(V293_control_Core(spec_done None))(CSO,CSc).
Proof.
 intro Step;apply(V293_control_switch_target_exact _ _ _ _ _ _ _ _ (RIfixed_tasks OwnershipWaiting))in Step.
 destruct Step as[_[Highest _]];exact(SXnot_highest Highest).
Qed.

(* The completed physical quiet return from stage308 embeds without any event;
   no new C program, no alternative CC/QC selection is introduced here. *)
Theorem CSquiet_actual_return : forall r n l,r<256 ->n<256 ->l<256 ->
 V293_control_dispatch(V293_control_enter(V293_control r n l))=false ->
 exists M0 frame O Of,
 join M0 frame(JBmemory n Int.zero Int.zero) /\join O Of(RIabstract OwnershipWaiting) /\
 let M:=QEinput r l M0 in let Mf:=QEmemory r n l M in
 QEpath M Mf /\QKstate(isrupd QKother 0 false)Mf O|=NGret /\
 V293_control_run V293_scheduler V293_fixed_control_handler(O,V293_control r n l)[]
 (V293_control_Core(spec_done None))(O,QEfinal r n l).
Proof.
 intros r n l R N L Quiet.
 destruct(QEnonempty_execution r n l R N L Quiet)as(M0&frame&O&Of&JM&JO&Pre&Snapshot&Path&Ret&Fixed).
 exists M0;exists frame;exists O;exists Of;split;[exact JM| ];split;[exact JO| ].
 cbn zeta;split;[exact Path| ];split;[exact Ret| ];apply V293_control_run_legacy_exact;exact Fixed.
Qed.
