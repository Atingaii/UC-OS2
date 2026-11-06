(* Same source time API simulation, using the assumption-clean soundness bridge.
   Initialization and ISR-body correctness remain separate obligations. *)
Require Import CertiOS.certiucos.v293.proofs.V293TimeSourceAPI.
Require Import CertiOS.certiucos.v293.proofs.V293TimeReadyAPI.
Require Import CertiOS.certiucos.v293.proofs.V293TimeReadyShared.
Require Import CertiOS.certiucos.v293.proofs.V293TimeNamesGood.
Require Import CertiOS.certiucos.v293.proofs.V293TimeGetAPI.
Require Import CertiOS.certiucos.v293.proofs.V293TimeSetAPI.
Require Import CertiOS.certiucos.v293.proofs.V293TimeAccess.
Require Import CertiOS.certiucos.v293.code.V293TimeSource.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.auxdef.
Require Import CertiOS.framework.proof.oscorrectness.
Require Import CertiOS.framework.proof.simulation.
Require Import CertiOS.framework.proof.soundness.
Require Import CertiOS.framework.proof.lemmasfortoptheo.
Require Import CertiOS.framework.proof.toptheorem.

Require Import CertiOS.certiucos.v293.proofs.V293TimeSourceTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293Soundness.

Theorem V293_time_source_method_sound : forall br bg bp fget fset now ticks saved bn
    pi Spec lg f ab ft vl pre post tid,
  ticks <> saved -> now <> ticks -> now <> saved ->
  WFFuncsSim pi Spec V293_scheduler (V293_time_names_li now bn)
    (V293_time_ready_inv br bg bp bn) ->
  V293_source_time_spec fget fset f=Some(ab,ft) ->
  Some pre=BuildPreA' (V293_source_time_program fget fset now ticks saved)
    f (ab,ft) vl (V293_time_names_li now bn) tid lg ->
  Some post=BuildRetA' (V293_source_time_program fget fset now ticks saved)
    f (ab,ft) vl (V293_time_names_li now bn) tid lg ->
  exists tau d1 d2 body,
    V293_source_time_program fget fset now ticks saved f=Some(tau,d1,d2,body) /\
    MethSimAsrt pi V293_scheduler (V293_time_names_li now bn)
      (V293_time_ready_inv br bg bp bn) post Afalse pre body Afalse tid.
Proof.
  intros br bg bp fget fset now ticks saved bn pi Spec lg f ab ft vl pre post tid
    TS NT NS Internal API Pre Post.
  destruct (V293_source_time_ready_WFAPI br bg bp fget fset now ticks saved bn
    Spec lg TS NT NS) as [Dom Bodies].
  destruct (Bodies f ab vl pre post ft tid API Pre Post) as
    (tau & d1 & d2 & body & Code & Hoare).
  exists tau. exists d1. exists d2. exists body. split;[exact Code | ].
  unfold MethSimAsrt. eapply MethSim_to_Methsim'.
  - apply V293_time_ready_names_good.
  - exact Internal.
  - apply V293_rule_sound. exact Hoare.
Qed.

(* This is the actual framework TaskSim, including its universal step,
   event, return and abort clauses; not an existential path closure.
   The source component is still only two APIs, not the whole kernel. *)
Theorem V293_time_source_tasksim_sound : forall br bg bp fget fset now ticks saved bn
    pc pi ip intspec Spec o O tid body,
  ticks <> saved -> now <> ticks -> now <> saved ->
  no_fun_same (V293_source_time_program fget fset now ticks saved) pi ->
  no_call_api_pu pi (V293_source_time_program fget fset now ticks saved) ->
  no_call_api_ipu ip (V293_source_time_program fget fset now ticks saved) ->
  good_os_pu pi ->
  WFFuncsSim pi Spec V293_scheduler (V293_time_names_li now bn)
    (V293_time_ready_inv br bg bp bn) ->
  EqDomInt ip intspec ->
  GoodClient pc (V293_source_time_program fget fset now ticks saved) pi ->
  InitTaskSt (V293_time_names_li now bn) tid (o,O) ->
  GoodStmt body pi ->
  TaskSim (pc,(V293_source_time_program fget fset now ticks saved,pi,ip))
    (nilcont body) o (pc,(V293_source_time_spec fget fset,intspec,V293_scheduler))
    (nilcont body) O (V293_time_names_li now bn) (V293_time_ready_inv br bg bp bn)
    (InitTaskSt (V293_time_names_li now bn) tid) tid.
Proof.
  intros br bg bp fget fset now ticks saved bn pc pi ip intspec Spec o O tid body
    TS NT NS Separate InternalCalls InterruptCalls Syntax Internal Domains Client Entry Stmt.
  eapply SmCTaskSim.
  - exact Separate.
  - split;[apply V293_source_time_no_api_calls | split;assumption].
  - apply V293_source_time_syntax;exact TS.
  - exact Syntax.
  - eapply V293_ApiMethSim with (Spec:=Spec).
    + apply V293_time_ready_names_good.
    + exact Internal.
    + apply bpr'_to_bpr. intros f ab vl pre post ft t API Pre Post.
      destruct (V293_source_time_ready_WFAPI br bg bp fget fset now ticks saved bn
        Spec init_lg TS NT NS) as [Dom Bodies].
      destruct (Bodies f ab vl pre post ft t API Pre Post) as
        (tau & d1 & d2 & s & Code & Hoare).
      exists tau. exists d1. exists d2. exists s. split;[exact Code | ]. split;[ | exact Hoare].
      exact (proj2 (V293_source_time_syntax fget fset now ticks saved TS
        f tau d1 d2 s Code)).
  - split;[exact Client | ].
    split;[exact (proj1 (V293_source_time_domains fget fset now ticks saved)) | ].
    split;[exact (proj2 (V293_source_time_domains fget fset now ticks saved)) | exact Domains].
  - exact Entry.
  - exists body. split;[reflexivity | split;[exact Stmt | exact I]].
Qed.
