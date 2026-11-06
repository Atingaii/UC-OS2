(* Independent literal resources reused unchanged from the earlier clock
   witness. This probe changes ONLY aop when reusing its physical layout. *)
Require Import CertiOS.audit.probes.V293TimeNamesGoodProbe.
Require Import CertiOS.audit.probes.V293ComponentLinkProbe.
Require Import CertiOS.certiucos.v293.proofs.V293TimeGetAPI.
Require Import CertiOS.certiucos.v293.proofs.V293TimeGetLink.
Require Import CertiOS.certiucos.v293.proofs.V293TimeNamesGood.
Require Import CertiOS.certiucos.v293.proofs.V293TimeShared.
Require Import CertiOS.certiucos.v293.proofs.V293TimeSetAPI.
Require Import CertiOS.certiucos.v293.proofs.V293TimeSharedSet.
Require Import CertiOS.certiucos.v293.proofs.V293TimeAccess.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.code.V293OSVersion.
Require Import CertiOS.certiucos.v293.code.V293OSSchedNew.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewInternal.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.toptheorem.
Require Import CertiOS.framework.proof.auxdef.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List.
Import ListNotations.
Local Open Scope nat_scope.

Definition GetState M O : RstateOP :=
  (NamesGE,NamesLE,M,(fun _=>false),(true,[],[]),O,V293_time_get_action).
Definition ClockAPI := V293_clock_api_unit 201%Z 202%Z 203%Z 1001%Z 1002%Z 1003%Z.
Definition GetResources :=
  p_local LinkLI NamesTid [] **
    ((EX v : val, LV 1002%Z @ Tint32 |-> v) **
      ((EX v : val, LV 1003%Z @ Tint32 |-> v) ** Aemp)) **
    Aie true ** Ais nil ** Acs nil ** Aisr empisr ** V293_time_api_domain 1002%Z 1003%Z.
Definition GetPre :=
  ((<||V293_time_get_action||> ** p_local LinkLI NamesTid [] **
    ((EX v : val, LV 1002%Z @ Tint32 |-> v) **
      ((EX v : val, LV 1003%Z @ Tint32 |-> v) ** Aemp)) **
    Aie true ** Ais nil ** Acs nil ** Aisr empisr) ** V293_time_api_domain 1002%Z 1003%Z).
Definition GetPost := fun result =>
  ((<||spec_done result||> ** p_local LinkLI NamesTid [] **
    ((EX v : val, LV 1002%Z @ Tint32 |-> v) **
      ((EX v : val, LV 1003%Z @ Tint32 |-> v) ** Aemp)) **
    Aie true ** Ais nil ** Acs nil ** Aisr empisr) ** V293_time_api_domain 1002%Z 1003%Z).

Theorem checked_get_actual_builders :
  Some GetPre=BuildPreA' ClockAPI 203%Z V293_TimeGet_api [] LinkLI NamesTid [] /\
  Some GetPost=BuildRetA' ClockAPI 203%Z V293_TimeGet_api [] LinkLI NamesTid [].
Proof. split;reflexivity. Qed.

Theorem checked_get_rejects_extra_argument :
  BuildPreA' ClockAPI 203%Z V293_TimeGet_api [Vint32 Int.zero] LinkLI NamesTid []=None.
Proof. reflexivity. Qed.

Lemma GetResourceIndependent : can_change_aop GetResources.
Proof.
  unfold GetResources,p_local,LINV,LinkLI,V293_time_names_li,CurTid,Agvarmapsto,Aptrmapsto.
  simpl. repeat split;intros;auto.
Qed.
Lemma GetCoreIndependent : can_change_aop (V293_time_shared_core 80%positive).
Proof.
  unfold V293_time_shared_core,V293_time_shared_fields,V293_shared_fields,
    CurTid,Agvarmapsto,Aptrmapsto.
  simpl. repeat split;intros;auto.
Qed.

Theorem checked_get_joint_entry : forall clock,
  GetState (NamesJointMemory clock) (NamesAbstract clock) |=
    V293_time_shared_core 80%positive ** GetPre.
Proof.
  intro clock. pose proof (NamesJointEntry clock) as H.
  assert (Pack : NamesState (NamesJointMemory clock) (NamesAbstract clock) |=
    <||V293_time_set_action (Int.repr 42)||> **
      (V293_time_shared_core 80%positive ** GetResources)).
  { unfold NamesPre,GetResources,NamesLi,LinkLI in *. sep auto. }
  apply astar_l_aop'_elim in Pack. destruct Pack as [_ Pack].
  assert (Moved : GetState (NamesJointMemory clock) (NamesAbstract clock) |=
    V293_time_shared_core 80%positive ** GetResources).
  { eapply change_aop_rule;[exact Pack | split;[apply GetCoreIndependent | apply GetResourceIndependent]]. }
  apply astar_l_aop'_intro with (aop:=V293_time_get_action) in Moved;[ | reflexivity].
  clear H Pack. unfold GetPre,GetResources in *. sep auto.
Qed.

(* The caller frame owns NO global clock bytes: the shared Inv supplies
   the clock only on entry to the actual critical section. *)
Theorem checked_get_caller_entry : GetState NamesCallerMemory emp |= GetPre.
Proof.
  pose proof NamesCallerEntry as H.
  assert (Pack : NamesState NamesCallerMemory emp |=
    <||V293_time_set_action (Int.repr 42)||> ** GetResources).
  { unfold NamesPre,GetResources,NamesLi,LinkLI in *. sep auto. }
  apply astar_l_aop'_elim in Pack. destruct Pack as [_ Pack].
  assert (Moved : GetState NamesCallerMemory emp |= GetResources).
  { eapply change_aop_rule;[exact Pack | apply GetResourceIndependent]. }
  apply astar_l_aop'_intro with (aop:=V293_time_get_action) in Moved;[ | reflexivity].
  clear H Pack. unfold GetPre,GetResources in *. sep auto.
Qed.

Theorem checked_get_body_same_shared_environment :
  InfRules LinkSpec V293_scheduler LinkLI (V293_time_shared_inv 80%positive)
    GetPost Afalse GetPre (V293_TimeGet_body 1001%Z 1002%Z 1003%Z) Afalse NamesTid.
Proof.
  eapply (V293_TimeGet_api_contract ClockAPI 203%Z LinkSpec V293_scheduler LinkLI []
    NamesTid [] GetPre GetPost 1001%Z 1002%Z 1003%Z 80%positive);try discriminate.
  - apply V293_time_names_local_good.
  - apply V293_time_names_noabs.
  - apply V293_time_names_global.
  - reflexivity.
  - exact (proj1 checked_get_actual_builders).
  - exact (proj2 checked_get_actual_builders).
Qed.

Theorem checked_clock_component :
  GoodI (V293_time_shared_inv 80%positive) V293_scheduler LinkLI /\
  WFAPI ClockAPI (V293_clock_api_spec 201%Z 202%Z 203%Z) LinkLI LinkSpec
    V293_scheduler (V293_time_shared_inv 80%positive) [] /\
  WFIFun LinkInternal LinkSpec V293_scheduler (V293_time_shared_inv 80%positive) LinkLI /\
  no_fun_same ClockAPI LinkInternal.
Proof. apply V293_clock_components_checked;discriminate. Qed.

Theorem checked_four_actual_bindings :
  let P := pumerge ClockAPI LinkInternal in
  P 201%Z=Some V293_OSVersion_function /\
  P 202%Z=Some (V293_TimeSet_function 1001%Z 1002%Z 1003%Z) /\
  P 203%Z=Some (V293_TimeGet_function 1001%Z 1002%Z 1003%Z) /\
  P 200%Z=Some (V293_OSSchedNew_function 100%Z 101%Z 102%Z 103%Z 104%Z).
Proof. apply V293_clock_linked_entries;discriminate. Qed.

(* Both sides share the very same O and physical clock. The negative side
   does NOT fail because of an API argument/entry/name gate. *)
Theorem checked_get_read_positive : forall sd clock,
  get (NamesAbstract clock) ostmid=Some (ostm clock) /\
  load Tint32 (merge NamesPointer (NamesClock clock)) (80%positive,0%Z)=Some (Vint32 clock) /\
  spec_step sd V293_time_get_action (NamesAbstract clock)
    (END (Some (Vint32 clock))) (NamesAbstract clock).
Proof.
  intros sd clock. destruct (NamesLiteralClockAgreement clock) as [Abstract Physical].
  split;[exact Abstract | ]. split;[exact Physical | apply V293_time_get_transition;exact Abstract].
Qed.

Theorem checked_get_read_result_exact : forall sd O result O' clock,
  get O ostmid=Some (ostm clock) ->
  spec_step sd V293_time_get_action O (END result) O' ->
  result=Some (Vint32 clock) /\ O'=O.
Proof.
  intros sd O result O' clock Time Step.
  unfold V293_time_get_action in Step. inversion Step;subst.
  match goal with H : V293_time_get_step _ _ _ |- _ =>
    destruct H as [_ [n [Read Eq]]] end.
  inversion Eq;subst.
  assert (Whole : get O ostmid=Some (ostm n)).
  { eapply OSAbstMod.join_get_l;eassumption. }
  assert (n=clock) by congruence. subst n.
  split;[reflexivity | eapply map_join_deter;eassumption].
Qed.

Theorem checked_get_wrong_result_rejected : forall sd,
  ~spec_step sd V293_time_get_action (NamesAbstract (Int.repr 37))
    (END (Some (Vint32 (Int.repr 38)))) (NamesAbstract (Int.repr 37)).
Proof.
  intros sd Step.
  destruct (checked_get_read_result_exact sd (NamesAbstract (Int.repr 37))
    (Some (Vint32 (Int.repr 38))) (NamesAbstract (Int.repr 37)) (Int.repr 37) ltac:(reflexivity) Step) as [Wrong _].
  vm_compute in Wrong. discriminate.
Qed.
