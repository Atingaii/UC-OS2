(* Open the SAME canonical task/ready/clock witnesses. No caller-supplied
   focused record, copied abstract slot, or load-to-ownership reconstruction. *)
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickReadyUpdate.
Require Import CertiOS.certiucos.v293.proofs.V293TimeReadyShared.
Require Import CertiOS.certiucos.v293.proofs.V293TimeShared.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTarget.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickWhileHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickLosslessFields.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickReadyChain.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickRecordReassembly.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickWhileRecords.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickTaskBridge.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickLoop.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickExpiry.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickDelayHoare.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyTaskInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293TCBFieldsHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TCBSuccessHoare.
Require Import CertiOS.certiucos.v293.proofs.V293NullBytes.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.certiucos.v293.code.V293OSTimeTick.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.soundness.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List Coq.Sorting.Permutation Lia.
Import ListNotations.
Local Open Scope nat_scope.

Lemma V293_tick_wait_priority_unique : forall p q,
  p<13 -> q<13 -> Int.repr (Z.of_nat p)=Int.repr (Z.of_nat q) -> p=q.
Proof.
  intros p q P Q E. apply (f_equal Int.unsigned) in E.
  rewrite !V293_priority_repr_unsigned in E by assumption. lia.
Qed.

(* For event waits the actual pend value comes from canonical ownership.
   A time wait has no canonical pend byte: only the explicit supplement can
   determine it. Both cases preserve the jointly separated remainder. *)
Lemma V293_tick_wait_record_open : forall b base d reason message p timepend R,
  p<13 -> (reason=os_stat_time -> timepend<256) ->
  V293_owned_task_record (b,Int.repr base) (Int.repr (Z.of_nat p))
    (wait reason (Int.repr d)) message ** R ==>
  EX pend:nat, [|pend<256 /\ (reason=os_stat_time -> pend=timepend)|] **
    (V293_owned_record_cells (V293_record_layout (b,Int.repr base) p
      (wait reason (Int.repr d)) message pend) ** R).
Proof.
  intros b base d reason message p timepend R P T s H.
  unfold V293_owned_task_record in H.
  apply astar_l_aexists_elim in H. destruct H as [q H].
  apply astar_l_aexists_elim in H. destruct H as [pend H].
  assert (K:s |= [|q<13 /\ Int.repr (Z.of_nat p)=Int.repr (Z.of_nat q) /\ pend<256|] **
    (V293_owned_record_cells (V293_record_layout (b,Int.repr base) q
      (wait reason (Int.repr d)) message pend) ** R)) by (clear -H;sep auto).
  apply astar_l_apure_elim in K. destruct K as [[Q [E Bound]] K].
  assert (Same:p=q) by (eapply V293_tick_wait_priority_unique;eassumption). subst q.
  destruct reason.
  - exists pend. apply astar_l_apure_intro;[exact K|split;[exact Bound|discriminate]].
  - exists pend. apply astar_l_apure_intro;[exact K|split;[exact Bound|discriminate]].
  - exists timepend. apply astar_l_apure_intro;[exact K|split;[apply T;reflexivity|reflexivity]].
  - exists pend. apply astar_l_apure_intro;[exact K|split;[exact Bound|discriminate]].
  - exists pend. apply astar_l_apure_intro;[exact K|split;[exact Bound|discriminate]].
Qed.

Section CoreFocus.
Variables br bg bp bn : block.

(* Exactly one unfolded core, still containing the FULL canonical taskmap.
   Its existential witnesses are exposed only to state the lookup condition.
   Only Next (and pend for time waits) are additional physical resources. *)
Definition V293_tick_wait_core_pre ct tasks es n b base d reason p timepend bc next frame :=
  ((CurTid ct ** V293_shared_fields ct tasks es n) ** V293_ready_payload br bg bp tasks) **
  (PV (bn,Int.zero) @ Tint32 |-> Vint32 n **
  (V293_owned_record_cell (V293_tick_pointer_cell bc (b,Int.repr base)) **
  (V293_owned_record_cells (V293_tick_wait_missing
     (V293_tick_wait_node b base d reason timepend p) reason next) ** frame))).

Lemma V293_tick_wait_core_unfold : forall b base d reason p timepend bc next frame,
  V293_time_ready_core br bg bp bn **
  (V293_owned_record_cell (V293_tick_pointer_cell bc (b,Int.repr base)) **
  (V293_owned_record_cells (V293_tick_wait_missing
    (V293_tick_wait_node b base d reason timepend p) reason next) ** frame)) ==>
  EX ct:tid, EX tasks:TcbMod.map, EX es:EcbMod.map, EX n:int32,
    V293_tick_wait_core_pre ct tasks es n b base d reason p timepend bc next frame.
Proof.
  intros b base d reason p timepend bc next frame s H.
  unfold V293_time_ready_core,V293_time_ready_fields,V293_tick_wait_core_pre in *.
  clear -H;sep auto.
Qed.

Lemma V293_tick_wait_core_fold : forall ct tasks es n b base d reason p timepend bc next frame,
  V293_tick_wait_core_pre ct tasks es n b base d reason p timepend bc next frame ==>
  V293_time_ready_core br bg bp bn **
  (V293_owned_record_cell (V293_tick_pointer_cell bc (b,Int.repr base)) **
  (V293_owned_record_cells (V293_tick_wait_missing
    (V293_tick_wait_node b base d reason timepend p) reason next) ** frame)).
Proof.
  intros ct tasks es n b base d reason p timepend bc next frame s H.
  unfold V293_time_ready_core,V293_time_ready_fields,V293_tick_wait_core_pre in *.
  clear -H;sep auto.
Qed.

Lemma V293_tick_wait_core_focus : forall ct tasks es n b base d reason message p timepend bc next frame,
  p<13 -> (reason=os_stat_time -> timepend<256) ->
  get tasks (b,Int.repr base)=Some (Int.repr (Z.of_nat p),wait reason (Int.repr d),message) ->
  V293_tick_wait_core_pre ct tasks es n b base d reason p timepend bc next frame ==>
  EX pend:nat, EX lo:nat, EX hi:nat, EX entries:list val,
    [|pend<256 /\ V293_ready_rel lo hi entries tasks|] **
    V293_tick_ready_wait_pre br bg bp bn ct tasks es n
      (V293_tick_wait_node b base d reason pend p) reason message pend lo hi entries bc next frame.
Proof.
  intros ct tasks es n b base d reason message p timepend bc next frame P T Task s H.
  unfold V293_tick_wait_core_pre,V293_ready_payload in H.
  set (rest:=(CurTid ct ** V293_shared_fields ct tasks es n) **
    (PV (bn,Int.zero) @ Tint32 |-> Vint32 n **
    (V293_owned_record_cell (V293_tick_pointer_cell bc (b,Int.repr base)) **
    (V293_owned_record_cells (V293_tick_wait_missing
      (V293_tick_wait_node b base d reason timepend p) reason next) ** frame)))).
  assert (Ready:s |= V293_ready_owned br bg bp tasks ** (V293_owned_task_records tasks ** rest))
    by (unfold rest;clear -H;sep auto).
  unfold V293_ready_owned in Ready.
  apply astar_l_aexists_elim in Ready. destruct Ready as [lo Ready].
  apply astar_l_aexists_elim in Ready. destruct Ready as [hi Ready].
  apply astar_l_aexists_elim in Ready. destruct Ready as [entries Ready].
  assert (Ready':s |= [|V293_ready_rel lo hi entries tasks|] **
    (V293_owned_record_cells (V293_ready_cells br bg bp lo hi entries) **
     (V293_owned_task_records tasks ** rest))) by (clear -Ready;sep auto).
  apply astar_l_apure_elim in Ready'. destruct Ready' as [Rel Ready'].
  assert (Focused:s |= V293_owned_task_record (b,Int.repr base) (Int.repr (Z.of_nat p))
    (wait reason (Int.repr d)) message **
    (V293_owned_task_records (del tasks (b,Int.repr base)) **
    (V293_owned_record_cells (V293_ready_cells br bg bp lo hi entries) ** rest))).
  { apply V293_owned_task_records_focus;[exact Task | ]. clear -Ready';sep auto. }
  pose proof (V293_tick_wait_record_open b base d reason message p timepend _ P T s Focused) as Opened.
  destruct Opened as [pend Opened]. apply astar_l_apure_elim in Opened.
  destruct Opened as [[Bound Time] Opened].
  exists pend. exists lo. exists hi. exists entries.
  apply astar_l_apure_intro;[ |split;assumption].
  unfold V293_tick_ready_wait_pre,rest in *.
  cbn [V293_tick_task_pointer V293_tick_wait_node V293_tick_prio V293_tick_delay_value].
  assert (Missing:V293_tick_wait_missing (V293_tick_wait_node b base d reason timepend p) reason next =
    V293_tick_wait_missing (V293_tick_wait_node b base d reason pend p) reason next).
  { destruct reason;try reflexivity.
    rewrite (Time eq_refl). reflexivity. }
  rewrite Missing in Opened. clear -Opened. sep auto.
Qed.

Lemma V293_tick_wait_node_binding_valid : forall b base d reason pend p message,
  (0<=base /\ base+54<=Int.max_unsigned)%Z ->
  (0<=d<=Int.max_unsigned)%Z -> pend<256 -> p<13 -> p<>12 ->
  V293_tick_binding_valid
    (V293_tick_wait_node b base d reason pend p,(wait reason (Int.repr d),message)).
Proof.
  intros b base d reason pend p message Base D Pend P Nonidle.
  split;[apply V293_tick_wait_node_valid;assumption | ].
  split;[exact P|split;reflexivity].
Qed.

Theorem V293_tick_core_wait_iteration_hoare : forall Spec sd li I r ri tid
  ct tasks es n b base d reason message p timepend bc next frame ptcb rows group ir si ci,
  NoAbs li -> (0<=base /\ base+54<=Int.max_unsigned)%Z ->
  (0<=d<=Int.max_unsigned)%Z -> p<13 -> p<>12 -> (reason=os_stat_time -> timepend<256) ->
  get tasks (b,Int.repr base)=Some (Int.repr (Z.of_nat p),wait reason (Int.repr d),message) ->
  (forall st, st |= frame -> V293_tick_delay_env ptcb rows group bc br bg (getgenv st) (getlenv st)) ->
  ((CurTid ct ** frame) ==> CurLINV li tid) -> GoodFrm frame -> can_change_aop frame ->
  (gettopis si<=INUM)%nat ->
  InfRules Spec sd li I r ri
    (<||spec_prim nil (V293_tick_wait_step (b,Int.repr base))||> ** OS[ir,false,si,ci] **
      V293_tick_wait_core_pre ct tasks es n b base d reason p timepend bc next frame)
    (V293_tick_iteration ptcb rows group)
    (EX pend:nat, <||END None||> ** OS[ir,false,si,ci] **
      V293_tick_ready_wait_post br bg bp bn
        (V293_tick_wait_node b base d reason pend p) reason message bc next frame) tid.
Proof.
  intros Spec sd li I r ri tid ct tasks es n b base d reason message p timepend bc next frame
    ptcb rows group ir si ci NA Base D P Nonidle T Task Env Inv GF Free Bound.
  eapply conseq_rule with
    (p:=EX pend:nat, EX lo:nat, EX hi:nat, EX entries:list val,
      (<||spec_prim nil (V293_tick_wait_step (b,Int.repr base))||> ** OS[ir,false,si,ci] **
      V293_tick_ready_wait_pre br bg bp bn ct tasks es n
        (V293_tick_wait_node b base d reason pend p) reason message pend lo hi entries bc next frame) **
      [|pend<256 /\ V293_ready_rel lo hi entries tasks|]).
  - intros st H.
    assert (K:st |= <||spec_prim nil (V293_tick_wait_step (b,Int.repr base))||> ** OS[ir,false,si,ci] **
      (EX pend:nat, EX lo:nat, EX hi:nat, EX entries:list val,
      [|pend<256 /\ V293_ready_rel lo hi entries tasks|] **
      V293_tick_ready_wait_pre br bg bp bn ct tasks es n
        (V293_tick_wait_node b base d reason pend p) reason message pend lo hi entries bc next frame)).
    { eapply astar_mono;[intros st0 H0;exact H0| |exact H].
      apply astar_mono;[intros st0 H0;exact H0|apply V293_tick_wait_core_focus;assumption]. }
    clear -K;sep auto.
  - intros st H;exact H.
  - apply ex_intro_rule. intros pend. apply ex_intro_rule. intros lo.
    apply ex_intro_rule. intros hi. apply ex_intro_rule. intros entries.
    apply pure_split_rule. intros [Pend Rel].
    eapply conseq_rule with
      (q:=<||END None||> ** OS[ir,false,si,ci] **
        V293_tick_ready_wait_post br bg bp bn
          (V293_tick_wait_node b base d reason pend p) reason message bc next frame).
    + intros st H;exact H.
    + intros st H. exists pend. exact H.
    + apply V293_tick_ready_wait_iteration_hoare with
        (t:=V293_tick_wait_node b base d reason pend p).
      * exact NA.
      * apply V293_tick_wait_node_binding_valid;assumption.
      * exact Task.
      * exact Rel.
      * exact Env.
      * exact Inv.
      * exact GF.
      * exact Free.
      * exact Bound.
Qed.

(* The same source rule, without exposing the invariant's task/event/clock
   witnesses to its caller. The lookup fact is tied to the very same map,
   not asserted using another separated abstract task slot. *)
Theorem V293_tick_core_wait_iteration : forall Spec sd li I r ri tid ct
  b base d reason message p timepend bc next frame ptcb rows group ir si ci,
  NoAbs li -> (0<=base /\ base+54<=Int.max_unsigned)%Z ->
  (0<=d<=Int.max_unsigned)%Z -> p<13 -> p<>12 -> (reason=os_stat_time -> timepend<256) ->
  (forall st, st |= frame -> V293_tick_delay_env ptcb rows group bc br bg (getgenv st) (getlenv st)) ->
  ((CurTid ct ** frame) ==> CurLINV li tid) -> GoodFrm frame -> can_change_aop frame ->
  (gettopis si<=INUM)%nat ->
  InfRules Spec sd li I r ri
    (EX tasks:TcbMod.map, EX es:EcbMod.map, EX n:int32,
      (<||spec_prim nil (V293_tick_wait_step (b,Int.repr base))||> ** OS[ir,false,si,ci] **
      V293_tick_wait_core_pre ct tasks es n b base d reason p timepend bc next frame) **
      [|get tasks (b,Int.repr base)=Some (Int.repr (Z.of_nat p),wait reason (Int.repr d),message)|])
    (V293_tick_iteration ptcb rows group)
    (EX pend:nat, <||END None||> ** OS[ir,false,si,ci] **
      V293_tick_ready_wait_post br bg bp bn
        (V293_tick_wait_node b base d reason pend p) reason message bc next frame) tid.
Proof.
  intros Spec sd li I r ri tid ct b base d reason message p timepend bc next frame ptcb rows group
    ir si ci NA Base D P Nonidle T Env Inv GF Free Bound.
  apply ex_intro_rule. intros tasks. apply ex_intro_rule. intros es. apply ex_intro_rule. intros n.
  apply pure_split_rule. intro Task.
  apply V293_tick_core_wait_iteration_hoare;assumption.
Qed.

Theorem V293_tick_core_wait_iteration_semantics : forall Spec sd li I r ri tid ct
  b base d reason message p timepend bc next frame ptcb rows group ir si ci,
  NoAbs li -> (0<=base /\ base+54<=Int.max_unsigned)%Z ->
  (0<=d<=Int.max_unsigned)%Z -> p<13 -> p<>12 -> (reason=os_stat_time -> timepend<256) ->
  (forall st, st |= frame -> V293_tick_delay_env ptcb rows group bc br bg (getgenv st) (getlenv st)) ->
  ((CurTid ct ** frame) ==> CurLINV li tid) -> GoodFrm frame -> can_change_aop frame ->
  (gettopis si<=INUM)%nat ->
  simulation.RuleSem Spec sd li I r ri
    (EX tasks:TcbMod.map, EX es:EcbMod.map, EX n:int32,
      (<||spec_prim nil (V293_tick_wait_step (b,Int.repr base))||> ** OS[ir,false,si,ci] **
      V293_tick_wait_core_pre ct tasks es n b base d reason p timepend bc next frame) **
      [|get tasks (b,Int.repr base)=Some (Int.repr (Z.of_nat p),wait reason (Int.repr d),message)|])
    (V293_tick_iteration ptcb rows group)
    (EX pend:nat, <||END None||> ** OS[ir,false,si,ci] **
      V293_tick_ready_wait_post br bg bp bn
        (V293_tick_wait_node b base d reason pend p) reason message bc next frame) tid.
Proof. intros. apply RuleSound. apply V293_tick_core_wait_iteration;assumption. Qed.
End CoreFocus.
