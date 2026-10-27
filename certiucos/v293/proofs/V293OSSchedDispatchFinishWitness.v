(* A complete locked source-prefix entry need not satisfy sched_self.
   This rules out consuming every disabled branch with the self rule.
   The fixture is satisfiable, not asserted reachable from initialization. *)
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedDispatchFinish.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedDispatchTailWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedDispatchShared.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCurrentWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewWitness.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTargetWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTarget.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedGuards.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedChange.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import Coq.Lists.List Lia.
Local Open Scope nat_scope.

Lemma V293_dispatch_entry_schedule_observation : forall target tp t tasks events now frame s,
  s |= V293_dispatch_entry target tp t tasks events now ** frame ->
  (sched_self V293_scheduler (getabst s) <-> V293_highest_ready tasks t).
Proof.
  intros target tp t tasks events now frame s Hs.
  assert (HC : get (getabst s) curtid = Some (oscurt t)).
  { eapply V293_star_abst_get_l; [ | exact Hs].
    intros st [_ H]. exact (proj1 (V293_shared_fields_core_get _ _ _ _ _ _ H)). }
  assert (HT : get (getabst s) abstcblsid = Some (abstcblist tasks)).
  { eapply V293_star_abst_get_l; [ | exact Hs].
    intros st [_ H]. exact (proj1 (proj2 (V293_shared_fields_core_get _ _ _ _ _ _ H))). }
  split.
  - intros [u [Hu [ts [Hts Hhighest]]]].
    assert (u = t) by congruence. assert (ts = tasks) by congruence. subst. exact Hhighest.
  - intro Hhighest. exists t. split; [exact HC | exists tasks; auto].
Qed.

Theorem V293_locked_dispatch_deferred_witness : forall c events now aop, exists s,
  s |= V293_dispatch_prefix_pre 100%Z 101%Z 102%Z 103%Z 1%positive 2%positive 3%positive 4%positive
    0 16 V293_shared_li V293_idle_tid (sched;;aop)
    106%Z 107%Z Tvoid 8%positive 10%positive
    (V293_current_mode_entries true) (V293_current_mode_tasks true) events now
    (V293_guard_cell 110%Z 13%positive (V293_current_mode_priority true) **
      (V293_counter_cell 111%Z 14%positive c **
        (V293_guard_cell 108%Z 11%positive 0 ** (V293_guard_cell 109%Z 12%positive 1 ** Aemp)))) nil nil /\
  ~ sched_self V293_scheduler (getabst s).
Proof.
  intros c events now aop.
  destruct (V293_dispatch_full_precondition_witness true 0 1 c events now aop ltac:(lia) ltac:(lia))
    as [s [_ [_ [_ [_ Hs]]]]].
  exists s. split; [exact Hs | ].
  assert (HE : s |= V293_dispatch_entry 107%Z Tvoid V293_idle_tid
    (V293_current_mode_tasks true) events now ** Atrue)
    by (unfold V293_dispatch_prefix_pre in Hs; sep auto).
  intro Hself. apply (proj1 (V293_dispatch_entry_schedule_observation _ _ _ _ _ _ _ _ HE)) in Hself.
  destruct Hself as [priority [message [Hready _]]].
  vm_compute in Hready. discriminate.
Qed.
