(* Non-vacuous equal and different targets with current membership.
   The different case keeps current blocked, as a scheduling caller may be. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.auxdef.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedChange.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedGuards.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedGuardsWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedPrefix.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedPrefixWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTargetWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTarget.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List Lia.
Local Open Scope nat_scope.

Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCurrent.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedChangeWitness.

Definition V293_current_next : Modules.addrval := (15%positive, Int.zero).
Definition V293_current_tasks : TcbMod.map :=
  set (sig V293_idle_tid (Int.repr 4, wait os_stat_time Int.one, Vnull))
    V293_current_next (Int.repr 12, rdy, Vnull).
Definition V293_current_entries : list val :=
  repeat Vnull 4 ++ cons (Vptr V293_idle_tid)
    (repeat Vnull 7 ++ cons (Vptr V293_current_next) nil).
Definition V293_current_mode_tasks (different : bool) := if different then V293_current_tasks else V293_idle_tasks.
Definition V293_current_mode_entries (different : bool) := if different then V293_current_entries else V293_idle_entries.
Definition V293_current_mode_priority (different : bool) := if different then 4 else 12.

Lemma V293_current_relations :
  V293_bitmap_tasks 0 16 V293_current_tasks /\
  V293_priority_table V293_current_entries V293_current_tasks /\
  V293_current_task V293_current_tasks V293_idle_tid 4.
Proof.
  assert (Hcur : get V293_current_tasks V293_idle_tid =
    Some (Int.repr 4, wait os_stat_time Int.one, Vnull)) by (vm_compute; reflexivity).
  assert (Hnext : get V293_current_tasks V293_current_next =
    Some (Int.repr 12, rdy, Vnull)) by (vm_compute; reflexivity).
  assert (Honly : forall t p st m, get V293_current_tasks t = Some (p, st, m) ->
    (t = V293_idle_tid /\ p = Int.repr 4 /\ st = wait os_stat_time Int.one /\ m = Vnull) \/
    (t = V293_current_next /\ p = Int.repr 12 /\ st = rdy /\ m = Vnull)).
  { intros t p st m H. unfold V293_current_tasks in H.
    destruct (tid_eq_dec V293_current_next t) as [E | E].
    - subst t. rewrite map_get_set in H. inversion H. right; auto.
    - rewrite map_get_set' in H by exact E.
      destruct (tid_eq_dec V293_idle_tid t) as [E' | E'].
      + subst t. rewrite map_get_sig in H. inversion H. left; auto.
      + rewrite map_get_sig' in H by exact E'. discriminate. }
  split.
  - intros p Hp. split.
    + intros Hb. assert (p = 12).
      { do 13 (destruct p as [ | p]; [vm_compute in Hb; intuition lia | ]); lia. }
      subst p. exists V293_current_next. exists Vnull. exact Hnext.
    + intros [t [m H]]. destruct (Honly _ _ _ _ H) as [[_ [_ [E _]]] | [_ [E _]]]; [discriminate | ].
      assert (p = 12) by (apply V293_priority_repr_injective; [exact Hp | lia | exact E]).
      subst p. vm_compute; intuition lia.
  - split.
    + split; [reflexivity | ]. intros t p st m H.
      destruct (Honly _ _ _ _ H) as [[Et [Ep _]] | [Et [Ep _]]]; subst t p.
      * exists 4. split; [lia | ]. split; reflexivity.
      * exists 12. split; [lia | ]. split; reflexivity.
    + split; [lia | ]. exists (wait os_stat_time Int.one). exists Vnull. exact Hcur.
Qed.

Lemma V293_current_mode_relations : forall different,
  V293_bitmap_tasks 0 16 (V293_current_mode_tasks different) /\
  V293_priority_table (V293_current_mode_entries different) (V293_current_mode_tasks different) /\
  V293_current_task (V293_current_mode_tasks different) V293_idle_tid (V293_current_mode_priority different).
Proof.
  intros [ | ]; [exact V293_current_relations | ].
  destruct V293_idle_relations as [Hb Ht]. split; [exact Hb | ]. split; [exact Ht | ].
  cbn [V293_current_mode_priority V293_current_mode_tasks]. split; [lia | ]. exists rdy. exists Vnull. apply map_get_sig.
Qed.

Definition V293_current_caller different :=
  merge (V293_pointer_memory Tvoid 8%positive 0 (V293_current_mode_entries different)) V293_prefix_fixture_output.
Definition V293_current_abs different : osabst :=
  sig abstcblsid (abstcblist (V293_current_mode_tasks different)).
Definition V293_current_memory different := merge V293_prefix_fixture_internal (V293_current_caller different).

Ltac V293_current_outside :=
  unfold V293_current_memory, V293_current_caller;
  repeat rewrite map_merge_semp by reflexivity;
  first [V293_prefix_outside | idtac];
  repeat first [rewrite V293_pointer_memory_outside by (left; congruence) |
    rewrite V293_encoded_memory_outside by (left; congruence)];
  try V293_prefix_outside; reflexivity.

Lemma V293_current_caller_sat : forall different,
  V293_target_wstate V293_change_fixture_ge emp (V293_current_caller different) (V293_current_abs different) |=
    V293_prefix_frame 106%Z 103%Z 107%Z Tvoid 8%positive 10%positive
      (V293_current_mode_entries different) (V293_current_mode_tasks different) Aemp ** V293_prefix_output Tvoid 10%positive Vnull.
Proof.
  intro different.
  eapply V293_target_wstate_star; [apply map_join_merge; apply map_disjoint; intros [b i];
    destruct (Pos.eq_dec b 8%positive); [subst b; right; left; V293_prefix_outside |
      left; apply V293_pointer_memory_outside; left; assumption] | apply map_join_emp | | ].
  - apply astar_r_aemp_intro.
    eapply V293_target_wstate_star with (m1 := emp) (m2 := (V293_pointer_memory Tvoid 8%positive 0 (V293_current_mode_entries different)))
      (o1 := emp) (o2 := (V293_current_abs different)).
    + apply map_join_comm. apply map_join_emp.
    + apply map_join_comm. apply map_join_emp.
    + unfold V293_prefix_bindings. repeat split.
      * exists 8%positive. split; [vm_compute; reflexivity | ]. repeat split; reflexivity.
      * exists 10%positive. split; [vm_compute; reflexivity | ]. repeat split; reflexivity.
      * intros [v H]; discriminate.
      * intros [v H]; discriminate.
      * intros [v H]; discriminate.
    + eapply V293_target_wstate_star with (m1 := (V293_pointer_memory Tvoid 8%positive 0 (V293_current_mode_entries different))) (m2 := emp)
        (o1 := emp) (o2 := (V293_current_abs different)).
      * apply map_join_emp.
      * apply map_join_comm. apply map_join_emp.
      * apply V293_read_pointers_witness.
      * split; reflexivity.
  - split; [apply V293_encoded_memory_mapsto | reflexivity].
Qed.

Lemma V293_current_pre_base : forall different,
  V293_target_wstate V293_change_fixture_ge emp (V293_current_memory different) (V293_current_abs different) |=
    V293_sched_internal_pre 100%Z 101%Z 102%Z 103%Z 1%positive 2%positive 3%positive 4%positive
      0 16 V293_witness_li V293_idle_tid (spec_done None) **
    (V293_prefix_frame 106%Z 103%Z 107%Z Tvoid 8%positive 10%positive
      (V293_current_mode_entries different) (V293_current_mode_tasks different) Aemp **
      V293_prefix_output Tvoid 10%positive Vnull).
Proof.
  intro different. eapply V293_target_wstate_star with (o1 := emp) (o2 := V293_current_abs different).
  - apply map_join_merge. apply map_disjoint. intros [b i].
    destruct (Pos.eq_dec b 8%positive); [subst b; left; V293_prefix_outside | ].
    destruct (Pos.eq_dec b 10%positive); [subst b; left; V293_prefix_outside | ].
    right; left. V293_current_outside.
  - apply map_join_comm. apply map_join_emp.
  - apply V293_prefix_fixture_internal_sat; vm_compute; reflexivity.
  - apply V293_current_caller_sat.
Qed.

Theorem V293_OSSched_current_precondition_witness : forall different ni nl c,
  ni < 256 -> nl < 256 -> exists s,
  V293_bitmap_tasks 0 16 (V293_current_mode_tasks different) /\
  V293_priority_table (V293_current_mode_entries different) (V293_current_mode_tasks different) /\
  V293_current_task (V293_current_mode_tasks different) V293_idle_tid (V293_current_mode_priority different) /\
  (V293_ready_select 0 16 (V293_ready_group 0 16) <> V293_current_mode_priority different <-> different = true) /\
  s |= V293_sched_internal_pre 100%Z 101%Z 102%Z 103%Z 1%positive 2%positive 3%positive 4%positive
    0 16 V293_witness_li V293_idle_tid (spec_done None) **
    (V293_prefix_frame 106%Z 103%Z 107%Z Tvoid 8%positive 10%positive
      (V293_current_mode_entries different) (V293_current_mode_tasks different)
      (V293_guard_cell 110%Z 13%positive (V293_current_mode_priority different) **
        (V293_guard_cell 108%Z 11%positive ni ** (V293_guard_cell 109%Z 12%positive nl ** Aemp))) **
      (V293_prefix_output Tvoid 10%positive Vnull ** V293_counter_cell 111%Z 14%positive c)).
Proof.
  intros different ni nl c Hni Hnl.
  exists (V293_target_wstate V293_change_fixture_ge emp
    (merge (V293_current_memory different) (V293_change_all_extra ni nl (V293_current_mode_priority different) c))
      (V293_current_abs different)).
  destruct (V293_current_mode_relations different) as [Hb [Ht Hcur]].
  split; [exact Hb | ]. split; [exact Ht | ]. split; [exact Hcur | ]. split.
  - destruct different; vm_compute; intuition congruence.
  - assert (Hs : V293_target_wstate V293_change_fixture_ge emp
      (merge (V293_current_memory different) (V293_change_all_extra ni nl (V293_current_mode_priority different) c))
        (V293_current_abs different) |=
      (V293_sched_internal_pre 100%Z 101%Z 102%Z 103%Z 1%positive 2%positive 3%positive 4%positive
        0 16 V293_witness_li V293_idle_tid (spec_done None) **
        (V293_prefix_frame 106%Z 103%Z 107%Z Tvoid 8%positive 10%positive
          (V293_current_mode_entries different) (V293_current_mode_tasks different) Aemp **
          V293_prefix_output Tvoid 10%positive Vnull)) **
      ((V293_guard_cell 108%Z 11%positive ni ** V293_guard_cell 109%Z 12%positive nl) **
        (V293_guard_cell 110%Z 13%positive (V293_current_mode_priority different) ** V293_counter_cell 111%Z 14%positive c))).
    { eapply V293_target_wstate_star with (o1 := V293_current_abs different) (o2 := emp).
      - apply map_join_merge. apply map_disjoint. intros [b i].
        destruct (Pos.eq_dec b 11%positive); [subst b; left; V293_current_outside | ].
        destruct (Pos.eq_dec b 12%positive); [subst b; left; V293_current_outside | ].
        destruct (Pos.eq_dec b 13%positive); [subst b; left; V293_current_outside | ].
        destruct (Pos.eq_dec b 14%positive); [subst b; left; V293_current_outside | ].
        right; left. V293_change_outside.
      - apply map_join_emp.
      - apply V293_current_pre_base.
      - apply V293_change_all_extra_witness. }
    unfold V293_prefix_frame in *. sep auto.
Qed.
