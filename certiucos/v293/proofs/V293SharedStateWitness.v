(* Non-vacuity for the ownership core, not initialized/reachable kernel states.
   Task/event tables are arbitrary: in particular, the current task need not
   be a member. Pointer bytes have full write permission in the same state. *)
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTargetWitness.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.auxdef.
Require Import CertiOS.framework.proof.rulesoundlib.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import Coq.Lists.List Lia.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCurrentWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCurrent.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTarget.
Local Open Scope nat_scope.

Definition V293_shared_fixture_ge : env := sig OSTCBCur (1%positive, Tptr Tvoid).
Definition V293_shared_fixture_mem t := V293_encoded_memory 1%positive 0 true
  (encode_val (Tptr Tvoid) (Vptr t)).
Definition V293_shared_fixture_abs t ts es n : osabst :=
  merge (sig curtid (oscurt t)) (merge (sig abstcblsid (abstcblist ts))
    (merge (sig absecblsid (absecblist es)) (sig ostmid (ostm n)))).
Definition V293_shared_fixture_state t ts es n :=
  V293_target_wstate V293_shared_fixture_ge emp
    (V293_shared_fixture_mem t) (V293_shared_fixture_abs t ts es n).

Lemma V293_shared_fixture_fields : forall t ts es n,
  V293_target_wstate V293_shared_fixture_ge emp emp (V293_shared_fixture_abs t ts es n) |=
  V293_shared_fields t ts es n.
Proof.
  intros. unfold V293_shared_fields, V293_shared_fixture_abs.
  repeat (eapply V293_target_wstate_star; [apply map_join_emp | apply map_join_merge; apply map_disjoint; intros key; destruct key; simpl; auto | split; reflexivity | ]).
  split; reflexivity.
Qed.

Lemma V293_shared_fixture_pointer : forall t,
  V293_target_wstate V293_shared_fixture_ge emp (V293_shared_fixture_mem t) emp |=
  GV OSTCBCur @ (Tptr Tvoid) |-> (Vptr t).
Proof.
  intros. exists 1%positive. eapply V293_target_wstate_star with
    (m1 := emp) (m2 := V293_shared_fixture_mem t) (o1 := emp) (o2 := emp).
  - apply map_join_comm. apply map_join_emp.
  - apply map_join_emp.
  - exists 1%positive. split; [apply map_get_sig | ]. repeat split; reflexivity.
  - split; [apply V293_encoded_memory_mapsto | reflexivity].
Qed.

Lemma V293_shared_fixture_flags :
  V293_target_wstate V293_shared_fixture_ge emp emp emp |= V293_shared_flags.
Proof.
  unfold V293_shared_flags.
  repeat (eapply V293_target_wstate_star with (m1 := emp) (m2 := emp) (o1 := emp) (o2 := emp);
    [apply map_join_emp | apply map_join_emp | | ]).
  - exists (fun _ : hid => false). split; repeat split; reflexivity.
  - repeat split; reflexivity.
  - exists INUM. repeat split; reflexivity.
Qed.

Lemma V293_shared_fixture_spatial : forall t ts es n,
  V293_shared_fixture_state t ts es n |= SWINVt V293_shared_inv t.
Proof.
  intros. apply V293_shared_switch_halves.
  eapply V293_target_wstate_star with (m1 := emp) (m2 := V293_shared_fixture_mem t)
    (o1 := emp) (o2 := V293_shared_fixture_abs t ts es n).
  - apply map_join_comm. apply map_join_emp.
  - apply map_join_comm. apply map_join_emp.
  - apply V293_shared_fixture_flags.
  - unfold V293_shared_full. exists ts. exists es. exists n.
    eapply V293_target_wstate_star with (m1 := V293_shared_fixture_mem t) (m2 := emp)
      (o1 := emp) (o2 := V293_shared_fixture_abs t ts es n).
    + apply map_join_emp.
    + apply map_join_comm. apply map_join_emp.
    + exists Tvoid. apply V293_shared_fixture_pointer.
    + apply V293_shared_fixture_fields.
Qed.

(* One actual writable store, for ANY task table, including a deleted current
   task. This is independent of GoodI's proof and discharges store existence. *)
Theorem V293_shared_store_witness : forall ct t ts es n,
  exists ge M M' O,
  get ge OSTCBCur = Some (1%positive, Tptr Tvoid) /\
  (ge, emp, M, (fun _ => false), (false, nil, nil), O, spec_done None) |= SWINVt V293_shared_inv ct /\
  store (Tptr Tvoid) M (1%positive, 0%Z) (Vptr t) = Some M' /\
  (ge, emp, M', (fun _ => false), (false, nil, nil), set O curtid (oscurt t), spec_done None) |= SWINVt V293_shared_inv t /\
  get O abstcblsid = Some (abstcblist ts) /\
  get O absecblsid = Some (absecblist es) /\ get O ostmid = Some (ostm n).
Proof.
  intros ct t ts es n.
  assert (HM : mapstoval (1%positive, 0%Z) (Tptr Tvoid) true (Vptr ct) (V293_shared_fixture_mem ct))
    by apply V293_encoded_memory_mapsto.
  destruct (store_exist_join' _ _ _ (Vptr t) _ _ _ HM (map_join_emp (V293_shared_fixture_mem ct))) as [M' HS].
  exists V293_shared_fixture_ge. exists (V293_shared_fixture_mem ct). exists M'.
  exists (V293_shared_fixture_abs ct ts es n).
  assert (GE : get V293_shared_fixture_ge OSTCBCur = Some (1%positive, Tptr Tvoid)) by apply map_get_sig.
  pose proof (V293_shared_fixture_spatial ct ts es n) as HP.
  split; [exact GE | ]. split; [exact HP | ]. split; [exact HS | ]. split.
  - eapply V293_shared_store; eassumption.
  - pose proof (V293_shared_fields_get _ _ _ _ _ (V293_shared_fixture_fields ct ts es n)) as [_ H]. exact H.
Qed.

Definition V293_shared_case_tasks (live : bool) : TcbMod.map := if live then V293_current_tasks
  else sig V293_current_next (Int.repr 12, rdy, Vnull).

Lemma V293_shared_case_highest : forall live,
  V293_highest_ready (V293_shared_case_tasks live) V293_current_next.
Proof.
  intros live. exists (Int.repr 12). exists Vnull. split.
  - destruct live; vm_compute; reflexivity.
  - intros t' p' m' H. destruct live.
    + unfold V293_shared_case_tasks, V293_current_tasks in H.
      destruct (tid_eq_dec V293_current_next t') as [E | E].
      * subst t'. rewrite map_get_set in H. inversion H; subst. lia.
      * rewrite map_get_set' in H by exact E.
        destruct (tid_eq_dec V293_idle_tid t') as [E' | E'].
        -- subst t'. rewrite map_get_sig in H. discriminate.
        -- rewrite map_get_sig' in H by exact E'. discriminate.
    + unfold V293_shared_case_tasks in H.
      destruct (tid_eq_dec V293_current_next t') as [E | E].
      * subst t'. rewrite map_get_sig in H. inversion H; subst. lia.
      * rewrite map_get_sig' in H by exact E. discriminate.
Qed.

(* Both GoodI branches have concrete states AND a highest-ready target.
   'live' means a waiting current member, not a ready current task. *)
Theorem V293_shared_switch_cases_witness : forall live,
  exists ge M M' O,
  get ge OSTCBCur = Some (1%positive, Tptr Tvoid) /\
  (ge, emp, M, (fun _ => false), (false, nil, nil), O, spec_done None) |= SWINVt V293_shared_inv V293_idle_tid /\
  (ge, emp, M, (fun _ => false), (false, nil, nil), O, spec_done None) |= AHprio V293_scheduler V293_current_next ** Atrue /\
  get O abstcblsid = Some (abstcblist (V293_shared_case_tasks live)) /\
  get (V293_shared_case_tasks live) V293_idle_tid =
    (if live then Some (Int.repr 4, wait os_stat_time Int.one, Vnull) else None) /\
  store (Tptr Tvoid) M (1%positive, 0%Z) (Vptr V293_current_next) = Some M' /\
  (ge, emp, M', (fun _ => false), (false, nil, nil), set O curtid (oscurt V293_current_next), spec_done None) |=
    SWINVt V293_shared_inv V293_current_next.
Proof.
  intros live. destruct (V293_shared_store_witness V293_idle_tid V293_current_next
    (V293_shared_case_tasks live) (emp : EcbMod.map) Int.zero)
    as [ge [M [M' [O [GE [HP [HS [HN [HT _]]]]]]]]].
  exists ge. exists M. exists M'. exists O.
  split; [exact GE | ]. split; [exact HP | ]. split.
  - apply V293_shared_switch_full in HP. unfold V293_shared_full in HP. sep normal in HP. sep destruct HP.
    assert (ET : x = V293_shared_case_tasks live).
    { assert (HT' : get O abstcblsid = Some (abstcblist x)).
      { change (get (getabst (ge, emp, M, (fun _ => false), (false, nil, nil), O, spec_done None)) abstcblsid = Some (abstcblist x)).
        eapply V293_star_abst_get_l with (p := Aabsdata abstcblsid (abstcblist x)) (q := Atrue).
        - apply V293_shared_abs_get.
        - unfold V293_shared_fields in HP. sep auto. }
      congruence. } subst x.
    eapply astar_mono with (P := Aabsdata abstcblsid (abstcblist (V293_shared_case_tasks live))) (Q := Atrue).
    + apply V293_tasks_highest_spatial. apply V293_shared_case_highest.
    + intros st H; exact H.
    + unfold V293_shared_fields in HP. sep auto.
  - split; [exact HT | ]. split; [destruct live; vm_compute; reflexivity | ]. split; assumption.
Qed.
