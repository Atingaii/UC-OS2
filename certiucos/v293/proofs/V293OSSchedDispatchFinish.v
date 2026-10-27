(* Complete the abstract schedule on both enabled branches of the SAME
   normalized dispatch program. Disabled guards still defer scheduling.
   The port, critical section and full physical invariant remain open. *)
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedDispatchTail.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedShared.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedDispatchShared.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedSwitch.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchState.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCurrent.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedGuards.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCritical.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedChange.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTarget.
Require Import CertiOS.certiucos.v293.code.V293OSSchedChange.
Require Import CertiOS.certiucos.v293.code.V293OSSchedGuards.
Require Import CertiOS.certiucos.v293.code.V293OSSchedDispatch.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import Coq.Lists.List Lia.
Local Open Scope nat_scope.

Lemma V293_good_frame_action_free : forall p, GoodFrm p -> can_change_aop p.
Proof.
  induction p; simpl in *; intuition eauto.
Qed.

Section DispatchFinish.
Variables unmap group rows high : var.
Variables bt bg br bh : block.
Variables lo hi : nat.
Variable tid : Modules.tid.
Variable aop : spec_code.
Variables table target : var.
Variable tp : type.
Variables bp bo : block.
Variable entries : list val.
Variable tasks : TcbMod.map.
Variable events : EcbMod.map.
Variable now : int32.
Variables current counter : var.
Variables bcur bcounter : block.
Variable nc : nat.
Variable frame : asrt.
Variable stack : list hid.
Variable critical : list bool.
Let tail c := V293_dispatch_tail unmap group rows high bt bg br bh lo hi tid aop
  table target tp bp bo entries tasks events now current counter bcur bcounter nc frame stack critical c.
Let locals c := V293_dispatch_locals unmap group rows high bt bg br bh lo hi
  table target tp bp bo entries current counter bcur bcounter nc frame c.
Let resumed op c := V293_switch_resume target tp tid op stack critical (locals c).

(* Open precisely the existing snapshot; no abstract table is duplicated.
   All resources are retained, including the residual Atrue in locals. *)
Definition V293_dispatch_self_resources c :=
  ((V293_shared_flags ** ((CurTid tid ** V293_shared_fields tid tasks events now) **
    (GV target @ (Tptr tp) |-> (Vptr tid)))) ** CurTid tid) **
  ((Ais stack ** Acs critical) ** locals c).

Lemma V293_dispatch_self_action_free : forall c,
  GoodFrm frame -> can_change_aop (V293_dispatch_self_resources c).
Proof.
  intros c Hf.
  pose proof (V293_dispatch_locals_good unmap group rows high bt bg br bh lo hi
    table target tp bp bo entries current counter bcur bcounter nc frame c Hf) as Hl.
  apply V293_good_frame_action_free in Hl.
  unfold V293_dispatch_self_resources, V293_shared_flags, V293_shared_fields,
    CurTid, Agvarmapsto, Aptrmapsto, isrclr.
  cbn [can_change_aop]. repeat split; intros; auto.
  all: unfold V293_dispatch_locals in Hl; cbn in Hl; tauto.
Qed.

Theorem V293_dispatch_self_sched : forall c s,
  V293_highest_ready tasks tid -> s |= V293_dispatch_self_resources c ->
  sched_self V293_scheduler (getabst s).
Proof.
  intros c s Hhighest Hs.
  assert (Hp : s |= (CurTid tid ** V293_shared_fields tid tasks events now) ** Atrue)
    by (unfold V293_dispatch_self_resources in Hs; sep auto).
  destruct (V293_shared_fields_core_get _ _ _ _ _ _ Hp) as [HC [HT _]].
  exists tid. split; [exact HC | exists tasks; auto].
Qed.

Theorem V293_dispatch_equal_finish : forall c,
  lo < 256 -> hi < 256 -> (exists p, V293_bitmap_ready lo hi p) ->
  V293_bitmap_tasks lo hi tasks -> V293_priority_table entries tasks ->
  V293_current_task tasks tid nc -> GoodFrm frame ->
  V293_ready_select lo hi (V293_ready_group lo hi) = nc ->
  absinferfull V293_scheduler V293_shared_li (tail c) (resumed aop c) tid.
Proof.
  intros c Hlo Hhi Hr Hb Htable Hcur Hf Heq.
  assert (Hhighest : V293_highest_ready tasks tid).
  { destruct (V293_ready_selection_task lo hi entries tasks Hlo Hhi Hr Hb Htable)
      as [next [m [Ht [Hp Hnext]]]].
    pose proof (proj2 (V293_OSSched_current_target lo hi entries tasks tid nc next
      Hlo Hhi Hr Hb Htable Hcur Hnext) Heq). subst next. exact Hnext. }
  assert (Hfree : can_change_aop (V293_dispatch_self_resources c))
    by (apply V293_dispatch_self_action_free; exact Hf).
  eapply absinfer_conseq' with
    (p := <||sched;;aop||> ** V293_dispatch_self_resources c)
    (q := <||aop||> ** V293_dispatch_self_resources c).
  - intros s Hs. unfold resumed, V293_switch_resume, V293_dispatch_self_resources in *.
    assert (HK : s |= <||aop||> **
      ((V293_dispatch_snapshot target tp tid tasks events now tid ** CurTid tid) **
        ((Ais stack ** Acs critical) ** locals c))).
    { eapply astar_mono with (P := <||aop||>); [intros st H; exact H | | exact Hs].
      eapply astar_mono; [ | intros st H; exact H].
      apply astar_mono; [apply V293_dispatch_snapshot_close | intros st H; exact H]. }
    assert (HQ : s |= <||aop||> **
      ((SWINV (V293_dispatch_inv target tp) ** CurTid tid) **
        ((Ais stack ** Acs critical) ** locals c))).
    { eapply astar_mono; [intros st H; exact H | | exact HK].
      eapply astar_mono; [ | intros st H; exact H].
      apply astar_mono; [intros st H; exact (proj1 H) | intros st H; exact H]. }
    unfold SWINVt, CurTid in *. sep auto.
  - eapply absinfer_trans' with
      (q := <||END None;;aop||> ** V293_dispatch_self_resources c).
    + apply absinfer_seq'; try exact Hfree.
      eapply (absinfer_sched' _ (fun _ => True) _ _ _ _); try exact Hfree.
      * intros s H; exact H.
      * intros s Hs. apply V293_dispatch_self_sched with (c := c); assumption.
    + apply absinfer_seq_end'; try exact Hfree. intros s H; exact H.
  - intros s Hs. apply V293_dispatch_tail_split in Hs.
    destruct Hs as [next Hs]. apply astar_l_apure_elim in Hs. destruct Hs as [Hnext Hs].
    pose proof (proj2 (V293_OSSched_current_target lo hi entries tasks tid nc next
      Hlo Hhi Hr Hb Htable Hcur Hnext) Heq). subst next.
    unfold V293_switch_payload in Hs. unfold V293_dispatch_self_resources.
    assert (HK : s |= <||sched;;aop||> **
      ((V293_dispatch_snapshot target tp tid tasks events now tid ** CurTid tid) **
        ((Ais stack ** Acs critical) ** locals c))) by (sep auto).
    eapply astar_mono; [intros st H; exact H | | exact HK].
    eapply astar_mono; [ | intros st H; exact H].
    apply astar_mono; [apply V293_dispatch_snapshot_open | intros st H; exact H].
Qed.

Definition V293_dispatch_completed_counter c :=
  if Nat.eqb (V293_ready_select lo hi (V293_ready_group lo hi)) nc then c else Int.add c Int.one.

Theorem V293_dispatch_change_finish : forall Spec r ri c,
  lo < 256 -> hi < 256 -> (exists p, V293_bitmap_ready lo hi p) ->
  V293_bitmap_tasks lo hi tasks -> V293_priority_table entries tasks ->
  V293_current_task tasks tid nc -> GoodFrm frame ->
  InfRules Spec V293_scheduler V293_shared_li (V293_dispatch_inv target tp) r ri
    (tail c) (V293_OSSched_change high current counter (sprim (switch target)))
    (resumed aop (V293_dispatch_completed_counter c)) tid.
Proof.
  intros Spec r ri c Hlo Hhi Hr Hb Htable Hcur Hf.
  eapply abscsq_rule_full with (p := tail c)
    (q := V293_dispatch_changed_post unmap group rows high bt bg br bh lo hi tid aop
      table target tp bp bo entries tasks events now current counter bcur bcounter nc frame stack critical c).
  - apply absinfer_eq'.
  - unfold V293_dispatch_changed_post, V293_dispatch_completed_counter.
    destruct (Nat.eqb (V293_ready_select lo hi (V293_ready_group lo hi)) nc) eqn:E.
    + apply Nat.eqb_eq in E. apply V293_dispatch_equal_finish; assumption.
    + apply absinfer_eq'.
  - apply V293_dispatch_change_switch; try assumption.
    + pose proof (proj1 Hcur). lia.
    + destruct Hcur as [_ [st [m Hget]]]. exists (Int.repr (Z.of_nat nc), st, m). exact Hget.
Qed.

Theorem V293_dispatch_prefix_finish : forall Spec r ri sched_id c,
  lo < 256 -> hi < 256 -> (exists p, V293_bitmap_ready lo hi p) ->
  V293_bitmap_tasks lo hi tasks -> V293_priority_table entries tasks ->
  V293_current_task tasks tid nc -> GoodFrm frame ->
  Spec sched_id = Some
    (V293_critical_fpre unmap group rows high bt bg br bh V293_shared_li V293_opened_inv V293_switch_li_good,
     V293_critical_fpost unmap group rows high bt bg br bh V293_shared_li V293_opened_inv V293_switch_li_good, (Tvoid, nil)) ->
  InfRules Spec V293_scheduler V293_shared_li (V293_dispatch_inv target tp) r ri
    (V293_dispatch_prefix_pre unmap group rows high bt bg br bh lo hi V293_shared_li tid (sched;;aop)
      table target tp bp bo entries tasks events now
      (V293_guard_cell current bcur nc ** (V293_counter_cell counter bcounter c ** frame)) stack critical)
    (sseq (V293_OSSched_unlocked_prefix sched_id table high target)
      (V293_OSSched_change high current counter (sprim (switch target))))
    (resumed aop (V293_dispatch_completed_counter c)) tid.
Proof.
  intros Spec r ri sched_id c Hlo Hhi Hr Hb Htable Hcur Hf Hspec.
  eapply seq_rule with (p' := tail c).
  - apply V293_OSSched_dispatch_prefix with (Hli := V293_switch_li_good); try assumption.
    repeat split; try apply V293_guard_cell_good; try apply V293_counter_cell_good; exact Hf.
  - apply V293_dispatch_change_finish; assumption.
Qed.
End DispatchFinish.

Theorem V293_OSSched_guarded_dispatch_finish : forall Spec r ri tid aop frame
    sched_id unmap group rows high bt bg br bh lo hi table target tp bp bo entries tasks events now
    stack critical interrupt lock bi bl ni nl current counter bcur bcounter nc c,
  lo < 256 -> hi < 256 -> (exists p, V293_bitmap_ready lo hi p) ->
  V293_bitmap_tasks lo hi tasks -> V293_priority_table entries tasks ->
  V293_current_task tasks tid nc -> GoodFrm frame -> ni < 256 -> nl < 256 ->
  Spec sched_id = Some
    (V293_critical_fpre unmap group rows high bt bg br bh V293_shared_li V293_opened_inv V293_switch_li_good,
     V293_critical_fpost unmap group rows high bt bg br bh V293_shared_li V293_opened_inv V293_switch_li_good, (Tvoid, nil)) ->
  let gf := V293_guard_cell interrupt bi ni ** (V293_guard_cell lock bl nl ** frame) in
  let pre := V293_dispatch_prefix_pre unmap group rows high bt bg br bh lo hi V293_shared_li tid (sched;;aop)
    table target tp bp bo entries tasks events now
    (V293_guard_cell current bcur nc ** (V293_counter_cell counter bcounter c ** gf)) stack critical in
  let post := V293_switch_resume target tp tid aop stack critical
    (V293_dispatch_locals unmap group rows high bt bg br bh lo hi table target tp bp bo entries
      current counter bcur bcounter nc gf
      (V293_dispatch_completed_counter lo hi nc c)) in
  InfRules Spec V293_scheduler V293_shared_li (V293_dispatch_inv target tp) r ri pre
    (V293_OSSched_guards interrupt lock
      (sseq (V293_OSSched_unlocked_prefix sched_id table high target)
        (V293_OSSched_change high current counter (sprim (switch target)))))
    (if Nat.eqb ni 0 && Nat.eqb nl 0 then post else pre) tid.
Proof.
  intros Spec r ri tid aop frame sched_id unmap group rows high bt bg br bh lo hi
    table target tp bp bo entries tasks events now stack critical interrupt lock bi bl ni nl
    current counter bcur bcounter nc c Hlo Hhi Hr Hb Htable Hcur Hframe Hni Hnl Hspec gf pre post.
  eapply V293_OSSched_guards_rule with (ri_mem := Atrue) (rl_mem := Atrue); try eassumption.
  - unfold pre, V293_dispatch_prefix_pre, gf. intros s Hs. sep auto.
  - unfold pre, V293_dispatch_prefix_pre, gf. intros s Hs. sep auto.
  - intros Hi Hl. apply V293_dispatch_prefix_finish; try assumption.
    unfold gf. repeat split; try apply V293_guard_cell_good; exact Hframe.
Qed.
