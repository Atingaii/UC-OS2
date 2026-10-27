(* One shared task table is lent to the actual internal call/target assignment
   and returned afterwards. The conjunction observes the SAME invariant heap;
   it does not allocate another copy of its abstract slots. *)
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCritical.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedPrefix.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTarget.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.certiucos.v293.code.V293OSSchedDispatch.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import Coq.Lists.List Lia.
Local Open Scope nat_scope.

Definition V293_shared_snapshot t ts es n := SWINV V293_shared_inv //\\
  ((CurTid t ** V293_shared_fields t ts es n) ** Atrue).

Lemma V293_shared_snapshot_open : forall t ts es n,
  V293_shared_snapshot t ts es n ==>
  V293_shared_flags ** (CurTid t ** V293_shared_fields t ts es n).
Proof.
  intros t ts es n s [HI Hobs].
  pose proof (V293_shared_fields_core_get _ _ _ _ _ _ Hobs) as [HC [HT [HE HN]]].
  apply V293_shared_switch_open in HI. unfold V293_shared_core in HI.
  sep normal in HI. sep destruct HI.
  assert (HP : s |= (CurTid x ** V293_shared_fields x x0 x1 x2) ** V293_shared_flags) by (sep auto).
  pose proof (V293_shared_fields_core_get _ _ _ _ _ _ HP) as [HC' [HT' [HE' HN']]].
  assert (x = t) by congruence. assert (x0 = ts) by congruence.
  assert (x1 = es) by congruence. assert (x2 = n) by congruence. subst.
  clear HP Hobs. sep auto.
Qed.
Lemma V293_shared_snapshot_close : forall t ts es n,
  V293_shared_flags ** (CurTid t ** V293_shared_fields t ts es n) ==>
  V293_shared_snapshot t ts es n.
Proof.
  intros t ts es n s Hs. split.
  - apply V293_shared_switch_close. unfold V293_shared_core. sep auto.
  - sep auto.
Qed.

(* The opened callee needs the interrupt protocol, but must NOT own a second
   copy of the shared core. RI remains V293_shared_inv in all InfRules. *)
Definition V293_opened_inv : Inv := fun k => V293_shared_inv (S k).
Lemma V293_opened_noisr : forall low n, starinv_noisr V293_opened_inv low n <==> Aemp.
Proof.
  intros low n. revert low. induction n; intros low s; simpl starinv_noisr.
  - reflexivity.
  - split; intro Hs.
    + apply astar_l_aemp_elim in Hs. apply IHn in Hs. exact Hs.
    + apply astar_l_aemp_intro. apply IHn. exact Hs.
Qed.
Lemma V293_opened_switch_open : SWINV V293_opened_inv ==> V293_shared_flags.
Proof.
  intros s Hs. destruct s as [[[[[[ge le] M] ir] aux] O] op].
  assert (HC : forall i, ir i = false).
  { eapply (V293_shared_clear_state ge le M ir aux O op). unfold SWINV in Hs. sep auto. }
  unfold SWINV in Hs. apply sat_split in Hs.
  destruct Hs as (m1 & m2 & o1 & o2 & JM & JO & HF & k & HK).
  apply sat_split in HK. destruct HK as (m3 & m4 & o3 & o4 & JM2 & JO2 & HT & HI).
  unfold invlth_isr in HI. rewrite Nat.sub_0_r in HI.
  apply invisr_imply_noisr' in HI; [ | intros; apply HC].
  apply V293_opened_noisr in HI.
  assert (HK' : (ge, le, m2, ir, aux, o2, op) |= ATopis k ** Aemp).
  { apply sat_split'. exists m3. exists m4. exists o3. exists o4. repeat first [assumption | split]. }
  apply astar_r_aemp_elim in HK'.
  unfold V293_shared_flags. apply sat_split'. exists m1. exists m2. exists o1. exists o2.
  repeat first [assumption | split]. exists k. exact HK'.
Qed.
Lemma V293_opened_switch_close : V293_shared_flags ==> SWINV V293_opened_inv.
Proof.
  intros s Hs. destruct s as [[[[[[ge le] M] ir] aux] O] op].
  assert (HC : forall i, ir i = false).
  { eapply (V293_shared_clear_state ge le M ir aux O op). unfold V293_shared_flags in Hs. sep auto. }
  unfold V293_shared_flags in Hs. apply sat_split in Hs.
  destruct Hs as [m1 [m2 [o1 [o2 [JM [JO [HF [k HT]]]]]]]].
  assert (HK : (ge, le, m2, ir, aux, o2, op) |= ATopis k ** Aemp) by (apply astar_r_aemp_intro; exact HT).
  eapply astar_mono in HK; [ | intros st H; exact H | intros st H; apply (proj2 (V293_opened_noisr 0 k st)); exact H].
  apply sat_split in HK. destruct HK as [m3 [m4 [o3 [o4 [JM2 [JO2 [HT' HI]]]]]]].
  apply V293_shared_clear_noisr_close in HI; [ | exact HC].
  unfold SWINV. apply sat_split'. exists m1. exists m2. exists o1. exists o2.
  repeat first [assumption | split]. exists k. unfold invlth_isr. rewrite Nat.sub_0_r.
  apply sat_split'. exists m3. exists m4. exists o3. exists o4. repeat first [assumption | split].
Qed.

Definition V293_shared_remainder t es n := CurTid t **
  (Aabsdata curtid (oscurt t) ** (Aabsdata absecblsid (absecblist es) ** Aabsdata ostmid (ostm n))).
Lemma V293_shared_remainder_good : forall t es n, GoodFrm (V293_shared_remainder t es n).
Proof. intros. unfold V293_shared_remainder, CurTid, Agvarmapsto, Aptrmapsto. simpl. repeat split; auto. Qed.

Definition V293_shared_prefix_pre unmap group rows high bt bg br bh lo hi li tid aop
    table target tp bp bo entries tasks events now frame old stack critical :=
  (V293_sched_internal_pre unmap group rows high bt bg br bh lo hi li tid aop **
    (V293_shared_snapshot tid tasks events now ** (Ais stack ** Acs critical))) **
  ((V293_prefix_bindings table high target tp bp bo ** V293_read_pointers tp bp 0 entries) **
    (frame ** V293_prefix_output tp bo old)).
Definition V293_shared_prefix_post unmap group rows high bt bg br bh lo hi li tid aop
    table target tp bp bo entries tasks events now frame stack critical :=
  EX t : Modules.tid, [|V293_highest_ready tasks t|] **
    ((V293_sched_internal_post unmap group rows high bt bg br bh lo hi li tid aop None **
      (V293_shared_snapshot tid tasks events now ** (Ais stack ** Acs critical))) **
      ((V293_prefix_bindings table high target tp bp bo ** V293_read_pointers tp bp 0 entries) **
        (frame ** V293_prefix_output tp bo (Vptr t)))).

(* Stable vertical interface: an actual call and assignment, ambient nonempty
   invariant, one table, fixed snapshots returned, no continuation oracle. *)
Theorem V293_OSSched_shared_prefix : forall Spec sd li r ri tid aop frame
    sched_id unmap group rows high bt bg br bh lo hi table target tp bp bo entries tasks events now old
    stack critical (Hli : GoodLInvAsrt li),
  lo < 256 -> hi < 256 -> (exists p, V293_bitmap_ready lo hi p) ->
  V293_bitmap_tasks lo hi tasks -> V293_priority_table entries tasks -> GoodFrm frame ->
  Spec sched_id = Some
    (V293_critical_fpre unmap group rows high bt bg br bh li V293_opened_inv Hli,
     V293_critical_fpost unmap group rows high bt bg br bh li V293_opened_inv Hli, (Tvoid, nil)) ->
  InfRules Spec sd li V293_shared_inv r ri
    (V293_shared_prefix_pre unmap group rows high bt bg br bh lo hi li tid aop
      table target tp bp bo entries tasks events now frame old stack critical)
    (V293_OSSched_unlocked_prefix sched_id table high target)
    (V293_shared_prefix_post unmap group rows high bt bg br bh lo hi li tid aop
      table target tp bp bo entries tasks events now frame stack critical) tid.
Proof.
  intros Spec sd li r ri tid aop frame sched_id unmap group rows high bt bg br bh lo hi
    table target tp bp bo entries tasks events now old stack critical Hli Hlo Hhi Hr Hb Htable Hframe Hspec.
  eapply conseq_rule.
  3: { eapply V293_resource_OSSched_critical_prefix with (I := V293_opened_inv)
       (frame := V293_shared_remainder tid events now ** frame) (Hli := Hli)
       (unmap := unmap) (group := group) (rows := rows) (bt := bt) (bg := bg) (br := br) (bh := bh)
       (lo := lo) (hi := hi) (tp := tp) (bp := bp) (bo := bo) (entries := entries) (tasks := tasks)
       (aop := aop) (old := old) (stack := stack) (critical := critical); try eassumption.
       split; [apply V293_shared_remainder_good | exact Hframe]. }
  - unfold V293_shared_prefix_pre, V293_prefix_frame, V293_sched_critical.
    intros s Hs.
    assert (HP : s |= V293_shared_snapshot tid tasks events now **
      (V293_sched_internal_pre unmap group rows high bt bg br bh lo hi li tid aop **
        ((Ais stack ** Acs critical) **
          ((V293_prefix_bindings table high target tp bp bo ** V293_read_pointers tp bp 0 entries) **
            (frame ** V293_prefix_output tp bo old))))) by (sep auto).
    eapply astar_mono in HP; [ | apply V293_shared_snapshot_open | intros st H; exact H].
    unfold V293_shared_fields in HP.
    assert (HK : s |= V293_shared_flags **
      ((CurTid tid ** (Aabsdata curtid (oscurt tid) **
        (Aabsdata abstcblsid (abstcblist tasks) **
          (Aabsdata absecblsid (absecblist events) ** Aabsdata ostmid (ostm now))))) **
       (V293_sched_internal_pre unmap group rows high bt bg br bh lo hi li tid aop **
        ((Ais stack ** Acs critical) **
          ((V293_prefix_bindings table high target tp bp bo ** V293_read_pointers tp bp 0 entries) **
            (frame ** V293_prefix_output tp bo old)))))) by (clear Hs; sep auto).
    eapply astar_mono in HK; [ | apply V293_opened_switch_close | intros st H; exact H].
    unfold V293_shared_remainder. clear Hs HP. sep auto.
  - unfold V293_shared_prefix_post, V293_prefix_frame, V293_shared_remainder, V293_sched_critical.
    intros s [t Hs]. exists t.
    assert (HP : s |= SWINV V293_opened_inv **
      ([|V293_highest_ready tasks t|] **
        (V293_sched_internal_post unmap group rows high bt bg br bh lo hi li tid aop None **
          ((V293_prefix_bindings table high target tp bp bo **
            (V293_read_pointers tp bp 0 entries ** Aabsdata abstcblsid (abstcblist tasks))) **
            ((Ais stack ** Acs critical) **
              ((CurTid tid ** (Aabsdata curtid (oscurt tid) **
                (Aabsdata absecblsid (absecblist events) ** Aabsdata ostmid (ostm now)))) **
                (frame ** V293_prefix_output tp bo (Vptr t)))))))) by (sep auto).
    eapply astar_mono in HP; [ | apply V293_opened_switch_open | intros st H; exact H].
    assert (HK : s |= (V293_shared_flags ** (CurTid tid ** V293_shared_fields tid tasks events now)) **
      ([|V293_highest_ready tasks t|] **
        (V293_sched_internal_post unmap group rows high bt bg br bh lo hi li tid aop None **
          ((Ais stack ** Acs critical) **
            ((V293_prefix_bindings table high target tp bp bo ** V293_read_pointers tp bp 0 entries) **
              (frame ** V293_prefix_output tp bo (Vptr t)))))))
      by (unfold V293_shared_fields; clear Hs; sep auto).
    eapply astar_mono in HK; [ | apply V293_shared_snapshot_close | intros st H; exact H].
    clear Hs HP. sep auto.
Qed.
