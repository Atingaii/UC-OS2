(* Borrow both the unique task table and the shared target cell. The actual
   source prefix returns them to dispatch_inv, not to the old target-free Inv. *)
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedShared.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedSwitch.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchState.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCritical.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedPrefix.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTarget.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedGuards.
Require Import CertiOS.certiucos.v293.code.V293OSSchedGuards.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.certiucos.v293.code.V293OSSchedDispatch.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import Coq.Lists.List Lia.
Local Open Scope nat_scope.

Definition V293_dispatch_entry target tp t tasks events now :=
  SWINV (V293_dispatch_inv target tp) //\\
    ((CurTid t ** V293_shared_fields t tasks events now) ** Atrue).
Lemma V293_dispatch_entry_open : forall target tp t tasks events now,
  V293_dispatch_entry target tp t tasks events now ==>
    V293_shared_flags ** ((CurTid t ** V293_shared_fields t tasks events now) **
      V293_dispatch_cell target tp).
Proof.
  intros target tp t tasks events now s [HI HO].
  pose proof (V293_shared_fields_core_get _ _ _ _ _ _ HO) as [HC [HT [HE HN]]].
  apply V293_dispatch_switch_open in HI.
  unfold V293_dispatch_core, V293_shared_core in HI. sep normal in HI. sep destruct HI.
  assert (HP : s |= (CurTid x ** V293_shared_fields x x0 x1 x2) ** Atrue) by (sep auto).
  pose proof (V293_shared_fields_core_get _ _ _ _ _ _ HP) as [HC' [HT' [HE' HN']]].
  assert (x = t) by congruence. assert (x0 = tasks) by congruence.
  assert (x1 = events) by congruence. assert (x2 = now) by congruence. subst.
  clear HP HO. sep auto.
Qed.
Lemma V293_dispatch_entry_close : forall target tp t tasks events now,
  V293_shared_flags ** ((CurTid t ** V293_shared_fields t tasks events now) **
    V293_dispatch_cell target tp) ==> V293_dispatch_entry target tp t tasks events now.
Proof.
  intros target tp t tasks events now s Hs. split; [ | sep auto].
  apply V293_dispatch_switch_close. unfold V293_dispatch_core, V293_shared_core. sep auto.
Qed.

Lemma V293_dispatch_named_output : forall table high target tp bp bo v,
  V293_prefix_bindings table high target tp bp bo ** (GV target @ (Tptr tp) |-> v) ==>
    V293_prefix_bindings table high target tp bp bo ** V293_prefix_output tp bo v.
Proof.
  intros table high target tp bp bo v s Hs.
  destruct s as [[[[[[ge le] M] ir] aux] O] op].
  apply sat_split in Hs. destruct Hs as (m1 & m2 & o1 & o2 & JM & JO & HB & HV).
  pose proof (V293_prefix_bindings_view _ _ _ _ _ _ _ HB) as [_ [HG _]].
  destruct (V293_dispatch_named_cell_parts _ _ _ _ _ _ _ _ _ _ HV) as (b & HG' & HM & HO).
  change (get ge target = Some (bo, Tptr tp)) in HG. assert (b = bo) by congruence. subst b.
  apply sat_split'. exists m1. exists m2. exists o1. exists o2. repeat first [assumption | split].
Qed.
Lemma V293_dispatch_output_named : forall table high target tp bp bo v,
  V293_prefix_bindings table high target tp bp bo ** V293_prefix_output tp bo v ==>
    V293_prefix_bindings table high target tp bp bo ** (GV target @ (Tptr tp) |-> v).
Proof.
  intros table high target tp bp bo v s Hs.
  destruct s as [[[[[[ge le] M] ir] aux] O] op].
  apply sat_split in Hs. destruct Hs as (m1 & m2 & o1 & o2 & JM & JO & HB & HV).
  pose proof (V293_prefix_bindings_view _ _ _ _ _ _ _ HB) as [_ [HG _]].
  change (get ge target = Some (bo, Tptr tp)) in HG.
  apply sat_split'. exists m1. exists m2. exists o1. exists o2.
  repeat first [assumption | split].
  exists bo. apply sat_split'. exists (emp : mem). exists m2. exists (emp : osabst). exists o2.
  split; [apply map_join_comm; apply map_join_emp | ].
  split; [apply map_join_comm; apply map_join_emp | ].
  split; [exists bo; repeat split; auto | exact HV].
Qed.

Definition V293_dispatch_prefix_pre unmap group rows high bt bg br bh lo hi li tid aop
    table target tp bp bo entries tasks events now frame stack critical :=
  (V293_sched_internal_pre unmap group rows high bt bg br bh lo hi li tid aop **
    (V293_dispatch_entry target tp tid tasks events now ** (Ais stack ** Acs critical))) **
  ((V293_prefix_bindings table high target tp bp bo ** V293_read_pointers tp bp 0 entries) ** frame).
Definition V293_dispatch_prefix_post unmap group rows high bt bg br bh lo hi li tid aop
    table target tp bp bo entries tasks events now frame stack critical :=
  EX next : Modules.tid, [|V293_highest_ready tasks next|] **
    ((V293_sched_internal_post unmap group rows high bt bg br bh lo hi li tid aop None **
      (V293_dispatch_snapshot target tp tid tasks events now next ** (Ais stack ** Acs critical))) **
      ((V293_prefix_bindings table high target tp bp bo ** V293_read_pointers tp bp 0 entries) ** frame)).

Theorem V293_OSSched_dispatch_prefix : forall Spec sd li r ri tid aop frame
    sched_id unmap group rows high bt bg br bh lo hi table target tp bp bo entries tasks events now
    stack critical (Hli : GoodLInvAsrt li),
  lo < 256 -> hi < 256 -> (exists p, V293_bitmap_ready lo hi p) ->
  V293_bitmap_tasks lo hi tasks -> V293_priority_table entries tasks -> GoodFrm frame ->
  Spec sched_id = Some
    (V293_critical_fpre unmap group rows high bt bg br bh li V293_opened_inv Hli,
     V293_critical_fpost unmap group rows high bt bg br bh li V293_opened_inv Hli, (Tvoid, nil)) ->
  InfRules Spec sd li (V293_dispatch_inv target tp) r ri
    (V293_dispatch_prefix_pre unmap group rows high bt bg br bh lo hi li tid aop
      table target tp bp bo entries tasks events now frame stack critical)
    (V293_OSSched_unlocked_prefix sched_id table high target)
    (V293_dispatch_prefix_post unmap group rows high bt bg br bh lo hi li tid aop
      table target tp bp bo entries tasks events now frame stack critical) tid.
Proof.
  intros Spec sd li r ri tid aop frame sched_id unmap group rows high bt bg br bh lo hi
    table target tp bp bo entries tasks events now stack critical Hli Hlo Hhi Hr Hb Htable Hframe Hspec.
  eapply conseq_rule with (p := EX old : val,
    ((V293_sched_internal_pre unmap group rows high bt bg br bh lo hi li tid aop **
       V293_sched_critical V293_opened_inv stack critical) **
     (V293_prefix_frame table high target tp bp bo entries tasks
       (V293_shared_remainder tid events now ** frame) ** V293_prefix_output tp bo old))).
  - unfold V293_dispatch_prefix_pre. intros s Hs.
    eapply astar_mono in Hs.
    2: { apply astar_mono; [intros st Hz; exact Hz | apply astar_mono;
      [apply V293_dispatch_entry_open | intros st Hz; exact Hz]]. }
    2: { intros st Hz; exact Hz. }
    unfold V293_dispatch_cell in Hs. sep normal in Hs. sep destruct Hs. sep split in Hs.
    exists x.
    assert (HK : s |= (V293_prefix_bindings table high target tp bp bo **
      (GV target @ (Tptr tp) |-> x)) **
      (V293_shared_flags ** ((CurTid tid ** V293_shared_fields tid tasks events now) **
        (V293_sched_internal_pre unmap group rows high bt bg br bh lo hi li tid aop **
          ((Ais stack ** Acs critical) ** (V293_read_pointers tp bp 0 entries ** frame)))))) by (sep auto).
    eapply astar_mono in HK; [ | apply V293_dispatch_named_output | intros st Hz; exact Hz].
    assert (HL : s |= V293_shared_flags **
      ((V293_prefix_bindings table high target tp bp bo ** V293_prefix_output tp bo x) **
        ((CurTid tid ** V293_shared_fields tid tasks events now) **
          (V293_sched_internal_pre unmap group rows high bt bg br bh lo hi li tid aop **
            ((Ais stack ** Acs critical) ** (V293_read_pointers tp bp 0 entries ** frame)))))) by (clear Hs; sep auto).
    eapply astar_mono in HL; [ | apply V293_opened_switch_close | intros st Hz; exact Hz].
    unfold V293_prefix_frame, V293_shared_remainder, V293_shared_fields, V293_sched_critical.
    unfold V293_shared_fields in HL. clear Hs HK. sep auto.
  - intros s Hs. exact Hs.
  - apply ex_intro_rule. intro old. eapply conseq_rule.
    3: { eapply V293_resource_OSSched_critical_prefix with (I := V293_opened_inv) (Hli := Hli)
           (frame := V293_shared_remainder tid events now ** frame)
           (unmap := unmap) (group := group) (rows := rows) (bt := bt) (bg := bg) (br := br) (bh := bh)
           (lo := lo) (hi := hi) (tp := tp) (bp := bp) (bo := bo) (entries := entries) (tasks := tasks)
           (aop := aop) (old := old) (stack := stack) (critical := critical); try eassumption.
         split; [apply V293_shared_remainder_good | exact Hframe]. }
    + intros s Hs; exact Hs.
    + unfold V293_dispatch_prefix_post, V293_prefix_frame, V293_shared_remainder, V293_sched_critical.
      intros s [next Hs]. exists next.
      assert (HP : s |= SWINV V293_opened_inv **
        ([|V293_highest_ready tasks next|] **
          ((V293_prefix_bindings table high target tp bp bo ** V293_prefix_output tp bo (Vptr next)) **
            ((CurTid tid ** V293_shared_fields tid tasks events now) **
              (V293_sched_internal_post unmap group rows high bt bg br bh lo hi li tid aop None **
                ((Ais stack ** Acs critical) ** (V293_read_pointers tp bp 0 entries ** frame)))))))
        by (unfold V293_shared_fields; sep auto).
      eapply astar_mono in HP; [ | apply V293_opened_switch_open | intros st Hz; exact Hz].
      assert (HK : s |= (V293_prefix_bindings table high target tp bp bo ** V293_prefix_output tp bo (Vptr next)) **
        (V293_shared_flags ** ([|V293_highest_ready tasks next|] **
          ((CurTid tid ** V293_shared_fields tid tasks events now) **
            (V293_sched_internal_post unmap group rows high bt bg br bh lo hi li tid aop None **
              ((Ais stack ** Acs critical) ** (V293_read_pointers tp bp 0 entries ** frame))))))) by (clear Hs; sep auto).
      eapply astar_mono in HK; [ | apply V293_dispatch_output_named | intros st Hz; exact Hz].
      assert (HL : s |= (V293_shared_flags ** ((CurTid tid ** V293_shared_fields tid tasks events now) **
        (GV target @ (Tptr tp) |-> (Vptr next)))) **
        ([|V293_highest_ready tasks next|] **
          (V293_sched_internal_post unmap group rows high bt bg br bh lo hi li tid aop None **
            ((Ais stack ** Acs critical) **
              ((V293_prefix_bindings table high target tp bp bo ** V293_read_pointers tp bp 0 entries) ** frame)))))
        by (clear Hs HP; sep auto).
      eapply astar_mono in HL; [ | apply V293_dispatch_snapshot_close | intros st Hz; exact Hz].
      clear Hs HP HK. sep auto.
Qed.

(* Both disabled branches preserve the complete shared target unchanged.
   The enabled branch is exactly the frozen call/assignment prefix, no suffix. *)
Theorem V293_OSSched_guarded_dispatch_prefix : forall Spec sd li r ri tid aop frame
    sched_id unmap group rows high bt bg br bh lo hi table target tp bp bo entries tasks events now
    stack critical interrupt lock bi bl ni nl (Hli : GoodLInvAsrt li),
  lo < 256 -> hi < 256 -> (exists p, V293_bitmap_ready lo hi p) ->
  V293_bitmap_tasks lo hi tasks -> V293_priority_table entries tasks -> GoodFrm frame ->
  ni < 256 -> nl < 256 ->
  Spec sched_id = Some
    (V293_critical_fpre unmap group rows high bt bg br bh li V293_opened_inv Hli,
     V293_critical_fpost unmap group rows high bt bg br bh li V293_opened_inv Hli, (Tvoid, nil)) ->
  let gf := V293_guard_cell interrupt bi ni ** (V293_guard_cell lock bl nl ** frame) in
  let pre := V293_dispatch_prefix_pre unmap group rows high bt bg br bh lo hi li tid aop
    table target tp bp bo entries tasks events now gf stack critical in
  let post := V293_dispatch_prefix_post unmap group rows high bt bg br bh lo hi li tid aop
    table target tp bp bo entries tasks events now gf stack critical in
  InfRules Spec sd li (V293_dispatch_inv target tp) r ri pre
    (V293_OSSched_guards interrupt lock (V293_OSSched_unlocked_prefix sched_id table high target))
    (if Nat.eqb ni 0 && Nat.eqb nl 0 then post else pre) tid.
Proof.
  intros Spec sd li r ri tid aop frame sched_id unmap group rows high bt bg br bh lo hi
    table target tp bp bo entries tasks events now stack critical interrupt lock bi bl ni nl
    Hli Hlo Hhi Hr Hb Htable Hframe Hni Hnl Hspec gf pre post.
  eapply V293_OSSched_guards_rule with (ri_mem := Atrue) (rl_mem := Atrue); try eassumption.
  - unfold pre, V293_dispatch_prefix_pre, gf. intros s Hs. sep auto.
  - unfold pre, V293_dispatch_prefix_pre, gf. intros s Hs. sep auto.
  - intros Hi Hl. apply V293_OSSched_dispatch_prefix with (Hli := Hli); try assumption.
    unfold gf. repeat split; try apply V293_guard_cell_good; exact Hframe.
Qed.
