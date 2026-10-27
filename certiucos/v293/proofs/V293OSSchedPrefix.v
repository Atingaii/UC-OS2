(* The source-bound call and pointer assignment composed with actual rules.
   Symbol addresses, the pointee layout and the shared task relations are
   parameters; the critical-section wrapper is not part of this contract. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCall.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTarget.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.certiucos.v293.code.V293OSSchedDispatch.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import Coq.Lists.List Lia.
Local Open Scope nat_scope.

Definition V293_prefix_bindings table high target tp bp bo : asrt :=
  Agvarenv table (Tarray (Tptr tp) 13) (bp, 0%Z) //\\
  Agvarenv target (Tptr tp) (bo, 0%Z) //\\
  A_notin_lenv table //\\ A_notin_lenv high //\\ A_notin_lenv target.

Definition V293_prefix_frame table high target tp bp bo entries tasks frame :=
  (V293_prefix_bindings table high target tp bp bo **
    (V293_read_pointers tp bp 0 entries ** Aabsdata abstcblsid (abstcblist tasks))) ** frame.

Definition V293_prefix_output tp bo v := Amapsto (bo, 0%Z) (Tptr tp) true v.

Lemma V293_prefix_frame_good : forall table high target tp bp bo entries tasks frame,
  GoodFrm frame -> GoodFrm (V293_prefix_frame table high target tp bp bo entries tasks frame).
Proof.
  intros table high target tp bp bo entries tasks frame Hframe.
  assert (Hp : GoodFrm (V293_read_pointers tp bp 0 entries)).
  { generalize 0%Z. induction entries; intros offset; simpl; auto. }
  unfold V293_prefix_frame, V293_prefix_bindings. cbn [GoodFrm]. tauto.
Qed.

Lemma V293_prefix_bindings_view : forall table high target tp bp bo s,
  s |= V293_prefix_bindings table high target tp bp bo ->
  get (getgenv s) table = Some (bp, Tarray (Tptr tp) 13) /\
  get (getgenv s) target = Some (bo, Tptr tp) /\
  get (getlenv s) table = None /\ get (getlenv s) high = None /\ get (getlenv s) target = None.
Proof.
  intros table high target tp bp bo s [Gt [Go [Nt [Nh No]]]].
  destruct Gt as [b [E [Eb _]]]. inversion Eb; subst b.
  destruct Go as [b [E' [Eb2 _]]]. inversion Eb2; subst b.
  assert (N : forall (le : env) x, ~ indom le x -> get le x = None).
  { intros le x H. destruct (get le x) as [v | ] eqn:Ex; [ | reflexivity].
    exfalso. apply H. exists v; exact Ex. }
  cbn [sat] in Nt, Nh, No.
  repeat split; try assumption; apply N; tauto.
Qed.

Lemma V293_prefix_high_global : forall unmap group rows high bt bg br bh lo hi li tid hv s,
  s |= V293_sched_internal_resource unmap group rows high bt bg br bh lo hi li tid hv ->
  get (getgenv s) high = Some (bh, Tint8).
Proof.
  intros. eapply V293_star_env_l with (E := fun ge _ => get ge high = Some (bh, Tint8)); [ | exact H]. intros s0 H0.
  eapply V293_star_env_l with (E := fun ge _ => get ge high = Some (bh, Tint8)); [ | exact H0]. intros s1 H1.
  eapply V293_star_env_l with (E := fun ge _ => get ge high = Some (bh, Tint8)); [ | exact H1].
  intros s2 [_ [_ [_ [b [E [Eb _]]]]]]. inversion Eb; subst b; exact E.
Qed.

Lemma V293_prefix_selected_load : forall unmap group rows high bt bg br bh lo hi li tid s,
  lo < 256 -> hi < 256 -> (exists p, V293_bitmap_ready lo hi p) ->
  s |= V293_sched_internal_resource unmap group rows high bt bg br bh lo hi li tid
    (V293_byteval (V293_ready_select lo hi (V293_ready_group lo hi))) ->
  load Tint8 (getmem s) (bh, 0%Z) =
    Some (V293_byteval (V293_ready_select lo hi (V293_ready_group lo hi))).
Proof.
  intros unmap group rows high bt bg br bh lo hi li tid s Hlo Hhi Hr Hs.
  eapply V293_star_load_r; [ | exact Hs]. intros s0 H0.
  eapply V293_mapsto_load; [ | exact H0].
  pose proof (V293_ready_selection_range lo hi (V293_ready_group lo hi) Hlo Hhi eq_refl Hr). lia.
Qed.

Lemma V293_prefix_common_CurLINV : forall unmap group rows high bt bg br bh lo hi li tid hv rest,
  V293_sched_internal_resource unmap group rows high bt bg br bh lo hi li tid hv ** rest ==> CurLINV li tid.
Proof.
  intros unmap group rows high bt bg br bh lo hi li tid hv rest s Hs.
  eapply V293_star_CurLINV_l; [ | exact Hs]. apply V293_sched_internal_resource_CurLINV.
Qed.

Lemma V293_prefix_target_eval : forall unmap group rows high bt bg br bh lo hi li tid
    table target tp bp bo entries tasks frame t s,
  lo < 256 -> hi < 256 -> (exists p, V293_bitmap_ready lo hi p) ->
  V293_bitmap_tasks lo hi tasks -> V293_priority_table entries tasks ->
  nth (V293_ready_select lo hi (V293_ready_group lo hi)) entries Vnull = Vptr t ->
  s |= V293_sched_internal_resource unmap group rows high bt bg br bh lo hi li tid
      (V293_byteval (V293_ready_select lo hi (V293_ready_group lo hi))) **
    V293_prefix_frame table high target tp bp bo entries tasks frame ->
  evalval (V293_OSSched_target_expr table high) (getgenv s, getlenv s, getmem s) = Some (Vptr t) /\
  evaltype (V293_OSSched_target_expr table high) (getgenv s, getlenv s, getmem s) = Some (Tptr tp).
Proof.
  intros unmap group rows high bt bg br bh lo hi li tid table target tp bp bo entries tasks frame t s
    Hlo Hhi Hr Hb Htable Hentry Hs.
  assert (Ghigh : get (getgenv s) high = Some (bh, Tint8)).
  { eapply V293_star_env_l with (E := fun ge _ => get ge high = Some (bh, Tint8));
    [ | exact Hs]. apply V293_prefix_high_global. }
  assert (Mh : load Tint8 (getmem s) (bh, 0%Z) =
    Some (V293_byteval (V293_ready_select lo hi (V293_ready_group lo hi)))).
  { eapply V293_star_load_l; [ | exact Hs]. intros s0 H0.
    eapply V293_prefix_selected_load; eauto. }
  assert (E : get (getgenv s) table = Some (bp, Tarray (Tptr tp) 13) /\
    get (getgenv s) target = Some (bo, Tptr tp) /\ get (getlenv s) table = None /\
    get (getlenv s) high = None /\ get (getlenv s) target = None).
  { eapply V293_star_env_r; [ | exact Hs]. intros s0 H0.
    eapply V293_star_env_l; [ | exact H0]. intros s1 H1.
    eapply V293_star_env_l; [ | exact H1]. apply V293_prefix_bindings_view. }
  destruct E as [Gt [Go [Nt [Nh No]]]].
  assert (Hsp : s |= (V293_read_pointers tp bp 0 entries ** Aabsdata abstcblsid (abstcblist tasks)) **
    (V293_sched_internal_resource unmap group rows high bt bg br bh lo hi li tid
      (V293_byteval (V293_ready_select lo hi (V293_ready_group lo hi))) **
      (V293_prefix_bindings table high target tp bp bo ** frame))).
  { unfold V293_prefix_frame in Hs. sep auto. }
  destruct (V293_OSSched_target_task s table high tp bp bh lo hi entries tasks _
    Hlo Hhi Hr Hb Htable Nt Nh Gt Ghigh Mh Hsp) as [t' [m [Ht [Ev [Et Hsched]]]]].
  destruct (proj2 Htable _ _ _ _ Ht) as [p [Hp [Ep Hptr]]].
  pose proof (V293_ready_selection_range lo hi (V293_ready_group lo hi) Hlo Hhi eq_refl Hr) as Hrange.
  assert (p = V293_ready_select lo hi (V293_ready_group lo hi)).
  { symmetry. apply V293_priority_repr_injective; assumption. }
  subst p. rewrite Hentry in Hptr. inversion Hptr; subst t'. auto.
Qed.

Lemma V293_prefix_call_post : forall unmap group rows high bt bg br bh lo hi li tid aop rest,
  (EX result : option val,
    V293_sched_internal_post unmap group rows high bt bg br bh lo hi li tid aop result ** rest) ==>
  V293_sched_internal_post unmap group rows high bt bg br bh lo hi li tid aop None ** rest.
Proof.
  intros unmap group rows high bt bg br bh lo hi li tid aop rest s [result Hs].
  unfold V293_sched_internal_post in *. apply astar_assoc_elim in Hs.
  apply astar_l_apure_elim in Hs. destruct Hs as [[E Hp] Hs]. subst result.
  apply astar_assoc_intro. apply astar_l_apure_intro; [exact Hs | auto].
Qed.

Theorem V293_OSSched_target_assign : forall Spec sd li I r ri tid aop frame
    unmap group rows high bt bg br bh lo hi table target tp bp bo entries tasks old t,
  lo < 256 -> hi < 256 -> (exists p, V293_bitmap_ready lo hi p) ->
  V293_bitmap_tasks lo hi tasks -> V293_priority_table entries tasks ->
  nth (V293_ready_select lo hi (V293_ready_group lo hi)) entries Vnull = Vptr t ->
  InfRules Spec sd li I r ri
    (V293_sched_internal_post unmap group rows high bt bg br bh lo hi li tid aop None **
      (V293_prefix_frame table high target tp bp bo entries tasks frame ** V293_prefix_output tp bo old))
    (V293_OSSched_target_update table high target)
    (V293_sched_internal_post unmap group rows high bt bg br bh lo hi li tid aop None **
      (V293_prefix_frame table high target tp bp bo entries tasks frame ** V293_prefix_output tp bo (Vptr t))) tid.
Proof.
  intros Spec sd li I r ri tid aop frame unmap group rows high bt bg br bh lo hi table target tp bp bo
    entries tasks old t Hlo Hhi Hr Hb Htable Hentry.
  pose proof (proj2 (V293_ready_selection lo hi (V293_ready_group lo hi) Hlo Hhi eq_refl Hr)) as Hselected.
  unfold V293_OSSched_target_update, V293_prefix_output.
  eapply conseq_rule with
    (p := <||aop||> ** ((V293_sched_internal_resource unmap group rows high bt bg br bh lo hi li tid
      (V293_byteval (V293_ready_select lo hi (V293_ready_group lo hi))) **
      V293_prefix_frame table high target tp bp bo entries tasks frame) ** PV (bo, Int.zero) @ (Tptr tp) |-> old))
    (q := <||aop||> ** ((V293_sched_internal_resource unmap group rows high bt bg br bh lo hi li tid
      (V293_byteval (V293_ready_select lo hi (V293_ready_group lo hi))) **
      V293_prefix_frame table high target tp bp bo entries tasks frame) ** PV (bo, Int.zero) @ (Tptr tp) |-> (Vptr t))).
  - unfold V293_sched_internal_post. intros s Hs. sep auto.
  - unfold V293_sched_internal_post. intros s Hs. sep auto.
  - eapply assign_rule with (tp2 := Tptr tp).
    + apply eq_vptr. exists tp. exists tp. auto.
    + intros s Hs.
      assert (Ev : evalval (V293_OSSched_target_expr table high) (getgenv s, getlenv s, getmem s) = Some (Vptr t) /\
        evaltype (V293_OSSched_target_expr table high) (getgenv s, getlenv s, getmem s) = Some (Tptr tp)).
      { assert (Ha : s |= V293_sched_internal_resource unmap group rows high bt bg br bh lo hi li tid
          (V293_byteval (V293_ready_select lo hi (V293_ready_group lo hi))) **
          V293_prefix_frame table high target tp bp bo entries tasks
            (frame ** PV (bo, Int.zero) @ (Tptr tp) |-> old)).
        { unfold V293_prefix_frame in *. sep auto. }
        exact (V293_prefix_target_eval unmap group rows high bt bg br bh lo hi li tid table target tp bp bo
          entries tasks (frame ** PV (bo, Int.zero) @ (Tptr tp) |-> old) t s Hlo Hhi Hr Hb Htable Hentry Ha). }
      assert (E : get (getgenv s) table = Some (bp, Tarray (Tptr tp) 13) /\
        get (getgenv s) target = Some (bo, Tptr tp) /\ get (getlenv s) table = None /\
        get (getlenv s) high = None /\ get (getlenv s) target = None).
      { eapply V293_star_env_l; [ | exact Hs]. intros s0 H0.
        eapply V293_star_env_r; [ | exact H0]. intros s1 H1.
        eapply V293_star_env_l; [ | exact H1]. intros s2 H2.
        eapply V293_star_env_l; [ | exact H2]. apply V293_prefix_bindings_view. }
      destruct E as [Gt [Go [Nt [Nh No]]]]. destruct Ev as [Ev Et].
      destruct s as [[[[[[ge le] M] irs] aux] O] op].
      cbn [getgenv getlenv getmem get_smem get_genv get_lenv get_mem] in Go, No, Ev, Et.
      split.
      * cbn [sat evaladdr evaltype getsmem get_smem get_lenv get_genv]. rewrite No, Go. auto.
      * cbn [sat getsmem get_smem]. split; [exact Ev | ]. split; [exact Et | discriminate].
    + intros s Hs. eapply V293_star_CurLINV_l; [ | exact Hs].
      apply V293_prefix_common_CurLINV.
Qed.

Theorem V293_OSSched_unlocked_prefix_hoare : forall Spec sd li I r ri tid aop frame
    sched_id unmap group rows high bt bg br bh lo hi table target tp bp bo entries tasks old
    (Hli : GoodLInvAsrt li),
  lo < 256 -> hi < 256 -> (exists p, V293_bitmap_ready lo hi p) ->
  V293_bitmap_tasks lo hi tasks -> V293_priority_table entries tasks -> GoodFrm frame ->
  Spec sched_id = Some
    (V293_sched_fpre unmap group rows high bt bg br bh li Hli,
     V293_sched_fpost unmap group rows high bt bg br bh li Hli, (Tvoid, nil)) ->
  InfRules Spec sd li I r ri
    (V293_sched_internal_pre unmap group rows high bt bg br bh lo hi li tid aop **
      (V293_prefix_frame table high target tp bp bo entries tasks frame ** V293_prefix_output tp bo old))
    (V293_OSSched_unlocked_prefix sched_id table high target)
    (EX t : Modules.tid, [|V293_highest_ready tasks t|] **
      (V293_sched_internal_post unmap group rows high bt bg br bh lo hi li tid aop None **
        (V293_prefix_frame table high target tp bp bo entries tasks frame ** V293_prefix_output tp bo (Vptr t)))) tid.
Proof.
  intros Spec sd li I r ri tid aop frame sched_id unmap group rows high bt bg br bh lo hi
    table target tp bp bo entries tasks old Hli Hlo Hhi Hr Hb Htable Hframe Hspec.
  destruct (V293_ready_selection_task lo hi entries tasks Hlo Hhi Hr Hb Htable)
    as [t [m [Ht [Hentry Hhighest]]]].
  unfold V293_OSSched_unlocked_prefix. eapply seq_rule with
    (p' := V293_sched_internal_post unmap group rows high bt bg br bh lo hi li tid aop None **
      (V293_prefix_frame table high target tp bp bo entries tasks frame ** V293_prefix_output tp bo old)).
  - eapply conseq_rule.
    + intros s Hs; exact Hs.
    + apply V293_prefix_call_post.
    + apply V293_OSSchedNew_call_rule with (Hli := Hli); try assumption.
      split; [apply V293_prefix_frame_good; exact Hframe | constructor].
  - eapply conseq_rule with
      (q := V293_sched_internal_post unmap group rows high bt bg br bh lo hi li tid aop None **
        (V293_prefix_frame table high target tp bp bo entries tasks frame ** V293_prefix_output tp bo (Vptr t))).
    + intros s Hs; exact Hs.
    + intros s Hs. exists t. apply astar_l_apure_intro; assumption.
    + apply V293_OSSched_target_assign; assumption.
Qed.
