(* Exact resources through the original call and target pointer assignment.
   Existing weak resources are used only to check expression reads. *)
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedExactLocal.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedPrefix.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedStoragePrefix.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedStorageTail.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedShared.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedSwitch.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCritical.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTarget.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchStorage.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedDispatchShared.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.certiucos.v293.code.V293OSSchedDispatch.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import Coq.Lists.List Lia.
Local Open Scope nat_scope.

Lemma V293_exact_prefix_read_resource : forall unmap group rows high bt bg br bh lo hi li tid hv,
 V293_sched_exact_resource unmap group rows high bt bg br bh lo hi li tid hv ==>
 V293_sched_internal_resource unmap group rows high bt bg br bh lo hi li tid hv.
Proof.
 intros unmap group rows high bt bg br bh lo hi li tid hv s H.
 unfold V293_sched_exact_resource,V293_sched_internal_resource in *.
 eapply astar_mono;[ |intros s0 H0;exact H0|exact H].
 apply astar_mono;[intros s0 H0;exact H0| ].
 apply astar_mono;[apply V293_exact_local_weakens|intros s0 H0;exact H0].
Qed.

Lemma V293_exact_prefix_call_post : forall unmap group rows high bt bg br bh lo hi li tid aop rest,
  (EX result : option val,
    V293_sched_exact_post unmap group rows high bt bg br bh lo hi li tid aop result ** rest) ==>
  V293_sched_exact_post unmap group rows high bt bg br bh lo hi li tid aop None ** rest.
Proof.
  intros unmap group rows high bt bg br bh lo hi li tid aop rest s [result Hs].
  unfold V293_sched_exact_post in *. apply astar_assoc_elim in Hs.
  apply astar_l_apure_elim in Hs. destruct Hs as [[E Hp] Hs]. subst result.
  apply astar_assoc_intro. apply astar_l_apure_intro; [exact Hs | auto].
Qed.

Theorem V293_OSSched_exact_target_assign : forall Spec sd li I r ri tid aop frame
    unmap group rows high bt bg br bh lo hi table target tp bp bo entries tasks old t,
  lo < 256 -> hi < 256 -> (exists p, V293_bitmap_ready lo hi p) ->
  V293_bitmap_tasks lo hi tasks -> V293_priority_table entries tasks ->
  nth (V293_ready_select lo hi (V293_ready_group lo hi)) entries Vnull = Vptr t ->
  InfRules Spec sd li I r ri
    (V293_sched_exact_post unmap group rows high bt bg br bh lo hi li tid aop None **
      (V293_prefix_frame table high target tp bp bo entries tasks frame ** V293_prefix_output tp bo old))
    (V293_OSSched_target_update table high target)
    (V293_sched_exact_post unmap group rows high bt bg br bh lo hi li tid aop None **
      (V293_prefix_frame table high target tp bp bo entries tasks frame ** V293_prefix_output tp bo (Vptr t))) tid.
Proof.
  intros Spec sd li I r ri tid aop frame unmap group rows high bt bg br bh lo hi table target tp bp bo
    entries tasks old t Hlo Hhi Hr Hb Htable Hentry.
  pose proof (proj2 (V293_ready_selection lo hi (V293_ready_group lo hi) Hlo Hhi eq_refl Hr)) as Hselected.
  unfold V293_OSSched_target_update, V293_prefix_output.
  eapply conseq_rule with
    (p := <||aop||> ** ((V293_sched_exact_resource unmap group rows high bt bg br bh lo hi li tid
      (V293_byteval (V293_ready_select lo hi (V293_ready_group lo hi))) **
      V293_prefix_frame table high target tp bp bo entries tasks frame) ** PV (bo, Int.zero) @ (Tptr tp) |-> old))
    (q := <||aop||> ** ((V293_sched_exact_resource unmap group rows high bt bg br bh lo hi li tid
      (V293_byteval (V293_ready_select lo hi (V293_ready_group lo hi))) **
      V293_prefix_frame table high target tp bp bo entries tasks frame) ** PV (bo, Int.zero) @ (Tptr tp) |-> (Vptr t))).
  - unfold V293_sched_exact_post. intros s Hs. sep auto.
  - unfold V293_sched_exact_post. intros s Hs. sep auto.
  - eapply assign_rule with (tp2 := Tptr tp).
    + apply eq_vptr. exists tp. exists tp. auto.
    + intros s Hs.
      assert (Ev : evalval (V293_OSSched_target_expr table high) (getgenv s, getlenv s, getmem s) = Some (Vptr t) /\
        evaltype (V293_OSSched_target_expr table high) (getgenv s, getlenv s, getmem s) = Some (Tptr tp)).
      { assert (Ha : s |= V293_sched_exact_resource unmap group rows high bt bg br bh lo hi li tid
          (V293_byteval (V293_ready_select lo hi (V293_ready_group lo hi))) **
          V293_prefix_frame table high target tp bp bo entries tasks
            (frame ** PV (bo, Int.zero) @ (Tptr tp) |-> old)).
        { unfold V293_prefix_frame in *. sep auto. }
        eapply (V293_prefix_target_eval unmap group rows high bt bg br bh lo hi li tid
          table target tp bp bo entries tasks (frame ** PV (bo,Int.zero) @ (Tptr tp) |-> old)
          t s Hlo Hhi Hr Hb Htable Hentry).
        eapply astar_mono;[apply V293_exact_prefix_read_resource|intros s0 H0;exact H0|exact Ha]. }
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
      eapply V293_star_CurLINV_l. apply V293_sched_exact_resource_local.
Qed.

Theorem V293_OSSched_exact_critical_prefix : forall Spec sd li I RI r ri tid aop frame
    sched_id unmap group rows high bt bg br bh lo hi table target tp bp bo entries tasks old
    stack critical (Hli : GoodLInvAsrt li),
  lo < 256 -> hi < 256 -> (exists p, V293_bitmap_ready lo hi p) ->
  V293_bitmap_tasks lo hi tasks -> V293_priority_table entries tasks -> GoodFrm frame ->
  Spec sched_id = Some
    (V293_sched_exact_fpre unmap group rows high bt bg br bh li I Hli,
     V293_sched_exact_fpost unmap group rows high bt bg br bh li I Hli, (Tvoid, nil)) ->
  InfRules Spec sd li RI r ri
    ((V293_sched_exact_pre unmap group rows high bt bg br bh lo hi li tid aop **
      V293_sched_critical I stack critical) **
      (V293_prefix_frame table high target tp bp bo entries tasks frame ** V293_prefix_output tp bo old))
    (V293_OSSched_unlocked_prefix sched_id table high target)
    (EX t : Modules.tid, [|V293_highest_ready tasks t|] **
      (V293_sched_exact_post unmap group rows high bt bg br bh lo hi li tid aop None **
        (V293_prefix_frame table high target tp bp bo entries tasks
          (V293_sched_critical I stack critical ** frame) ** V293_prefix_output tp bo (Vptr t)))) tid.
Proof.
  intros Spec sd li I RI r ri tid aop frame sched_id unmap group rows high bt bg br bh lo hi
    table target tp bp bo entries tasks old stack critical Hli Hlo Hhi Hr Hb Htable Hframe Hspec.
  destruct (V293_ready_selection_task lo hi entries tasks Hlo Hhi Hr Hb Htable)
    as [t [m [Ht [Hentry Hhighest]]]].
  unfold V293_OSSched_unlocked_prefix. eapply seq_rule with
    (p' := V293_sched_exact_post unmap group rows high bt bg br bh lo hi li tid aop None **
      (V293_prefix_frame table high target tp bp bo entries tasks
        (V293_sched_critical I stack critical ** frame) ** V293_prefix_output tp bo old)).
  - eapply conseq_rule with (q := EX result : option val,
      (V293_sched_exact_post unmap group rows high bt bg br bh lo hi li tid aop result **
        V293_sched_critical I stack critical) **
        (V293_prefix_frame table high target tp bp bo entries tasks frame ** V293_prefix_output tp bo old)).
    + intros s Hs; exact Hs.
    + intros s [result Hs].
      assert (Hs' : s |= V293_sched_exact_post unmap group rows high bt bg br bh lo hi li tid aop result **
        (V293_prefix_frame table high target tp bp bo entries tasks
          (V293_sched_critical I stack critical ** frame) ** V293_prefix_output tp bo old)).
      { unfold V293_prefix_frame in *. sep auto. }
      apply V293_exact_prefix_call_post. exists result. exact Hs'.
    + apply V293_OSSchedNew_exact_call with (Hli := Hli); try assumption.
      split; [apply V293_prefix_frame_good; exact Hframe | constructor].
  - eapply conseq_rule with (q :=
      V293_sched_exact_post unmap group rows high bt bg br bh lo hi li tid aop None **
        (V293_prefix_frame table high target tp bp bo entries tasks
          (V293_sched_critical I stack critical ** frame) ** V293_prefix_output tp bo (Vptr t))).
    + intros s Hs; exact Hs.
    + intros s Hs. exists t. apply astar_l_apure_intro; [exact Hs | exact Hhighest].
    + apply V293_OSSched_exact_target_assign; assumption.
Qed.

Section ExactStoragePrefix.
Variables unmap group rows high table target : var.
Variables bt bg br bh bp bo : block.
Variable tp : type.
Variables lo hi : nat.
Variable entries : list val.
Variable kept : asrt.
Variable tid : Modules.tid.
Variable tasks : TcbMod.map.
Variable events : EcbMod.map.
Variable now : int32.
Variable aop : spec_code.
Variable stack : list hid.
Variable critical : list bool.
Variable px : asrt.
(* This is an OPENED borrowing boundary. The old target and the callee's
   initial output value are not claimed reachable from initialization. *)
Definition V293_exact_storage_prefix_borrowed old :=
  (V293_sched_exact_pre unmap group rows high bt bg br bh lo hi V293_shared_li tid aop **
    V293_sched_critical V293_opened_inv stack critical) **
  (V293_prefix_frame table high target tp bp bo entries tasks
    (V293_shared_remainder tid events now ** V293_retained_prefix_reserve bt bg br bp tp lo hi entries kept px) ** V293_prefix_output tp bo old).
Definition V293_exact_storage_prefix_returned :=
  EX next : Modules.tid, [|V293_highest_ready tasks next|] **
  ((<||aop||> ** ((V293_retained_prefix_returned target bt bg br bh bp tp lo hi entries kept tid tasks events now next ** p_local V293_shared_li tid nil) ** (Ais stack ** Acs critical))) **
    ((V293_sched_globals unmap group rows high bt bg br bh **
      V293_prefix_bindings table high target tp bp bo) ** px)).

Theorem V293_OSSched_exact_storage_prefix_returned : forall Spec (RI : Inv) r ri sched_id old,
  GoodFrm kept ->
  lo < 256 -> hi < 256 -> (exists p, V293_bitmap_ready lo hi p) ->
  V293_bitmap_tasks lo hi tasks -> V293_priority_table entries tasks ->
  GoodFrm px ->
  Spec sched_id = Some
    (V293_sched_exact_fpre unmap group rows high bt bg br bh V293_shared_li V293_opened_inv V293_switch_li_good,
     V293_sched_exact_fpost unmap group rows high bt bg br bh V293_shared_li V293_opened_inv V293_switch_li_good,
     (Tvoid, nil)) ->
  InfRules Spec V293_scheduler V293_shared_li RI r ri
    (V293_exact_storage_prefix_borrowed old)
    (V293_OSSched_unlocked_prefix sched_id table high target)
    V293_exact_storage_prefix_returned tid.
Proof.
  intros Spec RI r ri sched_id old Hkept Hlo Hhi Hr Hb Htable Hpx Hspec.
  eapply conseq_rule.
  3: { eapply V293_OSSched_exact_critical_prefix with
      (I := V293_opened_inv) (Hli := V293_switch_li_good)
      (frame := V293_shared_remainder tid events now ** V293_retained_prefix_reserve bt bg br bp tp lo hi entries kept px)
      (unmap := unmap) (group := group) (rows := rows) (bt := bt) (bg := bg) (br := br) (bh := bh)
      (lo := lo) (hi := hi) (tp := tp) (bp := bp) (bo := bo) (entries := entries) (tasks := tasks)
      (aop := aop) (old := old) (stack := stack) (critical := critical); try eassumption.
    split; [apply V293_shared_remainder_good | ].
    unfold V293_retained_prefix_reserve, V293_sched_inputs.
    repeat rewrite V293_read_bytes_array. rewrite V293_read_pointers_array.
    repeat split; try apply V293_array_good; try exact Hkept; try exact I; exact Hpx. }
  - intros s Hs. exact Hs.
  - intros s [next Hs]. unfold V293_exact_storage_prefix_returned. exists next.
    unfold V293_sched_exact_post, V293_sched_exact_resource,
      V293_prefix_frame, V293_shared_remainder, V293_retained_prefix_reserve, V293_sched_critical in Hs.
    sep normal in Hs. sep split in Hs.
    assert (HP : s |= SWINV V293_opened_inv **
      ([|V293_highest_ready tasks next|] **
        ((V293_prefix_bindings table high target tp bp bo ** V293_prefix_output tp bo (Vptr next)) **
          ((CurTid tid ** V293_shared_fields tid tasks events now) **
            ((V293_sched_inputs bt bg br lo hi (V293_ready_group lo hi) **
              V293_sched_inputs bt bg br lo hi (V293_ready_group lo hi)) **
              ((V293_read_pointers tp bp 0 entries ** V293_read_pointers tp bp 0 entries) **
                ((PV (bh, Int.zero) @ Tint8 |->
                  (V293_byteval (V293_ready_select lo hi (V293_ready_group lo hi)))) **
                  (kept **
                    ((<||aop||> ** p_local V293_shared_li tid nil) ** ((Ais stack ** Acs critical) **
                      (V293_sched_globals unmap group rows high bt bg br bh ** px)))))))))))
      by (unfold V293_shared_fields; sep auto).
    eapply astar_mono in HP; [ | apply V293_opened_switch_open | intros st Hz; exact Hz].
    assert (HK : s |=
      ((V293_prefix_bindings table high target tp bp bo ** V293_prefix_output tp bo (Vptr next)) **
        ((V293_sched_inputs bt bg br lo hi (V293_ready_group lo hi) **
          V293_sched_inputs bt bg br lo hi (V293_ready_group lo hi)) **
          (V293_read_pointers tp bp 0 entries ** V293_read_pointers tp bp 0 entries))) **
      (V293_shared_flags ** ([|V293_highest_ready tasks next|] **
        ((CurTid tid ** V293_shared_fields tid tasks events now) **
          ((PV (bh, Int.zero) @ Tint8 |->
            (V293_byteval (V293_ready_select lo hi (V293_ready_group lo hi)))) **
            (kept **
              ((<||aop||> ** p_local V293_shared_li tid nil) ** ((Ais stack ** Acs critical) **
                (V293_sched_globals unmap group rows high bt bg br bh ** px)))))))))
      by (clear Hs; sep auto).
    eapply astar_mono in HK.
    2: { apply astar_mono; [apply V293_dispatch_output_named | apply astar_mono].
         - apply V293_inputs_reunite.
         - rewrite V293_read_pointers_array. apply V293_array_reunite. }
    2: { intros st Hz; exact Hz. }
    assert (HL : s |= V293_retained_prefix_returned target bt bg br bh bp tp lo hi entries kept tid tasks events now next **
      ([|V293_highest_ready tasks next|] **
        ((<||aop||> ** p_local V293_shared_li tid nil) ** ((Ais stack ** Acs critical) **
          ((V293_sched_globals unmap group rows high bt bg br bh **
            V293_prefix_bindings table high target tp bp bo) ** px)))))
      by (unfold V293_retained_prefix_returned, V293_storage_open, V293_retained_prefix_physical; clear Hs HP; sep auto).
    clear Hs HP HK. sep auto.
Qed.
Lemma V293_exact_storage_prefix_lend_value : forall old hv,
  lo < 256 -> hi < 256 -> (exists p, V293_bitmap_ready lo hi p) ->
  (<||aop||> **
    ((((V293_shared_flags ** ((CurTid tid ** V293_shared_fields tid tasks events now) **
      (GV target @ (Tptr tp) |-> old))) ** V293_retained_prefix_entry_heap bt bg br bh bp tp lo hi entries kept hv) ** CurTid tid) **
      ((Ais stack ** Acs critical) **
        ((V293_sched_globals unmap group rows high bt bg br bh **
          V293_prefix_bindings table high target tp bp bo) ** px)))) ==>
    V293_exact_storage_prefix_borrowed old.
Proof.
  intros old hv Hlo Hhi Hr s Hs.
  unfold V293_retained_prefix_entry_heap in Hs.
  assert (HP : s |=
    ((V293_inputs_full bt bg br lo hi ** V293_array true bp 0 4 (Tptr tp) entries) **
      (V293_prefix_bindings table high target tp bp bo ** (GV target @ (Tptr tp) |-> old))) **
    ((V293_shared_flags ** (CurTid tid ** (CurTid tid ** V293_shared_fields tid tasks events now))) **
      ((PV (bh, Int.zero) @ Tint8 |-> hv) **
        (<||aop||> ** ((Ais stack ** Acs critical) **
          (V293_sched_globals unmap group rows high bt bg br bh ** (kept ** px))))))) by (sep auto).
  eapply astar_mono in HP.
  2: { apply astar_mono; [apply astar_mono;
      [apply V293_inputs_borrow | intros st H;
        pose proof (V293_array_borrow bp 0 4 (Tptr tp) entries st H) as HB;
        rewrite <- V293_read_pointers_array in HB; exact HB] |
      apply V293_dispatch_named_output]. }
  2: { intros st H; exact H. }
  assert (HC : CurTid tid ==> p_local V293_shared_li tid nil).
  { intros st H. unfold p_local.
    eapply astar_mono;[intros st0 H0;exact H0|apply V293_switch_local_empty|
      apply astar_r_aemp_intro;exact H]. }
  assert (HK : s |=
    V293_shared_flags **
      (CurTid tid **
        ((V293_sched_globals unmap group rows high bt bg br bh **
          V293_sched_inputs bt bg br lo hi (V293_ready_group lo hi)) **
          ((PV (bh, Int.zero) @ Tint8 |-> hv) **
            (V293_shared_fields tid tasks events now **
              ((V293_sched_inputs bt bg br lo hi (V293_ready_group lo hi) **
                V293_read_pointers tp bp 0 entries) **
                ((V293_prefix_bindings table high target tp bp bo **
                  V293_read_pointers tp bp 0 entries) **
                  ((V293_prefix_output tp bo old ** CurTid tid) **
                    (<||aop||> ** ((Ais stack ** Acs critical) ** (kept ** px)))))))))))
    by (clear Hs; sep auto).
  eapply astar_mono in HK; [ | intros st H; exact H | apply astar_mono;
    [exact HC | intros st H; exact H]].
  (* Aie false is a state observation, not an owned memory cell. *)
  assert (HF : V293_shared_flags ==> Aie false ** SWINV V293_opened_inv).
  { intros st H. apply astar_l_aie_intro; [apply V293_opened_switch_close; exact H | ].
    unfold V293_shared_flags in H. sep auto. }
  eapply astar_mono in HK; [ | exact HF | intros st H; exact H].
  assert (HE : (<||aop||> **
    V293_sched_exact_resource unmap group rows high bt bg br bh lo hi V293_shared_li tid hv) ==>
    V293_sched_exact_pre unmap group rows high bt bg br bh lo hi V293_shared_li tid aop).
  { intros st H. exists hv. sep auto. }
  assert (HL : s |= (<||aop||> **
    V293_sched_exact_resource unmap group rows high bt bg br bh lo hi V293_shared_li tid hv) **
    (V293_sched_critical V293_opened_inv stack critical **
      (V293_prefix_frame table high target tp bp bo entries tasks
        (V293_shared_remainder tid events now ** V293_retained_prefix_reserve bt bg br bp tp lo hi entries kept px) ** V293_prefix_output tp bo old))).
  { unfold V293_sched_exact_resource, V293_sched_critical, V293_prefix_frame,
      V293_retained_prefix_reserve, V293_shared_remainder, V293_shared_fields in *.
    clear HP Hs. sep auto. }
  eapply astar_mono in HL; [ | exact HE | intros st H; exact H].
  unfold V293_exact_storage_prefix_borrowed. clear Hs HP HK. sep auto.
Qed.


Lemma V293_exact_storage_prefix_lend : forall rest old hv,
 lo<256 ->hi<256 ->(exists p,V293_bitmap_ready lo hi p) ->
 V293_retained_storage_prefix_entry unmap group rows high table target
 bt bg br bh bp bo tp lo hi entries rest kept tid tasks events now aop stack critical px old hv ==>
 V293_exact_storage_prefix_borrowed(Vptr old).
Proof.
 intros rest old hv Hlo Hhi Hr s Hs.
 apply V293_exact_storage_prefix_lend_value with(hv:=hv);try assumption.
 unfold V293_retained_storage_prefix_entry in Hs.
 eapply astar_mono in Hs;[ |intros st H;exact H|apply astar_mono].
 2:{apply astar_mono;[intros st [_ H];exact H|intros st H;exact H]. }
 2:{intros st H;exact H. }
 unfold V293_storage_open in Hs;exact Hs.
Qed.

Theorem V293_OSSched_exact_storage_closed_prefix : forall Spec(RI:Inv) r ri sched_id rest old hv,
 GoodFrm kept ->lo<256 ->hi<256 ->(exists p,V293_bitmap_ready lo hi p) ->
 V293_bitmap_tasks lo hi tasks ->V293_priority_table entries tasks ->GoodFrm px ->
 Spec sched_id=Some
 (V293_sched_exact_fpre unmap group rows high bt bg br bh V293_shared_li V293_opened_inv V293_switch_li_good,
  V293_sched_exact_fpost unmap group rows high bt bg br bh V293_shared_li V293_opened_inv V293_switch_li_good,
  (Tvoid,nil)) ->
 InfRules Spec V293_scheduler V293_shared_li RI r ri
 (V293_retained_storage_prefix_entry unmap group rows high table target
 bt bg br bh bp bo tp lo hi entries rest kept tid tasks events now aop stack critical px old hv)
 (V293_OSSched_unlocked_prefix sched_id table high target)
 V293_exact_storage_prefix_returned tid.
Proof.
 intros Spec RI r ri sched_id rest old hv Hkept Hlo Hhi Hr Hb Ht Hpx Hspec.
 eapply conseq_rule.
 - apply V293_exact_storage_prefix_lend;assumption.
 - intros s H;exact H.
 - apply V293_OSSched_exact_storage_prefix_returned;assumption.
Qed.
End ExactStoragePrefix.
