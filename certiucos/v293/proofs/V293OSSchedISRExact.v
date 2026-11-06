(* Exact local resources through the real ISR scheduler body, call and prefix. *)
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCritical.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitDispatch.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitBoundarySwitch.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCall.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedPrefix.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedChange.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedGuards.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntEnterInternal.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.certiucos.v293.code.V293OSSchedNew.
Require Import CertiOS.certiucos.v293.code.V293OSIntExit.
Require Import CertiOS.certiucos.v293.code.V293OSSchedDispatch.
Require Import CertiOS.certiucos.v293.code.V293OSSchedChange.
Require Import CertiOS.certiucos.v293.code.V293OSSchedGuards.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Require Import CertiOS.certiucos.v293.proofs.V293OSSchedISRContext.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedExactLocal.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedExactPrefix.
Definition V293_ISR_exact_sched_pre unmap group rows high bt bg br bh li I tid lg :=
  match V293_ISR_sched_args lg with
  | Some (lo, hi, aop, held, ir, si, ci) =>
      V293_sched_exact_pre unmap group rows high bt bg br bh lo hi li tid aop **
        V293_sched_ISR_context I held ir si ci
  | None => Afalse
  end.
Definition V293_ISR_exact_sched_post unmap group rows high bt bg br bh li I tid lg result :=
  match V293_ISR_sched_args lg with
  | Some (lo, hi, aop, held, ir, si, ci) =>
      V293_sched_exact_post unmap group rows high bt bg br bh lo hi li tid aop result **
        V293_sched_ISR_context I held ir si ci
  | None => Afalse
  end.
Definition V293_ISR_exact_sched_fpre (unmap group rows high : var) (bt bg br bh : block) (li : LocalInv) (I : Inv)
    (Hli : GoodLInvAsrt li) : fpre.
Proof.
  intros vl lg tid. refine (@mkfunasrt
    (V293_ISR_exact_sched_pre unmap group rows high bt bg br bh li I tid lg) _).
  unfold V293_ISR_exact_sched_pre. destruct (V293_ISR_sched_args lg) as [[[[[[[lo hi] op] held] ir] si] ci] | ]; [ | exact Logic.I].
  split; [apply V293_sched_exact_pre_good; exact Hli | apply V293_sched_ISR_context_good].
Defined.
Definition V293_ISR_exact_sched_fpost (unmap group rows high : var) (bt bg br bh : block) (li : LocalInv) (I : Inv)
    (Hli : GoodLInvAsrt li) : fpost.
Proof.
  intros vl result lg tid. refine (@mkfunasrt
    (V293_ISR_exact_sched_post unmap group rows high bt bg br bh li I tid lg result) _).
  unfold V293_ISR_exact_sched_post. destruct (V293_ISR_sched_args lg) as [[[[[[[lo hi] op] held] ir] si] ci] | ]; [ | exact Logic.I].
  split; [apply V293_sched_exact_post_good; exact Hli | apply V293_sched_ISR_context_good].
Defined.

(* Resource ownership I and ambient rule invariant RI need not coincide. *)
Theorem V293_OSSchedNew_ISR_exact_contract : forall P f Spec sd li I RI
    unmap group rows high y bt bg br bh (Hli : GoodLInvAsrt li) lg tid vl pre post,
  unmap <> y -> group <> y -> rows <> y -> high <> y ->
  P f = Some (V293_OSSchedNew_function unmap group rows high y) ->
  Some pre = BuildPreI P f vl lg (V293_ISR_exact_sched_fpre unmap group rows high bt bg br bh li I Hli) tid ->
  Some post = BuildRetI P f vl lg (V293_ISR_exact_sched_fpost unmap group rows high bt bg br bh li I Hli) tid ->
  InfRules Spec sd li RI post Afalse pre (V293_OSSchedNew_body unmap group rows high y) Afalse tid.
Proof.
  intros P f Spec sd li I RI unmap group rows high y bt bg br bh Hli lg tid vl pre post
    Hu Hg Hr Hh Hcode Hpre Hpost.
  unfold BuildPreI in Hpre. rewrite Hcode in Hpre.
  destruct vl as [ | v vl].
  2: { assert (E : dl_vl_match dnil (rev (v :: vl)) = false).
       { destruct (rev (v :: vl)) eqn:Er; [ | reflexivity].
         apply (f_equal (@rev val)) in Er. rewrite rev_involutive in Er. discriminate. }
       unfold V293_OSSchedNew_function in Hpre. rewrite E in Hpre. discriminate. }
  change (Some pre = Some (((EX v : val, LV y @ Tint8 |-> v) ** Aemp) **
    V293_ISR_exact_sched_pre unmap group rows high bt bg br bh li I tid lg ** V293_sched_local_domain y)) in Hpre.
  inversion Hpre; subst pre.
  unfold BuildRetI in Hpost. rewrite Hcode in Hpost.
  change (Some post = Some (fun result => ((EX v : val, LV y @ Tint8 |-> v) ** Aemp) **
    V293_ISR_exact_sched_post unmap group rows high bt bg br bh li I tid lg result ** V293_sched_local_domain y)) in Hpost.
  inversion Hpost; subst post.
  unfold V293_ISR_exact_sched_pre, V293_ISR_exact_sched_post.
  destruct (V293_ISR_sched_args lg) as [[[[[[[lo hi] op] held] ir] si] ci] | ];
    [apply V293_sched_exact_payload; assumption | apply V293_sched_false_entry].
Qed.

Definition V293_ISR_exact_sched_spec sched_id unmap group rows high bt bg br bh li I
    (Hli : GoodLInvAsrt li) : funspec :=
  fun f => if Z.eq_dec f sched_id then Some
    (V293_ISR_exact_sched_fpre unmap group rows high bt bg br bh li I Hli,
     V293_ISR_exact_sched_fpost unmap group rows high bt bg br bh li I Hli, (Tvoid, nil)) else None.
(* Resource ownership I and ambient rule invariant RI need not coincide. *)
Theorem V293_OSSchedNew_ISR_exact_WFFunEnv : forall sched_id unmap group rows high y bt bg br bh li I RI Hli sd,
  unmap <> y -> group <> y -> rows <> y -> high <> y ->
  WFFunEnv (V293_OSSchedNew_internal_unit sched_id unmap group rows high y)
    (V293_ISR_exact_sched_spec sched_id unmap group rows high bt bg br bh li I Hli) sd li RI.
Proof.
  intros sched_id unmap group rows high y bt bg br bh li I RI Hli sd Hu Hg Hr Hh. split.
  - intros f. unfold V293_OSSchedNew_internal_unit, V293_ISR_exact_sched_spec.
    destruct (Z.eq_dec f sched_id); split; intros [a H]; try discriminate; eexists; reflexivity.
  - intros f pre post t tl Hspec. unfold V293_ISR_exact_sched_spec in Hspec.
    destruct (Z.eq_dec f sched_id); try discriminate. inversion Hspec; subst pre post t tl.
    exists dnil. exists (dcons y Tint8 dnil). exists (V293_OSSchedNew_body unmap group rows high y).
    split.
    + unfold V293_OSSchedNew_internal_unit. destruct (Z.eq_dec f sched_id); [reflexivity | contradiction].
    + split; [constructor | ]. split; [reflexivity | ].
      intros vl pre post lg tid Hpre Hpost.
      eapply V293_OSSchedNew_ISR_exact_contract; try eassumption.
      unfold V293_OSSchedNew_internal_unit. destruct (Z.eq_dec f sched_id); [reflexivity | contradiction].
Qed.

Theorem V293_OSSchedNew_ISR_exact_call : forall Spec sd li I RI r ri tid aop frame
    sched_id unmap group rows high bt bg br bh lo hi held ir si ci (Hli : GoodLInvAsrt li),
  lo < 256 -> hi < 256 -> GoodFrm frame ->
  Spec sched_id = Some
    (V293_ISR_exact_sched_fpre unmap group rows high bt bg br bh li I Hli,
     V293_ISR_exact_sched_fpost unmap group rows high bt bg br bh li I Hli, (Tvoid, nil)) ->
  InfRules Spec sd li RI r ri
    ((V293_sched_exact_pre unmap group rows high bt bg br bh lo hi li tid aop **
       V293_sched_ISR_context I held ir si ci) ** frame)
    (scall sched_id nil)
    (EX result : option val,
      (V293_sched_exact_post unmap group rows high bt bg br bh lo hi li tid aop result **
        V293_sched_ISR_context I held ir si ci) ** frame) tid.
Proof.
  intros Spec sd li I RI r ri tid aop frame sched_id unmap group rows high bt bg br bh lo hi held ir si ci Hli
    Hlo Hhi Hframe Hspec.
  assert (Ep : getasrt (V293_ISR_exact_sched_fpre unmap group rows high bt bg br bh li I Hli nil
    (V293_ISR_sched_call_lg lo hi aop held ir si ci) tid) =
    V293_sched_exact_pre unmap group rows high bt bg br bh lo hi li tid aop ** V293_sched_ISR_context I held ir si ci).
  { change (V293_ISR_exact_sched_pre unmap group rows high bt bg br bh li I tid
      (V293_ISR_sched_call_lg lo hi aop held ir si ci) =
      V293_sched_exact_pre unmap group rows high bt bg br bh lo hi li tid aop ** V293_sched_ISR_context I held ir si ci).
    unfold V293_ISR_exact_sched_pre. rewrite V293_ISR_sched_args_roundtrip by assumption. reflexivity. }
  assert (Eq : forall result, getasrt (V293_ISR_exact_sched_fpost unmap group rows high bt bg br bh li I Hli nil result
    (V293_ISR_sched_call_lg lo hi aop held ir si ci) tid) =
    V293_sched_exact_post unmap group rows high bt bg br bh lo hi li tid aop result ** V293_sched_ISR_context I held ir si ci).
  { intro. change (V293_ISR_exact_sched_post unmap group rows high bt bg br bh li I tid
      (V293_ISR_sched_call_lg lo hi aop held ir si ci) result =
      V293_sched_exact_post unmap group rows high bt bg br bh lo hi li tid aop result ** V293_sched_ISR_context I held ir si ci).
    unfold V293_ISR_exact_sched_post. rewrite V293_ISR_sched_args_roundtrip by assumption. reflexivity. }
  eapply conseq_rule with (q := EX result : option val,
    getasrt (V293_ISR_exact_sched_fpost unmap group rows high bt bg br bh li I Hli nil result
      (V293_ISR_sched_call_lg lo hi aop held ir si ci) tid) ** frame).
  - intros s H; exact H.
  - intros s [result Hs]. exists result. rewrite Eq in Hs. exact Hs.
  - eapply call_rule with
      (pre := V293_ISR_exact_sched_fpre unmap group rows high bt bg br bh li I Hli)
      (post := V293_ISR_exact_sched_fpost unmap group rows high bt bg br bh li I Hli)
      (vl := nil) (logicl := V293_ISR_sched_call_lg lo hi aop held ir si ci) (tp := Tvoid) (tl := nil).
    + exact Hframe.
    + exact Hspec.
    + rewrite Ep. intros s H; exact H.
    + intros s H. reflexivity.
    + reflexivity.
    + rewrite Ep. eapply V293_star_CurLINV_l. apply V293_sched_exact_pre_local.
    + intros s [result Hs]. rewrite Eq in Hs.
      eapply V293_star_CurLINV_l; [ | exact Hs]. apply V293_sched_exact_post_local.
Qed.

Theorem V293_OSSched_ISR_exact_prefix : forall Spec sd li I RI r ri tid aop frame
    sched_id unmap group rows high bt bg br bh lo hi table target tp bp bo entries tasks old
    held ir si ci (Hli : GoodLInvAsrt li),
  lo < 256 -> hi < 256 -> (exists p, V293_bitmap_ready lo hi p) ->
  V293_bitmap_tasks lo hi tasks -> V293_priority_table entries tasks -> GoodFrm frame ->
  Spec sched_id = Some
    (V293_ISR_exact_sched_fpre unmap group rows high bt bg br bh li I Hli,
     V293_ISR_exact_sched_fpost unmap group rows high bt bg br bh li I Hli, (Tvoid, nil)) ->
  InfRules Spec sd li RI r ri
    ((V293_sched_exact_pre unmap group rows high bt bg br bh lo hi li tid aop **
      V293_sched_ISR_context I held ir si ci) **
      (V293_prefix_frame table high target tp bp bo entries tasks frame ** V293_prefix_output tp bo old))
    (V293_OSSched_unlocked_prefix sched_id table high target)
    (EX t : Modules.tid, [|V293_highest_ready tasks t|] **
      (V293_sched_exact_post unmap group rows high bt bg br bh lo hi li tid aop None **
        (V293_prefix_frame table high target tp bp bo entries tasks
          (V293_sched_ISR_context I held ir si ci ** frame) ** V293_prefix_output tp bo (Vptr t)))) tid.
Proof.
  intros Spec sd li I RI r ri tid aop frame sched_id unmap group rows high bt bg br bh lo hi
    table target tp bp bo entries tasks old held ir si ci Hli Hlo Hhi Hr Hb Htable Hframe Hspec.
  destruct (V293_ready_selection_task lo hi entries tasks Hlo Hhi Hr Hb Htable)
    as [t [m [Ht [Hentry Hhighest]]]].
  unfold V293_OSSched_unlocked_prefix. eapply seq_rule with
    (p' := V293_sched_exact_post unmap group rows high bt bg br bh lo hi li tid aop None **
      (V293_prefix_frame table high target tp bp bo entries tasks
        (V293_sched_ISR_context I held ir si ci ** frame) ** V293_prefix_output tp bo old)).
  - eapply conseq_rule with (q := EX result : option val,
      (V293_sched_exact_post unmap group rows high bt bg br bh lo hi li tid aop result **
        V293_sched_ISR_context I held ir si ci) **
        (V293_prefix_frame table high target tp bp bo entries tasks frame ** V293_prefix_output tp bo old)).
    + intros s Hs; exact Hs.
    + intros s [result Hs].
      assert (Hs' : s |= V293_sched_exact_post unmap group rows high bt bg br bh lo hi li tid aop result **
        (V293_prefix_frame table high target tp bp bo entries tasks
          (V293_sched_ISR_context I held ir si ci ** frame) ** V293_prefix_output tp bo old)).
      { unfold V293_prefix_frame in *. sep auto. }
      apply V293_exact_prefix_call_post. exists result. exact Hs'.
    + apply V293_OSSchedNew_ISR_exact_call with (Hli := Hli); try assumption.
      split; [apply V293_prefix_frame_good; exact Hframe | constructor].
  - eapply conseq_rule with (q :=
      V293_sched_exact_post unmap group rows high bt bg br bh lo hi li tid aop None **
        (V293_prefix_frame table high target tp bp bo entries tasks
          (V293_sched_ISR_context I held ir si ci ** frame) ** V293_prefix_output tp bo (Vptr t))).
    + intros s Hs; exact Hs.
    + intros s Hs. exists t. apply astar_l_apure_intro; [exact Hs | exact Hhighest].
    + apply V293_OSSched_exact_target_assign; assumption.
Qed.


