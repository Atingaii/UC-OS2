(* The actual internal call at the start of OS_Sched's unlocked branch.
   No callee-local address is supplied by the caller. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import Coq.Lists.List Lia.
Local Open Scope nat_scope.

Definition V293_sched_call_lg lo hi aop : list logicvar :=
  cons (logic_lv (cons (V293_byteval lo) (cons (V293_byteval hi) nil)))
    (cons (logic_code aop) nil).

Lemma V293_sched_snapshot_roundtrip : forall n,
  n < 256 -> Z.to_nat (Int.unsigned (Int.repr (Z.of_nat n))) = n.
Proof.
  intros n Hn. rewrite Int.unsigned_repr by
    (unfold Int.max_unsigned, Int.modulus, Int.wordsize; simpl; lia).
  apply Nat2Z.id.
Qed.

Lemma V293_sched_call_pre_selector : forall unmap group rows high bt bg br bh li Hli lo hi aop tid,
  lo < 256 -> hi < 256 ->
  getasrt (V293_sched_fpre unmap group rows high bt bg br bh li Hli nil
    (V293_sched_call_lg lo hi aop) tid) =
  V293_sched_internal_pre unmap group rows high bt bg br bh lo hi li tid aop.
Proof.
  intros. change (V293_sched_internal_pre unmap group rows high bt bg br bh
    (Z.to_nat (Int.unsigned (Int.repr (Z.of_nat lo))))
    (Z.to_nat (Int.unsigned (Int.repr (Z.of_nat hi)))) li tid aop =
    V293_sched_internal_pre unmap group rows high bt bg br bh lo hi li tid aop).
  rewrite !V293_sched_snapshot_roundtrip by assumption. reflexivity.
Qed.

Lemma V293_sched_call_post_selector : forall unmap group rows high bt bg br bh li Hli lo hi aop tid result,
  lo < 256 -> hi < 256 ->
  getasrt (V293_sched_fpost unmap group rows high bt bg br bh li Hli nil result
    (V293_sched_call_lg lo hi aop) tid) =
  V293_sched_internal_post unmap group rows high bt bg br bh lo hi li tid aop result.
Proof.
  intros. change (V293_sched_internal_post unmap group rows high bt bg br bh
    (Z.to_nat (Int.unsigned (Int.repr (Z.of_nat lo))))
    (Z.to_nat (Int.unsigned (Int.repr (Z.of_nat hi)))) li tid aop result =
    V293_sched_internal_post unmap group rows high bt bg br bh lo hi li tid aop result).
  rewrite !V293_sched_snapshot_roundtrip by assumption. reflexivity.
Qed.

Lemma V293_sched_internal_resource_CurLINV : forall unmap group rows high bt bg br bh lo hi li tid hv,
  V293_sched_internal_resource unmap group rows high bt bg br bh lo hi li tid hv ==> CurLINV li tid.
Proof.
  intros unmap group rows high bt bg br bh lo hi li tid hv. unfold V293_sched_internal_resource.
  apply V293_star_CurLINV_l. apply V293_star_CurLINV_r.
  apply V293_star_CurLINV_l. intros s H; exact H.
Qed.

Lemma V293_sched_internal_pre_CurLINV : forall unmap group rows high bt bg br bh lo hi li tid aop,
  V293_sched_internal_pre unmap group rows high bt bg br bh lo hi li tid aop ==> CurLINV li tid.
Proof.
  intros unmap group rows high bt bg br bh lo hi li tid aop s [hv Hs].
  eapply V293_star_CurLINV_l; [ | exact Hs].
  apply V293_star_CurLINV_r. apply V293_sched_internal_resource_CurLINV.
Qed.

Lemma V293_sched_internal_post_CurLINV : forall unmap group rows high bt bg br bh lo hi li tid aop result,
  V293_sched_internal_post unmap group rows high bt bg br bh lo hi li tid aop result ==> CurLINV li tid.
Proof.
  intros unmap group rows high bt bg br bh lo hi li tid aop result. unfold V293_sched_internal_post.
  apply V293_star_CurLINV_r. apply V293_star_CurLINV_r.
  apply V293_sched_internal_resource_CurLINV.
Qed.

(* This is the framework call rule, not a second proof of the callee body.
   Its table lookup will later be discharged by the full internal unit. *)
Theorem V293_OSSchedNew_call_rule : forall Spec sd li I r ri tid aop frame
    sched_id unmap group rows high bt bg br bh lo hi (Hli : GoodLInvAsrt li),
  lo < 256 -> hi < 256 -> GoodFrm frame ->
  Spec sched_id = Some
    (V293_sched_fpre unmap group rows high bt bg br bh li Hli,
     V293_sched_fpost unmap group rows high bt bg br bh li Hli, (Tvoid, nil)) ->
  InfRules Spec sd li I r ri
    (V293_sched_internal_pre unmap group rows high bt bg br bh lo hi li tid aop ** frame)
    (scall sched_id nil)
    (EX result : option val,
      V293_sched_internal_post unmap group rows high bt bg br bh lo hi li tid aop result ** frame) tid.
Proof.
  intros Spec sd li I r ri tid aop frame sched_id unmap group rows high bt bg br bh lo hi Hli
    Hlo Hhi Hframe Hspec.
  assert (Ep := V293_sched_call_pre_selector unmap group rows high bt bg br bh li Hli lo hi aop tid Hlo Hhi).
  assert (Eq := V293_sched_call_post_selector unmap group rows high bt bg br bh li Hli lo hi aop tid).
  eapply conseq_rule with (q := EX result : option val,
    getasrt (V293_sched_fpost unmap group rows high bt bg br bh li Hli nil result
      (V293_sched_call_lg lo hi aop) tid) ** frame).
  - intros s H; exact H.
  - intros s [result Hs]. exists result. rewrite Eq in Hs by assumption. exact Hs.
  - eapply call_rule with
      (pre := V293_sched_fpre unmap group rows high bt bg br bh li Hli)
      (post := V293_sched_fpost unmap group rows high bt bg br bh li Hli)
      (vl := nil) (logicl := V293_sched_call_lg lo hi aop) (tp := Tvoid) (tl := nil).
    + exact Hframe.
    + exact Hspec.
    + rewrite Ep. intros s H; exact H.
    + intros s H. simpl. reflexivity.
    + reflexivity.
    + rewrite Ep. apply V293_sched_internal_pre_CurLINV.
    + intros s [result Hs]. rewrite Eq in Hs by assumption.
      eapply V293_sched_internal_post_CurLINV; exact Hs.
Qed.
