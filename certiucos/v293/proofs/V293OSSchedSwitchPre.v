(* Full spatial SWPRE_NDEAD from the actual tail, with a reserved second
   current-pointer half.  SWINVt/GoodI and the switch remain OPEN. *)
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCritical.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCurrent.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedChange.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedPrefix.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedGuards.
Require Import CertiOS.certiucos.v293.code.V293OSSchedGuards.
Require Import CertiOS.certiucos.v293.code.V293OSSchedChange.
Require Import CertiOS.certiucos.v293.code.V293OSSchedDispatch.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.sep_combine_lemmas.
Require Import Coq.Lists.List Lia.
Local Open Scope nat_scope.

Lemma V293_global_cell_type : forall x tp permission v s,
  s |= GV x @ tp |=> v @ permission ->
  exists b, get (getgenv s) x = Some (b, tp).
Proof.
  intros x tp permission v s [b Hs].
  eapply V293_star_env_l with (E := fun ge _ => exists b, get ge x = Some (b, tp)); [ | exact Hs].
  intros s0 [b0 [G _]]. exists b0. exact G.
Qed.

(* The existential pointee types must agree because both halves use the SAME
   global environment.  No untyped pointer reinterpretation is assumed. *)
Theorem V293_current_halves_write : forall tid,
  CurTid tid ** CurTid tid ==> EX tp : type, GV OSTCBCur @ (Tptr tp) |-> (Vptr tid).
Proof.
  intros tid s Hs. unfold CurTid in Hs.
  apply astar_l_aexists_elim in Hs. destruct Hs as [tp Hs].
  apply astar_r_aexists_elim in Hs. destruct Hs as [tq Hs].
  assert (G1 : exists b, get (getgenv s) OSTCBCur = Some (b, Tptr tp)).
  { eapply V293_star_env_l with (E := fun ge _ => exists b, get ge OSTCBCur = Some (b, Tptr tp)); [ | exact Hs]. intros s0 H0. eapply V293_global_cell_type; exact H0. }
  assert (G2 : exists b, get (getgenv s) OSTCBCur = Some (b, Tptr tq)).
  { eapply V293_star_env_r with (E := fun ge _ => exists b, get ge OSTCBCur = Some (b, Tptr tq)); [ | exact Hs]. intros s0 H0. eapply V293_global_cell_type; exact H0. }
  destruct G1 as [b1 G1]. destruct G2 as [b2 G2].
  assert (tp = tq) by congruence. subst tq.
  exists tp. eapply GV_combine_ro_p1; exact Hs.
Qed.


Lemma V293_critical_isr_clear : forall I stack critical,
  V293_sched_critical I stack critical ==> isrclr ** Atrue.
Proof.
  intros I stack critical s Hs. unfold V293_sched_critical, SWINV in Hs. sep auto.
Qed.

(* The same memory has two views: the full source tail remains available;
   the conjunction does not duplicate any spatial resource. *)
Theorem V293_OSSched_tail_switch_pre : forall
    unmap group rows high bt bg br bh lo hi li tid aop
    table target tp bp bo entries tasks current counter bcur bcounter nc frame c I stack critical,
  V293_current_task tasks tid nc ->
  V293_OSSched_tail_state unmap group rows high bt bg br bh lo hi li tid aop
    table target tp bp bo entries tasks current counter bcur bcounter nc
      (V293_sched_critical I stack critical ** (CurTid tid ** frame)) c ==>
  SWPRE_NDEAD V293_scheduler target tid.
Proof.
  intros unmap group rows high bt bg br bh lo hi li tid aop table target tp bp bo entries tasks
    current counter bcur bcounter nc frame c I stack critical Hcur s [next Hs].
  apply astar_l_apure_elim in Hs. destruct Hs as [Hhighest Hs].
  assert (Hmember : indom tasks tid).
  { destruct Hcur as [_ [st [m Hget]]]. exists (Int.repr (Z.of_nat nc), st, m). exact Hget. }
  unfold SWPRE_NDEAD. split.
  - assert (Hpack : s |=
      (V293_prefix_bindings table high target tp bp bo ** V293_prefix_output tp bo (Vptr next)) **
      ((CurTid tid ** CurTid tid) ** (V293_sched_critical I stack critical **
        (Aabsdata abstcblsid (abstcblist tasks) ** Atrue)))).
    { unfold V293_sched_internal_post, V293_sched_internal_resource, V293_prefix_frame, CurLINV in Hs.
      sep auto. }
    eapply astar_mono in Hpack.
    2: { apply V293_target_global_spatial. }
    2: { apply astar_mono; [apply V293_current_halves_write | intros s0 H0; exact H0]. }
    assert (Hpack' : s |= (GV target @ (Tptr tp) |-> (Vptr next)) **
      ((EX p : type, GV OSTCBCur @ (Tptr p) |-> (Vptr tid)) **
        ((isrclr ** Atrue) ** (AHprio V293_scheduler next ** Atrue)))).
    { eapply astar_mono; [intros s0 H0; exact H0 | | exact Hpack].
      apply astar_mono; [intros s0 H0; exact H0 | ].
      apply astar_mono; [apply V293_critical_isr_clear | ].
      apply astar_mono; [apply V293_tasks_highest_spatial; exact Hhighest | intros s0 H0; exact H0]. }
    unfold SWPRE. exists next. sep auto.
  - exists tasks. unfold V293_prefix_frame in Hs. sep auto.
Qed.


Theorem V293_OSSched_guarded_switch_pre_prefix : forall Spec sd li I r ri tid aop frame
    sched_id unmap group rows high bt bg br bh lo hi table target tp bp bo entries tasks old
    interrupt lock bi bl ni nl current counter bcur bcounter nc c stack critical suffix q (Hli : GoodLInvAsrt li),
  lo < 256 -> hi < 256 -> (exists p, V293_bitmap_ready lo hi p) ->
  V293_bitmap_tasks lo hi tasks -> V293_priority_table entries tasks -> GoodFrm frame ->
  ni < 256 -> nl < 256 -> V293_current_task tasks tid nc ->
  Spec sched_id = Some
    (V293_critical_fpre unmap group rows high bt bg br bh li I Hli,
     V293_critical_fpost unmap group rows high bt bg br bh li I Hli, (Tvoid, nil)) ->
  let gf := V293_guard_cell interrupt bi ni ** (V293_guard_cell lock bl nl ** (CurTid tid ** frame)) in
  let k := V293_sched_critical I stack critical in
  let pre := (V293_sched_internal_pre unmap group rows high bt bg br bh lo hi li tid aop ** k) **
    (V293_prefix_frame table high target tp bp bo entries tasks
      (V293_guard_cell current bcur nc ** gf) **
      (V293_prefix_output tp bo old ** V293_counter_cell counter bcounter c)) in
  let mid := V293_OSSched_tail_state unmap group rows high bt bg br bh lo hi li tid aop
    table target tp bp bo entries tasks current counter bcur bcounter nc (k ** gf) in
  let current_link := V293_OSSched_current_tail unmap group rows high bt bg br bh lo hi li tid aop
    table target tp bp bo entries tasks current counter bcur bcounter nc (k ** gf) in
  let linked := fun n => current_link n //\\ SWPRE_NDEAD V293_scheduler target tid in
  (ni = 0 -> nl = 0 -> V293_ready_select lo hi (V293_ready_group lo hi) <> nc ->
    InfRules Spec sd li I r ri (linked (Int.add c Int.one)) suffix q tid) ->
  InfRules Spec sd li I r ri pre
    (V293_OSSched_guards interrupt lock
      (sseq (V293_OSSched_unlocked_prefix sched_id table high target)
        (V293_OSSched_change high current counter suffix)))
    (if Nat.eqb ni 0 && Nat.eqb nl 0 then
      (if Nat.eqb (V293_ready_select lo hi (V293_ready_group lo hi)) nc then mid c else q) else pre) tid.
Proof.
  intros Spec sd li I r ri tid aop frame sched_id unmap group rows high bt bg br bh lo hi
    table target tp bp bo entries tasks old interrupt lock bi bl ni nl current counter bcur bcounter nc c stack critical suffix q
    Hli Hlo Hhi Hr Hb Htable Hframe Hni Hnl Hcur Hspec gf k pre mid current_link linked Hsuffix.
  apply V293_OSSched_guarded_critical_prefix with (Hli := Hli); try assumption.
  - split; [unfold CurTid, Agvarmapsto, Aptrmapsto; simpl; auto | exact Hframe].
  - intros Ei El Hd. eapply conseq_rule with (p := linked (Int.add c Int.one)) (q := q).
    + intros s Hs. split; [exact Hs | ].
      destruct Hs as [Hs _].
      eapply V293_OSSched_tail_switch_pre with
        (frame := V293_guard_cell interrupt bi ni ** (V293_guard_cell lock bl nl ** frame)); [exact Hcur | ].
      unfold V293_OSSched_tail_state in *. destruct Hs as [next Hs]. exists next.
      unfold V293_prefix_frame, gf in *. sep auto.
    + intros s Hs; exact Hs.
    + apply Hsuffix; assumption.
Qed.
