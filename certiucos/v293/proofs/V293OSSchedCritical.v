(* Preserve the actual switch invariant INSIDE the internal callee contract.
   No GoodFrm assertion is imposed on interrupt/critical-section resources. *)
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCurrent.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCall.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedPrefix.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTarget.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedGuards.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedChange.
Require Import CertiOS.certiucos.v293.code.V293OSSchedGuards.
Require Import CertiOS.certiucos.v293.code.V293OSSchedNew.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.code.V293OSSchedChange.
Require Import CertiOS.certiucos.v293.code.V293OSSchedDispatch.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import Coq.Lists.List Lia.
Local Open Scope nat_scope.

Lemma V293_inv_function_assertion : forall p,
  GoodInvAsrt p -> GoodFunAsrt p.
Proof.
  induction p; simpl; intros Hgood; try exact I; try contradiction;
    try (destruct Hgood; split; auto); auto.
  destruct b; exact I.
Qed.
Lemma V293_starinv_function_assertion : forall I low n,
  GoodFunAsrt (starinv_isr I low n).
Proof.
  intros Inv low n. revert low. induction n; intros low; simpl.
  - intros sr. repeat split; apply V293_inv_function_assertion; apply invp.
  - split; [intros sr; repeat split; apply V293_inv_function_assertion; apply invp | apply IHn].
Qed.
Definition V293_sched_critical (I : Inv) (stack : is) (critical : cs) : asrt :=
  SWINV I ** (Ais stack ** Acs critical).
Lemma V293_sched_critical_good : forall I stack critical,
  GoodFunAsrt (V293_sched_critical I stack critical).
Proof.
  intros. unfold V293_sched_critical, SWINV, isrclr, invlth_isr.
  repeat split; try exact I; intros;
    repeat split; try exact I; apply V293_starinv_function_assertion.
Qed.

(* Payload is used only inside a verified body, never as call_rule's frame. *)
Lemma V293_sched_entry_resource_payload : forall unmap group rows high y bt bg br bh byblock lo hi li tid aop yold hold (payload : asrt),
  unmap <> y -> group <> y -> rows <> y -> high <> y ->
  (((Alvarenv y Tint8 (byblock, 0%Z) ** PV (byblock, Int.zero) @ Tint8 |-> yold) ** Aemp) **
    (<||aop||> ** (V293_sched_internal_resource unmap group rows high bt bg br bh lo hi li tid hold ** payload))) **
    V293_sched_local_domain y ==>
  <||aop||> ** V293_sched_state
    (V293_sched_common unmap group rows high y bt bg br bh byblock lo hi (V293_ready_group lo hi)
      li tid ((Aie false ** payload) ** V293_sched_local_domain y)) byblock bh yold hold.
Proof.
  intros unmap group rows high y bt bg br bh byblock lo hi li tid aop yold hold payload Hu Hg Hr Hh s Hs.
  unfold V293_sched_internal_resource in Hs.
  assert (Hs' : s |= ((Alvarenv y Tint8 (byblock, 0%Z) **
    V293_sched_globals unmap group rows high bt bg br bh) ** V293_sched_local_domain y) **
    (((<||aop||> ** V293_sched_inputs bt bg br lo hi (V293_ready_group lo hi)) **
       (CurLINV li tid ** (Aie false ** payload))) **
       (PV (byblock, Int.zero) @ Tint8 |-> yold ** PV (bh, Int.zero) @ Tint8 |-> hold))).
  { sep auto. }
  clear Hs. rename Hs' into Hs.
  eapply astar_mono in Hs.
  2: { apply V293_sched_entry_context; assumption. }
  2: { intros s0 H0; exact H0. }
  unfold V293_sched_state, V293_sched_common.
  sep auto.
Qed.

Lemma V293_sched_return_resource_payload : forall unmap group rows high y bt bg br bh byblock lo hi li tid aop yv hv (payload : asrt),
  <||aop||> ** V293_sched_state
    (V293_sched_common unmap group rows high y bt bg br bh byblock lo hi (V293_ready_group lo hi)
      li tid ((Aie false ** payload) ** V293_sched_local_domain y)) byblock bh yv hv ==>
  ((EX v : val, LV y @ Tint8 |-> v) ** Aemp) **
    (<||aop||> ** (V293_sched_internal_resource unmap group rows high bt bg br bh lo hi li tid hv ** payload)) **
    V293_sched_local_domain y.
Proof.
  intros unmap group rows high y bt bg br bh byblock lo hi li tid aop yv hv payload s Hs.
  unfold V293_sched_state, V293_sched_common in Hs.
  assert (Hs' : s |= V293_sched_bindings unmap group rows high y bt bg br bh byblock **
    (PV (byblock, Int.zero) @ Tint8 |-> yv ** (V293_sched_local_domain y **
      (<||aop||> ** ((V293_sched_inputs bt bg br lo hi (V293_ready_group lo hi) **
        (CurLINV li tid ** Aie false)) ** PV (bh, Int.zero) @ Tint8 |-> hv) ** payload)))).
  { sep auto. }
  clear Hs. rename Hs' into Hs.
  eapply astar_mono in Hs.
  2: { apply V293_sched_return_bindings. }
  2: { intros s0 H0; exact H0. }
  assert (Hs' : s |= (((Alvarenv y Tint8 (byblock, 0%Z) ** PV (byblock, Int.zero) @ Tint8 |-> yv) ** Aemp) **
    (<||aop||> ** (V293_sched_internal_resource unmap group rows high bt bg br bh lo hi li tid hv ** payload))) **
      V293_sched_local_domain y).
  { unfold V293_sched_internal_resource. sep auto. }
  apply astar_assoc_elim in Hs'.
  eapply astar_mono; [apply V293_local_return_pack | intros s0 H0; exact H0 | exact Hs'].
Qed.

(* The same two assignments and return prove preservation of payload. *)
Lemma V293_sched_internal_payload : forall Spec sd li I tid aop
    unmap group rows high y bt bg br bh lo hi payload,
  unmap <> y -> group <> y -> rows <> y -> high <> y ->
  InfRules Spec sd li I
    (fun result => ((EX v : val, LV y @ Tint8 |-> v) ** Aemp) **
      (V293_sched_internal_post unmap group rows high bt bg br bh lo hi li tid aop result ** payload) **
      V293_sched_local_domain y) Afalse
    (((EX v : val, LV y @ Tint8 |-> v) ** Aemp) **
      (V293_sched_internal_pre unmap group rows high bt bg br bh lo hi li tid aop ** payload) **
      V293_sched_local_domain y)
    (V293_OSSchedNew_body unmap group rows high y) Afalse tid.
Proof.
  intros Spec sd li I tid aop unmap group rows high y bt bg br bh lo hi payload Hu Hg Hr Hh.
  eapply conseq_rule with (p := EX hv : val, EX yv : val, EX byblock : block,
    (((((Alvarenv y Tint8 (byblock, 0%Z) ** PV (byblock, Int.zero) @ Tint8 |-> yv) ** Aemp) **
       (<||aop||> ** (V293_sched_internal_resource unmap group rows high bt bg br bh lo hi li tid hv ** payload))) **
       V293_sched_local_domain y) ** [|lo < 256 /\ hi < 256 /\ (exists p, V293_bitmap_ready lo hi p)|])).
  - unfold V293_sched_internal_pre, Alvarmapsto, Alvarenv'. intros s Hs. sep auto.
  - intros s Hfalse; exact Hfalse.
  - apply ex_intro_rule. intros hold. apply ex_intro_rule. intros yold.
    apply ex_intro_rule. intros byblock. apply pure_split_rule. intros [Hlo [Hhi Hready]].
    eapply conseq_rule.
    + apply V293_sched_entry_resource_payload; assumption.
    + intros s Hfalse; exact Hfalse.
    + eapply r_conseq_rule.
      3: { apply V293_OSSchedNew_body_hoare; auto. }
      * intros result s Hs. unfold V293_OSSchedNew_post in Hs.
        apply V293_pure_move in Hs. apply astar_l_apure_elim in Hs.
        destruct Hs as [Hp Hs]. apply V293_sched_return_resource_payload in Hs.
        unfold V293_sched_internal_post. sep auto.
      * intros s Hfalse; exact Hfalse.
Qed.

(* Dynamic snapshots are logic arguments, not fixed per-program stack states. *)
Definition V293_critical_args (lg : list logicvar) :
    option (nat * nat * spec_code * is * cs) :=
  match lg with
  | cons (logic_lv (cons (Vint32 low) (cons (Vint32 upper) nil)))
      (cons (logic_code aop) (cons (logic_is stack) (cons (logic_cs critical) nil))) =>
      Some (Z.to_nat (Int.unsigned low), Z.to_nat (Int.unsigned upper), aop, stack, critical)
  | _ => None
  end.
Definition V293_critical_pre unmap group rows high bt bg br bh li I tid lg :=
  match V293_critical_args lg with
  | Some (lo, hi, aop, stack, critical) =>
      V293_sched_internal_pre unmap group rows high bt bg br bh lo hi li tid aop **
        V293_sched_critical I stack critical
  | None => Afalse
  end.
Definition V293_critical_post unmap group rows high bt bg br bh li I tid lg result :=
  match V293_critical_args lg with
  | Some (lo, hi, aop, stack, critical) =>
      V293_sched_internal_post unmap group rows high bt bg br bh lo hi li tid aop result **
        V293_sched_critical I stack critical
  | None => Afalse
  end.
Definition V293_critical_fpre (unmap group rows high : var) (bt bg br bh : block) (li : LocalInv) (I : Inv)
    (Hli : GoodLInvAsrt li) : fpre.
Proof.
  intros vl lg tid. refine (@mkfunasrt
    (V293_critical_pre unmap group rows high bt bg br bh li I tid lg) _).
  unfold V293_critical_pre. destruct (V293_critical_args lg) as [[[[[lo hi] op] stack] critical] | ]; [ | exact Logic.I].
  split; [apply V293_sched_internal_pre_good; exact Hli | apply V293_sched_critical_good].
Defined.
Definition V293_critical_fpost (unmap group rows high : var) (bt bg br bh : block) (li : LocalInv) (I : Inv)
    (Hli : GoodLInvAsrt li) : fpost.
Proof.
  intros vl result lg tid. refine (@mkfunasrt
    (V293_critical_post unmap group rows high bt bg br bh li I tid lg result) _).
  unfold V293_critical_post. destruct (V293_critical_args lg) as [[[[[lo hi] op] stack] critical] | ]; [ | exact Logic.I].
  split; [apply V293_sched_internal_post_good; exact Hli | apply V293_sched_critical_good].
Defined.

Theorem V293_OSSchedNew_critical_contract : forall P f Spec sd li I
    unmap group rows high y bt bg br bh (Hli : GoodLInvAsrt li) lg tid vl pre post,
  unmap <> y -> group <> y -> rows <> y -> high <> y ->
  P f = Some (V293_OSSchedNew_function unmap group rows high y) ->
  Some pre = BuildPreI P f vl lg (V293_critical_fpre unmap group rows high bt bg br bh li I Hli) tid ->
  Some post = BuildRetI P f vl lg (V293_critical_fpost unmap group rows high bt bg br bh li I Hli) tid ->
  InfRules Spec sd li I post Afalse pre (V293_OSSchedNew_body unmap group rows high y) Afalse tid.
Proof.
  intros P f Spec sd li I unmap group rows high y bt bg br bh Hli lg tid vl pre post
    Hu Hg Hr Hh Hcode Hpre Hpost.
  unfold BuildPreI in Hpre. rewrite Hcode in Hpre.
  destruct vl as [ | v vl].
  2: { assert (E : dl_vl_match dnil (rev (v :: vl)) = false).
       { destruct (rev (v :: vl)) eqn:Er; [ | reflexivity].
         apply (f_equal (@rev val)) in Er. rewrite rev_involutive in Er. discriminate. }
       unfold V293_OSSchedNew_function in Hpre. rewrite E in Hpre. discriminate. }
  change (Some pre = Some (((EX v : val, LV y @ Tint8 |-> v) ** Aemp) **
    V293_critical_pre unmap group rows high bt bg br bh li I tid lg ** V293_sched_local_domain y)) in Hpre.
  inversion Hpre; subst pre.
  unfold BuildRetI in Hpost. rewrite Hcode in Hpost.
  change (Some post = Some (fun result => ((EX v : val, LV y @ Tint8 |-> v) ** Aemp) **
    V293_critical_post unmap group rows high bt bg br bh li I tid lg result ** V293_sched_local_domain y)) in Hpost.
  inversion Hpost; subst post.
  unfold V293_critical_pre, V293_critical_post.
  destruct (V293_critical_args lg) as [[[[[lo hi] op] stack] critical] | ];
    [apply V293_sched_internal_payload; assumption | apply V293_sched_false_entry].
Qed.
Definition V293_critical_spec sched_id unmap group rows high bt bg br bh li I
    (Hli : GoodLInvAsrt li) : funspec :=
  fun f => if Z.eq_dec f sched_id then Some
    (V293_critical_fpre unmap group rows high bt bg br bh li I Hli,
     V293_critical_fpost unmap group rows high bt bg br bh li I Hli, (Tvoid, nil)) else None.
Theorem V293_OSSchedNew_critical_WFFunEnv : forall sched_id unmap group rows high y bt bg br bh li I Hli sd,
  unmap <> y -> group <> y -> rows <> y -> high <> y ->
  WFFunEnv (V293_OSSchedNew_internal_unit sched_id unmap group rows high y)
    (V293_critical_spec sched_id unmap group rows high bt bg br bh li I Hli) sd li I.
Proof.
  intros sched_id unmap group rows high y bt bg br bh li I Hli sd Hu Hg Hr Hh. split.
  - intros f. unfold V293_OSSchedNew_internal_unit, V293_critical_spec.
    destruct (Z.eq_dec f sched_id); split; intros [a H]; try discriminate; eexists; reflexivity.
  - intros f pre post t tl Hspec. unfold V293_critical_spec in Hspec.
    destruct (Z.eq_dec f sched_id); try discriminate. inversion Hspec; subst pre post t tl.
    exists dnil. exists (dcons y Tint8 dnil). exists (V293_OSSchedNew_body unmap group rows high y).
    split.
    + unfold V293_OSSchedNew_internal_unit. destruct (Z.eq_dec f sched_id); [reflexivity | contradiction].
    + split; [constructor | ]. split; [reflexivity | ].
      intros vl pre post lg tid Hpre Hpost.
      eapply V293_OSSchedNew_critical_contract; try eassumption.
      unfold V293_OSSchedNew_internal_unit. destruct (Z.eq_dec f sched_id); [reflexivity | contradiction].
Qed.

Definition V293_critical_call_lg lo hi aop stack (critical : cs) : list logicvar :=
  cons (logic_lv (cons (V293_byteval lo) (cons (V293_byteval hi) nil)))
    (cons (logic_code aop) (cons (logic_is stack) (cons (logic_cs critical) nil))).
Lemma V293_critical_args_roundtrip : forall lo hi aop stack critical,
  lo < 256 -> hi < 256 ->
  V293_critical_args (V293_critical_call_lg lo hi aop stack critical) = Some (lo,hi,aop,stack,critical).
Proof.
  intros. unfold V293_critical_args, V293_critical_call_lg, V293_byteval.
  rewrite !V293_sched_snapshot_roundtrip by assumption. reflexivity.
Qed.
Theorem V293_OSSchedNew_critical_call : forall Spec sd li I r ri tid aop frame
    sched_id unmap group rows high bt bg br bh lo hi stack critical (Hli : GoodLInvAsrt li),
  lo < 256 -> hi < 256 -> GoodFrm frame ->
  Spec sched_id = Some
    (V293_critical_fpre unmap group rows high bt bg br bh li I Hli,
     V293_critical_fpost unmap group rows high bt bg br bh li I Hli, (Tvoid, nil)) ->
  InfRules Spec sd li I r ri
    ((V293_sched_internal_pre unmap group rows high bt bg br bh lo hi li tid aop **
       V293_sched_critical I stack critical) ** frame)
    (scall sched_id nil)
    (EX result : option val,
      (V293_sched_internal_post unmap group rows high bt bg br bh lo hi li tid aop result **
        V293_sched_critical I stack critical) ** frame) tid.
Proof.
  intros Spec sd li I r ri tid aop frame sched_id unmap group rows high bt bg br bh lo hi stack critical Hli
    Hlo Hhi Hframe Hspec.
  assert (Ep : getasrt (V293_critical_fpre unmap group rows high bt bg br bh li I Hli nil
    (V293_critical_call_lg lo hi aop stack critical) tid) =
    V293_sched_internal_pre unmap group rows high bt bg br bh lo hi li tid aop ** V293_sched_critical I stack critical).
  { change (V293_critical_pre unmap group rows high bt bg br bh li I tid
      (V293_critical_call_lg lo hi aop stack critical) =
      V293_sched_internal_pre unmap group rows high bt bg br bh lo hi li tid aop ** V293_sched_critical I stack critical).
    unfold V293_critical_pre. rewrite V293_critical_args_roundtrip by assumption. reflexivity. }
  assert (Eq : forall result, getasrt (V293_critical_fpost unmap group rows high bt bg br bh li I Hli nil result
    (V293_critical_call_lg lo hi aop stack critical) tid) =
    V293_sched_internal_post unmap group rows high bt bg br bh lo hi li tid aop result ** V293_sched_critical I stack critical).
  { intro. change (V293_critical_post unmap group rows high bt bg br bh li I tid
      (V293_critical_call_lg lo hi aop stack critical) result =
      V293_sched_internal_post unmap group rows high bt bg br bh lo hi li tid aop result ** V293_sched_critical I stack critical).
    unfold V293_critical_post. rewrite V293_critical_args_roundtrip by assumption. reflexivity. }
  eapply conseq_rule with (q := EX result : option val,
    getasrt (V293_critical_fpost unmap group rows high bt bg br bh li I Hli nil result
      (V293_critical_call_lg lo hi aop stack critical) tid) ** frame).
  - intros s H; exact H.
  - intros s [result Hs]. exists result. rewrite Eq in Hs. exact Hs.
  - eapply call_rule with
      (pre := V293_critical_fpre unmap group rows high bt bg br bh li I Hli)
      (post := V293_critical_fpost unmap group rows high bt bg br bh li I Hli)
      (vl := nil) (logicl := V293_critical_call_lg lo hi aop stack critical) (tp := Tvoid) (tl := nil).
    + exact Hframe.
    + exact Hspec.
    + rewrite Ep. intros s H; exact H.
    + intros s H. reflexivity.
    + reflexivity.
    + rewrite Ep. eapply V293_star_CurLINV_l. apply V293_sched_internal_pre_CurLINV.
    + intros s [result Hs]. rewrite Eq in Hs.
      eapply V293_star_CurLINV_l; [ | exact Hs]. apply V293_sched_internal_post_CurLINV.
Qed.

(* Resume the same source prefix with the switch invariant in the callee,
   and only genuinely admissible memory/abstract resources in its frame. *)
Theorem V293_OSSched_critical_prefix : forall Spec sd li I r ri tid aop frame
    sched_id unmap group rows high bt bg br bh lo hi table target tp bp bo entries tasks old
    stack critical (Hli : GoodLInvAsrt li),
  lo < 256 -> hi < 256 -> (exists p, V293_bitmap_ready lo hi p) ->
  V293_bitmap_tasks lo hi tasks -> V293_priority_table entries tasks -> GoodFrm frame ->
  Spec sched_id = Some
    (V293_critical_fpre unmap group rows high bt bg br bh li I Hli,
     V293_critical_fpost unmap group rows high bt bg br bh li I Hli, (Tvoid, nil)) ->
  InfRules Spec sd li I r ri
    ((V293_sched_internal_pre unmap group rows high bt bg br bh lo hi li tid aop **
      V293_sched_critical I stack critical) **
      (V293_prefix_frame table high target tp bp bo entries tasks frame ** V293_prefix_output tp bo old))
    (V293_OSSched_unlocked_prefix sched_id table high target)
    (EX t : Modules.tid, [|V293_highest_ready tasks t|] **
      (V293_sched_internal_post unmap group rows high bt bg br bh lo hi li tid aop None **
        (V293_prefix_frame table high target tp bp bo entries tasks
          (V293_sched_critical I stack critical ** frame) ** V293_prefix_output tp bo (Vptr t)))) tid.
Proof.
  intros Spec sd li I r ri tid aop frame sched_id unmap group rows high bt bg br bh lo hi
    table target tp bp bo entries tasks old stack critical Hli Hlo Hhi Hr Hb Htable Hframe Hspec.
  destruct (V293_ready_selection_task lo hi entries tasks Hlo Hhi Hr Hb Htable)
    as [t [m [Ht [Hentry Hhighest]]]].
  unfold V293_OSSched_unlocked_prefix. eapply seq_rule with
    (p' := V293_sched_internal_post unmap group rows high bt bg br bh lo hi li tid aop None **
      (V293_prefix_frame table high target tp bp bo entries tasks
        (V293_sched_critical I stack critical ** frame) ** V293_prefix_output tp bo old)).
  - eapply conseq_rule with (q := EX result : option val,
      (V293_sched_internal_post unmap group rows high bt bg br bh lo hi li tid aop result **
        V293_sched_critical I stack critical) **
        (V293_prefix_frame table high target tp bp bo entries tasks frame ** V293_prefix_output tp bo old)).
    + intros s Hs; exact Hs.
    + intros s [result Hs].
      assert (Hs' : s |= V293_sched_internal_post unmap group rows high bt bg br bh lo hi li tid aop result **
        (V293_prefix_frame table high target tp bp bo entries tasks
          (V293_sched_critical I stack critical ** frame) ** V293_prefix_output tp bo old)).
      { unfold V293_prefix_frame in *. sep auto. }
      apply V293_prefix_call_post. exists result. exact Hs'.
    + apply V293_OSSchedNew_critical_call with (Hli := Hli); try assumption.
      split; [apply V293_prefix_frame_good; exact Hframe | constructor].
  - eapply conseq_rule with (q :=
      V293_sched_internal_post unmap group rows high bt bg br bh lo hi li tid aop None **
        (V293_prefix_frame table high target tp bp bo entries tasks
          (V293_sched_critical I stack critical ** frame) ** V293_prefix_output tp bo (Vptr t))).
    + intros s Hs; exact Hs.
    + intros s Hs. exists t. apply astar_l_apure_intro; [exact Hs | exact Hhighest].
    + apply V293_OSSched_target_assign; assumption.
Qed.

Theorem V293_OSSched_guarded_critical_prefix : forall Spec sd li I r ri tid aop frame
    sched_id unmap group rows high bt bg br bh lo hi table target tp bp bo entries tasks old
    interrupt lock bi bl ni nl current counter bcur bcounter nc c stack critical suffix q (Hli : GoodLInvAsrt li),
  lo < 256 -> hi < 256 -> (exists p, V293_bitmap_ready lo hi p) ->
  V293_bitmap_tasks lo hi tasks -> V293_priority_table entries tasks -> GoodFrm frame ->
  ni < 256 -> nl < 256 -> V293_current_task tasks tid nc ->
  Spec sched_id = Some
    (V293_critical_fpre unmap group rows high bt bg br bh li I Hli,
     V293_critical_fpost unmap group rows high bt bg br bh li I Hli, (Tvoid, nil)) ->
  let gf := V293_guard_cell interrupt bi ni ** (V293_guard_cell lock bl nl ** frame) in
  let k := V293_sched_critical I stack critical in
  let pre := (V293_sched_internal_pre unmap group rows high bt bg br bh lo hi li tid aop ** k) **
    (V293_prefix_frame table high target tp bp bo entries tasks
      (V293_guard_cell current bcur nc ** gf) **
      (V293_prefix_output tp bo old ** V293_counter_cell counter bcounter c)) in
  let mid := V293_OSSched_tail_state unmap group rows high bt bg br bh lo hi li tid aop
    table target tp bp bo entries tasks current counter bcur bcounter nc (k ** gf) in
  let linked := V293_OSSched_current_tail unmap group rows high bt bg br bh lo hi li tid aop
    table target tp bp bo entries tasks current counter bcur bcounter nc (k ** gf) in
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
    Hli Hlo Hhi Hr Hb Htable Hframe Hni Hnl Hcur Hspec gf k pre mid linked Hsuffix.
  assert (Hnc : nc < 256) by (destruct Hcur as [Hnc _]; lia).
  eapply V293_OSSched_guards_rule with (ri_mem := Atrue) (rl_mem := Atrue); try assumption.
  - unfold pre, gf, V293_prefix_frame. intros s Hs. sep auto.
  - unfold pre, gf, V293_prefix_frame. intros s Hs. sep auto.
  - intros Ei El. eapply seq_rule with (p' := mid c).
    + eapply conseq_rule with
        (p := (V293_sched_internal_pre unmap group rows high bt bg br bh lo hi li tid aop ** k) **
          (V293_prefix_frame table high target tp bp bo entries tasks
            (V293_guard_cell current bcur nc ** (V293_counter_cell counter bcounter c ** gf)) **
            V293_prefix_output tp bo old))
        (q := EX t : Modules.tid, [|V293_highest_ready tasks t|] **
          (V293_sched_internal_post unmap group rows high bt bg br bh lo hi li tid aop None **
            (V293_prefix_frame table high target tp bp bo entries tasks
              (k ** (V293_guard_cell current bcur nc ** (V293_counter_cell counter bcounter c ** gf))) **
              V293_prefix_output tp bo (Vptr t)))).
      * unfold pre, V293_prefix_frame. intros s Hs. sep auto.
      * unfold mid, V293_OSSched_tail_state, V293_prefix_frame. intros s [t Hs]. exists t. sep auto.
      * apply V293_OSSched_critical_prefix with (Hli := Hli); try assumption.
        unfold gf. repeat split; try apply V293_guard_cell_good; try apply V293_counter_cell_good; exact Hframe.
    + apply V293_OSSched_change_continuation; try assumption.
      intro Hd. eapply conseq_rule with (p := linked (Int.add c Int.one)) (q := q).
      * apply V293_OSSched_current_tail_entails; assumption.
      * intros s Hs; exact Hs.
      * apply Hsuffix; assumption.
Qed.
