(* Real prefix -> priority branch -> modular counter -> actual SCAP switch.
   The port correspondence and physical shared invariant remain open. *)
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedDispatchShared.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedSwitch.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchState.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedChange.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCall.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCurrent.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedPrefix.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTarget.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedGuards.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCritical.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedShared.
Require Import CertiOS.certiucos.v293.code.V293OSSchedDispatch.
Require Import CertiOS.certiucos.v293.code.V293OSSchedChange.
Require Import CertiOS.certiucos.v293.code.V293OSSchedGuards.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import Coq.Lists.List Lia.
Local Open Scope nat_scope.

Section DispatchTail.
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
Definition V293_dispatch_tail c :=
  V293_dispatch_prefix_post unmap group rows high bt bg br bh lo hi V293_shared_li tid (sched;;aop)
    table target tp bp bo entries tasks events now
    (V293_guard_cell current bcur nc ** (V293_counter_cell counter bcounter c ** frame)) stack critical.

(* This frame contains no current pointer, shared abstract slots, target cell,
   action, interrupt flag or stack. Atrue preserves the CurLINV remainder. *)
Definition V293_dispatch_locals c :=
  ((V293_sched_globals unmap group rows high bt bg br bh **
    V293_sched_inputs bt bg br lo hi (V293_ready_group lo hi)) **
    PV (bh, Int.zero) @ Tint8 |->
      (V293_byteval (V293_ready_select lo hi (V293_ready_group lo hi)))) **
  ((V293_prefix_bindings table high target tp bp bo ** V293_read_pointers tp bp 0 entries) **
    (V293_guard_cell current bcur nc ** (V293_counter_cell counter bcounter c ** (frame ** Atrue)))).

Lemma V293_dispatch_locals_good : forall c, GoodFrm frame -> GoodFrm (V293_dispatch_locals c).
Proof.
  intros c Hf.
  assert (HB : forall b off vs, GoodFrm (V293_read_bytes b off vs)).
  { intros b off vs. revert off. induction vs; intros; simpl; auto. }
  assert (HP : forall b off vs, GoodFrm (V293_read_pointers tp b off vs)).
  { intros b off vs. revert off. induction vs; intros; simpl; auto. }
  unfold V293_dispatch_locals, V293_sched_globals, V293_sched_inputs,
    V293_prefix_bindings, V293_guard_cell, V293_counter_cell,
    V293_counter_bindings, Aptrmapsto.
  repeat split; try exact I; try exact Hf; auto.
Qed.

Lemma V293_dispatch_tail_split : forall c,
  V293_dispatch_tail c ==>
  EX next : Modules.tid, [|V293_highest_ready tasks next|] **
    (V293_switch_payload target tp tid tasks events now next aop stack critical ** V293_dispatch_locals c).
Proof.
  intros c s [next Hs]. exists next.
  unfold V293_dispatch_prefix_post, V293_sched_internal_post in Hs.
  unfold V293_dispatch_locals, V293_switch_payload, V293_sched_internal_resource in *.
  unfold CurLINV, LINV, V293_shared_li in Hs. sep normal in Hs. sep destruct Hs. sep split in Hs.
  assert (HK : s |= Aie false **
    ([|V293_highest_ready tasks next|] **
      ((<||sched;;aop||> ** ((V293_dispatch_snapshot target tp tid tasks events now next ** CurTid tid) **
        (Ais stack ** Acs critical))) **
        (((V293_sched_globals unmap group rows high bt bg br bh **
          V293_sched_inputs bt bg br lo hi (V293_ready_group lo hi)) **
          PV (bh, Int.zero) @ Tint8 |-> (V293_byteval (V293_ready_select lo hi (V293_ready_group lo hi)))) **
          ((V293_prefix_bindings table high target tp bp bo ** V293_read_pointers tp bp 0 entries) **
            (V293_guard_cell current bcur nc ** (V293_counter_cell counter bcounter c ** (frame ** Atrue))))))))
    by (sep auto).
  apply astar_l_aie_elim in HK. exact (proj2 HK).
Qed.

Theorem V293_dispatch_tail_comparison : forall c s,
  lo < 256 -> hi < 256 -> (exists p, V293_bitmap_ready lo hi p) -> nc < 256 ->
  s |= V293_dispatch_tail c ->
  evalval (V293_OSSched_different high current) (getsmem s) =
    Some (Vint32 (if Nat.eqb (V293_ready_select lo hi (V293_ready_group lo hi)) nc then Int.zero else Int.one)) /\
  evaltype (V293_OSSched_different high current) (getsmem s) = Some Tint32.
Proof.
  intros c s Hlo Hhi Hr Hnc [next Hs].
  assert (HP : s |= V293_sched_internal_resource unmap group rows high bt bg br bh lo hi V293_shared_li tid
    (V293_byteval (V293_ready_select lo hi (V293_ready_group lo hi))) **
    (V293_prefix_bindings table high target tp bp bo ** Atrue))
    by (unfold V293_sched_internal_post in Hs; fold (V293_sched_internal_resource unmap group rows high bt bg br bh lo hi V293_shared_li tid (V293_byteval (V293_ready_select lo hi (V293_ready_group lo hi)))) in Hs; sep auto).
  assert (Eh : evalval (ecast (evar high) Tint32) (getsmem s) =
    Some (V293_byteval (V293_ready_select lo hi (V293_ready_group lo hi))) /\
    evaltype (ecast (evar high) Tint32) (getsmem s) = Some Tint32).
  { eapply V293_byte_variable.
    - eapply V293_star_env_l with (E := fun ge _ => get ge high = Some (bh, Tint8)); [ | exact HP]. apply V293_prefix_high_global.
    - eapply V293_star_env_r with (E := fun _ le => get le high = None); [ | exact HP].
      intros s0 H0. eapply V293_star_env_l with (E := fun _ le => get le high = None); [ | exact H0].
      intros s1 H1. exact (proj1 (proj2 (proj2 (proj2 (V293_prefix_bindings_view _ _ _ _ _ _ _ H1))))).
    - eapply V293_star_load_l; [ | exact HP]. intros s0 H0. eapply V293_prefix_selected_load; eauto. }
  clear HP.
  assert (HC : s |= V293_guard_cell current bcur nc ** Atrue) by (sep auto).
  destruct (V293_current_variable current bcur nc Atrue s Hnc HC) as [Ec Tc].
  destruct Eh as [Eh Th]. unfold V293_OSSched_different.
  destruct s as [[[[[[ge le] M] ir] aux] O] op].
  cbn [getsmem get_smem evalval evaltype] in Eh, Th, Ec, Tc |- *. rewrite Eh, Ec, Th, Tc.
  unfold V293_byteval. cbn [bop_eval val_eq bop_type]. rewrite V293_byte_eq.
  - destruct (Nat.eqb (V293_ready_select lo hi (V293_ready_group lo hi)) nc); split; reflexivity.
  - pose proof (V293_ready_selection_range lo hi (V293_ready_group lo hi) Hlo Hhi eq_refl Hr). lia.
  - exact Hnc.
Qed.

Theorem V293_dispatch_tail_increment : forall Spec sd I r ri c,
  InfRules Spec sd V293_shared_li I r ri (V293_dispatch_tail c)
    (V293_OSSched_increment counter) (V293_dispatch_tail (Int.add c Int.one)) tid.
Proof.
  intros Spec sd I r ri c. unfold V293_dispatch_tail, V293_dispatch_prefix_post.
  apply ex_intro_rule. intro next.
  let rest := constr:([|V293_highest_ready tasks next|] **
    ([|(None : option val) = None /\ V293_bitmap_ready lo hi (V293_ready_select lo hi (V293_ready_group lo hi)) /\
      (forall p, V293_bitmap_ready lo hi p -> V293_ready_select lo hi (V293_ready_group lo hi) <= p)|] **
      ((V293_sched_internal_resource unmap group rows high bt bg br bh lo hi V293_shared_li tid
        (V293_byteval (V293_ready_select lo hi (V293_ready_group lo hi))) **
        (V293_dispatch_snapshot target tp tid tasks events now next ** (Ais stack ** Acs critical))) **
        ((V293_prefix_bindings table high target tp bp bo ** V293_read_pointers tp bp 0 entries) **
          (V293_guard_cell current bcur nc ** frame))))) in
  eapply conseq_rule with
    (p := <||sched;;aop||> ** (rest ** V293_counter_cell counter bcounter c))
    (q := <||sched;;aop||> ** (rest ** V293_counter_cell counter bcounter (Int.add c Int.one))).
  - unfold V293_sched_internal_post. intros s Hs. fold (V293_sched_internal_resource unmap group rows high bt bg br bh lo hi V293_shared_li tid (V293_byteval (V293_ready_select lo hi (V293_ready_group lo hi)))) in *. sep auto; assumption.
  - unfold V293_sched_internal_post. intros s Hs. exists next. fold (V293_sched_internal_resource unmap group rows high bt bg br bh lo hi V293_shared_li tid (V293_byteval (V293_ready_select lo hi (V293_ready_group lo hi)))) in *. sep auto; assumption.
  - apply V293_OSSched_counter_increment.
    intros s Hs. eapply V293_star_CurLINV_r; [ | exact Hs].
    intros s0 H0. eapply V293_star_CurLINV_r; [ | exact H0].
    intros s1 H1. eapply V293_star_CurLINV_l; [ | exact H1].
    intros s2 H2. eapply V293_star_CurLINV_l; [ | exact H2].
    apply V293_sched_internal_resource_CurLINV.
Qed.

Definition V293_dispatch_resumed c :=
  V293_switch_resume target tp tid aop stack critical (V293_dispatch_locals c).
Theorem V293_dispatch_tail_switch : forall Spec r ri c,
  indom tasks tid -> GoodFrm frame ->
  InfRules Spec V293_scheduler V293_shared_li (V293_dispatch_inv target tp) r ri
    (V293_dispatch_tail c) (sprim (switch target)) (V293_dispatch_resumed c) tid.
Proof.
  intros Spec r ri c Hmem Hf.
  eapply conseq_rule with
    (p := EX next : Modules.tid, [|V293_highest_ready tasks next|] **
      (V293_switch_payload target tp tid tasks events now next aop stack critical ** V293_dispatch_locals c)).
  - apply V293_dispatch_tail_split.
  - intros s H; exact H.
  - apply ex_intro_rule. intro next.
    eapply conseq_rule with (p :=
      (V293_switch_payload target tp tid tasks events now next aop stack critical ** V293_dispatch_locals c) **
      [|V293_highest_ready tasks next|]).
    + intros s Hs. sep auto.
    + intros s Hs; exact Hs.
    + apply pure_split_rule. intro Hhighest.
      apply V293_shared_normal_switch; try assumption.
      * apply V293_dispatch_locals_good; exact Hf.
      * intros s Hs. apply astar_l_aemp_intro in Hs.
        eapply astar_mono in Hs; [ | apply V293_switch_local_empty | intros st H; exact H]. sep auto.
Qed.
Definition V293_dispatch_changed_post c :=
  if Nat.eqb (V293_ready_select lo hi (V293_ready_group lo hi)) nc
  then V293_dispatch_tail c else V293_dispatch_resumed (Int.add c Int.one).
Theorem V293_dispatch_change_switch : forall Spec r ri c,
  lo < 256 -> hi < 256 -> (exists p, V293_bitmap_ready lo hi p) -> nc < 256 ->
  indom tasks tid -> GoodFrm frame ->
  InfRules Spec V293_scheduler V293_shared_li (V293_dispatch_inv target tp) r ri
    (V293_dispatch_tail c)
    (V293_OSSched_change high current counter (sprim (switch target)))
    (V293_dispatch_changed_post c) tid.
Proof.
  intros Spec r ri c Hlo Hhi Hr Hnc Hmem Hf.
  unfold V293_OSSched_change, V293_dispatch_changed_post. eapply ift_rule with (tp := Tint32).
  - intros s Hs. destruct (V293_dispatch_tail_comparison c s Hlo Hhi Hr Hnc Hs) as [Ev Et].
    eexists. split; [exact Ev | ]. split; [exact Et | discriminate].
  - intros s [Hs [v [Ev Hv]]].
    destruct (V293_dispatch_tail_comparison c s Hlo Hhi Hr Hnc Hs) as [E _].
    rewrite E in Ev. inversion Ev; subst v.
    destruct (Nat.eqb (V293_ready_select lo hi (V293_ready_group lo hi)) nc);
      [exact Hs | vm_compute in Hv; discriminate].
  - destruct (Nat.eqb (V293_ready_select lo hi (V293_ready_group lo hi)) nc) eqn:En.
    + eapply conseq_rule with (p := Afalse).
      * intros s [Hs [v [Ev Hv]]].
        destruct (V293_dispatch_tail_comparison c s Hlo Hhi Hr Hnc Hs) as [E _].
        rewrite En in E. rewrite E in Ev. inversion Ev; subst v. vm_compute in Hv; discriminate.
      * intros s Hs; exact Hs.
      * apply pfalse_rule.
    + eapply conseq_rule with (p := V293_dispatch_tail c).
      * intros s [Hs _]; exact Hs.
      * intros s Hs; exact Hs.
      * eapply seq_rule.
        -- apply V293_dispatch_tail_increment.
        -- apply V293_dispatch_tail_switch; assumption.
Qed.

Theorem V293_dispatch_prefix_change_switch : forall Spec r ri sched_id c,
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
    (V293_dispatch_changed_post c) tid.
Proof.
  intros Spec r ri sched_id c Hlo Hhi Hr Hb Htable Hcur Hf Hspec.
  eapply seq_rule with (p' := V293_dispatch_tail c).
  - apply V293_OSSched_dispatch_prefix with (Hli := V293_switch_li_good); try assumption.
    repeat split; try apply V293_guard_cell_good; try apply V293_counter_cell_good; exact Hf.
  - apply V293_dispatch_change_switch; try assumption.
    + pose proof (proj1 Hcur). lia.
    + destruct Hcur as [_ [st [m Hget]]]. exists (Int.repr (Z.of_nat nc), st, m). exact Hget.
Qed.
End DispatchTail.


(* Enabled guards execute the complete normalized ordinary-switch path;
   disabled guards retain the full entry, including the pending action. *)
Theorem V293_OSSched_guarded_dispatch_switch : forall Spec r ri tid aop frame
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
  let post := V293_dispatch_changed_post unmap group rows high bt bg br bh lo hi tid aop
    table target tp bp bo entries tasks events now current counter bcur bcounter nc gf stack critical c in
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
  - intros Hi Hl. apply V293_dispatch_prefix_change_switch; try assumption.
    unfold gf. repeat split; try apply V293_guard_cell_good; exact Hframe.
Qed.
