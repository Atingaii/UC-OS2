(* Current membership and the switch target of the SAME guarded source prefix.
   Current may already be blocked; readiness is required only of the target.
   This supplies part of SWPRE_NDEAD, not its interrupt/current-write resources. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedChange.
Require Import CertiOS.certiucos.v293.code.V293OSSchedChange.
Require Import CertiOS.certiucos.v293.code.V293OSSchedGuards.
Require Import CertiOS.certiucos.v293.code.V293OSSchedDispatch.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedGuards.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedPrefix.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTarget.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import Coq.Lists.List Lia.
Local Open Scope nat_scope.

Definition V293_current_task (tasks : TcbMod.map) (t : Modules.addrval) nc :=
  nc < 13 /\ exists status m, get tasks t = Some (Int.repr (Z.of_nat nc), status, m).

Lemma V293_highest_unique : forall entries tasks t u,
  V293_priority_table entries tasks ->
  V293_highest_ready tasks t -> V293_highest_ready tasks u -> t = u.
Proof.
  intros entries tasks t u [_ Htable] [pr [m [Ht Hmin]]] [pr' [m' [Hu Hmin']]].
  destruct (Htable _ _ _ _ Ht) as [p [Hp [Ep Et]]].
  destruct (Htable _ _ _ _ Hu) as [q [Hq [Eq Eu]]].
  specialize (Hmin _ _ _ Hu). specialize (Hmin' _ _ _ Ht).
  subst pr pr'. rewrite !V293_priority_repr_unsigned in Hmin, Hmin' by assumption.
  assert (p = q) by lia. subst q. rewrite Et in Eu. inversion Eu; reflexivity.
Qed.

Theorem V293_OSSched_current_target : forall lo hi entries tasks current nc next,
  lo < 256 -> hi < 256 -> (exists p, V293_bitmap_ready lo hi p) ->
  V293_bitmap_tasks lo hi tasks -> V293_priority_table entries tasks ->
  V293_current_task tasks current nc -> V293_highest_ready tasks next ->
  (next = current <-> V293_ready_select lo hi (V293_ready_group lo hi) = nc).
Proof.
  intros lo hi entries tasks current nc next Hlo Hhi Hr Hb Htable [Hnc [st [msg Hcur]]] Hnext.
  destruct (V293_ready_selection_task lo hi entries tasks Hlo Hhi Hr Hb Htable)
    as [selected [m [Ht [Hentry Hhighest]]]].
  pose proof (V293_highest_unique entries tasks next selected Htable Hnext Hhighest) as E. subst selected.
  pose proof (V293_ready_selection_range lo hi (V293_ready_group lo hi) Hlo Hhi eq_refl Hr) as Hrange.
  split.
  - intro E. rewrite E in Ht. assert (Ep : Int.repr (Z.of_nat (V293_ready_select lo hi (V293_ready_group lo hi))) = Int.repr (Z.of_nat nc)) by congruence.
    apply V293_priority_repr_injective; assumption.
  - intro E. destruct (proj2 Htable _ _ _ _ Hcur) as [p [Hp [Ep Hptr]]].
    assert (nc = p) by (apply V293_priority_repr_injective; assumption).
    subst p. rewrite E in Hentry. rewrite Hptr in Hentry. inversion Hentry; reflexivity.
Qed.

(* The abstract table is consumed by AHprio, not copied as a pure oracle. *)
Lemma V293_tasks_highest_spatial : forall tasks next,
  V293_highest_ready tasks next ->
  Aabsdata abstcblsid (abstcblist tasks) ==> AHprio V293_scheduler next.
Proof.
  intros tasks next Hnext [[[[[[ge le] M] ir] aux] O] op] [Ho Hm].
  split; [exists tasks; split; [rewrite <- Ho; apply map_get_sig | exact Hnext] | exact Hm].
Qed.

Lemma V293_target_global_spatial : forall table high target tp bp bo next,
  V293_prefix_bindings table high target tp bp bo ** V293_prefix_output tp bo (Vptr next) ==>
    GV target @ (Tptr tp) |-> (Vptr next).
Proof.
  intros table high target tp bp bo next s Hs. exists bo.
  unfold Agvarmapsto, Aptrmapsto. change (s |= Agvarenv target (Tptr tp) (bo, 0%Z) ** V293_prefix_output tp bo (Vptr next)).
  eapply astar_mono; [ | intros s0 H; exact H | exact Hs].
  intros s0 H. exact (proj1 (proj2 H)).
Qed.

Section Tail.
Variables unmap group rows high : var.
Variables bt bg br bh : block.
Variables lo hi : nat.
Variable li : LocalInv.
Variable tid : Modules.tid.
Variable aop : spec_code.
Variables table target : var.
Variable tp : type.
Variables bp bo : block.
Variable entries : list val.
Variable tasks : TcbMod.map.
Variables current counter : var.
Variables bcur bcounter : block.
Variable nc : nat.
Variable frame : asrt.
Let tail := V293_OSSched_tail_state unmap group rows high bt bg br bh lo hi li tid aop
  table target tp bp bo entries tasks current counter bcur bcounter nc frame.
Definition V293_OSSched_switch_target : asrt :=
  EX next : Modules.tid, [|indom tasks tid /\ next <> tid|] **
    (AHprio V293_scheduler next ** ((EX p : type, GV target @ (Tptr p) |-> (Vptr next)) ** Atrue)).
Definition V293_OSSched_current_tail c : asrt := tail c //\\ V293_OSSched_switch_target.

Theorem V293_OSSched_current_tail_entails : forall c,
  lo < 256 -> hi < 256 -> (exists p, V293_bitmap_ready lo hi p) ->
  V293_bitmap_tasks lo hi tasks -> V293_priority_table entries tasks ->
  V293_current_task tasks tid nc -> V293_ready_select lo hi (V293_ready_group lo hi) <> nc ->
  tail c ==> V293_OSSched_current_tail c.
Proof.
  intros c Hlo Hhi Hr Hb Htable Hcur Hd s Hs. split; [exact Hs | ].
  destruct Hs as [next Hs].
  assert (Hhighest : V293_highest_ready tasks next).
  { apply astar_l_apure_elim in Hs. exact (proj1 Hs). }
  assert (Hne : next <> tid).
  { intro E. apply Hd. apply (proj1 (V293_OSSched_current_target lo hi entries tasks tid nc next
      Hlo Hhi Hr Hb Htable Hcur Hhighest)). exact E. }
  assert (Hmember : indom tasks tid).
  { destruct Hcur as [_ [st [m Hget]]]. exists (Int.repr (Z.of_nat nc), st, m). exact Hget. }
  assert (Hsp : s |= Aabsdata abstcblsid (abstcblist tasks) **
    ((V293_prefix_bindings table high target tp bp bo ** V293_prefix_output tp bo (Vptr next)) ** Atrue)).
  { unfold V293_prefix_frame in Hs. sep auto. }
  exists next. apply astar_l_apure_intro; [ | auto].
  eapply astar_mono; [apply V293_tasks_highest_spatial; exact Hhighest | | exact Hsp].
  eapply astar_mono; [ | intros s0 H; exact H].
  intros s0 H. exists tp. eapply V293_target_global_spatial; exact H.
Qed.
End Tail.

(* Stable full-prefix interface: only the still-open real switch suffix now
   receives current membership, target inequality and actual spatial resources. *)
Theorem V293_OSSched_guarded_current_prefix : forall Spec sd li I r ri tid aop frame
    sched_id unmap group rows high bt bg br bh lo hi table target tp bp bo entries tasks old
    interrupt lock bi bl ni nl current counter bcur bcounter nc c suffix q (Hli : GoodLInvAsrt li),
  lo < 256 -> hi < 256 -> (exists p, V293_bitmap_ready lo hi p) ->
  V293_bitmap_tasks lo hi tasks -> V293_priority_table entries tasks -> GoodFrm frame ->
  ni < 256 -> nl < 256 -> V293_current_task tasks tid nc ->
  Spec sched_id = Some
    (V293_sched_fpre unmap group rows high bt bg br bh li Hli,
     V293_sched_fpost unmap group rows high bt bg br bh li Hli, (Tvoid, nil)) ->
  let guardframe := V293_guard_cell interrupt bi ni ** (V293_guard_cell lock bl nl ** frame) in
  let pre := V293_sched_internal_pre unmap group rows high bt bg br bh lo hi li tid aop **
    (V293_prefix_frame table high target tp bp bo entries tasks
      (V293_guard_cell current bcur nc ** guardframe) **
      (V293_prefix_output tp bo old ** V293_counter_cell counter bcounter c)) in
  let mid := V293_OSSched_tail_state unmap group rows high bt bg br bh lo hi li tid aop
    table target tp bp bo entries tasks current counter bcur bcounter nc guardframe in
  let linked := V293_OSSched_current_tail unmap group rows high bt bg br bh lo hi li tid aop
    table target tp bp bo entries tasks current counter bcur bcounter nc guardframe in
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
    table target tp bp bo entries tasks old interrupt lock bi bl ni nl current counter bcur bcounter nc c suffix q
    Hli Hlo Hhi Hr Hb Htable Hframe Hni Hnl Hcur Hspec guardframe pre mid linked Hsuffix.
  apply V293_OSSched_guarded_changed_prefix with (Hli := Hli); try assumption.
  - destruct Hcur as [Hnc _]; lia.
  - intros Ei El Hd. eapply conseq_rule with (p := linked (Int.add c Int.one)) (q := q).
    + apply V293_OSSched_current_tail_entails; assumption.
    + intros s Hs; exact Hs.
    + apply Hsuffix; assumption.
Qed.
