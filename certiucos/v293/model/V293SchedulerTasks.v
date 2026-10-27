(* Connect byte membership to the framework's task map and priority table.
   These are relations to be established by the real shared invariant, not
   assumptions that the selected task is already highest priority. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.auxlibs.MapLib.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import Coq.Lists.List Lia.
Local Open Scope nat_scope.

Definition V293_bitmap_tasks lo hi (tasks : TcbMod.map) : Prop :=
  forall p, p < 13 ->
    (V293_bitmap_ready lo hi p <->
      exists t m, get tasks t = Some (Int.repr (Z.of_nat p), rdy, m)).

Definition V293_priority_table (entries : list val) (tasks : TcbMod.map) : Prop :=
  length entries = 13 /\
  forall t priority status m, get tasks t = Some (priority, status, m) ->
    exists p, p < 13 /\ priority = Int.repr (Z.of_nat p) /\ nth p entries Vnull = Vptr t.

Definition V293_highest_ready (tasks : TcbMod.map) (t : tid) : Prop :=
  exists priority m,
    get tasks t = Some (priority, rdy, m) /\
    forall t' priority' m', get tasks t' = Some (priority', rdy, m') ->
      (Int.unsigned priority <= Int.unsigned priority')%Z.

Definition V293_scheduler : ossched := fun O t =>
  exists tasks, get O abstcblsid = Some (abstcblist tasks) /\ V293_highest_ready tasks t.

Lemma V293_priority_repr_unsigned : forall p,
  p < 13 -> Int.unsigned (Int.repr (Z.of_nat p)) = Z.of_nat p.
Proof.
  intros. apply Int.unsigned_repr.
  unfold Int.max_unsigned, Int.modulus, Int.wordsize; simpl; lia.
Qed.

Lemma V293_priority_repr_injective : forall p q,
  p < 13 -> q < 13 -> Int.repr (Z.of_nat p) = Int.repr (Z.of_nat q) -> p = q.
Proof.
  intros p q Hp Hq E. apply (f_equal Int.unsigned) in E.
  rewrite !V293_priority_repr_unsigned in E by assumption. lia.
Qed.

Theorem V293_ready_selection_task : forall lo hi entries tasks,
  lo < 256 -> hi < 256 ->
  (exists p, V293_bitmap_ready lo hi p) ->
  V293_bitmap_tasks lo hi tasks -> V293_priority_table entries tasks ->
  exists t m,
    get tasks t = Some (Int.repr (Z.of_nat (V293_ready_select lo hi (V293_ready_group lo hi))), rdy, m) /\
    nth (V293_ready_select lo hi (V293_ready_group lo hi)) entries Vnull = Vptr t /\
    V293_highest_ready tasks t.
Proof.
  intros lo hi entries tasks Hlo Hhi Hnonempty Hbitmap [Hlen Htable].
  pose proof (V293_ready_selection lo hi (V293_ready_group lo hi) Hlo Hhi eq_refl Hnonempty)
    as [_ [Hready Hmin]].
  pose proof (V293_ready_selection_range lo hi (V293_ready_group lo hi) Hlo Hhi eq_refl Hnonempty)
    as Hrange.
  destruct (proj1 (Hbitmap _ Hrange) Hready) as [t [m Ht]].
  exists t. exists m. split; [exact Ht | ].
  destruct (Htable _ _ _ _ Ht) as [p [Hp [Ep Et]]].
  assert (E : p = V293_ready_select lo hi (V293_ready_group lo hi)).
  { symmetry. apply V293_priority_repr_injective; assumption. }
  subst p. split; [exact Et | ].
  exists (Int.repr (Z.of_nat (V293_ready_select lo hi (V293_ready_group lo hi)))). exists m.
  split; [exact Ht | ]. intros t' priority' m' Ht'.
  destruct (Htable _ _ _ _ Ht') as [p [Hp' [Ep' Et']]]. subst priority'.
  rewrite !V293_priority_repr_unsigned by assumption.
  assert (Hbit : V293_bitmap_ready lo hi p).
  { apply (proj2 (Hbitmap p Hp')). exists t'. exists m'. exact Ht'. }
  specialize (Hmin p Hbit). lia.
Qed.

(* GoodSched expresses stability under separating extension and actual task
   membership. It does not assert that every abstract state has a ready task. *)
Theorem V293_scheduler_good : GoodSched V293_scheduler.
Proof.
  split.
  - intros x a y t Hjoin [tasks [Hget Hhighest]].
    exists tasks. split; [ | exact Hhighest]. eapply OSAbstMod.join_get_l; eauto.
  - split.
    + intros O t [tasks [Hget [p [m [Ht Hmin]]]]].
      exists tasks. exists (p, rdy, m). auto.
    + intros O1 O2 O t t' Hjoin [tasks [Hget Hhighest]] [tasks' [Hget' Hhighest']].
      assert (E : get O abstcblsid = Some (abstcblist tasks)) by (eapply OSAbstMod.join_get_l; eauto).
      rewrite E in Hget'. inversion Hget'; subst tasks'. exists tasks. auto.
Qed.
