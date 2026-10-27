Require Import Coq.Arith.Arith Coq.Lists.List Coq.Bool.Bool Lia.
Require Import CertiOS.certiucos.v293.code.V293ReadyTable.
Import ListNotations.

(* Priorities 13..15 are deliberately not required to be clear. *)
Definition V293_bitmap_ready (lo hi p : nat) : Prop :=
  (p < 8 /\ Nat.testbit lo p = true) \/
  (8 <= p /\ p < 13 /\ Nat.testbit hi (p - 8) = true).

Definition V293_ready_group (lo hi : nat) : nat :=
  (if lo =? 0 then 0 else 1) + (if hi =? 0 then 0 else 2).

Definition V293_ready_row (lo hi y : nat) : nat := if y =? 0 then lo else hi.
Definition V293_ready_select (lo hi group : nat) : nat :=
  8 * V293_ready_lookup group +
  V293_ready_lookup (V293_ready_row lo hi (V293_ready_lookup group)).

(* A 256-entry data check, evaluated by Coq's kernel-checked VM. The second
   conjunct is independent of the table: testbit determines membership. *)
Definition V293_row_check (n : nat) : bool :=
  (V293_ready_lookup n <? 8) &&
  ((n =? 0) || Nat.testbit n (V293_ready_lookup n)) &&
  forallb (fun b => negb (Nat.testbit n b) || (V293_ready_lookup n <=? b)) (seq 0 8).

Lemma V293_ready_table_checked : forallb V293_row_check (seq 0 256) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma V293_ready_row_spec : forall n,
  n < 256 ->
  V293_ready_lookup n < 8 /\
  (n <> 0 -> Nat.testbit n (V293_ready_lookup n) = true) /\
  (forall b, b < 8 -> Nat.testbit n b = true -> V293_ready_lookup n <= b).
Proof.
  intros n Hn.
  pose proof V293_ready_table_checked as H.
  rewrite forallb_forall in H.
  specialize (H n (proj2 (in_seq 256 0 n) ltac:(lia))).
  unfold V293_row_check in H.
  apply andb_true_iff in H as [H Hmin].
  apply andb_true_iff in H as [Hbound Hbit].
  apply Nat.ltb_lt in Hbound. split; [exact Hbound | ]. split.
  - intros Hnz. apply orb_true_iff in Hbit as [Hz | Hbit]; [ | exact Hbit].
    apply Nat.eqb_eq in Hz. contradiction.
  - intros b Hb Hbset. rewrite forallb_forall in Hmin.
    specialize (Hmin b (proj2 (in_seq 8 0 b) ltac:(lia))).
    rewrite Hbset in Hmin. simpl in Hmin. apply Nat.leb_le. exact Hmin.
Qed.

Theorem V293_ready_selection : forall lo hi group,
  lo < 256 -> hi < 256 -> group = V293_ready_group lo hi ->
  (exists p, V293_bitmap_ready lo hi p) ->
  V293_ready_lookup group < 2 /\
  V293_bitmap_ready lo hi (V293_ready_select lo hi group) /\
  (forall p, V293_bitmap_ready lo hi p -> V293_ready_select lo hi group <= p).
Proof.
  intros lo hi group Hlo Hhi Hgroup [w Hw]. subst group.
  destruct (V293_ready_row_spec lo Hlo) as [L [Lbit Lmin]].
  destruct (V293_ready_row_spec hi Hhi) as [H [Hbit Hmin]].
  unfold V293_ready_group, V293_ready_select, V293_ready_row.
  destruct (lo =? 0) eqn:Elo; destruct (hi =? 0) eqn:Ehi;
    apply Nat.eqb_eq in Elo || apply Nat.eqb_neq in Elo;
    apply Nat.eqb_eq in Ehi || apply Nat.eqb_neq in Ehi.
  - subst lo hi. destruct Hw as [[_ Hw] | [_ [_ Hw]]];
      rewrite Nat.testbit_0_l in Hw; discriminate.
  - change (1 < 2 /\ V293_bitmap_ready lo hi (8 + V293_ready_lookup hi) /\
        (forall p, V293_bitmap_ready lo hi p -> 8 + V293_ready_lookup hi <= p)).
    assert (Hwrow : 8 <= w /\ w < 13 /\ Nat.testbit hi (w - 8) = true).
    { destruct Hw as [[_ Hbad] | Hw]; [subst lo; rewrite Nat.testbit_0_l in Hbad; discriminate | exact Hw]. }
    destruct Hwrow as [Wlo [Whi Wbit]].
    assert (K : V293_ready_lookup hi <= w - 8) by (apply Hmin; [lia | exact Wbit]).
    split; [lia | ]. split.
    + right. split; [lia | ]. split; [lia | ].
      replace (8 + V293_ready_lookup hi - 8) with (V293_ready_lookup hi) by lia.
      apply Hbit. exact Ehi.
    + intros p [[_ Hbad] | [Plo [Phi Pbit]]].
      * subst lo. rewrite Nat.testbit_0_l in Hbad. discriminate.
      * specialize (Hmin (p - 8) ltac:(lia) Pbit). lia.
  - change (0 < 2 /\ V293_bitmap_ready lo hi (V293_ready_lookup lo) /\
        (forall p, V293_bitmap_ready lo hi p -> V293_ready_lookup lo <= p)).
    split; [lia | ]. split.
    + left. auto.
    + intros p [[Plo Pbit] | [Plo _]]; [apply Lmin; assumption | lia].
  - change (0 < 2 /\ V293_bitmap_ready lo hi (V293_ready_lookup lo) /\
        (forall p, V293_bitmap_ready lo hi p -> V293_ready_lookup lo <= p)).
    split; [lia | ]. split.
    + left. auto.
    + intros p [[Plo Pbit] | [Plo _]]; [apply Lmin; assumption | lia].
Qed.

Corollary V293_ready_selection_range : forall lo hi group,
  lo < 256 -> hi < 256 -> group = V293_ready_group lo hi ->
  (exists p, V293_bitmap_ready lo hi p) -> V293_ready_select lo hi group < 13.
Proof.
  intros. destruct (V293_ready_selection lo hi group H H0 H1 H2) as [_ [Hr _]].
  destruct Hr as [[Hr _] | [_ [Hr _]]]; lia.
Qed.
