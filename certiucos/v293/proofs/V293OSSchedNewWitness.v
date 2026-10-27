(* A constructive, spatial witness for the body contract, not merely its
   load equations. The empty local invariant here is a test fixture only. *)
Require Import Coq.Arith.Arith Coq.Lists.List Lia.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.certiucos.v293.code.V293ReadyTable.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Local Open Scope nat_scope.

Fixpoint V293_encoded_memory b (offset : Z) permission (bytes : list memval) : mem :=
  match bytes with
  | nil => emp
  | cons head tail => merge (sig (b, offset) (permission, head))
      (V293_encoded_memory b (offset + 1)%Z permission tail)
  end.

Lemma V293_encoded_memory_outside : forall bytes b offset permission b' i,
  b' <> b \/ (i < offset)%Z \/ (offset + Z.of_nat (length bytes) <= i)%Z ->
  get (V293_encoded_memory b offset permission bytes) (b', i) = None.
Proof.
  induction bytes as [ | head tail IH]; intros b offset permission b' i H; [apply map_emp_get | ].
  cbn [V293_encoded_memory]. rewrite map_merge_semp by reflexivity.
  rewrite map_get_sig' by (intro E; inversion E; subst; simpl in H; intuition lia).
  rewrite IH by (simpl in H; intuition lia). reflexivity.
Qed.

Lemma V293_encoded_memory_join : forall bytes b offset permission head,
  join (sig (b, offset) (permission, head))
    (V293_encoded_memory b (offset + 1)%Z permission bytes)
    (V293_encoded_memory b offset permission (cons head bytes)).
Proof.
  intros. apply map_join_merge. apply map_disjoint. intros [b' i].
  destruct (addr_eq_dec (b, offset) (b', i)) as [E | E].
  - inversion E; subst. right; left. apply V293_encoded_memory_outside. right; left; lia.
  - left. apply map_get_sig'; exact E.
Qed.

Lemma V293_encoded_memory_mapsto : forall b offset permission t v,
  mapstoval (b, offset) t permission v
    (V293_encoded_memory b offset permission (encode_val t v)).
Proof.
  intros. exists (encode_val t v). split; [reflexivity | ].
  generalize (encode_val t v). clear t v. intros bytes.
  revert offset. induction bytes as [ | head tail IH]; intros offset; [reflexivity | ].
  exists (sig (b, offset) (permission, head)).
  exists (V293_encoded_memory b (offset + 1)%Z permission tail).
  split; [apply V293_encoded_memory_join | ]. split; [reflexivity | apply IH].
Qed.

Definition V293_wstate ge le M : RstateOP :=
  (ge, le, M, (fun _ => false), (false, nil, nil), (emp : osabst), spec_done None).

Lemma V293_wstate_star : forall ge le m1 m2 m p q,
  join m1 m2 m -> V293_wstate ge le m1 |= p -> V293_wstate ge le m2 |= q ->
  V293_wstate ge le m |= p ** q.
Proof.
  intros ge le m1 m2 m p q J Hp Hq.
  exists m1. exists m2. exists m. exists (emp : osabst). exists (emp : osabst). exists (emp : osabst).
  split; [reflexivity | ]. split; [exact J | ]. split; [reflexivity | ].
  split; [apply map_join_emp | ]. split; assumption.
Qed.

Definition V293_nat_memory b offset values := V293_encoded_memory b offset false
  (List.map (fun n => Byte (Byte.repr (Int.unsigned (Int.repr (Z.of_nat n))))) values).

Lemma V293_read_bytes_witness : forall values ge le b offset,
  V293_wstate ge le (V293_nat_memory b offset values) |= V293_read_bytes b offset values.
Proof.
  induction values as [ | head tail IH]; intros ge le b offset; [split; reflexivity | ].
  eapply V293_wstate_star.
  - apply V293_encoded_memory_join.
  - split; [ | reflexivity].
    unfold mapstoval. eexists. split; [reflexivity | ].
    cbn [encode_val V293_byteval inj_bytes encode_int List.map ptomvallist].
    exists (sig (b, offset) (false, Byte (Byte.repr (Int.unsigned (Int.repr (Z.of_nat head)))))). exists (emp : mem).
    split; [apply map_join_emp | ]. split; reflexivity.
  - apply IH.
Qed.

Definition V293_witness_li : LocalInv := fun _ _ => Aemp.

Lemma V293_witness_li_good : GoodLInvAsrt V293_witness_li.
Proof.
  intros tid lg. split; [exact I | ].
  intros ge le M ir aux O le' M' aux' ir' O' H H'.
  specialize (H (spec_done None)). specialize (H' (spec_done None)).
  destruct H as [HM HO]. destruct H' as [HM' HO'].
  cbn [emptaskst emposabst] in *. split; congruence.
Qed.

Definition V293_witness_ge : env :=
  set (set (set (set (set (emp : env) 100%Z (1%positive, Tarray Tint8 256))
    101%Z (2%positive, Tint8)) 102%Z (3%positive, Tarray Tint8 2))
    103%Z (4%positive, Tint8)) OSTCBCur (6%positive, Tptr Tvoid).
Definition V293_witness_le : env := set (emp : env) 104%Z (5%positive, Tint8).
Definition V293_witness_table := V293_nat_memory 1%positive 0 V293_ready_table.
Definition V293_witness_rows := V293_nat_memory 3%positive 0 (cons 0 (cons 16 nil)).
Definition V293_witness_group := V293_encoded_memory 2%positive 0 false (encode_val Tint8 (V293_byteval 2)).
Definition V293_witness_high := V293_encoded_memory 4%positive 0 true (encode_val Tint8 (V293_byteval 0)).
Definition V293_witness_y := V293_encoded_memory 5%positive 0 true (encode_val Tint8 (V293_byteval 0)).
Definition V293_witness_current := V293_encoded_memory 6%positive 0 false
  (encode_val (Tptr Tvoid) (Vptr (7%positive, Int.zero))).
Definition V293_witness_inputs := merge V293_witness_table (merge V293_witness_rows V293_witness_group).
Definition V293_witness_common := merge V293_witness_inputs V293_witness_current.
Definition V293_witness_memory := merge (merge V293_witness_common V293_witness_y) V293_witness_high.

Ltac V293_outside :=
  unfold V293_witness_common, V293_witness_inputs,
    V293_witness_table, V293_witness_rows, V293_witness_group,
    V293_witness_high, V293_witness_y, V293_witness_current, V293_nat_memory;
  repeat rewrite map_merge_semp by reflexivity;
  repeat rewrite V293_encoded_memory_outside by (left; congruence);
  reflexivity.

Ltac V293_witness_join :=
  apply map_join_merge; apply map_disjoint; intros [b i];
  destruct (Pos.eq_dec b 1%positive); [subst b | ];
  first [left; V293_outside | right; left; V293_outside].

Lemma V293_witness_inputs_sat :
  V293_wstate V293_witness_ge V293_witness_le V293_witness_inputs |=
    V293_sched_inputs 1%positive 2%positive 3%positive 0 16 2.
Proof.
  eapply V293_wstate_star; [V293_witness_join | apply V293_read_bytes_witness | ].
  eapply V293_wstate_star.
  - apply map_join_merge. apply map_disjoint. intros [b i].
    destruct (Pos.eq_dec b 3%positive); [subst b; right; left | left]; V293_outside.
  - apply V293_read_bytes_witness.
  - split; [apply V293_encoded_memory_mapsto | reflexivity].
Qed.

Lemma V293_witness_current_sat :
  V293_wstate V293_witness_ge V293_witness_le V293_witness_current |=
    CurLINV V293_witness_li (7%positive, Int.zero).
Proof.
  exists (nil : list logicvar).
  eapply V293_wstate_star with (m1 := V293_witness_current) (m2 := emp).
  - apply map_join_emp.
  - exists Tvoid. exists 6%positive.
    eapply V293_wstate_star with (m1 := emp) (m2 := V293_witness_current).
    + apply map_join_comm. apply map_join_emp.
    + exists 6%positive. split; [vm_compute; reflexivity | ]. split; [reflexivity | split; reflexivity].
    + split; [apply V293_encoded_memory_mapsto | reflexivity].
  - eapply V293_wstate_star with (m1 := emp) (m2 := emp).
    + apply map_join_emp.
    + unfold LINV, V293_witness_li.
      eapply V293_wstate_star with (m1 := emp) (m2 := emp).
      * apply map_join_emp.
      * split; reflexivity.
      * split; [apply V293_witness_li_good | split; reflexivity].
    + exact I.
Qed.

Lemma V293_witness_bindings_sat :
  V293_wstate V293_witness_ge V293_witness_le emp |=
    V293_sched_bindings 100%Z 101%Z 102%Z 103%Z 104%Z
      1%positive 2%positive 3%positive 4%positive 5%positive.
Proof.
  unfold V293_sched_bindings. repeat split.
  - exists 1%positive. vm_compute. repeat split; reflexivity.
  - exists 2%positive. vm_compute. repeat split; reflexivity.
  - exists 3%positive. vm_compute. repeat split; reflexivity.
  - exists 4%positive. vm_compute. repeat split; reflexivity.
  - exists 5%positive. vm_compute. repeat split; reflexivity.
  - intros [v H]. vm_compute in H. discriminate.
  - intros [v H]. vm_compute in H. discriminate.
  - intros [v H]. vm_compute in H. discriminate.
  - intros [v H]. vm_compute in H. discriminate.
Qed.

Ltac V293_single_join k :=
  apply map_join_merge; apply map_disjoint; intros [b i];
  destruct (Pos.eq_dec b k); [subst b | ];
  first [left; V293_outside | right; left; V293_outside].

Lemma V293_witness_common_sat :
  V293_wstate V293_witness_ge V293_witness_le V293_witness_common |=
    V293_sched_common 100%Z 101%Z 102%Z 103%Z 104%Z
      1%positive 2%positive 3%positive 4%positive 5%positive
      0 16 2 V293_witness_li (7%positive, Int.zero) Aemp.
Proof.
  eapply V293_wstate_star.
  - V293_single_join 6%positive.
  - eapply V293_wstate_star with (m1 := emp) (m2 := V293_witness_inputs).
    + apply map_join_comm. apply map_join_emp.
    + apply V293_witness_bindings_sat.
    + apply V293_witness_inputs_sat.
  - apply astar_r_aemp_intro. apply V293_witness_current_sat.
Qed.

Theorem V293_OSSchedNew_spatial_precondition_witness :
  exists s,
    s |= <||spec_done None||> **
      V293_sched_state
        (V293_sched_common 100%Z 101%Z 102%Z 103%Z 104%Z
          1%positive 2%positive 3%positive 4%positive 5%positive
          0 16 2 V293_witness_li (7%positive, Int.zero) Aemp)
        5%positive 4%positive (V293_byteval 0) (V293_byteval 0).
Proof.
  exists (V293_wstate V293_witness_ge V293_witness_le V293_witness_memory).
  eapply V293_wstate_star with (m1 := emp) (m2 := V293_witness_memory).
  - apply map_join_comm. apply map_join_emp.
  - split; [reflexivity | split; reflexivity].
  - eapply V293_wstate_star.
    + unfold V293_witness_memory. V293_single_join 4%positive.
    + eapply V293_wstate_star.
      * V293_single_join 5%positive.
      * apply V293_witness_common_sat.
      * split; [apply V293_encoded_memory_mapsto | reflexivity].
    + split; [apply V293_encoded_memory_mapsto | reflexivity].
Qed.
