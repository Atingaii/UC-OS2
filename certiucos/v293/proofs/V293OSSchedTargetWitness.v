(* Satisfiability of the target-read premises, including physical pointer
   bytes, the same state's abstract task map, and its readable priority byte.
   This is not a witness for the whole OS_Sched / critical-section contract. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.auxdef.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTarget.
Require Import Coq.Lists.List Lia.
Local Open Scope nat_scope.

Fixpoint V293_pointer_memory tp b offset entries : mem :=
  match entries with
  | nil => emp
  | cons v tail => merge (V293_encoded_memory b offset false (encode_val (Tptr tp) v))
      (V293_pointer_memory tp b (offset + 4)%Z tail)
  end.

Lemma V293_pointer_memory_outside : forall entries tp b offset b' i,
  b' <> b \/ (i < offset)%Z \/ (offset + 4 * Z.of_nat (length entries) <= i)%Z ->
  get (V293_pointer_memory tp b offset entries) (b', i) = None.
Proof.
  induction entries as [ | v tail IH]; intros tp b offset b' i H; [apply map_emp_get | ].
  cbn [V293_pointer_memory]. rewrite map_merge_semp by reflexivity.
  rewrite V293_encoded_memory_outside.
  - rewrite IH; [reflexivity | simpl length in H; rewrite Nat2Z.inj_succ in H; intuition lia].
  - rewrite encode_val_length. simpl typelen. simpl length in H.
    rewrite Nat2Z.inj_succ in H. intuition lia.
Qed.

Lemma V293_pointer_memory_join : forall entries tp b offset v,
  join (V293_encoded_memory b offset false (encode_val (Tptr tp) v))
    (V293_pointer_memory tp b (offset + 4)%Z entries)
    (V293_pointer_memory tp b offset (cons v entries)).
Proof.
  intros. apply map_join_merge. apply map_disjoint. intros [b' i].
  destruct (Pos.eq_dec b' b) as [E | E].
  - subst b'. destruct (Z_lt_dec i (offset + 4)) as [H | H].
    + right; left. apply V293_pointer_memory_outside. right; left; exact H.
    + left. apply V293_encoded_memory_outside. right; right.
      rewrite encode_val_length. simpl typelen; lia.
  - left. apply V293_encoded_memory_outside. left; exact E.
Qed.

Lemma V293_read_pointers_witness : forall entries ge le tp b offset,
  V293_wstate ge le (V293_pointer_memory tp b offset entries) |= V293_read_pointers tp b offset entries.
Proof.
  induction entries as [ | v tail IH]; intros ge le tp b offset; [split; reflexivity | ].
  eapply V293_wstate_star; [apply V293_pointer_memory_join | | apply IH].
  split; [apply V293_encoded_memory_mapsto | reflexivity].
Qed.

Definition V293_idle_tid : tid := (7%positive, Int.zero).
Definition V293_idle_tasks : TcbMod.map := sig V293_idle_tid (Int.repr 12, rdy, Vnull).
Definition V293_idle_entries : list val := repeat Vnull 12 ++ cons (Vptr V293_idle_tid) nil.

Lemma V293_idle_relations :
  V293_bitmap_tasks 0 16 V293_idle_tasks /\ V293_priority_table V293_idle_entries V293_idle_tasks.
Proof.
  assert (Ht : get V293_idle_tasks V293_idle_tid = Some (Int.repr 12, rdy, Vnull)).
  { apply map_get_sig. }
  assert (Honly : forall t p status m, get V293_idle_tasks t = Some (p, status, m) ->
    t = V293_idle_tid /\ p = Int.repr 12 /\ status = rdy /\ m = Vnull).
  { intros t p status m H. unfold V293_idle_tasks in H.
    destruct (tid_eq_dec V293_idle_tid t) as [E | E].
    - subst t. rewrite map_get_sig in H. inversion H; auto.
    - rewrite map_get_sig' in H by exact E. discriminate. }
  split.
  - intros p Hp. split.
    + intros Hb. assert (p = 12).
      { do 13 (destruct p as [ | p]; [vm_compute in Hb; intuition lia | ]); lia. }
      subst p. exists V293_idle_tid. exists Vnull. exact Ht.
    + intros [t [m H]]. destruct (Honly _ _ _ _ H) as [_ [E _]].
      assert (Ep : p = 12).
      { apply V293_priority_repr_injective; [exact Hp | lia | exact E]. }
      subst p. vm_compute; intuition lia.
  - split; [reflexivity | ]. intros t p status m H.
    destruct (Honly _ _ _ _ H) as [Et [Ep _]]. subst t; subst p.
    exists 12. split; [lia | ]. split; reflexivity.
Qed.

Definition V293_target_wstate ge le M O : RstateOP :=
  (ge, le, M, (fun _ => false), (false, nil, nil), O, spec_done None).

Lemma V293_target_wstate_star : forall ge le m1 m2 m o1 o2 o p q,
  join m1 m2 m -> join o1 o2 o ->
  V293_target_wstate ge le m1 o1 |= p -> V293_target_wstate ge le m2 o2 |= q ->
  V293_target_wstate ge le m o |= p ** q.
Proof.
  intros ge le m1 m2 m o1 o2 o p q Jm Jo Hp Hq.
  exists m1. exists m2. exists m. exists o1. exists o2. exists o.
  split; [reflexivity | ]. split; [exact Jm | ]. split; [reflexivity | ].
  split; [exact Jo | ]. split; assumption.
Qed.

Definition V293_target_fixture_ge : env :=
  set (set (emp : env) 100%Z (8%positive, Tarray (Tptr Tvoid) 13)) 101%Z (9%positive, Tint8).
Definition V293_target_fixture_table := V293_pointer_memory Tvoid 8%positive 0 V293_idle_entries.
Definition V293_target_fixture_high := V293_encoded_memory 9%positive 0 false
  (encode_val Tint8 (V293_byteval 12)).
Definition V293_target_fixture_mem := merge V293_target_fixture_table V293_target_fixture_high.
Definition V293_target_fixture_abs : osabst := sig abstcblsid (abstcblist V293_idle_tasks).
Definition V293_target_fixture_state := V293_target_wstate V293_target_fixture_ge emp
  V293_target_fixture_mem V293_target_fixture_abs.

Lemma V293_target_fixture_mem_join :
  join V293_target_fixture_table V293_target_fixture_high V293_target_fixture_mem.
Proof.
  apply map_join_merge. apply map_disjoint. intros [b i].
  destruct (Pos.eq_dec b 8%positive) as [E | E].
  - subst b. right; left. apply V293_encoded_memory_outside. left; discriminate.
  - left. apply V293_pointer_memory_outside. left; exact E.
Qed.

Lemma V293_target_fixture_spatial : V293_target_fixture_state |=
  (V293_read_pointers Tvoid 8%positive 0 V293_idle_entries **
    Aabsdata abstcblsid (abstcblist V293_idle_tasks)) **
  Amapsto (9%positive, 0%Z) Tint8 false (V293_byteval 12).
Proof.
  eapply V293_target_wstate_star; [apply V293_target_fixture_mem_join | apply map_join_emp | | ].
  - eapply V293_target_wstate_star with (m1 := V293_target_fixture_table) (m2 := emp)
      (o1 := emp) (o2 := V293_target_fixture_abs).
    + apply map_join_emp.
    + apply map_join_comm. apply map_join_emp.
    + apply V293_read_pointers_witness.
    + split; reflexivity.
  - split; [apply V293_encoded_memory_mapsto | reflexivity].
Qed.

Theorem V293_OSSched_target_precondition_witness : exists s entries tasks,
  V293_bitmap_tasks 0 16 tasks /\ V293_priority_table entries tasks /\
  get (getlenv s) 100%Z = None /\ get (getlenv s) 101%Z = None /\
  get (getgenv s) 100%Z = Some (8%positive, Tarray (Tptr Tvoid) 13) /\
  get (getgenv s) 101%Z = Some (9%positive, Tint8) /\
  load Tint8 (getmem s) (9%positive, 0%Z) = Some (V293_byteval 12) /\
  s |= (V293_read_pointers Tvoid 8%positive 0 entries ** Aabsdata abstcblsid (abstcblist tasks)) **
    Amapsto (9%positive, 0%Z) Tint8 false (V293_byteval 12).
Proof.
  exists V293_target_fixture_state. exists V293_idle_entries. exists V293_idle_tasks.
  destruct V293_idle_relations as [Hb Ht]. split; [exact Hb | ]. split; [exact Ht | ].
  split; [reflexivity | ]. split; [reflexivity | ].
  split; [vm_compute; reflexivity | ]. split; [vm_compute; reflexivity | ].
  split; [ | apply V293_target_fixture_spatial].
  eapply V293_star_load_r; [ | exact V293_target_fixture_spatial].
  intros s [Hm _]. eapply mapstoval_load; [apply V293_byte_type; lia | exact Hm].
Qed.
