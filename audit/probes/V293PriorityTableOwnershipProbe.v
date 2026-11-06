(* Literal full 13-slot entry. This is not an initialized kernel or an API trace. *)
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewWitness.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.rulesoundlib.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.
Local Opaque HalfPermMap.set.

Definition PriorityEntries : list val :=
  [Vnull;Vnull;Vnull;Vnull;Vptr (60%positive,Int.zero);Vnull;Vnull;Vnull;
    Vptr (41%positive,Int.repr 8);Vnull;Vnull;Vnull;Vnull].
Definition PriorityBytes := flat_map (encode_val (Tptr V293_tcb_type)) PriorityEntries.
Definition PriorityMemory permission := V293_encoded_memory 20%positive 0%Z permission PriorityBytes.

Lemma PriorityEncodedNth : forall bytes b offset permission k,
  k < length bytes ->
  get (V293_encoded_memory b offset permission bytes) (b,(offset+Z.of_nat k)%Z) =
    Some (permission,nth k bytes Undef).
Proof.
  induction bytes as [ | byte rest IH]; intros b offset permission [ | k] Bound;
    cbn [length] in Bound; try lia.
  - replace (offset+Z.of_nat 0)%Z with offset by lia.
    cbn [V293_encoded_memory]. rewrite map_merge_semp by reflexivity.
    rewrite map_get_sig. rewrite V293_encoded_memory_outside by (right;left;lia). reflexivity.
  - cbn [V293_encoded_memory]. rewrite map_merge_semp by reflexivity.
    rewrite map_get_sig' by (intro Same;inversion Same;lia).
    replace (offset+Z.of_nat (S k))%Z with (offset+1+Z.of_nat k)%Z by lia.
    rewrite IH by lia. reflexivity.
Qed.

Lemma PriorityEntryWritable : V293_bytes_writable (PriorityMemory true) 20%positive 0%Z 52.
Proof.
  intros k Bound. exists (nth k PriorityBytes Undef).
  apply PriorityEncodedNth. vm_compute. exact Bound.
Qed.

Lemma PriorityEntryLoads : forall permission,
  V293_table_loads V293_tcb_type (PriorityMemory permission) 20%positive PriorityEntries.
Proof.
  intros permission p Bound.
  assert (Raw : loadbytes (PriorityMemory permission) (20%positive,(4*Z.of_nat p)%Z) 4 =
    Some (encode_val (Tptr V293_tcb_type) (nth p PriorityEntries Vnull))).
  { replace 4 with (length (encode_val (Tptr V293_tcb_type) (nth p PriorityEntries Vnull)))
      by (rewrite encode_val_length;reflexivity).
    apply V293_loadbytes_get. intros k K. exists permission.
    rewrite encode_val_length in K. change (k < 4) in K.
    replace (4*Z.of_nat p+Z.of_nat k)%Z with (0+Z.of_nat (4*p+k))%Z by lia.
    unfold PriorityMemory. rewrite PriorityEncodedNth by (change (4*p+k<52);lia).
    do 13 (destruct p as [ | p];
      [do 4 (destruct k as [ | k]; [vm_compute;reflexivity | ]);lia | ]). lia. }
  change (match loadbytes (PriorityMemory permission) (20%positive,(4*Z.of_nat p)%Z) 4 with
    | Some bs => Some (decode_val (Tptr V293_tcb_type) bs) | None => None end =
    Some (nth p PriorityEntries Vnull)).
  rewrite Raw.
  do 13 (destruct p as [ | p]; [vm_compute;reflexivity | ]). lia.
Qed.

Theorem PriorityLiteralOwned : forall ge le ir aux O op,
  (ge,le,PriorityMemory true,ir,aux,O,op) |= V293_owned_priority_table 20%positive PriorityEntries ** Atrue.
Proof.
  intros. apply V293_full_priority_table_entry.
  - reflexivity.
  - repeat constructor; reflexivity.
  - exact PriorityEntryWritable.
  - apply PriorityEntryLoads.
Qed.

Definition PriorityFinalEntries :=
  update_nth_val 6 (update_nth_val 8 PriorityEntries Vnull) (Vptr (41%positive,Int.repr 8)).

Theorem PriorityLiteralTwoStores : forall ge le ir aux O op,
  exists M1 M2,
    store (Tptr V293_tcb_type) (PriorityMemory true) (20%positive,32%Z) Vnull = Some M1 /\
    store (Tptr V293_tcb_type) M1 (20%positive,24%Z) (Vptr (41%positive,Int.repr 8)) = Some M2 /\
    (ge,le,M2,ir,aux,O,op) |= V293_owned_priority_table 20%positive PriorityFinalEntries ** Atrue /\
    V293_table_loads V293_tcb_type M2 20%positive PriorityFinalEntries.
Proof.
  intros ge le ir aux O op.
  pose proof (PriorityLiteralOwned ge le ir aux O op) as Entry.
  destruct (V293_full_priority_table_any_slot_store PriorityEntries 20%positive Atrue ge le (PriorityMemory true) ir aux O op eq_refl Entry 8 Vnull ltac:(lia) eq_refl)
    as [M1 [S1 Intermediate]].
  destruct (V293_full_priority_table_any_slot_store (update_nth_val 8 PriorityEntries Vnull) 20%positive Atrue ge le M1 ir aux O op eq_refl Intermediate 6
    (Vptr (41%positive,Int.repr 8)) ltac:(lia) eq_refl) as [M2 [S2 _]].
  assert (Final : (ge,le,M2,ir,aux,O,op) |=
    V293_owned_priority_table 20%positive PriorityFinalEntries ** Atrue).
  { eapply V293_full_priority_table_two_stores; [reflexivity | lia | lia | exact Entry | exact S1 | exact S2]. }
  exists M1. exists M2. split; [exact S1 | ]. split; [exact S2 | ].
  split; [exact Final | ]. eapply V293_full_priority_table_loads; [reflexivity | exact Final].
Qed.

Theorem PriorityAll13RemainWritable : forall ge le M ir aux O op,
  (ge,le,M,ir,aux,O,op) |= V293_owned_priority_table 20%positive PriorityFinalEntries ** Atrue ->
  forall p, p < 13 -> exists Mf,
    store (Tptr V293_tcb_type) M (20%positive,(4*Z.of_nat p)%Z) Vnull = Some Mf /\
    (ge,le,Mf,ir,aux,O,op) |=
      V293_owned_priority_table 20%positive (update_nth_val p PriorityFinalEntries Vnull) ** Atrue.
Proof.
  intros. eapply V293_full_priority_table_any_slot_store; [reflexivity | exact H | exact H0 | reflexivity].
Qed.

Theorem PriorityStaleAndUntouched : forall M,
  V293_table_loads V293_tcb_type M 20%positive PriorityFinalEntries ->
  load (Tptr V293_tcb_type) M (20%positive,32%Z) = Some Vnull /\
  load (Tptr V293_tcb_type) M (20%positive,24%Z) = Some (Vptr (41%positive,Int.repr 8)) /\
  load (Tptr V293_tcb_type) M (20%positive,16%Z) = Some (Vptr (60%positive,Int.zero)) /\
  ~ V293_table_loads V293_tcb_type M 20%positive PriorityEntries.
Proof.
  intros M Loads. pose proof (Loads 8 ltac:(lia)) as Old.
  pose proof (Loads 6 ltac:(lia)) as New. pose proof (Loads 4 ltac:(lia)) as Untouched.
  split; [exact Old | ]. split; [exact New | ]. split; [exact Untouched | ].
  intro Stale. specialize (Stale 8 ltac:(lia)). rewrite Old in Stale. discriminate.
Qed.

Theorem PriorityReadOnlyIsNotWritable :
  V293_table_loads V293_tcb_type (PriorityMemory false) 20%positive PriorityEntries /\
  store (Tptr V293_tcb_type) (PriorityMemory false) (20%positive,0%Z) Vnull = None /\
  ~ V293_bytes_writable (PriorityMemory false) 20%positive 0%Z 52.
Proof.
  assert (Half : get (PriorityMemory false) (20%positive,0%Z) = Some (false,MNull)).
  { exact (PriorityEncodedNth PriorityBytes 20%positive 0%Z false 0 ltac:(vm_compute;lia)). }
  split; [apply PriorityEntryLoads | ]. split.
  - change (storebytes (PriorityMemory false) (20%positive,0%Z)
      (MNull :: MNull :: MNull :: MNull :: nil) = None).
    unfold storebytes at 1. unfold addr,offset,block in *. rewrite Half. reflexivity.
  - intro W. destruct (W 0 ltac:(lia)) as [v Full].
    replace (0+Z.of_nat 0)%Z with 0%Z in Full by lia. unfold addr,offset,block in *. rewrite Half in Full. discriminate.
Qed.

Theorem PriorityTwoSlotsAreNotFullTable :
  V293_bytes_writable V293_rekey_fixture_memory 20%positive 32%Z 4 /\
  V293_bytes_writable V293_rekey_fixture_memory 20%positive 24%Z 4 /\
  ~ V293_bytes_writable V293_rekey_fixture_memory 20%positive 0%Z 52.
Proof.
  assert (Touched : forall offset, offset = 32%Z \/ offset = 24%Z ->
    V293_bytes_writable V293_rekey_fixture_memory 20%positive offset 4).
  { intros offset Choice k Bound. destruct Choice as [-> | ->].
    all: do 4 (destruct k as [ | k];
      [eexists; unfold V293_rekey_fixture_memory,addr,offset,block;
       repeat first [rewrite map_get_set | rewrite map_get_set' by (intro E;inversion E;lia)];reflexivity | ]); lia. }
  split; [apply Touched;left;reflexivity | ].
  split; [apply Touched;right;reflexivity | ].
  intro W. destruct (W 0 ltac:(lia)) as [raw Full].
  unfold V293_rekey_fixture_memory,addr,offset,block in Full.
  repeat rewrite map_get_set' in Full by (intro E;inversion E;lia).
  rewrite map_emp_get in Full. discriminate.
Qed.

Print Assumptions PriorityLiteralOwned.
Print Assumptions PriorityLiteralTwoStores.
Print Assumptions PriorityAll13RemainWritable.
Print Assumptions PriorityStaleAndUntouched.
Print Assumptions PriorityReadOnlyIsNotWritable.

Print Assumptions PriorityTwoSlotsAreNotFullTable.
