(* A satisfiable selected-field assertion is not a complete TCB invariant.
   This witnesses a resource gap, not an initialized kernel execution. *)
Require Import CertiOS.audit.probes.V293TaskRecordOwnershipProbe.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293SharedStateWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTargetWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewWitness.
Require Import CertiOS.framework.include_frm.
Require Import Coq.Lists.List Lia.

Lemma SelectedSharedMemoryHoles : forall offset,
  offset = 20%Z \/ offset = 44%Z \/ offset = 49%Z ->
  get OwnershipSharedMemory (60%positive,offset) = None.
Proof.
  intros offset Cases. unfold OwnershipSharedMemory.
  rewrite map_merge_semp by reflexivity.
  assert (Pointer : get OwnershipPointerMemory (60%positive,offset) = None).
  { apply V293_encoded_memory_outside. left. discriminate. }
  assert (Records : get OwnershipMemory (60%positive,offset) = None).
  { apply OwnershipCellsOutside.
    destruct Cases as [Same | [Same | Same]]; subst offset;
      intro Member; vm_compute in Member; intuition congruence. }
  rewrite Pointer, Records. reflexivity.
Qed.

Theorem SelectedReadyDelayLoadFails :
  load Tint32 OwnershipSharedMemory (60%positive,44%Z) = None.
Proof.
  unfold load, loadm. change
    (match loadbytes OwnershipSharedMemory (60%positive,44%Z) 4 with
     | Some bytes => Some (decode_val Tint32 bytes) | None => None end = None).
  unfold loadbytes at 1.
  rewrite SelectedSharedMemoryHoles by auto. reflexivity.
Qed.

Theorem SelectedReadyNextLoadFails :
  load (Tcom_ptr 411%Z) OwnershipSharedMemory (60%positive,20%Z) = None.
Proof.
  unfold load, loadm. change
    (match loadbytes OwnershipSharedMemory (60%positive,20%Z) 4 with
     | Some bytes => Some (decode_val (Tcom_ptr 411%Z) bytes) | None => None end = None).
  unfold loadbytes at 1.
  rewrite SelectedSharedMemoryHoles by auto. reflexivity.
Qed.

Theorem SelectedReadyPendLoadFails :
  load Tint8 OwnershipSharedMemory (60%positive,49%Z) = None.
Proof.
  unfold load, loadm. change
    (match loadbytes OwnershipSharedMemory (60%positive,49%Z) 1 with
     | Some bytes => Some (decode_val Tint8 bytes) | None => None end = None).
  unfold loadbytes at 1.
  rewrite SelectedSharedMemoryHoles by auto. reflexivity.
Qed.

Theorem SelectedSharedOwnershipHasActualMissingBytes :
  V293_target_wstate V293_shared_fixture_ge emp OwnershipSharedMemory OwnershipSharedAbs |=
    V293_shared_task_records OwnershipReady OwnershipTasks (emp : EcbMod.map) Int.zero /\
  get OwnershipTasks OwnershipReady = Some (Int.repr 4,rdy,Vnull) /\
  load Tint32 OwnershipSharedMemory (60%positive,44%Z) = None /\
  load (Tcom_ptr 411%Z) OwnershipSharedMemory (60%positive,20%Z) = None /\
  load Tint8 OwnershipSharedMemory (60%positive,49%Z) = None.
Proof.
  split; [exact OwnershipSharedLiteralSpatial | ].
  split.
  - unfold OwnershipTasks. rewrite map_get_set' by discriminate. apply map_get_sig.
  - split; [exact SelectedReadyDelayLoadFails | ].
    split; [exact SelectedReadyNextLoadFails | exact SelectedReadyPendLoadFails].
Qed.

Theorem SelectedSharedOwnershipDoesNotImplyReadyDelayReadable :
  ~ (forall s,
      s |= V293_shared_task_records OwnershipReady OwnershipTasks (emp : EcbMod.map) Int.zero ->
      exists value, load Tint32 (getmem s) (60%positive,44%Z) = Some value).
Proof.
  intro Implication.
  destruct (Implication _ OwnershipSharedLiteralSpatial) as [value Read].
  change (load Tint32 OwnershipSharedMemory (60%positive,44%Z) = Some value) in Read.
  rewrite SelectedReadyDelayLoadFails in Read. discriminate.
Qed.

Print Assumptions SelectedReadyDelayLoadFails.
Print Assumptions SelectedReadyNextLoadFails.
Print Assumptions SelectedReadyPendLoadFails.
Print Assumptions SelectedSharedOwnershipHasActualMissingBytes.
Print Assumptions SelectedSharedOwnershipDoesNotImplyReadyDelayReadable.
