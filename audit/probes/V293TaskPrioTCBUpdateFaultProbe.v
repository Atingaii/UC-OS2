(* Supplemental physical ablation, separate from the four literal roots.
   Only the first destination's permission bit changes; its byte is retained. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import Lia.
Local Open Scope nat_scope.
Definition normal_entry := V293_tcb_update_fixture_mem false 0 1.
Definition permission_fault := set normal_entry (41%positive,58%Z)
  (false,Byte (Byte.repr (Int.unsigned (Int.repr 8)))).
Example normal_first_field_has_exact_old_byte :
  get normal_entry (41%positive,58%Z) =
    Some (true,Byte (Byte.repr (Int.unsigned (Int.repr 8)))).
Proof.
  unfold normal_entry,V293_tcb_update_fixture_mem.
  repeat rewrite V293_put_byte_other by discriminate.
  apply V293_put_byte_get_same.
Qed.
Example permission_only_changed_at_first_field :
  get permission_fault (41%positive,58%Z) =
    Some (false,Byte (Byte.repr (Int.unsigned (Int.repr 8)))) /\
  (forall a, a <> (41%positive,58%Z) -> get permission_fault a = get normal_entry a).
Proof. split; unfold permission_fault; [apply map_get_set | intros; apply map_get_set'; congruence]. Qed.
Example normal_first_store_succeeds :
  store Tint8 normal_entry (41%positive,58%Z) (V293_byteval 6) =
    Some (V293_put_byte normal_entry (41%positive,58%Z) 6).
Proof. apply V293_put_byte_store with (old := Byte (Byte.repr (Int.unsigned (Int.repr 8)))).
  exact normal_first_field_has_exact_old_byte. Qed.
Example permission_fault_rejects_actual_first_store :
  store Tint8 permission_fault (41%positive,58%Z) (V293_byteval 6) = None.
Proof.
  unfold store,V293_byteval. cbn [encode_val encode_int inj_bytes List.map storebytes].
  unfold addr,offset,permission_fault. rewrite map_get_set. reflexivity.
Qed.
Example six_index_is_not_sixty_four_mask : forall M,
  load Tint8 M (41%positive,59%Z) = Some (V293_byteval 6) ->
  load Tint8 M (41%positive,59%Z) <> Some (V293_byteval 64).
Proof. intros M H. rewrite H. discriminate. Qed.
Print Assumptions normal_first_store_succeeds.
Print Assumptions permission_fault_rejects_actual_first_store.
Print Assumptions six_index_is_not_sixty_four_mask.
