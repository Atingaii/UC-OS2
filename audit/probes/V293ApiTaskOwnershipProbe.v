(* Literal full-return entry. Only entry construction and generic spatial
   lemmas are reused; no completed trace is used as an execution oracle. *)
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.audit.probes.V293TaskRecordsProbe.
Require Import CertiOS.audit.probes.V293TaskRecordOwnershipProbe.
Require Import CertiOS.audit.probes.V293CurrentConsistencyProbe.
Require Import CertiOS.tactics.basetac.join_lib.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewWitness.
Require Import CertiOS.audit.probes.V293EventDataProbe.
Require Import CertiOS.audit.probes.V293EventQueueProbe.
Require Import CertiOS.audit.probes.V293WaitPayloadProbe.
Require Import CertiOS.audit.probes.V293WaitEventOwnedProbe.
Require Import CertiOS.audit.probes.V293SuccessCompleteReturnProbe.
Require Import CertiOS.audit.probes.V293SuccessEntryWitnessProbe.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.proofs.V293SharedStateWitness.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewExec.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import Coq.Lists.List Lia.
Require Import Coq.Relations.Relation_Operators.
Require Import CertiOS.framework.proof.rulesoundlib.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.framework.proof.cstepLib.
Require Import CertiOS.certiucos.v293.code.V293OSSchedGuards.
Require Import CertiOS.certiucos.v293.code.V293OSSchedDispatch.
Require Import CertiOS.certiucos.v293.code.V293OSSchedChange.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTarget.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Import ListNotations.
Local Open Scope nat_scope.
Local Opaque HalfPermMap.set.


Require Import CertiOS.audit.probes.V293CurrentOwnershipProbe.
Definition ApiTarget : tid := (41%positive,Int.repr 8).
Definition ApiCells := V293_record_layout ApiTarget 8 (wait expected_wait_reason Int.one) expected_payload_message 0.
Definition ApiRecordMemory := OwnershipCellsMemory ApiCells.
Lemma ApiCellsSeparated : OwnershipCellsSeparated ApiCells.
Proof. vm_compute. repeat split; intros; intuition congruence. Qed.
Lemma ApiCellsValid : Forall
  (fun cell => let '(_,tp,v) := cell in rule_type_val_match tp v = true) ApiCells.
Proof. repeat constructor; vm_compute; reflexivity. Qed.
Lemma ApiRecordSpatial : forall ge le ir aux op,
  (ge,le,ApiRecordMemory,ir,aux,emp,op) |=
    V293_owned_task_record ApiTarget (Int.repr 8) (wait expected_wait_reason Int.one) expected_payload_message.
Proof.
  intros. pose proof (OwnershipCellsSpatial _ ApiCellsSeparated ApiCellsValid ge le) as Cells.
  assert (Record : V293_wstate ge le ApiRecordMemory |=
    V293_owned_task_record ApiTarget (Int.repr 8) (wait expected_wait_reason Int.one) expected_payload_message).
  { exists 8. exists 0. apply astar_l_apure_intro; [exact Cells | repeat split; reflexivity || lia]. }
  exact (proj2 (proj2 (V293_owned_task_record_block_local _ _ _ _ _ _ _ _ _ _ _ Record)) ge le ir aux op).
Qed.
Lemma ApiEncodedNth : forall bytes b offset k,
  k < length bytes ->
  get (V293_encoded_memory b offset true bytes) (b,(offset+Z.of_nat k)%Z) =
    Some (true,nth k bytes Undef).
Proof.
  induction bytes as [ | byte rest IH]; intros b offset [ | k] Bound; cbn [length] in Bound; try lia.
  - replace (offset+Z.of_nat 0)%Z with offset by lia.
    eapply join_get_get_l_true; [reflexivity | apply V293_encoded_memory_join | apply map_get_sig | reflexivity].
  - replace (offset+Z.of_nat (S k))%Z with ((offset+1)+Z.of_nat k)%Z by lia.
    eapply join_get_get_r_true; [reflexivity | apply V293_encoded_memory_join | apply IH;lia | reflexivity].
Qed.
Lemma ApiCellsByte : forall cells cell a v,
  OwnershipCellsSeparated cells -> In cell cells ->
  get (OwnershipCellMemory cell) a = Some (true,v) ->
  get (OwnershipCellsMemory cells) a = Some (true,v).
Proof.
  induction cells as [ | head rest IH]; intros cell a v Separated Member Byte; [contradiction | ].
  destruct Separated as [Apart Sep]. destruct Member as [Same | Member].
  - subst head. eapply join_get_get_l_true;
      [reflexivity | apply OwnershipCellsJoin;exact Apart | exact Byte | reflexivity].
  - eapply join_get_get_r_true;
      [reflexivity | apply OwnershipCellsJoin;exact Apart | eapply IH;eassumption | reflexivity].
Qed.
Lemma ApiRecordByte : forall cell a v,
  In cell ApiCells -> get (OwnershipCellMemory cell) a = Some (true,v) ->
  get ApiRecordMemory a = Some (true,v).
Proof. intros. eapply ApiCellsByte; [exact ApiCellsSeparated | eassumption | eassumption]. Qed.
Lemma ApiSubByteCondition : forall (v:memval) (x:option (bool*memval)),
  x=Some (true,v) ->
  match x with
  | Some b => if @isRw addr (bool*memval) mem memMap (true,v)
      then if @isRw addr (bool*memval) mem memMap b then (true,v)=b
        else (true,v)= @flip addr (bool*memval) mem memMap b
      else if @isRw addr (bool*memval) mem memMap b then False else (true,v)=b
  | None => True end.
Proof. intros v x E. subst x. reflexivity. Qed.
Lemma ApiRecordOutside : forall a,
  ~ In a (OwnershipCellsAddresses ApiCells) -> get ApiRecordMemory a = None.
Proof. intros. unfold ApiRecordMemory. apply OwnershipCellsOutside. assumption. Qed.
Local Opaque ApiRecordMemory.
Lemma ApiRecordSub : Maps.sub ApiRecordMemory RecordProbeMemory.
Proof.
  apply sub_semp; [reflexivity | ]. intros [c i].
  destruct (in_dec addr_eq_dec (c,i) (OwnershipCellsAddresses ApiCells)) as [Member | Outside].
  - vm_compute in Member.
    repeat match goal with H : _ \/ _ |- _ => destruct H end; try contradiction.
    all: match goal with E : (_,_) = (_,_) |- _ => inversion E; subst end.
    all: rewrite RecordProbeGetFrame by discriminate.
    all: rewrite CurrentProbeGetFrame by discriminate.
    all: rewrite EventDataProbeGetFrame by (left;discriminate).
    all: unfold expected_payload_entry_mem,expected_wait_entry_mem,
      V293_entry_update_fixture_mem,V293_coordinate_fixture_mem,
      V293_tcb_update_fixture_mem,V293_prefix_event_nonnull_mem,V293_event_fixture_mem.
    all: repeat first
      [ rewrite V293_put_byte_other by discriminate
      | rewrite V293_put_byte_get_same
      | rewrite V293_fixture_bytes_outside by
          (rewrite encode_val_length; cbn [typelen]; first [left;discriminate | right;left;lia | right;right;lia])
      | match goal with |- context [get (V293_fixture_put_bytes ?m ?b ?start ?bytes) (?b,?off)] =>
          let k := eval vm_compute in (Z.to_nat (off-start)%Z) in
          rewrite (V293_fixture_bytes_nth bytes m b start k ltac:(vm_compute;lia)) end ].
    all: repeat first [rewrite map_get_set | rewrite map_get_set' by discriminate
      | rewrite V293_put_byte_other by discriminate | rewrite V293_put_byte_get_same
      | match goal with |- context [get (V293_fixture_put_bytes ?m ?b ?start ?bytes) ?a] =>
          let value := eval vm_compute in bytes in
          change (V293_fixture_put_bytes m b start bytes) with (V293_fixture_put_bytes m b start value);
          cbn [V293_fixture_put_bytes] end ].
    all: apply ApiSubByteCondition.
    all: first [
      solve [eapply ApiRecordByte with (cell:=((41%positive,58%Z),(Tint8),(V293_byteval 8)));
        [vm_compute;intuition congruence | unfold OwnershipCellMemory;
         exact (ApiEncodedNth (encode_val (Tint8) (V293_byteval 8)) 41%positive 58%Z 0 ltac:(vm_compute;lia))]]
    | solve [eapply ApiRecordByte with (cell:=((41%positive,60%Z),(Tint8),(V293_byteval 1)));
        [vm_compute;intuition congruence | unfold OwnershipCellMemory;
         exact (ApiEncodedNth (encode_val (Tint8) (V293_byteval 1)) 41%positive 60%Z 0 ltac:(vm_compute;lia))]]
    | solve [eapply ApiRecordByte with (cell:=((41%positive,59%Z),(Tint8),(V293_byteval 0)));
        [vm_compute;intuition congruence | unfold OwnershipCellMemory;
         exact (ApiEncodedNth (encode_val (Tint8) (V293_byteval 0)) 41%positive 59%Z 0 ltac:(vm_compute;lia))]]
    | solve [eapply ApiRecordByte with (cell:=((41%positive,62%Z),(Tint8),(V293_byteval 2)));
        [vm_compute;intuition congruence | unfold OwnershipCellMemory;
         exact (ApiEncodedNth (encode_val (Tint8) (V293_byteval 2)) 41%positive 62%Z 0 ltac:(vm_compute;lia))]]
    | solve [eapply ApiRecordByte with (cell:=((41%positive,61%Z),(Tint8),(V293_byteval 1)));
        [vm_compute;intuition congruence | unfold OwnershipCellMemory;
         exact (ApiEncodedNth (encode_val (Tint8) (V293_byteval 1)) 41%positive 61%Z 0 ltac:(vm_compute;lia))]]
    | solve [eapply ApiRecordByte with (cell:=((41%positive,40%Z),(Tptr Tvoid),(expected_payload_message)));
        [vm_compute;intuition congruence | unfold OwnershipCellMemory;
         exact (ApiEncodedNth (encode_val (Tptr Tvoid) (expected_payload_message)) 41%positive 40%Z 0 ltac:(vm_compute;lia))]]
    | solve [eapply ApiRecordByte with (cell:=((41%positive,40%Z),(Tptr Tvoid),(expected_payload_message)));
        [vm_compute;intuition congruence | unfold OwnershipCellMemory;
         exact (ApiEncodedNth (encode_val (Tptr Tvoid) (expected_payload_message)) 41%positive 40%Z 1 ltac:(vm_compute;lia))]]
    | solve [eapply ApiRecordByte with (cell:=((41%positive,40%Z),(Tptr Tvoid),(expected_payload_message)));
        [vm_compute;intuition congruence | unfold OwnershipCellMemory;
         exact (ApiEncodedNth (encode_val (Tptr Tvoid) (expected_payload_message)) 41%positive 40%Z 2 ltac:(vm_compute;lia))]]
    | solve [eapply ApiRecordByte with (cell:=((41%positive,40%Z),(Tptr Tvoid),(expected_payload_message)));
        [vm_compute;intuition congruence | unfold OwnershipCellMemory;
         exact (ApiEncodedNth (encode_val (Tptr Tvoid) (expected_payload_message)) 41%positive 40%Z 3 ltac:(vm_compute;lia))]]
    | solve [eapply ApiRecordByte with (cell:=((41%positive,56%Z),(Tint8),(V293_byteval 1)));
        [vm_compute;intuition congruence | unfold OwnershipCellMemory;
         exact (ApiEncodedNth (encode_val (Tint8) (V293_byteval 1)) 41%positive 56%Z 0 ltac:(vm_compute;lia))]]
    | solve [eapply ApiRecordByte with (cell:=((41%positive,52%Z),(Tint32),(Vint32 Int.one)));
        [vm_compute;intuition congruence | unfold OwnershipCellMemory;
         exact (ApiEncodedNth (encode_val (Tint32) (Vint32 Int.one)) 41%positive 52%Z 0 ltac:(vm_compute;lia))]]
    | solve [eapply ApiRecordByte with (cell:=((41%positive,52%Z),(Tint32),(Vint32 Int.one)));
        [vm_compute;intuition congruence | unfold OwnershipCellMemory;
         exact (ApiEncodedNth (encode_val (Tint32) (Vint32 Int.one)) 41%positive 52%Z 1 ltac:(vm_compute;lia))]]
    | solve [eapply ApiRecordByte with (cell:=((41%positive,52%Z),(Tint32),(Vint32 Int.one)));
        [vm_compute;intuition congruence | unfold OwnershipCellMemory;
         exact (ApiEncodedNth (encode_val (Tint32) (Vint32 Int.one)) 41%positive 52%Z 2 ltac:(vm_compute;lia))]]
    | solve [eapply ApiRecordByte with (cell:=((41%positive,52%Z),(Tint32),(Vint32 Int.one)));
        [vm_compute;intuition congruence | unfold OwnershipCellMemory;
         exact (ApiEncodedNth (encode_val (Tint32) (Vint32 Int.one)) 41%positive 52%Z 3 ltac:(vm_compute;lia))]]
    | solve [eapply ApiRecordByte with (cell:=((41%positive,57%Z),(Tint8),(V293_byteval 0)));
        [vm_compute;intuition congruence | unfold OwnershipCellMemory;
         exact (ApiEncodedNth (encode_val (Tint8) (V293_byteval 0)) 41%positive 57%Z 0 ltac:(vm_compute;lia))]]
    | solve [eapply ApiRecordByte with (cell:=((41%positive,36%Z),(Tcom_ptr 411%Z),(Vptr (72%positive,Int.repr 5))));
        [vm_compute;intuition congruence | unfold OwnershipCellMemory;
         exact (ApiEncodedNth (encode_val (Tcom_ptr 411%Z) (Vptr (72%positive,Int.repr 5))) 41%positive 36%Z 0 ltac:(vm_compute;lia))]]
    | solve [eapply ApiRecordByte with (cell:=((41%positive,36%Z),(Tcom_ptr 411%Z),(Vptr (72%positive,Int.repr 5))));
        [vm_compute;intuition congruence | unfold OwnershipCellMemory;
         exact (ApiEncodedNth (encode_val (Tcom_ptr 411%Z) (Vptr (72%positive,Int.repr 5))) 41%positive 36%Z 1 ltac:(vm_compute;lia))]]
    | solve [eapply ApiRecordByte with (cell:=((41%positive,36%Z),(Tcom_ptr 411%Z),(Vptr (72%positive,Int.repr 5))));
        [vm_compute;intuition congruence | unfold OwnershipCellMemory;
         exact (ApiEncodedNth (encode_val (Tcom_ptr 411%Z) (Vptr (72%positive,Int.repr 5))) 41%positive 36%Z 2 ltac:(vm_compute;lia))]]
    | solve [eapply ApiRecordByte with (cell:=((41%positive,36%Z),(Tcom_ptr 411%Z),(Vptr (72%positive,Int.repr 5))));
        [vm_compute;intuition congruence | unfold OwnershipCellMemory;
         exact (ApiEncodedNth (encode_val (Tcom_ptr 411%Z) (Vptr (72%positive,Int.repr 5))) 41%positive 36%Z 3 ltac:(vm_compute;lia))]] ].
  - rewrite ApiRecordOutside by exact Outside.
    destruct (@get addr (bool*memval) mem memMap RecordProbeMemory (c,i)); exact I.
Qed.
Local Opaque HalfPermMap.set.
Lemma ApiEntryRecord : forall le ir aux O op,
  (CurrentProbeGE,le,RecordProbeMemory,ir,aux,O,op) |=
    V293_owned_task_record ApiTarget (Int.repr 8) (wait expected_wait_reason Int.one) expected_payload_message ** Atrue.
Proof.
  intros. destruct ApiRecordSub as [rest Joined].
  apply sat_split'. exists ApiRecordMemory. exists rest. exists (emp:osabst). exists O.
  split; [exact Joined | ]. split; [apply map_join_comm; apply map_join_emp | ].
  split; [apply ApiRecordSpatial | exact I].
Qed.
Lemma ApiEntryJoint : forall le ir aux now op,
  (CurrentProbeGE,le,RecordProbeMemory,ir,aux,
    V293_shared_fixture_abs (60%positive,Int.zero) expected_payload_tasks expected_queue_events now,op) |=
    V293_shared_fields (60%positive,Int.zero) expected_payload_tasks expected_queue_events now **
      (V293_owned_task_record ApiTarget (Int.repr 8) (wait expected_wait_reason Int.one) expected_payload_message ** Atrue).
Proof.
  intros. assert (Fields : (CurrentProbeGE,le,RecordProbeMemory,ir,aux,
    V293_shared_fixture_abs (60%positive,Int.zero) expected_payload_tasks expected_queue_events now,op) |=
    V293_shared_fields (60%positive,Int.zero) expected_payload_tasks expected_queue_events now ** Atrue).
  { eapply V293_shared_fields_heap_lift; [ | apply map_join_emp].
    eapply V293_shared_fields_rebase. apply V293_shared_fixture_fields. }
  pose proof (V293_owned_task_fields_reconstruct _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (ApiEntryRecord le ir aux _ op) Fields) as Joint.
  apply astar_assoc_elim.
  eapply astar_mono; [intros s H; apply astar_comm; exact H | intros s H; exact H | exact Joint].
Qed.
Local Ltac complete_entry_bind :=
  unfold V293_complete_fixture_ge,V293_entry_update_fixture_ge,V293_tcb_update_fixture_le,
    V293_event_fixture_le,V293_prefix_fixture_ge,V293_prefix_fixture_le,
    V293_read_ready_fixture_le,V293_ready_fragment_fixture_le;
  repeat first [rewrite map_get_set | rewrite map_get_set' by discriminate]; reflexivity.
Local Ltac complete_entry_get :=
  unfold V293_tcb_update_fixture_mem;
  repeat first [rewrite V293_put_byte_other by discriminate | rewrite V293_put_byte_get_same].
Local Ltac complete_entry_load :=
  unfold V293_tcb_update_fixture_mem;
  repeat rewrite V293_put_byte_other_load by discriminate;
  apply V293_put_byte_load; lia.


Theorem ApiOwnedFullReturn : forall sc now op ir enabled si ci,
  exists Mf OO',
  spec_step sc (spec_prim nil (expected_wait_step (41%positive,Int.repr 8) 8 6))
    (V293_shared_fixture_abs (60%positive,Int.zero) expected_payload_tasks expected_queue_events now)
    (spec_done (Some (Vint32 Int.zero))) OO' /\
  V293_local_steps V293_success_tail_fixture_program
    (curs (sseq (expected_success_program
      500%Z 501%Z 502%Z 400%Z 300%Z 301%Z 302%Z 303%Z 304%Z 305%Z 306%Z 307%Z 600%Z 601%Z OSTCBCur 900%Z)
      (expected_tail 1001%Z 999%Z)),(kenil,kcall 700%Z sret emp kstop))
    ((CurrentProbeGE,V293_tcb_update_fixture_le,RecordProbeMemory),ir,(enabled,si,ci))
    (curs (sskip (Some (Vint32 Int.zero))),(kenil,kstop))
    ((CurrentProbeGE,emp,Mf),ir,(enabled,si,ci)) /\
  V293_tcb_updated_loads Mf 41%positive 8%Z 6 /\
  V293_rekey_bitmap_loads Mf 30%positive 31%positive 16 0 1 /\
  V293_table_loads V293_tcb_type Mf 50%positive
    (update_nth_val 6 (update_nth_val 8 V293_prefix_fixture_entries Vnull)
      (Vptr (41%positive,Int.repr 8))) /\
  V293_event_bitmap_loads Mf 72%positive 5%Z 64 0 1 /\
  load (Tcom_ptr 411%Z) Mf (41%positive,36%Z) = Some (Vptr (72%positive,Int.repr 5)) /\
  (forall c ty k, In (c,ty) (getaddr V293_tcb_update_fixture_le) -> k < typelen ty ->
    get Mf (c,Z.of_nat k) = None) /\
  (CurrentProbeGE,emp,Mf,ir,(enabled,si,ci),OO',op) |=
    (V293_owned_task_record ApiTarget (Int.repr 6) (wait expected_wait_reason Int.one) expected_payload_message **
      V293_shared_fields (60%positive,Int.zero) expected_payload_tasks_updated expected_queue_events now) ** Atrue /\
  get expected_payload_tasks_updated ApiTarget = Some (Int.repr 6,wait expected_wait_reason Int.one,expected_payload_message).

Proof.
  intros sc now op ir enabled si ci.
  destruct expected_payload_fixture_relations as (EntryTable & EntryBitmap & EntryEvent & EntryTask).
  destruct (V293_prefix_event_nonnull_entry false 0 1 ltac:(lia) ltac:(lia))
    as (Lp & Event & We & Fields & View & Wo & Wn & Wy & Wby & Wx & Loads & W & NewLoc & Lo & Ln & Initial & ELoads & EW).
  set (M := V293_entry_update_fixture_mem true false 0 1).
  assert (CF : forall c i, c<>51%positive -> c<>40%positive -> c<>80%positive ->
    get M (c,i) = get (V293_coordinate_fixture_mem false 0 1) (c,i)).
  { intros. apply V293_entry_update_fixture_frame; assumption. }
  assert (LF : forall tp c i, c<>51%positive -> c<>40%positive -> c<>80%positive ->
    load tp M (c,i) = load tp (V293_coordinate_fixture_mem false 0 1) (c,i)).
  { intros. apply V293_load_block_frame. intro j. apply CF; assumption. }
  assert (RF : forall tp c i, c <> 41%positive -> c <> 73%positive -> c <> 33%positive -> c <> 37%positive -> c <> 35%positive ->
    c<>51%positive -> c<>40%positive -> c<>80%positive ->
    load tp M (c,i) = load tp (V293_prefix_event_nonnull_mem false 0 1) (c,i)).
  { intros. rewrite LF by assumption. apply V293_load_block_frame. intro j.
    rewrite V293_coordinate_fixture_delta by (intro E; inversion E; congruence).
    apply V293_tcb_update_fixture_outside; [assumption | left; assumption]. }
  assert (HEvent : load (Tcom_ptr 411%Z) M (41%positive,36%Z) = Some (Vptr (72%positive,Int.repr 5))).
  { unfold load,loadm. rewrite (V293_loadbytes_ext _ (V293_prefix_event_nonnull_mem false 0 1) M).
    - exact Event.
    - intros k K. cbn [typelen] in K.
      unfold M. rewrite V293_entry_update_fixture_frame by discriminate. rewrite V293_coordinate_fixture_delta by (intro Eq; inversion Eq; discriminate).
      apply V293_tcb_update_fixture_outside; [discriminate | right; left; lia]. }
  assert (HFields : V293_tcb_old_loads M 41%positive 8%Z 1 2 1).
  { unfold V293_tcb_old_loads; repeat rewrite LF by discriminate; unfold V293_coordinate_fixture_mem; repeat rewrite V293_put_byte_other_load by discriminate; repeat split; complete_entry_load. }
  assert (HView : V293_table_loads V293_tcb_type M 50%positive V293_prefix_fixture_entries).
  { intros p R. rewrite RF by discriminate. exact (View p R). }
  assert (HWo : V293_bytes_writable M 50%positive 32%Z 4).
  { intros k K. unfold M; repeat rewrite V293_entry_update_fixture_frame by discriminate; repeat rewrite V293_coordinate_fixture_delta by (intro Eq; inversion Eq; discriminate); rewrite V293_tcb_update_fixture_outside by (try discriminate; left; discriminate). exact (Wo k K). }
  assert (HWn : V293_bytes_writable M 50%positive 24%Z 4).
  { intros k K. unfold M; repeat rewrite V293_entry_update_fixture_frame by discriminate; repeat rewrite V293_coordinate_fixture_delta by (intro Eq; inversion Eq; discriminate); rewrite V293_tcb_update_fixture_outside by (try discriminate; left; discriminate). exact (Wn k K). }
  assert (HWe : V293_bytes_writable M 70%positive 0%Z 4).
  { intros k K. unfold M; repeat rewrite V293_entry_update_fixture_frame by discriminate; repeat rewrite V293_coordinate_fixture_delta by (intro Eq; inversion Eq; discriminate); rewrite V293_tcb_update_fixture_outside by (try discriminate; left; discriminate). exact (We k K). }
  assert (HWy : exists v, get M (32%positive,0%Z) = Some (true,v)).
  { unfold M; repeat rewrite V293_entry_update_fixture_frame by discriminate; repeat rewrite V293_coordinate_fixture_delta by (intro Eq; inversion Eq; discriminate); rewrite V293_tcb_update_fixture_outside by (try discriminate; left; discriminate). exact Wy. }
  assert (HWby : exists v, get M (36%positive,0%Z) = Some (true,v)).
  { unfold M; repeat rewrite V293_entry_update_fixture_frame by discriminate; repeat rewrite V293_coordinate_fixture_delta by (intro Eq; inversion Eq; discriminate); rewrite V293_tcb_update_fixture_outside by (try discriminate; left; discriminate). exact Wby. }
  assert (HWx : exists v, get M (34%positive,0%Z) = Some (true,v)).
  { unfold M; repeat rewrite V293_entry_update_fixture_frame by discriminate; repeat rewrite V293_coordinate_fixture_delta by (intro Eq; inversion Eq; discriminate); rewrite V293_tcb_update_fixture_outside by (try discriminate; left; discriminate). exact Wx. }
  assert (HLoads : V293_rekey_bitmap_loads M 30%positive 31%positive 16 (if false then 1 else 0)
    (V293_ready_group 16 (if false then 1 else 0))).
  { unfold V293_rekey_bitmap_loads in *. repeat rewrite RF by discriminate. exact Loads. }
  assert (HW : V293_rekey_bitmap_writable M 30%positive 31%positive).
  { unfold V293_rekey_bitmap_writable in *.
    unfold M; repeat rewrite V293_entry_update_fixture_frame by discriminate; repeat rewrite V293_coordinate_fixture_delta by (intro Eq; inversion Eq; discriminate); repeat rewrite V293_tcb_update_fixture_outside by (try discriminate; left; discriminate). exact W. }
  assert (HELoads : V293_event_bitmap_loads M 72%positive 5%Z 0 1 (V293_ready_group 0 1)).
  { unfold V293_event_bitmap_loads in *. repeat rewrite RF by discriminate. exact ELoads. }
  assert (HEW : V293_event_bitmap_writable M 72%positive 5%Z).
  { unfold V293_event_bitmap_writable in *.
    unfold M; repeat rewrite V293_entry_update_fixture_frame by discriminate; repeat rewrite V293_coordinate_fixture_delta by (intro Eq; inversion Eq; discriminate); repeat rewrite V293_tcb_update_fixture_outside by (try discriminate; left; discriminate). exact EW. }
  assert (HLn : load Tint8 M (52%positive,0%Z) = Some (V293_byteval 6)).
  { rewrite RF by discriminate. exact Ln. }
  assert (HTW : V293_tcb_update_writable M 41%positive 8%Z).
  { intros d D. assert (d=50 \/ d=51 \/ d=52 \/ d=53 \/ d=54)%Z by lia.
    destruct H as [-> | [-> | [-> | [-> | ->]]]]; unfold M; repeat rewrite V293_entry_update_fixture_frame by discriminate; repeat rewrite V293_coordinate_fixture_delta by (intro Eq; inversion Eq; discriminate);
      eexists; complete_entry_get; reflexivity. }
  assert (CW : V293_bytes_writable M 40%positive 0%Z 4).
  { intros k K. unfold M,V293_entry_update_fixture_mem.
    rewrite V293_put_byte_other by discriminate.
    rewrite V293_fixture_bytes_outside by (left; discriminate).
    eexists. apply V293_fixture_bytes_nth. rewrite encode_val_length; exact K. }
  assert (Addresses : getaddr V293_tcb_update_fixture_le =
    [(32%positive,Tint8);(33%positive,Tint8);(34%positive,Tint8);(35%positive,Tint8);
     (36%positive,Tint8);(37%positive,Tint8);(40%positive,Tptr V293_tcb_type);
     (51%positive,Tint8);(52%positive,Tint8);(70%positive,Tptr V293_event_type);(73%positive,Tint8)]) by reflexivity.
  assert (CoordsW : forall c, In c [33%positive;73%positive;37%positive;35%positive] ->
    exists v, get M (c,0%Z) = Some (true,v)).
  { intros c Cases. destruct Cases as [E | [E | [E | [E | F]]]];try contradiction;subst c;
      rewrite CF by discriminate; unfold V293_coordinate_fixture_mem;
      repeat rewrite V293_put_byte_other by discriminate;eexists;apply V293_put_byte_get_same. }
  assert (NewW : exists v,get M (52%positive,0%Z)=Some(true,v)).
  { unfold M.
    rewrite V293_entry_update_fixture_frame by discriminate.
    rewrite V293_coordinate_fixture_delta by (intro E;inversion E;discriminate).
    rewrite V293_tcb_update_fixture_outside by (try discriminate;left;discriminate).
    rewrite V293_prefix_event_nonnull_outside by discriminate.
    rewrite V293_event_fixture_outside by (try discriminate;left;discriminate).
    unfold V293_prefix_fixture_mem. eexists;apply V293_put_byte_get_same. }
  assert (AllWritable : forall c ty, In (c,ty) (getaddr V293_tcb_update_fixture_le) ->
    V293_bytes_writable (RecordProbeMemory) c 0%Z (typelen ty)).
  { intros c ty I. rewrite Addresses in I.
    repeat destruct I as [E|I];try contradiction;inversion E;subst c ty.
    all: intros k K; try solve [cbn [typelen] in K; assert (k=0) by lia; subst k;
      rewrite RecordProbeGetFrame by discriminate; unfold CurrentProbeMemory; eexists; apply V293_put_byte_get_same]; repeat rewrite RecordProbeGetFrame by discriminate;repeat rewrite CurrentProbeGetFrame by discriminate;repeat rewrite EventDataProbeGetFrame by (first [left;discriminate | right;lia]);rewrite expected_payload_entry_get_frame by (try (left;discriminate);right;lia);repeat rewrite expected_wait_entry_get_frame by discriminate.
    all: try solve [exact(CW k K)|exact(HWe k K)].
    all: cbn [typelen] in K;assert(k=0) by lia;subst k;cbn [Z.of_nat Z.add];
      first [assumption | apply CoordsW;cbn;tauto]. }
  destruct (V293_critical_wait_record_owned_execution V293_success_tail_fixture_program
    (kcall 700%Z sret emp kstop) CurrentProbeGE V293_tcb_update_fixture_le emp
    (RecordProbeMemory) ir enabled si ci
    500%Z 501%Z 502%Z 400%Z 300%Z 301%Z 302%Z 303%Z 304%Z 305%Z 306%Z 307%Z
    50%positive 51%positive 52%positive 40%positive 41%positive 32%positive 36%positive 34%positive
    8%Z 30%positive 31%positive 16 0 8 6 V293_prefix_fixture_entries
    600%Z 70%positive 72%positive 5%Z 0 1 601%Z 73%positive 33%positive 37%positive 35%positive
    OSTCBCur 900%Z 80%positive 41%positive 8%Z 99%positive 8
    1001%Z 100%positive 1 999%Z 1004%Z 1002%Z 1003%Z 1005%Z 1006%Z 1007%Z 1008%Z 1009%Z
    700%Z sret kstop
    sc (60%positive,Int.zero) expected_payload_tasks expected_queue_events now
    (V293_shared_fixture_abs (60%positive,Int.zero) expected_payload_tasks expected_queue_events now)
    emp (V293_shared_fixture_abs (60%positive,Int.zero) expected_payload_tasks expected_queue_events now)
    op Atrue expected_wait_reason Int.one expected_payload_message)
    as (Mf & Os' & OO' & Identity & AbstractFrame & Abstract & Physical & Joint & FinalBitmap & FinalTable & FinalEvent).

  all: try solve [assumption]; try solve [exact RecordProbeSelector]; try solve [left;reflexivity].
  all: try solve [reflexivity]; try solve [discriminate];try solve [unfold CurrentProbeGE; rewrite map_get_set' by discriminate;complete_entry_bind];
    try solve [change (0<=8)%Z;lia]; try solve [change (8+55<=4294967295)%Z;lia];
    try solve [change (8<256);lia];try solve [change (8<12);lia]; try solve [change (8<13);lia];
    try solve [change (6<12);lia]; try solve [change (16<256);lia]; try solve [change (1<256);lia].
  all: try solve [right;reflexivity];try solve [left;lia].
  all: try solve [repeat rewrite RecordProbeLoadFrame by discriminate;repeat rewrite CurrentProbeLoadFrame by discriminate;repeat rewrite EventDataProbeLoadFrame by (first [left;discriminate | right;right;lia | right;left;cbn [typelen];lia]);repeat rewrite expected_payload_entry_load_frame by (try (left;discriminate);right;cbn [typelen];lia);repeat rewrite expected_wait_entry_load_frame by discriminate;assumption].
  all: try solve [intros k K; repeat rewrite RecordProbeGetFrame by discriminate;repeat rewrite CurrentProbeGetFrame by discriminate;repeat rewrite EventDataProbeGetFrame by (first [left;discriminate | right;lia]);rewrite expected_payload_entry_get_frame by (try (left;discriminate);right;lia);repeat rewrite expected_wait_entry_get_frame by discriminate;
    first [exact (HWo k K)|exact(HWn k K)|exact(HWe k K)|exact(CW k K)]].
  all: try solve [intros p R;repeat rewrite RecordProbeLoadFrame by discriminate;repeat rewrite CurrentProbeLoadFrame by discriminate;repeat rewrite EventDataProbeLoadFrame by (first [left;discriminate | right;right;lia | right;left;cbn [typelen];lia]);rewrite expected_payload_entry_load_frame by (try (left;discriminate);right;cbn [typelen];lia);repeat rewrite expected_wait_entry_load_frame by discriminate;exact(HView p R)].
  all: try solve [unfold V293_tcb_old_loads in *;repeat rewrite RecordProbeLoadFrame by discriminate;repeat rewrite CurrentProbeLoadFrame by discriminate;repeat rewrite EventDataProbeLoadFrame by (first [left;discriminate | right;right;lia | right;left;cbn [typelen];lia]);repeat rewrite expected_payload_entry_load_frame by (try (left;discriminate);right;cbn [typelen];lia);repeat rewrite expected_wait_entry_load_frame by discriminate;exact HFields].
  all: try solve [repeat rewrite RecordProbeGetFrame by discriminate;repeat rewrite CurrentProbeGetFrame by discriminate;repeat rewrite EventDataProbeGetFrame by (first [left;discriminate | right;lia]);rewrite expected_payload_entry_get_frame by (try (left;discriminate);right;lia);repeat rewrite expected_wait_entry_get_frame by discriminate;assumption].
  all: try solve [unfold V293_rekey_bitmap_loads in *;repeat rewrite RecordProbeLoadFrame by discriminate;repeat rewrite CurrentProbeLoadFrame by discriminate;repeat rewrite EventDataProbeLoadFrame by (first [left;discriminate | right;right;lia | right;left;cbn [typelen];lia]);repeat rewrite expected_payload_entry_load_frame by (try (left;discriminate);right;cbn [typelen];lia);repeat rewrite expected_wait_entry_load_frame by discriminate;exact HLoads].
  all: try solve [unfold V293_rekey_bitmap_writable in *;repeat rewrite RecordProbeGetFrame by discriminate;repeat rewrite CurrentProbeGetFrame by discriminate;repeat rewrite EventDataProbeGetFrame by (first [left;discriminate | right;lia]);repeat rewrite expected_payload_entry_get_frame by (try (left;discriminate);right;lia);repeat rewrite expected_wait_entry_get_frame by discriminate;exact HW].
  all: try solve [intros d D;repeat rewrite RecordProbeGetFrame by discriminate;repeat rewrite CurrentProbeGetFrame by discriminate;repeat rewrite EventDataProbeGetFrame by (first [left;discriminate | right;lia]);rewrite expected_payload_entry_get_frame by (try (left;discriminate);right;lia);repeat rewrite expected_wait_entry_get_frame by discriminate;exact(HTW d D)].
  all: try solve [change (0<=5)%Z;lia];try solve [change (5+12<=4294967295)%Z;lia];try solve [change (0<256);lia].
  all: try solve [unfold V293_event_bitmap_loads in *;repeat rewrite RecordProbeLoadFrame by discriminate;repeat rewrite CurrentProbeLoadFrame by discriminate;repeat rewrite EventDataProbeLoadFrame by (first [left;discriminate | right;right;lia | right;left;cbn [typelen];lia]);repeat rewrite expected_payload_entry_load_frame by (try (left;discriminate);right;cbn [typelen];lia);repeat rewrite expected_wait_entry_load_frame by discriminate;exact HELoads].
  all: try solve [unfold V293_event_bitmap_writable in *;repeat rewrite RecordProbeGetFrame by discriminate;repeat rewrite CurrentProbeGetFrame by discriminate;repeat rewrite EventDataProbeGetFrame by (first [left;discriminate | right;lia]);repeat rewrite expected_payload_entry_get_frame by (try (left;discriminate);right;lia);repeat rewrite expected_wait_entry_get_frame by discriminate;exact HEW].
  - intros c Cases. cbn in Cases. intuition congruence.
  - intros x v c I Bind. cbn [V293_rekey_new_bindings In] in I.
    destruct I as [E|[E|[E|F]]]; try contradiction; inversion E; subst x v;
      unfold V293_tcb_update_fixture_le,V293_event_fixture_le,V293_prefix_fixture_le,V293_read_ready_fixture_le,V293_ready_fragment_fixture_le in Bind;
      repeat first [rewrite map_get_set in Bind | rewrite map_get_set' in Bind by discriminate];
      inversion Bind; subst c; repeat split; discriminate.
  - intros x v c I Bind. cbn [V293_rekey_ready_bindings In] in I.
    destruct I as [E|[E|[E|[E|[E|[E|F]]]]]];try contradiction;inversion E;subst x v;
      unfold V293_tcb_update_fixture_le,V293_event_fixture_le,V293_prefix_fixture_le,V293_read_ready_fixture_le,V293_ready_fragment_fixture_le in Bind;
      repeat first [rewrite map_get_set in Bind|rewrite map_get_set' in Bind by discriminate];
      inversion Bind;subst c;split;discriminate.
  - intros c Cases. cbn in Cases. intuition congruence.
  - intros x v c I Bind. cbn [V293_rekey_new_bindings In] in I.
    destruct I as [E|[E|[E|F]]]; try contradiction; inversion E; subst x v;
      unfold V293_tcb_update_fixture_le,V293_event_fixture_le,V293_prefix_fixture_le,V293_read_ready_fixture_le,V293_ready_fragment_fixture_le in Bind;
      repeat first [rewrite map_get_set in Bind | rewrite map_get_set' in Bind by discriminate];
      inversion Bind; subst c; discriminate.
  - intros c Cases. cbn in Cases. intuition congruence.
  - intros c Cases. destruct Cases as [-> | [-> | [-> | ->]]];
      repeat rewrite RecordProbeGetFrame by discriminate;repeat rewrite CurrentProbeGetFrame by discriminate;repeat rewrite EventDataProbeGetFrame by (first [left;discriminate | right;lia]);rewrite expected_payload_entry_get_frame by (try (left;discriminate);right;lia);repeat rewrite expected_wait_entry_get_frame by discriminate;
      rewrite CF by discriminate; unfold V293_coordinate_fixture_mem;
      repeat rewrite V293_put_byte_other by discriminate;
      eexists; apply V293_put_byte_get_same.
  - repeat rewrite RecordProbeLoadFrame by discriminate;repeat rewrite CurrentProbeLoadFrame by discriminate;repeat rewrite EventDataProbeLoadFrame by (first [left;discriminate | right;right;lia | right;left;cbn [typelen];lia]);rewrite expected_payload_entry_load_frame by (try (left;discriminate);right;cbn [typelen];lia);repeat rewrite expected_wait_entry_load_frame by discriminate.
    change (load (Tptr V293_tcb_type) M (50%positive,24%Z) = Some (nth 6 V293_prefix_fixture_entries Vnull)).
    exact (HView 6 ltac:(clear;lia)).
  - repeat rewrite RecordProbeLoadFrame by discriminate;repeat rewrite CurrentProbeLoadFrame by discriminate;repeat rewrite EventDataProbeLoadFrame by (first [left;discriminate | right;right;lia | right;left;cbn [typelen];lia]);rewrite expected_payload_entry_load_frame by (try (left;discriminate);right;cbn [typelen];lia);repeat rewrite expected_wait_entry_load_frame by discriminate.
    change (load (Tptr V293_tcb_type) M (50%positive,32%Z) = Some (nth 8 V293_prefix_fixture_entries Vnull)).
    exact (HView 8 ltac:(clear;lia)).

  - intros c Cases. cbn in Cases. intuition congruence.
  - repeat rewrite RecordProbeLoadFrame by discriminate;repeat rewrite CurrentProbeLoadFrame by discriminate;repeat rewrite EventDataProbeLoadFrame by (first [left;discriminate | right;right;lia | right;left;cbn [typelen];lia]);rewrite expected_payload_entry_load_frame by (left;discriminate).
    unfold expected_wait_entry_mem. repeat rewrite V293_put_byte_other_load by discriminate.
    apply V293_put_byte_load;lia.
  - intro One. split; [reflexivity | ]. split; [discriminate | ]. split; [discriminate | ].
    exists 101%positive. exists 1. split; [unfold CurrentProbeGE; rewrite map_get_set' by discriminate; complete_entry_bind | ]. split.
    + repeat rewrite RecordProbeLoadFrame by discriminate;repeat rewrite CurrentProbeLoadFrame by discriminate;repeat rewrite EventDataProbeLoadFrame by (first [left;discriminate | right;right;lia | right;left;cbn [typelen];lia]);rewrite expected_payload_entry_load_frame by (left;discriminate).
      unfold expected_wait_entry_mem. rewrite V293_put_byte_other_load by discriminate.
      apply V293_put_byte_load;lia.
    + split; [lia | left;discriminate].
  - intros x c I Bind. cbn in I. destruct I as [E | [E | [E | F]]];try contradiction;subst x;
      unfold CurrentProbeGE,V293_complete_fixture_ge in Bind;
      repeat first [rewrite map_get_set in Bind | rewrite map_get_set' in Bind by discriminate];
      inversion Bind;subst c;cbn;intuition discriminate.
  - rewrite Addresses. repeat constructor;cbn;intuition discriminate.
  - intros c I. rewrite Addresses. cbn in I. destruct I as [E | [E | [E | [E | [E | F]]]]];try contradiction;subst c;
      cbn;intuition discriminate.
  - apply ApiEntryJoint.
  - apply map_join_emp.
  - destruct Physical as (Exec & Updated & Ready & Table & EventReady & Internal & Frame & Removed & TcbFrame & EventFrame & ExactBlock).
    exists Mf. exists OO'. split; [exact Abstract | ]. split; [exact Exec | ].
    split; [exact Updated | ]. split; [exact Ready | ]. split; [exact Table | ].
    split; [exact EventReady | ]. split; [exact Internal | ]. split; [exact Removed | ].
    split; [exact Joint | apply map_get_set].
Qed.

(* These checks apply to the very Mf and OO' returned above, not a new run. *)
Theorem ApiRejectsOldPriority : forall Mf O ir aux op,
  V293_tcb_updated_loads Mf 41%positive 8%Z 6 ->
  ~ (CurrentProbeGE,emp,Mf,ir,aux,O,op) |=
    V293_owned_task_record ApiTarget (Int.repr 8) (wait expected_wait_reason Int.one) expected_payload_message ** Atrue.
Proof.
  intros Mf O ir aux op [Actual _] Stale.
  assert (Old : load Tint8 Mf (41%positive,58%Z) = Some (V293_byteval 8)).
  { eapply V293_record_star_load_l with
      (s := (CurrentProbeGE,emp,Mf,ir,aux,O,op)); [ | exact Stale].
    intros s Owned.
    destruct (V293_owned_task_record_sound _ _ _ _ _ Owned) as (p & Range & Priority & Fields & _).
    assert (Same : p=8).
    { apply V293_priority_repr_injective; [exact Range | lia | symmetry; exact Priority]. }
    subst p. exact (proj1 Fields). }
  change (load Tint8 Mf (41%positive,58%Z) = Some (V293_byteval 6)) in Actual.
  rewrite Actual in Old. discriminate.
Qed.

Theorem ApiFinalWritePermission : forall Mf O ir aux op now,
  (CurrentProbeGE,emp,Mf,ir,aux,O,op) |=
    (V293_owned_task_record ApiTarget (Int.repr 6) (wait expected_wait_reason Int.one) expected_payload_message **
      V293_shared_fields (60%positive,Int.zero) expected_payload_tasks_updated expected_queue_events now) ** Atrue ->
  exists after, store Tint8 Mf (41%positive,58%Z) (V293_byteval 7) = Some after.
Proof.
  intros Mf O ir aux op now Joint. apply astar_assoc_elim in Joint.
  destruct (V293_owned_task_record_update _ _ _ _ 7 _ _ _ _ _ _ _ _ ltac:(lia) Joint)
    as [Writable _].
  destruct (Writable 50%Z ltac:(lia)) as [v W].
  change (get Mf (41%positive,58%Z) = Some (true,v)) in W.
  exists (V293_put_byte Mf (41%positive,58%Z) 7). eapply V293_put_byte_store; exact W.
Qed.

Theorem ApiPermissionMatters :
  load Tint8 OwnershipReadOnlyCell (41%positive,58%Z) = Some (V293_byteval 6) /\
  ~ V293_wstate emp emp OwnershipReadOnlyCell |=
      V293_owned_record_cell ((41%positive,58%Z),Tint8,V293_byteval 6) /\
  ~ exists Mf, store Tint8 OwnershipReadOnlyCell (41%positive,58%Z) (V293_byteval 7) = Some Mf.
Proof. exact OwnershipReadableNotWritable. Qed.

Print Assumptions ApiEntryJoint.
Print Assumptions ApiOwnedFullReturn.
Print Assumptions ApiRejectsOldPriority.
Print Assumptions ApiFinalWritePermission.
Print Assumptions ApiPermissionMatters.
