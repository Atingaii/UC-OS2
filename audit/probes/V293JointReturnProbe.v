(* One literal entry owning the actual current read-half and both task
   records jointly. No completed old execution is used as an oracle. *)
Require Import CertiOS.audit.probes.V293AllTaskOwnershipProbe.
Require Import CertiOS.audit.probes.V293BitmapOwnershipProbe.
Require Import CertiOS.audit.probes.V293CurrentOwnershipProbe.
Require Import CertiOS.audit.probes.V293TaskRecordsProbe.
Require Import CertiOS.audit.probes.V293TaskRecordOwnershipProbe.
Require Import CertiOS.audit.probes.V293ApiTaskOwnershipProbe.
Require Import CertiOS.audit.probes.V293CurrentConsistencyProbe.
Require Import CertiOS.audit.probes.V293EventDataProbe.
Require Import CertiOS.audit.probes.V293EventQueueProbe.
Require Import CertiOS.audit.probes.V293WaitPayloadProbe.
Require Import CertiOS.audit.probes.V293WaitEventOwnedProbe.
Require Import CertiOS.audit.probes.V293SuccessCompleteReturnProbe.
Require Import CertiOS.audit.probes.V293SuccessEntryWitnessProbe.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.proofs.V293SharedStateWitness.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewExec.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTarget.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.code.V293OSSchedGuards.
Require Import CertiOS.certiucos.v293.code.V293OSSchedDispatch.
Require Import CertiOS.certiucos.v293.code.V293OSSchedChange.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.rulesoundlib.
Require Import CertiOS.framework.proof.cstepLib.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.tactics.basetac.join_lib.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List Lia Coq.Relations.Relation_Operators.
Import ListNotations.
Local Open Scope nat_scope.
Local Opaque HalfPermMap.set.

Definition UnifiedCurrentMemory := V293_encoded_memory 80%positive 0%Z false
  (encode_val (Tptr V293_tcb_type) (Vptr (60%positive,Int.zero))).
Definition UnifiedMemory := merge UnifiedCurrentMemory AllMemory.
Lemma UnifiedCurrentOutside : forall c i, c <> 80%positive -> get UnifiedCurrentMemory (c,i) = None.
Proof. intros. unfold UnifiedCurrentMemory. apply V293_encoded_memory_outside. left; assumption. Qed.
Lemma UnifiedTasksOutsideCurrent : forall i, get AllMemory (80%positive,i) = None.
Proof.
  intro. unfold AllMemory,addr. rewrite map_merge_semp by reflexivity.
  rewrite AllTargetOutside by discriminate. rewrite AllReadyOutside by discriminate. reflexivity.
Qed.
Lemma UnifiedCurrentSub : Maps.sub UnifiedCurrentMemory RecordProbeMemory.
Proof.
  eapply V293_owned_block_frame with (b:=80%positive) (before:=CurrentProbeMemory).
  - eapply V293_owned_block_frame with (b:=80%positive).
    + apply OwnershipProbeInstalledHalf.
    + apply UnifiedCurrentOutside.
    + intro i. unfold CurrentProbeMemory. apply V293_put_byte_other. discriminate.
  - apply UnifiedCurrentOutside.
  - intro i. apply RecordProbeGetFrame. discriminate.
Qed.
Lemma UnifiedFragmentsJoin : join UnifiedCurrentMemory AllMemory UnifiedMemory.
Proof.
  apply map_join_merge. apply map_disjoint. intros [c i].
  destruct (Pos.eq_dec c 80%positive) as [Same | Apart].
  - subst c. right; left. apply UnifiedTasksOutsideCurrent.
  - left. apply UnifiedCurrentOutside; exact Apart.
Qed.
Lemma UnifiedFragmentsSub : Maps.sub UnifiedMemory RecordProbeMemory.
Proof.
  unfold addr in *. apply sub_semp; [reflexivity | ]. intros [c i].
  unfold UnifiedMemory,addr.
  rewrite (@map_merge_semp (block*offset) (bool*memval) mem memMap UnifiedCurrentMemory AllMemory (c,i) eq_refl).
  destruct (Pos.eq_dec c 80%positive) as [BlockSame | Apart].
  - assert (Outside : get AllMemory (c,i) = None).
    { rewrite BlockSame. apply UnifiedTasksOutsideCurrent. }
    rewrite Outside. destruct (get UnifiedCurrentMemory (c,i)) as [[permission byte] | ] eqn:Cell.
    + destruct (@sub_semp1 (block*offset) (bool*memval) mem memMap UnifiedCurrentMemory RecordProbeMemory
        (c,i) (permission,byte) eq_refl UnifiedCurrentSub Cell) as [Same | [Split Read]].
      * rewrite Same; destruct permission; reflexivity.
      * rewrite Split; destruct permission; cbn in *; try discriminate; reflexivity.
    + destruct (get RecordProbeMemory (c,i)); exact I.
  - rewrite UnifiedCurrentOutside by exact Apart.
    destruct (get AllMemory (c,i)) as [[permission byte] | ] eqn:Cell.
    + destruct (@sub_semp1 (block*offset) (bool*memval) mem memMap AllMemory RecordProbeMemory
        (c,i) (permission,byte) eq_refl AllFragmentsSub Cell) as [Same | [Split Read]].
      * rewrite Same; destruct permission; reflexivity.
      * rewrite Split; destruct permission; cbn in *; try discriminate; reflexivity.
    + destruct (get RecordProbeMemory (c,i)); exact I.
Qed.
Lemma UnifiedCurrentSpatial : forall le ir aux op,
  (CurrentProbeGE,le,UnifiedCurrentMemory,ir,aux,emp,op) |= CurTid (60%positive,Int.zero).
Proof.
  intros. exists V293_tcb_type. unfold Agvarmapsto. exists 80%positive.
  apply sat_split'. exists (emp:mem). exists UnifiedCurrentMemory. exists (emp:osabst). exists (emp:osabst).
  split; [apply map_join_comm; apply map_join_emp | ]. split; [apply map_join_emp | ].
  split; [exists 80%positive; repeat split; try reflexivity; apply map_get_set | ].
  split; [unfold UnifiedCurrentMemory; apply V293_encoded_memory_mapsto | reflexivity].
Qed.
Lemma UnifiedLiteralSpatial : forall le ir aux op,
  (CurrentProbeGE,le,UnifiedMemory,ir,aux,emp,op) |=
    CurTid (60%positive,Int.zero) ** V293_owned_task_records expected_payload_tasks.
Proof.
  intros. apply sat_split'. exists UnifiedCurrentMemory. exists AllMemory.
  exists (emp:osabst). exists (emp:osabst).
  split; [exact UnifiedFragmentsJoin | ]. split; [apply map_join_emp | ]. split.
  - apply UnifiedCurrentSpatial.
  - apply AllLiteralSpatial.
Qed.
Lemma UnifiedEntryPhysical : forall le ir aux O op,
  (CurrentProbeGE,le,RecordProbeMemory,ir,aux,O,op) |=
    (CurTid (60%positive,Int.zero) ** V293_owned_task_records expected_payload_tasks) ** Atrue.
Proof.
  intros. destruct UnifiedFragmentsSub as [rest Joined]. apply sat_split'.
  exists UnifiedMemory. exists rest. exists (emp:osabst). exists O.
  split; [exact Joined | ]. split; [apply map_join_comm; apply map_join_emp | ].
  split; [apply UnifiedLiteralSpatial | exact I].
Qed.
Lemma UnifiedEntryFull : forall le ir aux now op,
  (CurrentProbeGE,le,RecordProbeMemory,ir,aux,
    V293_shared_fixture_abs (60%positive,Int.zero) expected_payload_tasks expected_queue_events now,op) |=
    V293_shared_fields (60%positive,Int.zero) expected_payload_tasks expected_queue_events now **
      ((CurTid (60%positive,Int.zero) ** V293_owned_task_records expected_payload_tasks) ** Atrue).
Proof.
  intros. assert (Fields : (CurrentProbeGE,le,RecordProbeMemory,ir,aux,
    V293_shared_fixture_abs (60%positive,Int.zero) expected_payload_tasks expected_queue_events now,op) |=
    V293_shared_fields (60%positive,Int.zero) expected_payload_tasks expected_queue_events now ** Atrue).
  { eapply V293_shared_fields_heap_lift; [ | apply map_join_emp].
    eapply V293_shared_fields_rebase. apply V293_shared_fixture_fields. }
  pose proof (V293_current_tasks_fields_reconstruct _ _ _ _ _ _ _ _ _ _ _
    (UnifiedEntryPhysical le ir aux _ op) Fields) as Joined.
  clear -Joined. sep auto.
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


Theorem UnifiedOwnedFullReturn : forall sc now op ir enabled si ci,
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
    (((CurTid (60%positive,Int.zero) ** V293_owned_task_records expected_payload_tasks_updated) **
      V293_owned_record_cells (V293_bitmap_layout 30%positive 31%positive 72%positive 5%Z 16 0 64 0)) **
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
  destruct (V293_critical_wait_joint_owned_execution V293_success_tail_fixture_program
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
    as (Mf & Os' & OO' & Identity & AbstractFrame & Abstract & Physical & Unified & FinalBitmap & FinalTable & FinalEvent).

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
  - apply UnifiedEntryFull.
  - apply map_join_emp.
  - intros t value Lookup Different.
    change (get (set (sig (60%positive,Int.zero) (Int.repr 4,rdy,Vnull))
      (41%positive,Int.repr 8)
      (Int.repr 8,wait expected_wait_reason Int.one,expected_payload_message)) t = Some value) in Lookup.
    rewrite map_get_set' in Lookup by (intro Same; subst t; cbn in Different; contradiction).
    assert (T : t = (60%positive,Int.zero)).
    { destruct (TcbMod.eq_dec t (60%positive,Int.zero)) as [Same | Apart]; [exact Same | ].
      rewrite map_get_sig' in Lookup by congruence. discriminate. }
    subst t. rewrite Addresses. cbn. intuition congruence.
  - intros pointer_block tp Binding Different.
    unfold CurrentProbeGE in Binding. rewrite map_get_set in Binding. inversion Binding; subst pointer_block tp.
    rewrite Addresses. cbn. intuition congruence.
  - destruct Physical as (Exec & Updated & Ready & Table & EventReady & Internal & Frame & Removed & TcbFrame & EventFrame & ExactBlock).
    exists Mf. exists OO'. split; [exact Abstract | ]. split; [exact Exec | ].
    split; [exact Updated | ]. split; [exact Ready | ]. split; [exact Table | ].
    split; [exact EventReady | ]. split; [exact Internal | ]. split; [exact Removed | ].
    split; [exact Unified | apply map_get_set].
Qed.


Theorem UnifiedFinalReadAndWritable : forall Mf O ir aux op now,
  (CurrentProbeGE,emp,Mf,ir,aux,O,op) |=
    ((CurTid (60%positive,Int.zero) ** V293_owned_task_records expected_payload_tasks_updated) **
      V293_shared_fields (60%positive,Int.zero) expected_payload_tasks_updated expected_queue_events now) ** Atrue ->
  load (Tptr V293_tcb_type) Mf (80%positive,0%Z) = Some (Vptr (60%positive,Int.zero)) /\
  (exists after, store Tint8 Mf (41%positive,58%Z) (V293_byteval 7) = Some after) /\
  (exists after, store Tint8 Mf (60%positive,50%Z) (V293_byteval 5) = Some after).
Proof.
  intros Mf O ir aux op now Unified. split.
  - assert (Current : (CurrentProbeGE,emp,Mf,ir,aux,O,op) |= CurTid (60%positive,Int.zero) ** Atrue)
      by (clear -Unified; sep auto).
    destruct (V293_shared_current_read _ _ _ _ _ _ _ _ _ Current) as (b & tp & Binding & Pointer).
    unfold CurrentProbeGE in Binding. rewrite map_get_set in Binding. inversion Binding; subst b tp.
    exact Pointer.
  - apply AllFinalBothWritable with O ir aux op now. clear -Unified. sep auto.
Qed.
Theorem UnifiedRejectsWrongCurrent : forall Mf O ir aux op,
  load (Tptr V293_tcb_type) Mf (80%positive,0%Z) = Some (Vptr (60%positive,Int.zero)) ->
  ~ (CurrentProbeGE,emp,Mf,ir,aux,O,op) |= CurTid ApiTarget ** Atrue.
Proof.
  intros Mf O ir aux op Actual Wrong.
  destruct (V293_shared_current_read _ _ _ _ _ _ _ _ _ Wrong) as (b & tp & Binding & Pointer).
  unfold CurrentProbeGE in Binding. rewrite map_get_set in Binding. inversion Binding; subst b tp.
  change (load (Tptr V293_tcb_type) Mf (80%positive,0%Z) = Some (Vptr (41%positive,Int.repr 8))) in Pointer.
  rewrite Actual in Pointer. discriminate.
Qed.
Theorem UnifiedRejectsOldCanonical : forall Mf O ir aux op,
  V293_tcb_updated_loads Mf 41%positive 8%Z 6 ->
  ~ (CurrentProbeGE,emp,Mf,ir,aux,O,op) |=
    (CurTid (60%positive,Int.zero) ** V293_owned_task_records expected_payload_tasks) ** Atrue.
Proof.
  intros Mf O ir aux op Actual Wrong. apply (AllRejectsOldCanonical Mf O ir aux op Actual).
  clear -Wrong. sep auto.
Qed.
(* Every consumer below projects from the SAME joint separating assertion.
   Stores are individual permissions, not a sequential arbitrary-write invariant. *)
Theorem UnifiedUseAllResources : forall Mf O ir aux op now,
  (CurrentProbeGE,emp,Mf,ir,aux,O,op) |=
    (((CurTid (60%positive,Int.zero) ** V293_owned_task_records expected_payload_tasks_updated) **
      V293_owned_record_cells (V293_bitmap_layout 30%positive 31%positive 72%positive 5%Z 16 0 64 0)) **
      V293_shared_fields (60%positive,Int.zero) expected_payload_tasks_updated expected_queue_events now) ** Atrue ->
  load (Tptr V293_tcb_type) Mf (80%positive,0%Z) = Some (Vptr (60%positive,Int.zero)) /\
  (exists after, store Tint8 Mf (41%positive,58%Z) (V293_byteval 7) = Some after) /\
  (exists after, store Tint8 Mf (60%positive,50%Z) (V293_byteval 5) = Some after) /\
  (forall a old replacement, In (a,Tint8,old)
      (V293_bitmap_layout 30%positive 31%positive 72%positive 5%Z 16 0 64 0) -> replacement < 256 ->
    exists prefix suffix after,
      V293_bitmap_layout 30%positive 31%positive 72%positive 5%Z 16 0 64 0 =
        prefix ++ (a,Tint8,old) :: suffix /\
      store Tint8 Mf a (V293_byteval replacement) = Some after /\
      (CurrentProbeGE,emp,after,ir,aux,O,op) |=
        V293_owned_record_cells (prefix ++ (a,Tint8,V293_byteval replacement) :: suffix) ** Atrue).
Proof.
  intros Mf O ir aux op now Owned.
  assert (Pair : (CurrentProbeGE,emp,Mf,ir,aux,O,op) |=
    ((CurTid (60%positive,Int.zero) ** V293_owned_task_records expected_payload_tasks_updated) **
      V293_shared_fields (60%positive,Int.zero) expected_payload_tasks_updated expected_queue_events now) ** Atrue)
    by (clear -Owned; sep auto).
  destruct (UnifiedFinalReadAndWritable _ _ _ _ _ _ Pair) as (Current & Target & Other).
  split; [exact Current | ]. split; [exact Target | ]. split; [exact Other | ].
  intros a old replacement Member Range.
  eapply BitmapEveryCellCanBeUpdated; [exact Member | exact Range | ]. clear -Owned. sep auto.
Qed.

Theorem UnifiedBitmapStorePreservesJoint : forall Mf O ir aux op now a old replacement,
  In (a,Tint8,old) (V293_bitmap_layout 30%positive 31%positive 72%positive 5%Z 16 0 64 0) ->
  replacement < 256 ->
  (CurrentProbeGE,emp,Mf,ir,aux,O,op) |=
    (((CurTid (60%positive,Int.zero) ** V293_owned_task_records expected_payload_tasks_updated) **
      V293_owned_record_cells (V293_bitmap_layout 30%positive 31%positive 72%positive 5%Z 16 0 64 0)) **
      V293_shared_fields (60%positive,Int.zero) expected_payload_tasks_updated expected_queue_events now) ** Atrue ->
  exists prefix suffix after,
    V293_bitmap_layout 30%positive 31%positive 72%positive 5%Z 16 0 64 0 =
      prefix ++ (a,Tint8,old) :: suffix /\
    store Tint8 Mf a (V293_byteval replacement) = Some after /\
    (CurrentProbeGE,emp,after,ir,aux,O,op) |=
      (((CurTid (60%positive,Int.zero) ** V293_owned_task_records expected_payload_tasks_updated) **
        V293_owned_record_cells (prefix ++ (a,Tint8,V293_byteval replacement) :: suffix)) **
        V293_shared_fields (60%positive,Int.zero) expected_payload_tasks_updated expected_queue_events now) ** Atrue.
Proof.
  intros Mf O ir aux op now a old replacement Member Range Owned.
  apply in_split in Member. destruct Member as (prefix & suffix & Layout).
  assert (Framed : (CurrentProbeGE,emp,Mf,ir,aux,O,op) |=
    V293_owned_record_cells (prefix ++ (a,Tint8,old) :: suffix) **
      ((CurTid (60%positive,Int.zero) ** V293_owned_task_records expected_payload_tasks_updated) **
        (V293_shared_fields (60%positive,Int.zero) expected_payload_tasks_updated expected_queue_events now ** Atrue))).
  { rewrite Layout in Owned. clear -Owned. sep auto. }
  destruct (V293_owned_cells_byte_update prefix a old suffix replacement _ _ _ _ _ _ _ _ Range Framed)
    as ([raw Full] & Updated).
  exists prefix. exists suffix. exists (V293_put_byte Mf a replacement).
  split; [exact Layout | ]. split; [apply V293_put_byte_store with raw; exact Full | ].
  clear -Updated. sep auto.
Qed.

Print Assumptions UnifiedEntryFull.
Print Assumptions UnifiedOwnedFullReturn.
Print Assumptions UnifiedFinalReadAndWritable.
Print Assumptions UnifiedRejectsWrongCurrent.
Print Assumptions UnifiedRejectsOldCanonical.
Print Assumptions UnifiedUseAllResources.
Print Assumptions UnifiedBitmapStorePreservesJoint.
