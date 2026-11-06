Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
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

Definition EventTypeProbeMemory : mem :=
  V293_put_byte (V293_event_body_fixture_mem 0 1 8 6) (72%positive,5%Z) 3.

Lemma EventTypeProbeEntry :
  load (Tptr V293_tcb_type) EventTypeProbeMemory (40%positive,0%Z) = Some (Vptr (41%positive,Int.repr 8)) /\
  load (Tcom_ptr 411%Z) EventTypeProbeMemory (41%positive,36%Z) = Some (Vptr (72%positive,Int.repr 5)) /\
  V293_bytes_writable EventTypeProbeMemory 70%positive 0%Z 4 /\
  V293_event_bitmap_loads EventTypeProbeMemory 72%positive 5%Z 0 1 2 /\
  V293_event_bitmap_writable EventTypeProbeMemory 72%positive 5%Z /\
  V293_rekey_locals V293_ready_fragment_fixture_ge V293_event_body_fixture_le EventTypeProbeMemory
    72%positive 72%positive (V293_rekey_ready_bindings 302%Z 303%Z 304%Z 305%Z 306%Z 307%Z 8 6) /\
  (forall x v c, In (x,v) (V293_rekey_ready_bindings 302%Z 303%Z 304%Z 305%Z 306%Z 307%Z 8 6) ->
    get V293_event_body_fixture_le x = Some (c,Tint8) -> c <> 70%positive) /\
  V293_event_type_matches EventTypeProbeMemory 72%positive 5%Z (abssem Int.zero).
Proof.
  destruct (V293_event_body_fixture_entry 0 1 8 6 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
    as (Lp & Event & Initial & Dest & Loads & W & Loc & Apart & Ready).
  assert (LF : forall tp c i, c <> 72%positive ->
    load tp EventTypeProbeMemory (c,i) = load tp (V293_event_body_fixture_mem 0 1 8 6) (c,i)).
  { intros. apply V293_load_block_frame. intro j. unfold EventTypeProbeMemory.
    apply V293_put_byte_other. congruence. }
  split; [rewrite LF by discriminate; exact Lp | ].
  split; [rewrite LF by discriminate; exact Event | ]. split.
  - intros k K. destruct (Dest k K) as [v Wv]. exists v.
    unfold EventTypeProbeMemory. rewrite V293_put_byte_other by discriminate. exact Wv.
  - split.
    + unfold V293_event_bitmap_loads in *. unfold EventTypeProbeMemory.
      repeat rewrite V293_put_byte_other_load by discriminate. exact Loads.
    + split.
      * unfold V293_event_bitmap_writable in *. unfold EventTypeProbeMemory.
        repeat rewrite V293_put_byte_other by discriminate. exact W.
      * split.
        -- intros x v I. destruct (Loc x v I) as (c & Bind & A & B & Load).
           exists c. split; [exact Bind | ]. split; [exact A | ]. split; [exact B | ].
           rewrite LF by exact A. exact Load.
        -- split; [exact Apart | ]. unfold V293_event_type_matches,EventTypeProbeMemory.
           apply V293_put_byte_load. cbn [V293_event_kind_code]. lia.
Qed.

Theorem EventTypeProbeExecution : forall P ks,
  exists Mf,
  cstepstar P (curs (V293_task_prio_event 601%Z 600%Z 302%Z 303%Z 304%Z 305%Z 306%Z 307%Z),
    (kenil,ks)) (V293_ready_fragment_fixture_ge,V293_event_body_fixture_le,EventTypeProbeMemory)
    (curs (sskip None),(kenil,ks)) (V293_ready_fragment_fixture_ge,V293_event_body_fixture_le,Mf) /\
  V293_event_bitmap_loads Mf 72%positive 5%Z 64 0 1 /\
  load (Tptr V293_event_type) Mf (70%positive,0%Z) = Some (Vptr (72%positive,Int.repr 5)) /\
  (forall i, (i < 15)%Z \/ (17 < i)%Z -> get Mf (72%positive,i) = get EventTypeProbeMemory (72%positive,i)) /\
  V293_event_type_matches Mf 72%positive 5%Z (abssem Int.zero).
Proof.
  intros P ks. destruct EventTypeProbeEntry as (Lp & Event & Dest & Loads & W & Loc & Apart & Kind).
  assert (Bp : get V293_event_body_fixture_le 601%Z = Some (40%positive,Tptr V293_tcb_type)).
  { unfold V293_event_body_fixture_le. apply map_get_set. }
  assert (Be : get V293_event_body_fixture_le 600%Z = Some (70%positive,Tptr V293_event_type)).
  { unfold V293_event_body_fixture_le. rewrite map_get_set' by discriminate. apply map_get_set. }
  destruct (V293_event_nonnull_type_execution P ks V293_ready_fragment_fixture_ge V293_event_body_fixture_le
    EventTypeProbeMemory 601%Z 600%Z 302%Z 303%Z 304%Z 305%Z 306%Z 307%Z
    40%positive 41%positive 70%positive 8%Z 72%positive 5%Z 0 1 8 6 (abssem Int.zero)
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(discriminate) Bp Be Lp
    ltac:(lia) ltac:(change (8+28 <= 4294967295)%Z; lia) Event Dest
    ltac:(lia) ltac:(change (5+12 <= 4294967295)%Z; lia) Loads W Loc Apart Kind)
    as (Me & Store & Exec & Final & FW & FL & PtrOut & Frame & Header & FinalType).
  exists (V293_event_rekey_memory Me 72%positive 5%Z 0 1 8 6).
  split; [exact Exec | ]. split; [exact Final | ]. split; [exact PtrOut | ].
  split; [exact Header | exact FinalType].
Qed.

Theorem EventTypeProbeRejectsMailbox :
  ~ V293_event_type_matches EventTypeProbeMemory 72%positive 5%Z (absmbox Vnull).
Proof.
  destruct EventTypeProbeEntry as (_ & _ & _ & _ & _ & _ & _ & Kind).
  unfold V293_event_type_matches in *. intro Wrong. rewrite Kind in Wrong. discriminate.
Qed.

Theorem EventTypeProbeWrittenByteIsNotFramed :
  load Tint8 EventTypeProbeMemory (72%positive,17%Z) = Some (V293_byteval 1) /\
  load Tint8 (V293_event_rekey_memory EventTypeProbeMemory 72%positive 5%Z 0 1 8 6)
    (72%positive,17%Z) = Some (V293_byteval 0) /\
  get (V293_event_rekey_memory EventTypeProbeMemory 72%positive 5%Z 0 1 8 6) (72%positive,17%Z) <>
    get EventTypeProbeMemory (72%positive,17%Z).
Proof.
  destruct EventTypeProbeEntry as (_ & _ & _ & Loads & _).
  destruct Loads as (Low & High & Group). split; [exact High | ].
  assert (Changed : load Tint8 (V293_event_rekey_memory EventTypeProbeMemory 72%positive 5%Z 0 1 8 6)
    (72%positive,17%Z) = Some (V293_byteval 0)).
  { change (load Tint8
      (V293_put_byte (V293_put_byte (V293_put_byte (V293_put_byte EventTypeProbeMemory
        (72%positive,17%Z) 0) (72%positive,15%Z) 0)
        (72%positive,15%Z) 1) (72%positive,16%Z) 64)
      (72%positive,17%Z) = Some (V293_byteval 0)).
    repeat rewrite V293_put_byte_other_load by discriminate. apply V293_put_byte_load. lia. }
  split; [exact Changed | ]. intro Same.
  pose proof (V293_event_type_matches_frame EventTypeProbeMemory
    (V293_event_rekey_memory EventTypeProbeMemory 72%positive 5%Z 0 1 8 6)
    72%positive 17%Z (absmbox Vnull) Same High) as Wrong.
  assert (Impossible : Some (V293_byteval 0) = Some (V293_byteval 1)).
  { rewrite <- Changed. exact Wrong. }
  discriminate.
Qed.

Print Assumptions EventTypeProbeEntry.
Print Assumptions EventTypeProbeExecution.
Print Assumptions EventTypeProbeRejectsMailbox.
Print Assumptions EventTypeProbeWrittenByteIsNotFramed.
