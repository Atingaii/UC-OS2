(* Fixed bytes, two abstract maps.  Prefix reaches the first CPU call;
   the after-return window is a separate entry, not execution of that call. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.certiucos.v293.code.V293OSTCBPublish.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.proofs.V293PublishRecords.
Require Import CertiOS.certiucos.v293.proofs.V293TCBPublish.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitPrefix.
Require Import CertiOS.certiucos.v293.proofs.V293InitAllRecords.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293InitTCBClear.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewWitness.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293NullBytes.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List Lia.
Require Import CertiOS.certiucos.v293.proofs.V293PublishReturnRecords.
Require Import CertiOS.certiucos.v293.proofs.V293TCBSuccessReturn.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickLifecycle.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitFunction.
Require Import CertiOS.certiucos.v293.proofs.V293TCBPriorityHook.
Require Import CertiOS.certiucos.v293.code.V293OSTCBInitFunction.
Require Import CertiOS.certiucos.v293.proofs.V293InitPublishRecords.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitEntry.
Require Import CertiOS.certiucos.v293.proofs.V293TCBCallSuccess.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitFields.
Require Import CertiOS.certiucos.v293.proofs.V293StartRecord.
Require Import CertiOS.certiucos.v293.code.V293OSTCBInitPrefix.
Require Import CertiOS.certiucos.v293.proofs.V293CanonicalInitReturn.
Require Import CertiOS.certiucos.v293.proofs.V293InitPriorityTable.
Require Import CertiOS.audit.probes.V293CanonicalInitReturnProbe.
Require Import CertiOS.certiucos.v293.proofs.V293ReservedCallShared.
Require Import CertiOS.certiucos.v293.proofs.V293CallRecords.
Require Import Coq.Sorting.Permutation.
Require Import CertiOS.certiucos.v293.proofs.V293PublicationWindow.
Require Import CertiOS.certiucos.v293.proofs.V293InitReadyPayload.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyTaskInvariant.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.audit.probes.V293ReservedCallSharedProbe.
Require Import CertiOS.audit.probes.V293InitReadyPayloadProbe.
Import ListNotations.
Local Open Scope nat_scope.


Definition PWRow0 : list V293_record_cell :=
 [((403%positive,0%Z),Tint8,V293_byteval 0)].
Definition PWInitial := CIROldFields++CIRInputs++CIRLinks++
 [((209%positive,0%Z),Tint32,Vint32 Int.zero);
  ((406%positive,44%Z),Tptr V293_tcb_type,Vptr RCSToken)]++
 CIRTail++CIRHole false++PWRow0++CIRSentinel.
Definition PWCells := PWInitial++CIROldRecord.
Definition PWHookCells := V293_record_hook_cells
 201%positive 202%positive 203%positive 204%positive 205%positive 206%positive 207%positive 208%positive 209%positive
 405%positive 406%positive 301%positive 128%Z 11 Vnull Vnull (Vint32 Int.zero) (Vint32 Int.zero)
 Vnull (Vint32 Int.zero) Vnull (Vptr RCSToken) (CIRTail++CIRHole false++PWRow0++CIRSentinel).
Definition PWSupport := CIRRemainder++
 tl(tl(V293_tcb_init_input_cells 208%positive 201%positive 202%positive 203%positive
 204%positive 205%positive 206%positive 207%positive 301%positive 128%Z 11
 Vnull Vnull (Vint32 Int.zero) (Vint32 Int.zero) Vnull (Vint32 Int.zero)))++
 V293_tcb_prefix_links 405%positive 301%positive 128%Z Vnull Vnull++
 [((209%positive,0%Z),Tint32,Vint32 Int.zero);
  ((301%positive,152%Z),Tcom_ptr 410%Z,Vnull);
  ((401%positive,0%Z),Tptr V293_tcb_type,Vptr CIROldTid);
  ((404%positive,0%Z),Tint8,V293_byteval 1);
  ((301%positive,32%Z),Tcom_ptr 410%Z,Vnull)]++CIRSentinel.
Definition PWFrame := V293_rdy_raw_cells
 (V293_publication_old_bitmap 403%positive 402%positive 0 16++CIRHole false++PWSupport)
 (V293_owned_task_records CIRUpdated ** Atrue).
Definition PWWindowCells := V293_tcb_priority_cells
 201%positive 208%positive 406%positive 301%positive 128%Z 11(Vptr CIRNewTid)++
 V293_publication_old_bitmap 403%positive 402%positive 0 16++CIRHole false++PWSupport.

Theorem PWLiteralEntry : CIREntryState(CIRMemory PWCells) |= V293_rdy_raw_cells PWCells Aemp.
Proof.
 unfold CIREntryState,PWCells,PWInitial,CIROldFields,CIRInputs,CIRLinks,
 CIRTail,PWRow0,CIRSentinel,CIROldRecord,CIRHole,CIREntries,CIRPositive,CIROldTid,RCSToken.
 cbn[app CIRMemory V293_rdy_raw_cells V293_priority_hole V293_priority_cells repeat update_nth_val].
 CIRLiteral.
Qed.

Lemma PWSpatialEntry : CIREntryState(CIRMemory PWCells) |=
 V293_rdy_raw_cells PWInitial(V293_owned_task_records CIRTasks ** Atrue).
Proof.
 eapply V293_raw_cells_mono.
 - intros st HS. apply CIROldOwned in HS.
   eapply astar_mono;[intros s H;exact H |intros s H;exact I |exact HS].
 - rewrite <-V293_raw_cells_append. exact PWLiteralEntry.
Qed.

Theorem PWPrefix : forall P f hi hc ks enabled si ci, exists Mf,
 V293_local_steps P (curs(CIRCode hi hc),(kenil,kcall f(V293_TCBInit_function_body hi hc)CIRCaller ks))
 ((CIRGE,CIRLE,CIRMemory PWCells),(fun _=>false),(enabled,si,ci))
 (curs(sfexec hi[Vptr CIRNewTid][Tptr V293_tcb_type]),
 (kenil,V293_tcb_first_hook_cont f hi hc CIRCaller ks))
 ((CIRGE,CIRLE,Mf),(fun _=>false),(enabled,si,ci)) /\
 (CIREntryState Mf |= V293_owned_task_records CIRUpdated ** V293_rdy_raw_cells PWHookCells Atrue).
Proof.
 intros P f hi hc ks enabled si ci.
 eapply(V293_TCBInit_prefix_to_record_hook CIRTasks P ks CIRGE CIRCaller(CIRMemory PWCells)
 (fun _=>false)(false,nil,nil)(emp:osabst)(spec_done None)enabled si ci f hi hc
 201%positive 202%positive 203%positive 204%positive 205%positive 206%positive 207%positive 208%positive 209%positive
 405%positive 406%positive 301%positive 128%Z 11 Vnull Vnull(Vint32 Int.zero)(Vint32 Int.zero)
 Vnull(Vint32 Int.zero)Vundef Vnull(fun _=>Vundef)(Vptr RCSToken)
 (CIRTail++CIRHole false++PWRow0++CIRSentinel));
 try reflexivity;try lia;try(change(128+55<=4294967295)%Z;lia).
 - repeat split;reflexivity.
 - exact PWSpatialEntry.
Qed.

Lemma PWBetweenOwned : forall M,
 CIREntryState M |= V293_owned_task_records CIRUpdated ** V293_rdy_raw_cells PWHookCells Atrue ->
 CIREntryState M |= V293_rdy_raw_cells
 (V293_tcb_priority_cells 201%positive 208%positive 406%positive 301%positive 128%Z 11(Vptr RCSToken))PWFrame.
Proof.
 intros M Held. apply V293_raw_cells_frame_in in Held.
 unfold PWHookCells,V293_record_hook_cells,PWFrame,PWSupport,CIRRemainder,
 V293_publication_old_bitmap,V293_tcb_priority_cells,CIRTail,PWRow0,
 CIRHole,CIREntries,CIRPositive,CIROldTid in *.
 unfold V293_tcb_init_record_remainder,V293_tcb_init_input_cells,V293_tcb_prefix_links in *.
 replace(V293_ready_group 0 16)with 2 in * by reflexivity.
 cbn[V293_rdy_raw_cells app tl V293_priority_hole V293_priority_cells update_nth_val repeat]in *.
 clear -Held. sep auto.
Qed.

Lemma PWOldReady : V293_ready_rel 0 16 CIRPositive CIRTasks.
Proof.
 split;[lia |  ]. split;[lia |  ]. split.
 - exists 12. right. repeat split;try lia;reflexivity.
 - split;[exact IRPPositiveBitmap |exact(proj1 CIRPositiveCanonical)].
Qed.

Theorem PWMapContrast :
 V293_ready_rel 0 16(update_nth_val 11 CIRPositive(Vptr CIRNewTid))CIRTasks /\
 ~V293_init_priority_table(update_nth_val 11 CIRPositive(Vptr CIRNewTid))CIRTasks /\
 ~V293_bitmap_tasks 0 16 CIRUpdated /\
 V293_ready_rel 0 24(update_nth_val 11 CIRPositive(Vptr CIRNewTid))CIRUpdated.
Proof.
 split.
 - apply V293_creation_old_ready_rel_preserved;[exact PWOldReady |reflexivity].
 - split.
   + apply V293_creation_pointer_before_insert_rejected;[exact CIRPositiveCanonical |lia |reflexivity].
   + split.
     * exact(V293_creation_insert_before_ready_rejected CIRPositive CIRTasks 0 16 11 CIRNewTid
       CIRPositiveCanonical IRPPositiveBitmap ltac:(lia)eq_refl).
     * exact(V293_init_ready_insert 0 16 CIRPositive CIRTasks CIRNewTid 11 ltac:(lia)ltac:(lia)
       ltac:(lia)eq_refl IRPPositiveBitmap CIRPositiveCanonical eq_refl).
Qed.

Theorem PWActualWindow : forall P f hi hc ks enabled si ci, exists M Mf,
 (CIREntryState M |= V293_owned_task_records CIRUpdated ** V293_rdy_raw_cells PWHookCells Atrue) /\
 V293_local_steps P
 (curs(sskip None),(kenil,V293_tcb_first_hook_cont f hi hc CIRCaller ks))
 ((CIRGE,CIRLE,M),(fun _=>false),(enabled,si,ci))
 (curs(sfexec hc[Vptr CIRNewTid][Tptr V293_tcb_type]),
 (kenil,V293_tcb_second_hook_cont f hi hc CIRCaller ks))
 ((CIRGE,CIRLE,Mf),(fun _=>false),(enabled,si,ci)) /\
 (CIREntryState Mf |= V293_rdy_raw_cells PWWindowCells(V293_owned_task_records CIRUpdated ** Atrue)) /\
 load(Tptr V293_tcb_type)Mf(406%positive,44%Z)=Some(Vptr CIRNewTid) /\
 load Tint8 Mf(403%positive,0%Z)=Some(V293_byteval 0) /\
 load Tint8 Mf(403%positive,1%Z)=Some(V293_byteval 16) /\
 load Tint8 Mf(402%positive,0%Z)=Some(V293_byteval 2) /\
 load Tint32 Mf(601%positive,0%Z)=Some(Vint32(Int.repr 77)) /\
 V293_task_records Mf CIRUpdated /\
 V293_ready_rel 0 16(update_nth_val 11 CIRPositive(Vptr CIRNewTid))CIRTasks /\
 ~V293_init_priority_table(update_nth_val 11 CIRPositive(Vptr CIRNewTid))CIRTasks /\
 ~V293_bitmap_tasks 0 16 CIRUpdated /\
 V293_ready_rel 0 24(update_nth_val 11 CIRPositive(Vptr CIRNewTid))CIRUpdated.
Proof.
 intros P f hi hc ks enabled si ci.
 destruct(PWPrefix P f hi hc ks enabled si ci)as(M&Prefix&Entry).
 pose proof(PWBetweenOwned M Entry)as Owned.
 destruct(V293_OS_TCBInit_publication_window P f hi hc CIRCaller ks CIRGE CIRLE M
 (fun _=>false)(false,nil,nil)(emp:osabst)(spec_done None)enabled si ci
 201%positive 208%positive 406%positive 301%positive 128%Z 11 RCSToken
 403%positive 402%positive 0 16 CIRPositive CIRTasks PWSupport Atrue
 eq_refl eq_refl eq_refl eq_refl ltac:(lia)ltac:(lia)ltac:(lia)
 CIRPositiveCanonical IRPPositiveBitmap eq_refl eq_refl Owned)
 as(Mf&Exec&Final&Slot&Low&High&Canonical&OldRejected&NewRejected&ReadyUpdated).
 assert(Raw:CIREntryState Mf |= V293_rdy_raw_cells PWWindowCells(V293_owned_task_records CIRUpdated ** Atrue)).
 { unfold PWWindowCells. rewrite V293_raw_cells_append. exact Final. }
 exists M. exists Mf. split;[exact Entry |  ]. split;[exact Exec |  ]. split;[exact Raw | ].
 split;[exact Slot |  ]. split;[exact Low |  ]. split;[exact High |  ]. split.
 - change(load Tint8(getmem(CIREntryState Mf))(402%positive,0%Z)=Some(V293_byteval 2)).
   eapply V293_rdy_raw_load;[ |reflexivity |exact Raw].
   unfold PWWindowCells. apply in_or_app;right. apply in_or_app;left.
   unfold V293_publication_old_bitmap. cbn. tauto.
 - split.
   + change(load Tint32(getmem(CIREntryState Mf))(601%positive,0%Z)=Some(Vint32(Int.repr 77))).
     eapply V293_rdy_raw_load;[ |reflexivity |exact Raw].
     unfold PWWindowCells. apply in_or_app;right. apply in_or_app;right.
     apply in_or_app;right. unfold PWSupport. repeat(apply in_or_app;right).
     unfold CIRSentinel;cbn;auto.
   + split.
     * apply V293_raw_cells_move_frame in Raw.
       apply sat_split in Raw. destruct Raw as(m1&m2&o1&o2&JM&JO&Records&Other).
       pose proof(V293_owned_task_records_sound _ _ Records)as Sound.
       intros t priority status message Lookup.
       eapply V293_task_record_sub;[exists m2;exact JM |apply Sound;exact Lookup].
     * exact PWMapContrast.
Qed.
