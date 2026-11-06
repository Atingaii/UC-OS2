(* Literal nonempty reserved-slot prefix, plus an independent after-hook
   publication control at that same heap. Neither hook is fabricated. *)
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
Import ListNotations.
Local Open Scope nat_scope.

Definition RCSToken : tid := (700%positive,Int.zero).
Definition RCSInitial := CIROldFields++CIRInputs++CIRLinks++
 [((209%positive,0%Z),Tint32,Vint32 Int.zero);
  ((406%positive,44%Z),Tptr V293_tcb_type,Vptr RCSToken)]++
 CIRTail++CIRHole false++CIRSentinel.
Definition RCSCells := RCSInitial++CIROldRecord.
Definition RCSHookCells := V293_record_hook_cells
 201%positive 202%positive 203%positive 204%positive 205%positive 206%positive 207%positive 208%positive 209%positive
 405%positive 406%positive 301%positive 128%Z 11 Vnull Vnull (Vint32 Int.zero) (Vint32 Int.zero)
 Vnull (Vint32 Int.zero) Vnull (Vptr RCSToken) (CIRTail++CIRHole false++CIRSentinel).
Definition RCSNonTable :=
 [((201%positive,0%Z),Tint8,V293_byteval 11);
  ((208%positive,0%Z),Tptr V293_tcb_type,Vptr CIRNewTid)]++
 CIRRemainder++
 tl(tl(V293_tcb_init_input_cells 208%positive 201%positive 202%positive 203%positive
  204%positive 205%positive 206%positive 207%positive 301%positive 128%Z 11
  Vnull Vnull (Vint32 Int.zero) (Vint32 Int.zero) Vnull (Vint32 Int.zero)))++
 V293_tcb_prefix_links 405%positive 301%positive 128%Z Vnull Vnull++
 ((209%positive,0%Z),Tint32,Vint32 Int.zero)::CIRTail.
Definition RCSJoint :=
 V293_owned_priority_table 406%positive(update_nth_val 11 CIRPositive(Vptr CIRNewTid)) **
 (V293_owned_task_records CIRUpdated ** V293_rdy_raw_cells(RCSNonTable++CIRSentinel)Atrue).

Theorem RCSliteral_entry : CIREntryState(CIRMemory RCSCells) |= V293_rdy_raw_cells RCSCells Aemp.
Proof.
 unfold CIREntryState,RCSCells,RCSInitial,CIROldFields,CIRInputs,CIRLinks,
  CIRTail,CIRSentinel,CIROldRecord,CIRHole,CIREntries,CIRPositive,CIROldTid,RCSToken.
 cbn[app CIRMemory V293_rdy_raw_cells V293_priority_hole V293_priority_cells repeat update_nth_val].
 CIRLiteral.
Qed.

Theorem RCSspatial_entry : CIREntryState(CIRMemory RCSCells) |=
 V293_rdy_raw_cells RCSInitial(V293_owned_task_records CIRTasks ** Atrue).
Proof.
 eapply V293_raw_cells_mono;[ | ].
 - intros st HS. apply CIROldOwned in HS.
   eapply astar_mono;[intros s H;exact H |intros s H;exact I |exact HS].
 - rewrite <-V293_raw_cells_append. exact RCSliteral_entry.
Qed.

Theorem RCSReservedPrefix : forall P f hi hc ks enabled si ci, exists Mf,
 V293_local_steps P (curs(CIRCode hi hc),(kenil,kcall f (V293_TCBInit_function_body hi hc) CIRCaller ks))
 ((CIRGE,CIRLE,CIRMemory RCSCells),(fun _=>false),(enabled,si,ci))
 (curs(sfexec hi [Vptr CIRNewTid] [Tptr V293_tcb_type]),
  (kenil,V293_tcb_first_hook_cont f hi hc CIRCaller ks))
 ((CIRGE,CIRLE,Mf),(fun _=>false),(enabled,si,ci)) /\
 (CIREntryState Mf |= V293_owned_task_records CIRUpdated ** V293_rdy_raw_cells (RCSHookCells) Atrue).
Proof.
 intros P f hi hc ks enabled si ci.
 eapply (V293_TCBInit_prefix_to_record_hook CIRTasks P ks CIRGE CIRCaller (CIRMemory RCSCells)
 (fun _=>false) (false,nil,nil) (emp:osabst) (spec_done None) enabled si ci f hi hc
 201%positive 202%positive 203%positive 204%positive 205%positive 206%positive 207%positive 208%positive 209%positive
 405%positive 406%positive 301%positive 128%Z 11 Vnull Vnull (Vint32 Int.zero) (Vint32 Int.zero)
 Vnull (Vint32 Int.zero) Vundef Vnull (fun _=>Vundef) (Vptr RCSToken) (CIRTail++CIRHole false++CIRSentinel));
 try reflexivity;try lia;try (change (128+55<=4294967295)%Z;lia).
 - repeat split;reflexivity.
 - exact RCSspatial_entry.
Qed.

Lemma RCSUpdatedCanonical : V293_init_priority_table
 (update_nth_val 11 CIRPositive(Vptr CIRNewTid))CIRUpdated.
Proof.
 apply V293_init_priority_insert;[exact CIRPositiveCanonical |lia |reflexivity |reflexivity].
Qed.

Lemma RCSBetweenOwned : forall M,
 CIREntryState M |= V293_owned_task_records CIRUpdated ** V293_rdy_raw_cells RCSHookCells Atrue ->
 CIREntryState M |= V293_rdy_raw_cells
 (V293_tcb_priority_cells 201%positive 208%positive 406%positive 301%positive 128%Z 11(Vptr RCSToken))
 (V293_rdy_raw_cells
  (tl(tl RCSNonTable)++CIRHole false++CIRSentinel)(V293_owned_task_records CIRUpdated ** Atrue)).
Proof.
 intros M Held. apply V293_raw_cells_frame_in in Held.
 unfold RCSHookCells,V293_record_hook_cells,RCSNonTable,CIRRemainder,V293_tcb_priority_cells in *.
 unfold V293_tcb_init_record_remainder,V293_tcb_init_input_cells,V293_tcb_prefix_links in *.
 cbn[V293_rdy_raw_cells app tl]in *.
 clear -Held. sep auto.
Qed.

Lemma RCSAfterTable : forall M,
 CIREntryState M |= V293_rdy_raw_cells
 (V293_tcb_priority_cells 201%positive 208%positive 406%positive 301%positive 128%Z 11(Vptr CIRNewTid))
 (V293_rdy_raw_cells
  (tl(tl RCSNonTable)++CIRHole false++CIRSentinel)(V293_owned_task_records CIRUpdated ** Atrue)) ->
 CIREntryState M |= RCSJoint.
Proof.
 intros M Held.
 unfold V293_tcb_priority_cells in Held.
 rewrite <-V293_raw_cells_append in Held.
 apply V293_raw_cells_move_frame in Held.
 assert(Order:Permutation
  ([((201%positive,0%Z),Tint8,V293_byteval 11);
    ((208%positive,0%Z),Tptr V293_tcb_type,Vptr CIRNewTid);
    ((406%positive,44%Z),Tptr V293_tcb_type,Vptr CIRNewTid)]++
   tl(tl RCSNonTable)++CIRHole false++CIRSentinel)
  (RCSNonTable++(((406%positive,44%Z),Tptr V293_tcb_type,Vptr CIRNewTid)::
   CIRHole false)++CIRSentinel)).
 { unfold RCSNonTable. cbn[app tl]. apply perm_skip. apply perm_skip.
   pose proof(Permutation_middle(tl(tl RCSNonTable))(CIRHole false++CIRSentinel)
    ((406%positive,44%Z),Tptr V293_tcb_type,Vptr CIRNewTid))as Move.
   unfold RCSNonTable in Move. cbn[app tl]in Move.
   repeat rewrite <-app_assoc in Move. repeat rewrite <-app_assoc.
   cbn[app]in Move |- *. exact Move. }
 eapply astar_mono in Held;[ |intros st H;exact H |apply(V293_raw_cells_permutation _ _ Order)].
 unfold RCSJoint,CIRHole,CIREntries.
 eapply V293_priority_reassemble_frame;[exact RCSUpdatedCanonical |cbn;lia |exact Held].
Qed.

Theorem RCSPublicationContrast : forall P f hi hc ks enabled si ci, exists M Mf,
 CIREntryState M |= V293_owned_task_records CIRUpdated ** V293_rdy_raw_cells RCSHookCells Atrue /\
 load(Tptr V293_tcb_type)M(406%positive,44%Z)=Some(Vptr RCSToken) /\
 V293_local_steps P
  (curs(sskip None),(kenil,V293_tcb_first_hook_cont f hi hc CIRCaller ks))
  ((CIRGE,CIRLE,M),(fun _=>false),(enabled,si,ci))
  (curs(sfexec hc [Vptr CIRNewTid] [Tptr V293_tcb_type]),
   (kenil,V293_tcb_second_hook_cont f hi hc CIRCaller ks))
  ((CIRGE,CIRLE,Mf),(fun _=>false),(enabled,si,ci)) /\
 CIREntryState Mf |= RCSJoint /\
 V293_table_loads V293_tcb_type Mf 406%positive(update_nth_val 11 CIRPositive(Vptr CIRNewTid)) /\
 load Tint32 Mf(601%positive,0%Z)=Some(Vint32(Int.repr 77)) /\
 ~ (CIREntryState M |= RCSJoint).
Proof.
 intros P f hi hc ks enabled si ci.
 destruct(RCSReservedPrefix P f hi hc ks enabled si ci)as(M&Prefix&Entry).
 pose proof(RCSBetweenOwned M Entry)as Owned.
 unfold V293_tcb_priority_cells in Owned.
 assert(Reserved:load(Tptr V293_tcb_type)M(406%positive,44%Z)=Some(Vptr RCSToken)).
 { change(load(Tptr V293_tcb_type)(getmem(CIREntryState M))(406%positive,44%Z)=Some(Vptr RCSToken)).
   eapply V293_rdy_raw_load;[ |reflexivity |exact Owned].
   cbn[In]. tauto. }
 destruct(V293_OS_TCBInit_priority_to_second_hook P f hi hc CIRCaller ks CIRGE CIRLE M
 (fun _=>false)(false,nil,nil)(emp:osabst)(spec_done None)
 (V293_rdy_raw_cells(tl(tl RCSNonTable)++CIRHole false++CIRSentinel)
  (V293_owned_task_records CIRUpdated ** Atrue)) enabled si ci
 201%positive 208%positive 406%positive 301%positive 128%Z 11(Vptr RCSToken))
 as(Mf&Exec&Final&Missing).
 - reflexivity.
 - reflexivity.
 - reflexivity.
 - reflexivity.
 - lia.
 - exact Owned.
 - pose proof(RCSAfterTable Mf Final)as Joint.
   pose proof(V293_full_priority_table_loads (update_nth_val 11 CIRPositive(Vptr CIRNewTid)) 406%positive _ _ _ Mf _ _ _ _ eq_refl Joint)as Reads.
   exists M. exists Mf. split;[exact Entry | ]. split;[exact Reserved | ]. split;[exact Exec | ].
   split;[exact Joint | ]. split;[exact Reads | ]. split.
   + change(load Tint32(getmem(CIREntryState Mf))(601%positive,0%Z)=Some(Vint32(Int.repr 77))).
     eapply V293_star_load_r;[ |exact Joint]. intros st Inner.
     eapply V293_star_load_r;[ |exact Inner]. intros st' Raw.
     eapply V293_rdy_raw_load;[ |reflexivity |exact Raw].
     apply in_or_app. right. unfold CIRSentinel;cbn;auto.
   + intro Bad.
     pose proof(V293_full_priority_table_loads (update_nth_val 11 CIRPositive(Vptr CIRNewTid)) 406%positive _ _ _ M _ _ _ _ eq_refl Bad 11 ltac:(lia))as Read.
     change(load(Tptr V293_tcb_type)M(406%positive,44%Z)=Some(Vptr CIRNewTid))in Read.
     rewrite Reserved in Read. discriminate.
Qed.
