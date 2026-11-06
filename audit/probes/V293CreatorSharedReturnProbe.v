Require Import CertiOS.certiucos.v293.code.V293OSTaskCreateExtPrefix.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateExtPrefix.
Require Import CertiOS.framework.proof.cstepLib.
Require Import Coq.Lists.List Lia.
Require Import CertiOS.certiucos.v293.code.V293OSTaskCreateExtCalls.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateStackEntry.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickStorage.
Require Import CertiOS.certiucos.v293.proofs.V293InitTCBCall.
Require Import CertiOS.certiucos.v293.proofs.V293TCBSuccessReturn.
Require Import CertiOS.certiucos.v293.proofs.V293InitReadyPayload.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyTaskInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTarget.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickLifecycle.
Require Import CertiOS.certiucos.v293.proofs.V293NullBytes.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293InitTCBClear.
Require Import CertiOS.certiucos.v293.proofs.V293CanonicalInitReturn.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.rulesoundlib.
Require Import CertiOS.framework.proof.lmachLib.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.sep_combine_lemmas.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import Coq.Lists.List Coq.Sorting.Permutation.
Require Import CertiOS.certiucos.v293.proofs.V293InitPriorityTable.
Require Import CertiOS.certiucos.v293.proofs.V293InitPublishRecords.
Require Import CertiOS.certiucos.v293.proofs.V293PublishRecords.
Require Import CertiOS.certiucos.v293.proofs.V293InitAllRecords.
Require Import CertiOS.certiucos.v293.proofs.V293StartRecord.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitFunction.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitEntry.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitPrefix.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitFields.
Require Import CertiOS.certiucos.v293.proofs.V293TCBPriorityHook.
Require Import CertiOS.certiucos.v293.proofs.V293TCBPublish.
Require Import CertiOS.certiucos.v293.proofs.V293TCBCallSuccess.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewExec.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.code.V293OSTCBInitPrefix.
Require Import CertiOS.certiucos.v293.code.V293OSTCBInitFunction.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.certiucos.v293.proofs.V293InitReadyCommit.
Require Import CertiOS.certiucos.v293.proofs.V293CallRecords.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateTCBEntry.
Require Import Lia.
Require Import CertiOS.certiucos.v293.proofs.V293CallResultShared.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateTCBSuccess.
Require Import CertiOS.certiucos.v293.proofs.V293ReservedCallShared.
Require Import CertiOS.certiucos.v293.code.V293OSTCBPublish.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewWitness.
Require Import CertiOS.certiucos.v293.proofs.V293PublishReturnRecords.
Require Import CertiOS.certiucos.v293.proofs.V293CreatorSharedReturn.
Require Import CertiOS.audit.probes.V293CanonicalInitReturnProbe.
Import ListNotations.
Local Open Scope nat_scope.
(* This heap anchors an independent after-stack-return continuation.
   No stack hook or CPU hook implementation is assumed in these roots. *)
Definition CSRValue := Vptr(800%positive,Int.zero).
Definition CSRLE : env :=
 set(set(set(set(set(set(set(set(set(set(set(set(emp:env)
 101%Z(901%positive,Tint8))109%Z(903%positive,Tint32))
 201%Z(904%positive,Tint32))202%Z(905%positive,Tptr Tvoid))
 203%Z(906%positive,Tptr Tint32))107%Z(907%positive,Tint16))
 108%Z(908%positive,Tptr Tint32))102%Z(909%positive,Tptr Tint32))
 103%Z(910%positive,Tint16))104%Z(911%positive,Tint32))
 105%Z(912%positive,Tptr Tvoid))106%Z(913%positive,Tint8).
Definition CSRBridge value := V293_create_bridge_cells
 901%positive 902%positive 903%positive 406%positive 11(Vint32 Int.zero)(Vptr(700%positive,Int.zero))
 904%positive 905%positive 906%positive 907%positive 17%Z Vnull Vnull(Vint32 Int.zero)
 908%positive 909%positive 910%positive 911%positive 912%positive 913%positive
 value Vnull(Vint32 Int.zero)(Vint32 Int.zero)Vnull(Vint32(Int.repr 66)).
Definition CSRSupport := CIROldFields++CIRLinks++CIRTail++CIRHole false++CIRSentinel.
Definition CSRInitial := CSRBridge Vnull++CSRSupport.
Definition CSRCells := CSRInitial++CIROldRecord.
Definition CSRState M := V293_wstate CIRGE CSRLE M.
Definition CSRRest := V293_rdy_raw_cells CSRSupport(V293_owned_task_records CIRTasks ** Atrue).

Theorem CSRLiteralEntry : CSRState(CIRMemory CSRCells) |= V293_rdy_raw_cells CSRCells Aemp.
Proof.
 unfold CSRState,CSRCells,CSRInitial,CSRBridge,V293_create_bridge_cells,
 V293_create_prefix_cells,V293_stack_argument_cells,V293_create_bridge_extra,
 CSRSupport,CIROldFields,CIRLinks,CIRTail,CIRHole,CIRSentinel,CIROldRecord,CIREntries,CIRPositive,CIROldTid,V293_task_selector.
 cbn[app CIRMemory V293_rdy_raw_cells V293_priority_hole V293_priority_cells repeat update_nth_val].
 CIRLiteral.
Qed.

Theorem CSRSpatialEntry : CSRState(CIRMemory CSRCells) |= V293_rdy_raw_cells(CSRBridge Vnull)CSRRest.
Proof.
 unfold CSRRest. rewrite <-V293_raw_cells_append.
 eapply V293_raw_cells_mono.
 - intros st Held. apply CIROldOwned in Held.
   eapply astar_mono;[intros s H;exact H |intros s H;exact I |exact Held].
 - rewrite <-V293_raw_cells_append. exact CSRLiteralEntry.
Qed.

Theorem CSRStackValueBridge : forall P ks tcb enabled si ci, exists Mf,
 V293_local_steps P
 (curs(sskip(Some CSRValue)),
  (kenil,V293_create_stack_cont 108%Z 106%Z tcb 101%Z 102%Z 103%Z 104%Z 105%Z 107%Z sret ks))
 ((CIRGE,CSRLE,CIRMemory CSRCells),(fun _=>false),(enabled,si,ci))
 (curs(sfexec tcb [Vint32 Int.zero;Vnull;Vint32 Int.zero;Vint32 Int.zero;Vnull;CSRValue;V293_byteval 11]
  V293_TCBInit_argument_types),(kenil,V293_create_TCB_cont 106%Z sret ks))
 ((CIRGE,CSRLE,Mf),(fun _=>false),(enabled,si,ci)) /\
 CSRState Mf |= V293_rdy_raw_cells(CSRBridge CSRValue)CSRRest.
Proof.
 intros P ks tcb enabled si ci.
 eapply(V293_OSTaskCreateExt_after_stack_to_TCB P ks CIRGE CSRLE(CIRMemory CSRCells)
 (fun _=>false)(false,nil,nil)(emp:osabst)(spec_done None)CSRRest enabled si ci
 108%Z 106%Z tcb 101%Z 102%Z 103%Z 104%Z 105%Z 107%Z sret
 901%positive 902%positive 903%positive 406%positive 700%positive 11
 904%positive 905%positive 906%positive 907%positive 17%Z Vnull Vnull(Vint32 Int.zero)
 908%positive 909%positive 910%positive 911%positive 912%positive 913%positive
 Vnull Vnull(Vint32 Int.zero)(Vint32 Int.zero)Vnull(Vint32(Int.repr 66))CSRValue).
 - reflexivity.
 - lia.
 - reflexivity.
 - repeat split;reflexivity.
 - repeat split;reflexivity.
 - exact CSRSpatialEntry.
Qed.

Lemma CSRBridgeLoads : forall M value,
 rule_type_val_match (Tptr Tint32) value=true ->
 CSRState M |= V293_rdy_raw_cells(CSRBridge value)CSRRest ->
 load(Tptr Tint32)M(908%positive,0%Z)=Some value /\
 load(Tptr V293_tcb_type)M(406%positive,44%Z)=Some(Vptr(700%positive,Int.zero)) /\
 load Tint32 M(601%positive,0%Z)=Some(Vint32(Int.repr 77)).
Proof.
 intros M value Valid Held. split.
 - eapply V293_rdy_raw_load with(s:=CSRState M);[ |exact Valid |exact Held].
   unfold CSRBridge,V293_create_bridge_cells. apply in_or_app;right.
   unfold V293_create_bridge_extra. left;reflexivity.
 - split.
   + eapply V293_rdy_raw_load with(s:=CSRState M);[ |reflexivity |exact Held].
     unfold CSRBridge,V293_create_bridge_cells. apply in_or_app;left.
     apply in_or_app;left. unfold V293_create_prefix_cells.
     right;right;right;left;reflexivity.
   + unfold CSRRest in Held. rewrite <-V293_raw_cells_append in Held.
     eapply V293_rdy_raw_load with(s:=CSRState M);[ |reflexivity |exact Held].
     apply in_or_app;right. unfold CSRSupport. do 4(apply in_or_app;right).
     unfold CIRSentinel. left;reflexivity.
Qed.

Theorem CSRStoreOnlyContrast : forall P ks tcb enabled si ci,
 load(Tptr Tint32)(CIRMemory CSRCells)(908%positive,0%Z)=Some Vnull /\
 ~(CSRState(CIRMemory CSRCells) |= V293_rdy_raw_cells(CSRBridge CSRValue)CSRRest) /\
 exists Mf,
 V293_local_steps P
 (curs(sskip(Some CSRValue)),
  (kenil,V293_create_stack_cont 108%Z 106%Z tcb 101%Z 102%Z 103%Z 104%Z 105%Z 107%Z sret ks))
 ((CIRGE,CSRLE,CIRMemory CSRCells),(fun _=>false),(enabled,si,ci))
 (curs(sfexec tcb [Vint32 Int.zero;Vnull;Vint32 Int.zero;Vint32 Int.zero;Vnull;CSRValue;V293_byteval 11]
  V293_TCBInit_argument_types),(kenil,V293_create_TCB_cont 106%Z sret ks))
 ((CIRGE,CSRLE,Mf),(fun _=>false),(enabled,si,ci)) /\
 load(Tptr Tint32)Mf(908%positive,0%Z)=Some CSRValue /\
 load(Tptr V293_tcb_type)Mf(406%positive,44%Z)=Some(Vptr(700%positive,Int.zero)) /\
 load Tint32 Mf(601%positive,0%Z)=Some(Vint32(Int.repr 77)) /\
 CSRState Mf |= V293_rdy_raw_cells(CSRBridge CSRValue)CSRRest.
Proof.
 intros P ks tcb enabled si ci.
 destruct(CSRBridgeLoads _ Vnull eq_refl CSRSpatialEntry)as(Old&Reserved&Sentinel).
 split;[exact Old | ]. split.
 - intro Hyp. destruct(CSRBridgeLoads _ CSRValue eq_refl Hyp)as(New&_).
   rewrite Old in New. discriminate.
 - destruct(CSRStackValueBridge P ks tcb enabled si ci)as(Mf&Exec&Final).
   destruct(CSRBridgeLoads _ CSRValue eq_refl Final)as(New&Slot&Kept).
   exists Mf. split;[exact Exec | ]. split;[exact New | ]. split;[exact Slot | ]. split;assumption.
Qed.
