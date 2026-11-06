(* Literal actual-call entry has no local objects; same-memory allocation and records. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.certiucos.v293.code.V293OSTCBPublish.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.proofs.V293PublishRecords.
Require Import CertiOS.certiucos.v293.proofs.V293TCBPublish.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitPrefix.
Require Import CertiOS.certiucos.v293.proofs.V293InitAllRecords.
Require Import CertiOS.certiucos.v293.proofs.V293InitTCBList.
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
Require Import CertiOS.certiucos.v293.proofs.V293CallRecords.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitEntry.
Require Import CertiOS.certiucos.v293.proofs.V293TCBCallSuccess.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitFields.
Require Import CertiOS.certiucos.v293.proofs.V293StartRecord.
Require Import CertiOS.certiucos.v293.code.V293OSTCBInitPrefix.
Import ListNotations.
Local Open Scope nat_scope.
Definition CallOldFields : list V293_record_cell :=
 [((301%positive,128%Z),(Tptr Tint32),(Vundef));
  ((301%positive,178%Z),(Tint8),(Vundef));
  ((301%positive,176%Z),(Tint8),(Vundef));
  ((301%positive,177%Z),(Tint8),(Vundef));
  ((301%positive,172%Z),(Tint32),(Vundef));
  ((301%positive,132%Z),(Tptr Tvoid),(Vundef));
  ((301%positive,140%Z),(Tint32),(Vundef));
  ((301%positive,136%Z),(Tptr Tint32),(Vundef));
  ((301%positive,144%Z),(Tint16),(Vundef));
  ((301%positive,146%Z),(Tint16),(Vundef));
  ((301%positive,183%Z),(Tint8),(Vundef));
  ((301%positive,180%Z),(Tint8),(Vundef));
  ((301%positive,179%Z),(Tint8),(Vundef));
  ((301%positive,182%Z),(Tint8),(Vundef));
  ((301%positive,181%Z),(Tint8),(Vundef));
  ((301%positive,156%Z),(Tcom_ptr 411%Z),(Vundef));
  ((301%positive,164%Z),(Tcom_ptr 412%Z),(Vundef));
  ((301%positive,160%Z),(Tptr Tvoid),(Vundef))].
Definition CallLinks : list V293_record_cell :=
 [((405%positive,0%Z),Tptr V293_tcb_type,Vptr(301%positive,Int.repr 128));
  ((301%positive,148%Z),Tcom_ptr 410%Z,Vnull)].
Definition CallSaved : list V293_record_cell :=
 [((406%positive,44%Z),Tptr V293_tcb_type,Vnull)].
Definition CallTail : list V293_record_cell :=
 [((301%positive,152%Z),Tcom_ptr 410%Z,Vnull);
  ((401%positive,0%Z),Tptr V293_tcb_type,Vptr(301%positive,Int.repr 8));
  ((402%positive,0%Z),Tint8,V293_byteval 2);
  ((403%positive,1%Z),Tint8,V293_byteval 16);
  ((404%positive,0%Z),Tint8,V293_byteval 1);
  ((301%positive,32%Z),Tcom_ptr 410%Z,Vnull)].
Definition CallOldRecord : list V293_record_cell :=
 [((301%positive,58%Z),(Tint8),(V293_byteval 12));
  ((301%positive,60%Z),(Tint8),(V293_byteval 1));
  ((301%positive,59%Z),(Tint8),(V293_byteval 4));
  ((301%positive,62%Z),(Tint8),(V293_byteval 2));
  ((301%positive,61%Z),(Tint8),(V293_byteval 16));
  ((301%positive,40%Z),(Tptr Tvoid),(Vnull));
  ((301%positive,56%Z),(Tint8),(V293_byteval 0))].
Definition CallSentinel : list V293_record_cell :=
 [((601%positive,0%Z),(Tint32),(Vint32(Int.repr 77)))].
Definition CallOldTid : tid := (301%positive,Int.repr 8).
Definition CallNewTid : tid := (301%positive,Int.repr 128).
Definition CallTasks : TcbMod.map := sig CallOldTid (Int.repr 12,rdy,Vnull).
Definition CallUpdated : TcbMod.map := set CallTasks CallNewTid (Int.repr 11,rdy,Vnull).
Definition CallGE : env := set (set (set (set (set (set (emp:env)
 91%Z (405%positive,Tptr V293_tcb_type)) 92%Z (406%positive,Tarray(Tptr V293_tcb_type) 13))
 93%Z (401%positive,Tptr V293_tcb_type)) 94%Z (402%positive,Tint8))
 95%Z (403%positive,Tarray Tint8 2)) 96%Z (404%positive,Tint8).
Definition CallLE := V293_tcb_function_env 201%positive 202%positive 203%positive 204%positive 205%positive 206%positive 207%positive 208%positive 209%positive.
Definition CallCaller : env := sig 777%Z (701%positive,Tint32).
Definition CallBlocks := V293_tcb_function_blocks 201%positive 202%positive 203%positive 204%positive 205%positive 206%positive 207%positive 208%positive 209%positive.
Definition CallAddresses := V293_tcb_function_addresses 201%positive 202%positive 203%positive 204%positive 205%positive 206%positive 207%positive 208%positive 209%positive.
Definition CallInitial := CallOldFields++CallLinks++CallSaved++CallTail++CallSentinel.
Definition CallCells := CallInitial++CallOldRecord.
Fixpoint CallMemory (cells : list V293_record_cell) : mem :=
 match cells with []=>emp | ((b,i),tp,v)::tail=>
 merge (V293_encoded_memory b i true (encode_val tp v)) (CallMemory tail) end.
Definition CallEntryState M := V293_wstate CallGE CallLE M.
Definition CallInitialState M := V293_wstate CallGE CallCaller M.
Definition CallState M := V293_wstate CallGE CallCaller M.
Definition CallFreed M := forall b tp k, In (b,tp) CallAddresses -> k<typelen tp -> get M (b,Z.of_nat k)=None.
Definition CallCode f := sfexec f
 [Vint32 Int.zero;Vnull;Vint32 Int.zero;Vint32 Int.zero;Vnull;Vnull;V293_byteval 11]
 V293_TCBInit_argument_types.
Definition CallRemainder := V293_tcb_init_record_remainder 301%positive 128%Z
 Vnull Vnull (Vint32 Int.zero) (Vint32 Int.zero) Vnull (Vint32 Int.zero).
Definition CallSurvivors := CallRemainder++
 [((405%positive,0%Z),Tptr V293_tcb_type,Vnull);
  ((406%positive,44%Z),Tptr V293_tcb_type,Vptr CallNewTid)]++CallSentinel.
Definition CallFinalLinks := V293_pub_link_cells 208%positive 301%positive 128%Z
 401%positive 402%positive 403%positive 404%positive 301%positive 8%Z true 11
 (Vptr CallOldTid) Vnull (Vptr CallNewTid) 2 24 2 (Vptr CallNewTid).
Definition CallPost := V293_owned_task_records CallUpdated **
 V293_rdy_raw_cells (tl CallFinalLinks++CallSurvivors) Atrue.
Definition CallHookCells (second : bool) := V293_record_hook_cells
 201%positive 202%positive 203%positive 204%positive 205%positive 206%positive 207%positive 208%positive 209%positive
 405%positive 406%positive 301%positive 128%Z 11 Vnull Vnull (Vint32 Int.zero) (Vint32 Int.zero)
 Vnull (Vint32 Int.zero) Vnull (if second then Vptr CallNewTid else Vnull) (CallTail++CallSentinel).
Definition CallHooks P f hi hc ks enabled si ci (second : bool) :=
 V293_records_hook_return CallUpdated P (if second then hc else hi) 301%positive 128%Z
 (if second then V293_tcb_second_hook_cont f hi hc CallCaller ks else V293_tcb_first_hook_cont f hi hc CallCaller ks)
 CallGE CallLE (fun _=>false) (false,nil,nil) (emp:osabst) (spec_done None) enabled si ci (CallHookCells second).
Ltac CallOutside :=
 repeat first [rewrite V293_encoded_memory_outside by
 (first [left;congruence | right;cbn [V293_byteval length encode_val typelen list_repeat inj_pointer inj_bytes encode_int List.map];lia])
 |rewrite map_merge_semp by reflexivity];reflexivity.
Ltac CallApart b start count :=
 apply map_join_merge;apply map_disjoint;intros [other off];
 destruct (Pos.eq_dec other b) as [B|B];
 [subst other;destruct (Z_lt_dec off start) as [Low|Low];
 [left;apply V293_encoded_memory_outside;right;left;exact Low |
 destruct (Z_lt_dec off (start+count)) as [Inside|Outside];
 [right;left;CallOutside |left;apply V293_encoded_memory_outside;right;right;
 cbn [V293_byteval length encode_val typelen list_repeat inj_pointer inj_bytes encode_int List.map];lia]] |
 left;apply V293_encoded_memory_outside;left;exact B].
Theorem CallLiteralEntry : CallInitialState (CallMemory CallCells) |= V293_rdy_raw_cells CallCells Aemp.
Proof.
 unfold CallInitialState,CallCells,CallInitial,CallOldFields,CallLinks,CallSaved,
  CallTail,CallSentinel,CallOldRecord.
 cbn [app CallMemory V293_rdy_raw_cells].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 128%Z true (encode_val (Tptr Tint32) (Vundef)));
 [CallApart 301%positive 128%Z 4%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 178%Z true (encode_val (Tint8) (Vundef)));
 [CallApart 301%positive 178%Z 1%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 176%Z true (encode_val (Tint8) (Vundef)));
 [CallApart 301%positive 176%Z 1%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 177%Z true (encode_val (Tint8) (Vundef)));
 [CallApart 301%positive 177%Z 1%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 172%Z true (encode_val (Tint32) (Vundef)));
 [CallApart 301%positive 172%Z 4%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 132%Z true (encode_val (Tptr Tvoid) (Vundef)));
 [CallApart 301%positive 132%Z 4%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 140%Z true (encode_val (Tint32) (Vundef)));
 [CallApart 301%positive 140%Z 4%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 136%Z true (encode_val (Tptr Tint32) (Vundef)));
 [CallApart 301%positive 136%Z 4%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 144%Z true (encode_val (Tint16) (Vundef)));
 [CallApart 301%positive 144%Z 2%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 146%Z true (encode_val (Tint16) (Vundef)));
 [CallApart 301%positive 146%Z 2%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 183%Z true (encode_val (Tint8) (Vundef)));
 [CallApart 301%positive 183%Z 1%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 180%Z true (encode_val (Tint8) (Vundef)));
 [CallApart 301%positive 180%Z 1%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 179%Z true (encode_val (Tint8) (Vundef)));
 [CallApart 301%positive 179%Z 1%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 182%Z true (encode_val (Tint8) (Vundef)));
 [CallApart 301%positive 182%Z 1%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 181%Z true (encode_val (Tint8) (Vundef)));
 [CallApart 301%positive 181%Z 1%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 156%Z true (encode_val (Tcom_ptr 411%Z) (Vundef)));
 [CallApart 301%positive 156%Z 4%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 164%Z true (encode_val (Tcom_ptr 412%Z) (Vundef)));
 [CallApart 301%positive 164%Z 4%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 160%Z true (encode_val (Tptr Tvoid) (Vundef)));
 [CallApart 301%positive 160%Z 4%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 405%positive 0%Z true (encode_val (Tptr V293_tcb_type) (Vptr(301%positive,Int.repr 128))));
 [CallApart 405%positive 0%Z 4%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 148%Z true (encode_val (Tcom_ptr 410%Z) (Vnull)));
 [CallApart 301%positive 148%Z 4%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 406%positive 44%Z true (encode_val (Tptr V293_tcb_type) (Vnull)));
 [CallApart 406%positive 44%Z 4%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 152%Z true (encode_val (Tcom_ptr 410%Z) (Vnull)));
 [CallApart 301%positive 152%Z 4%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 401%positive 0%Z true (encode_val (Tptr V293_tcb_type) (Vptr(301%positive,Int.repr 8))));
 [CallApart 401%positive 0%Z 4%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 402%positive 0%Z true (encode_val (Tint8) (V293_byteval 2)));
 [CallApart 402%positive 0%Z 1%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 403%positive 1%Z true (encode_val (Tint8) (V293_byteval 16)));
 [CallApart 403%positive 1%Z 1%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 404%positive 0%Z true (encode_val (Tint8) (V293_byteval 1)));
 [CallApart 404%positive 0%Z 1%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 32%Z true (encode_val (Tcom_ptr 410%Z) (Vnull)));
 [CallApart 301%positive 32%Z 4%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 601%positive 0%Z true (encode_val (Tint32) (Vint32(Int.repr 77))));
 [CallApart 601%positive 0%Z 4%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 58%Z true (encode_val (Tint8) (V293_byteval 12)));
 [CallApart 301%positive 58%Z 1%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 60%Z true (encode_val (Tint8) (V293_byteval 1)));
 [CallApart 301%positive 60%Z 1%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 59%Z true (encode_val (Tint8) (V293_byteval 4)));
 [CallApart 301%positive 59%Z 1%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 62%Z true (encode_val (Tint8) (V293_byteval 2)));
 [CallApart 301%positive 62%Z 1%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 61%Z true (encode_val (Tint8) (V293_byteval 16)));
 [CallApart 301%positive 61%Z 1%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 40%Z true (encode_val (Tptr Tvoid) (Vnull)));
 [CallApart 301%positive 40%Z 4%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 56%Z true (encode_val (Tint8) (V293_byteval 0)));
 [CallApart 301%positive 56%Z 1%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 split;reflexivity.
Qed.
Lemma CallEnvironment : V293_pub_env CallGE CallLE 108%Z 93%Z 94%Z 95%Z 96%Z
 208%positive 401%positive 402%positive 403%positive 404%positive.
Proof. unfold V293_pub_env,CallGE,CallLE,V293_tcb_function_env;repeat split;
 repeat first [rewrite map_get_set |rewrite map_get_set' by discriminate];reflexivity. Qed.
Lemma CallOldOwned : forall R,
 V293_rdy_raw_cells CallOldRecord R ==> V293_owned_task_records CallTasks ** R.
Proof.
 intros R s Owned. apply V293_raw_cells_separate in Owned.
 assert (Held : s |= V293_owned_task_record CallOldTid (Int.repr 12) rdy Vnull ** R).
 { eapply astar_mono;[apply (V293_raw_to_ready_record 301%positive 8%Z 12);lia |intros st HS;exact HS |exact Owned]. }
 change (s |= (V293_owned_task_record CallOldTid (Int.repr 12) rdy Vnull ** Aemp) ** R).
 clear -Held. sep auto.
Qed.
Theorem CallSpatialEntry : CallInitialState (CallMemory CallCells) |=
 V293_rdy_raw_cells CallInitial (V293_owned_task_records CallTasks ** Atrue).
Proof.
 eapply V293_raw_cells_mono;[ | ].
 - intros st HS. apply CallOldOwned in HS.
   eapply astar_mono;[intros s H;exact H |intros s H;exact I |exact HS].
 - rewrite <-V293_raw_cells_append. exact CallLiteralEntry.
Qed.
Lemma CallNoInitialLocals : forall b i, In b CallBlocks -> get (CallMemory CallCells) (b,i)=None.
Proof.
 intros b i Member. unfold CallBlocks,V293_tcb_function_blocks in Member.
 repeat destruct Member as [Same|Member];try contradiction;subst b;
 unfold CallCells,CallInitial,CallOldFields,CallLinks,CallSaved,CallTail,CallSentinel,CallOldRecord;
 cbn [app CallMemory];repeat first [rewrite V293_encoded_memory_outside by (left;discriminate)
 |rewrite map_merge_semp by reflexivity];reflexivity.
Qed.
Lemma CallFresh : forall b, In b CallBlocks -> fresh (CallMemory CallCells) b.
Proof.
 intros b Member a i Same [v Read]. subst a. rewrite CallNoInitialLocals in Read by exact Member. discriminate.
Qed.
Lemma CallND : NoDup CallBlocks.
Proof. repeat constructor;cbn;intuition congruence. Qed.
Theorem CallPrologue : forall P f hi hc ks enabled si ci,
 P f=Some(V293_TCBInit_function hi hc) -> exists Mi,
 V293_local_steps P (curs(CallCode f),(kenil,ks))
 ((CallGE,CallCaller,CallMemory CallCells),(fun _=>false),(enabled,si,ci))
 (curs(V293_TCBInit_prefix 91%Z 108%Z 101%Z 102%Z 103%Z 104%Z 105%Z 106%Z 107%Z
   (V293_TCBInit_success_suffix hi hc)),(kenil,kcall f (V293_TCBInit_function_body hi hc) CallCaller ks))
 ((CallGE,CallLE,Mi),(fun _=>false),(enabled,si,ci)) /\
 (CallEntryState Mi |= V293_owned_task_records CallTasks ** V293_rdy_raw_cells
 (V293_tcb_function_cells 201%positive 202%positive 203%positive 204%positive 205%positive 206%positive 207%positive 208%positive 209%positive
 (V293_byteval 11) Vnull Vnull (Vint32 Int.zero) (Vint32 Int.zero) Vnull (Vint32 Int.zero) Vundef (Vint32 Int.zero)++CallInitial) Atrue).
Proof.
 intros P f hi hc ks enabled si ci Program.
 eapply (V293_tcb_call_prologue_records CallTasks P ks CallGE CallCaller (CallMemory CallCells)
 (fun _=>false) (false,nil,nil) (emp:osabst) (spec_done None) enabled si ci f hi hc
 201%positive 202%positive 203%positive 204%positive 205%positive 206%positive 207%positive 208%positive 209%positive
 (V293_byteval 11) Vnull Vnull (Vint32 Int.zero) (Vint32 Int.zero) Vnull (Vint32 Int.zero) CallInitial).
 - exact Program.
 - exact CallND.
 - exact CallFresh.
 - repeat split;reflexivity.
 - apply V293_raw_cells_move_frame. exact CallSpatialEntry.
Qed.
Theorem CallPrefix : forall P f hi hc ks enabled si ci,
 P f=Some(V293_TCBInit_function hi hc) -> exists Mf,
 V293_local_steps P (curs(CallCode f),(kenil,ks))
 ((CallGE,CallCaller,CallMemory CallCells),(fun _=>false),(enabled,si,ci))
 (curs(sfexec hi [Vptr CallNewTid] [Tptr V293_tcb_type]),
  (kenil,V293_tcb_first_hook_cont f hi hc CallCaller ks))
 ((CallGE,CallLE,Mf),(fun _=>false),(enabled,si,ci)) /\
 (CallEntryState Mf |= V293_owned_task_records CallUpdated ** V293_rdy_raw_cells (CallHookCells false) Atrue).
Proof.
 intros P f hi hc ks enabled si ci Program.
 destruct (CallPrologue P f hi hc ks enabled si ci Program) as (Mi&Prologue&Allocated).
 assert (Start : CallEntryState Mi |= V293_rdy_raw_cells
 (V293_tcb_init_old_fields 301%positive 128%Z (fun _=>Vundef)++
 V293_tcb_prefix_inputs 208%positive 201%positive 202%positive 203%positive 204%positive 205%positive 206%positive 207%positive
 Vundef 11 Vnull Vnull (Vint32 Int.zero) (Vint32 Int.zero) Vnull (Vint32 Int.zero)++
 V293_tcb_prefix_links 405%positive 301%positive 128%Z (Vptr CallNewTid) Vnull++
 ((209%positive,0%Z),Tint32,Vint32 Int.zero)::((406%positive,44%Z),Tptr V293_tcb_type,Vnull)::(CallTail++CallSentinel))
 (V293_owned_task_records CallTasks ** Atrue)).
 { change (CallEntryState Mi |= V293_owned_task_records CallTasks ** V293_rdy_raw_cells
   (V293_tcb_function_cells 201%positive 202%positive 203%positive 204%positive 205%positive 206%positive 207%positive 208%positive 209%positive
    (V293_byteval 11) Vnull Vnull (Vint32 Int.zero) (Vint32 Int.zero) Vnull (Vint32 Int.zero) Vundef (Vint32 Int.zero)++
    (V293_tcb_init_old_fields 301%positive 128%Z (fun _=>Vundef)++
     V293_tcb_prefix_links 405%positive 301%positive 128%Z (Vptr CallNewTid) Vnull++
     ((406%positive,44%Z),Tptr V293_tcb_type,Vnull)::(CallTail++CallSentinel))) Atrue) in Allocated.
   apply V293_raw_cells_collect_frame in Allocated.
   repeat rewrite V293_raw_cells_append in Allocated |- *.
   apply V293_raw_cells_swap in Allocated.
   eapply V293_raw_cells_mono;[ |exact Allocated]. intros st Held.
   unfold V293_tcb_function_cells,V293_tcb_prefix_inputs,V293_tcb_init_input_cells,V293_tcb_prefix_links in Held |- *.
   cbn [V293_rdy_raw_cells tl] in Held |- *. clear -Held. sep auto. }
 destruct (V293_TCBInit_prefix_to_record_hook CallTasks P ks CallGE CallCaller Mi
 (fun _=>false) (false,nil,nil) (emp:osabst) (spec_done None) enabled si ci f hi hc
 201%positive 202%positive 203%positive 204%positive 205%positive 206%positive 207%positive 208%positive 209%positive
 405%positive 406%positive 301%positive 128%Z 11 Vnull Vnull (Vint32 Int.zero) (Vint32 Int.zero)
 Vnull (Vint32 Int.zero) Vundef Vnull (fun _=>Vundef) Vnull (CallTail++CallSentinel)
 eq_refl ltac:(lia) ltac:(lia) ltac:(change (128+55<=4294967295)%Z;lia) eq_refl
 ltac:(repeat split;reflexivity) eq_refl Start) as (Mf&Prefix&Final).
 exists Mf. split;[eapply V293_local_trans;[exact Prologue |exact Prefix] |exact Final].
Qed.
Theorem CallGoodCall : forall P f hi hc ks enabled si ci,
 P f=Some(V293_TCBInit_function hi hc) ->
 CallHooks P f hi hc ks enabled si ci false -> CallHooks P f hi hc ks enabled si ci true -> exists Mf,
 V293_local_steps P (curs(CallCode f),(kenil,ks))
 ((CallGE,CallCaller,CallMemory CallCells),(fun _=>false),(enabled,si,ci))
 (curs(sskip(Some(Vint32 Int.zero))),(kenil,ks)) ((CallGE,CallCaller,Mf),(fun _=>false),(enabled,si,ci)) /\
 (CallState Mf |= CallPost) /\ CallFreed Mf.
Proof.
 intros P f hi hc ks enabled si ci Program Hook1 Hook2.
 eapply (V293_OS_TCBInit_call_return_records_under_hooks CallTasks P f hi hc CallCaller ks CallGE
 (CallMemory CallCells) (fun _=>false) (false,nil,nil) (emp:osabst) (spec_done None) enabled si ci
 201%positive 202%positive 203%positive 204%positive 205%positive 206%positive 207%positive 208%positive 209%positive
 405%positive 406%positive 301%positive 128%Z 401%positive 402%positive 403%positive 404%positive
 301%positive 8%Z true 11 2 16 1 Vnull Vnull (Vint32 Int.zero) (Vint32 Int.zero) Vnull (Vint32 Int.zero)
 Vnull (fun _=>Vundef) Vnull Vnull Vnull CallSentinel);
 try lia;try (change (128+55<=4294967295)%Z;lia);try (change (8+24<=4294967295)%Z;lia).
 - exact Program.
 - exact CallFresh.
 - reflexivity.
 - reflexivity.
 - exact CallEnvironment.
 - reflexivity.
 - repeat constructor;cbn;intuition congruence.
 - repeat split;reflexivity.
 - reflexivity.
 - intros t value Member. change (In (t,value)
    [(CallOldTid,(Int.repr 12,rdy,Vnull));(CallNewTid,(Int.repr 11,rdy,Vnull))]) in Member.
   destruct Member as [Same |[Same |Impossible]];[inversion Same;subst |inversion Same;subst |contradiction];
   cbn [CallOldTid CallNewTid fst V293_tcb_function_blocks In];intuition discriminate.
 - intros a tp v Member. cbn [V293_pub_link_cells tl app V293_prio_row CallSentinel
   V293_tcb_init_record_remainder In] in Member.
   repeat destruct Member as [E |Member];try contradiction;inversion E;subst;
   cbn [fst V293_tcb_function_blocks In];intuition discriminate.
 - exact Hook1.
 - exact Hook2.
 - exact CallSpatialEntry.
Qed.
Lemma CallRecordsFrameSound : forall tasks R M,
 CallState M |= V293_owned_task_records tasks ** R -> V293_task_records M tasks.
Proof.
 intros tasks R M Held. apply sat_split in Held.
 destruct Held as (m1&m2&o1&o2&JM&JO&Records&Other).
 pose proof (V293_owned_task_records_sound _ _ Records) as Sound.
 intros t priority status message Lookup.
 eapply V293_task_record_sub;[exists m2;exact JM |apply Sound;exact Lookup].
Qed.
Lemma CallFinalRead : forall M a tp v,
 In (a,tp,v) (tl CallFinalLinks++CallSurvivors) -> rule_type_val_match tp v=true ->
 CallState M |= CallPost -> load tp M a=Some v.
Proof.
 intros M a tp v Member Valid Owned.
 change (load tp (getmem(CallState M)) a=Some v).
 eapply V293_star_load_r;[ |exact Owned]. intros st Raw.
 eapply V293_rdy_raw_load;[exact Member |exact Valid |exact Raw].
Qed.
Definition CallReads M : Prop :=
 load (Tptr V293_tcb_type) M (406%positive,44%Z)=Some(Vptr CallNewTid) /\
 load (Tptr V293_tcb_type) M (405%positive,0%Z)=Some Vnull /\
 load (Tptr Tint32) M (301%positive,128%Z)=Some Vnull /\
 load (Tcom_ptr 410%Z) M (301%positive,148%Z)=Some(Vptr CallOldTid) /\
 load (Tcom_ptr 410%Z) M (301%positive,152%Z)=Some Vnull /\
 load (Tptr V293_tcb_type) M (401%positive,0%Z)=Some(Vptr CallNewTid) /\
 load (Tcom_ptr 410%Z) M (301%positive,32%Z)=Some(Vptr CallNewTid) /\
 load Tint8 M (402%positive,0%Z)=Some(V293_byteval 2) /\
 load Tint8 M (403%positive,1%Z)=Some(V293_byteval 24) /\
 load Tint8 M (404%positive,0%Z)=Some(V293_byteval 2) /\
 load Tint32 M (601%positive,0%Z)=Some(Vint32(Int.repr 77)).
Lemma CallGoodPostReads : forall M, CallState M |= CallPost -> CallReads M.
Proof.
 intros M Owned. unfold CallReads. repeat split;
 (eapply CallFinalRead;[unfold CallFinalLinks,CallSurvivors,CallRemainder,CallSentinel,V293_pub_link_cells,V293_tcb_init_record_remainder;
  cbn [V293_prio_row In app tl];tauto |reflexivity |exact Owned]).
Qed.
Theorem CallGoodSameMf : forall P f hi hc ks enabled si ci,
 P f=Some(V293_TCBInit_function hi hc) ->
 CallHooks P f hi hc ks enabled si ci false -> CallHooks P f hi hc ks enabled si ci true -> exists Mf,
 V293_local_steps P (curs(CallCode f),(kenil,ks))
 ((CallGE,CallCaller,CallMemory CallCells),(fun _=>false),(enabled,si,ci))
 (curs(sskip(Some(Vint32 Int.zero))),(kenil,ks)) ((CallGE,CallCaller,Mf),(fun _=>false),(enabled,si,ci)) /\
 (CallState Mf |= CallPost) /\ V293_task_records Mf CallUpdated /\ CallReads Mf /\ CallFreed Mf.
Proof.
 intros P f hi hc ks enabled si ci Program H1 H2.
 destruct (CallGoodCall P f hi hc ks enabled si ci Program H1 H2) as (Mf&Exec&Owned&Freed).
 exists Mf. split;[exact Exec | ]. split;[exact Owned | ].
 split;[eapply CallRecordsFrameSound;exact Owned | ].
 split;[apply CallGoodPostReads;exact Owned |exact Freed].
Qed.
(* An unconditional actual prefix reaches a genuinely absent Hook. This is
   not evidence for the conditional downstream execution. *)
Theorem CallActualMissingHook : forall P f hi hc ks enabled si ci,
 P f=Some(V293_TCBInit_function hi hc) -> P hi=None -> exists Mf,
 V293_local_steps P (curs(CallCode f),(kenil,ks))
 ((CallGE,CallCaller,CallMemory CallCells),(fun _=>false),(enabled,si,ci))
 (curs(sfexec hi [Vptr CallNewTid] [Tptr V293_tcb_type]),
  (kenil,V293_tcb_first_hook_cont f hi hc CallCaller ks))
 ((CallGE,CallLE,Mf),(fun _=>false),(enabled,si,ci)) /\
 (CallEntryState Mf |= V293_owned_task_records CallUpdated ** V293_rdy_raw_cells (CallHookCells false) Atrue) /\
 (forall ks' state', ~V293_local_steps P
  (curs(sfexec hi [Vptr CallNewTid] [Tptr V293_tcb_type]),
   (kenil,V293_tcb_first_hook_cont f hi hc CallCaller ks))
  ((CallGE,CallLE,Mf),(fun _=>false),(enabled,si,ci)) (curs(sskip None),(kenil,ks')) state').
Proof.
 intros P f hi hc ks enabled si ci Program Missing.
 destruct (CallPrefix P f hi hc ks enabled si ci Program) as (Mf&Exec&Owned).
 exists Mf. split;[exact Exec | ]. split;[exact Owned | ].
 intros ks' state'. apply V293_missing_hook_cannot_return. exact Missing.
Qed.
Lemma CallPrefixRecordsSound : forall tasks R M,
 CallEntryState M |= V293_owned_task_records tasks ** R -> V293_task_records M tasks.
Proof.
 intros tasks R M Held. apply sat_split in Held.
 destruct Held as (m1&m2&o1&o2&JM&JO&Records&Other).
 pose proof (V293_owned_task_records_sound _ _ Records) as Sound.
 intros t priority status message Lookup.
 eapply V293_task_record_sub;[exists m2;exact JM |apply Sound;exact Lookup].
Qed.
Lemma CallRecordPriority : forall tasks M p,
 p<13 -> V293_task_records M tasks ->
 get tasks CallNewTid=Some(Int.repr(Z.of_nat p),rdy,Vnull) ->
 load Tint8 M (301%positive,178%Z)=Some(V293_byteval p).
Proof.
 intros tasks M p Range Sound Lookup. specialize (Sound _ _ _ _ Lookup).
 destruct Sound as (q&Qr&Priority&Fields&Status).
 assert (q=p) by (eapply V293_priority_repr_injective;[exact Qr |exact Range |symmetry;exact Priority]).
 subst q. exact (proj1 Fields).
Qed.
Theorem CallPrefixExcludesWrong : forall P f hi hc ks enabled si ci,
 P f=Some(V293_TCBInit_function hi hc) -> exists Mf,
 V293_local_steps P (curs(CallCode f),(kenil,ks))
 ((CallGE,CallCaller,CallMemory CallCells),(fun _=>false),(enabled,si,ci))
 (curs(sfexec hi [Vptr CallNewTid] [Tptr V293_tcb_type]),
  (kenil,V293_tcb_first_hook_cont f hi hc CallCaller ks))
 ((CallGE,CallLE,Mf),(fun _=>false),(enabled,si,ci)) /\
 (CallEntryState Mf |= V293_owned_task_records CallUpdated ** V293_rdy_raw_cells (CallHookCells false) Atrue) /\
 load Tint8 Mf (301%positive,178%Z)=Some(V293_byteval 11) /\
 ~ CallEntryState Mf |= V293_owned_task_records (set CallTasks CallNewTid (Int.repr 10,rdy,Vnull)) ** Atrue.
Proof.
 intros P f hi hc ks enabled si ci Program.
 destruct (CallPrefix P f hi hc ks enabled si ci Program) as (Mf&Exec&Owned).
 pose proof (CallPrefixRecordsSound _ _ _ Owned) as Records.
 assert (Read : load Tint8 Mf (301%positive,178%Z)=Some(V293_byteval 11)).
 { eapply (CallRecordPriority CallUpdated Mf 11);[lia |exact Records |reflexivity]. }
 exists Mf. split;[exact Exec | ]. split;[exact Owned | ]. split;[exact Read | ].
 intro Bad. pose proof (CallPrefixRecordsSound _ _ _ Bad) as Wrong.
 pose proof (CallRecordPriority _ Mf 10 ltac:(lia) Wrong eq_refl) as Physical.
 rewrite Read in Physical. discriminate.
Qed.
Print Assumptions CallLiteralEntry.
Print Assumptions CallEnvironment.
Print Assumptions CallOldOwned.
Print Assumptions CallSpatialEntry.
Print Assumptions CallPrefix.
Print Assumptions CallGoodCall.
Print Assumptions CallRecordsFrameSound.
Print Assumptions CallFinalRead.
Print Assumptions CallGoodPostReads.
Print Assumptions CallGoodSameMf.
Print Assumptions CallActualMissingHook.
Print Assumptions CallPrefixRecordsSound.
Print Assumptions CallRecordPriority.
Print Assumptions CallPrefixExcludesWrong.
Print Assumptions CallNoInitialLocals.
Print Assumptions CallFresh.
Print Assumptions CallND.
Print Assumptions CallPrologue.

Definition CallFixtureProgram (f:fid) : option function :=
 if Z.eq_dec f 900%Z then Some(V293_TCBInit_function 901%Z 902%Z) else None.
Theorem CallMissingHookFixture : forall ks enabled si ci, exists Mf,
 V293_local_steps CallFixtureProgram (curs(CallCode 900%Z),(kenil,ks))
 ((CallGE,CallCaller,CallMemory CallCells),(fun _=>false),(enabled,si,ci))
 (curs(sfexec 901%Z [Vptr CallNewTid] [Tptr V293_tcb_type]),
  (kenil,V293_tcb_first_hook_cont 900%Z 901%Z 902%Z CallCaller ks))
 ((CallGE,CallLE,Mf),(fun _=>false),(enabled,si,ci)) /\
 (CallEntryState Mf |= V293_owned_task_records CallUpdated ** V293_rdy_raw_cells (CallHookCells false) Atrue) /\
 (forall ks' state', ~V293_local_steps CallFixtureProgram
  (curs(sfexec 901%Z [Vptr CallNewTid] [Tptr V293_tcb_type]),
   (kenil,V293_tcb_first_hook_cont 900%Z 901%Z 902%Z CallCaller ks))
  ((CallGE,CallLE,Mf),(fun _=>false),(enabled,si,ci)) (curs(sskip None),(kenil,ks')) state').
Proof.
 intros ks enabled si ci. apply CallActualMissingHook;reflexivity.
Qed.
Print Assumptions CallMissingHookFixture.
