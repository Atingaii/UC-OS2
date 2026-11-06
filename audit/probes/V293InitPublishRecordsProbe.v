(* Literal uninitialized entry; actual prefix and conditional two-Hook return chain. *)
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
Import ListNotations.
Local Open Scope nat_scope.
Definition ChainOldFields : list V293_record_cell :=
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
Definition ChainInputs : list V293_record_cell :=
 [((208%positive,0%Z),Tptr V293_tcb_type,Vundef);
  ((201%positive,0%Z),Tint8,V293_byteval 11);
  ((202%positive,0%Z),Tptr Tint32,Vnull);
  ((203%positive,0%Z),Tptr Tint32,Vnull);
  ((204%positive,0%Z),Tint16,Vint32 Int.zero);
  ((205%positive,0%Z),Tint32,Vint32 Int.zero);
  ((206%positive,0%Z),Tptr Tvoid,Vnull);
  ((207%positive,0%Z),Tint16,Vint32 Int.zero)].
Definition ChainLinks : list V293_record_cell :=
 [((405%positive,0%Z),Tptr V293_tcb_type,Vptr(301%positive,Int.repr 128));
  ((301%positive,148%Z),Tcom_ptr 410%Z,Vnull)].
Definition ChainSaved : list V293_record_cell :=
 [((209%positive,0%Z),Tint32,Vint32 Int.zero);
  ((406%positive,44%Z),Tptr V293_tcb_type,Vnull)].
Definition ChainTail : list V293_record_cell :=
 [((301%positive,152%Z),Tcom_ptr 410%Z,Vnull);
  ((401%positive,0%Z),Tptr V293_tcb_type,Vptr(301%positive,Int.repr 8));
  ((402%positive,0%Z),Tint8,V293_byteval 2);
  ((403%positive,1%Z),Tint8,V293_byteval 16);
  ((404%positive,0%Z),Tint8,V293_byteval 1);
  ((301%positive,32%Z),Tcom_ptr 410%Z,Vnull)].
Definition ChainOldRecord : list V293_record_cell :=
 [((301%positive,58%Z),(Tint8),(V293_byteval 12));
  ((301%positive,60%Z),(Tint8),(V293_byteval 1));
  ((301%positive,59%Z),(Tint8),(V293_byteval 4));
  ((301%positive,62%Z),(Tint8),(V293_byteval 2));
  ((301%positive,61%Z),(Tint8),(V293_byteval 16));
  ((301%positive,40%Z),(Tptr Tvoid),(Vnull));
  ((301%positive,56%Z),(Tint8),(V293_byteval 0))].
Definition ChainSentinel : list V293_record_cell :=
 [((601%positive,0%Z),(Tint32),(Vint32(Int.repr 77)))].
Definition ChainOldTid : tid := (301%positive,Int.repr 8).
Definition ChainNewTid : tid := (301%positive,Int.repr 128).
Definition ChainTasks : TcbMod.map := sig ChainOldTid (Int.repr 12,rdy,Vnull).
Definition ChainUpdated : TcbMod.map := set ChainTasks ChainNewTid (Int.repr 11,rdy,Vnull).
Definition ChainGE : env := set (set (set (set (set (set (emp:env)
 91%Z (405%positive,Tptr V293_tcb_type)) 92%Z (406%positive,Tarray(Tptr V293_tcb_type) 13))
 93%Z (401%positive,Tptr V293_tcb_type)) 94%Z (402%positive,Tint8))
 95%Z (403%positive,Tarray Tint8 2)) 96%Z (404%positive,Tint8).
Definition ChainLE := V293_tcb_function_env 201%positive 202%positive 203%positive 204%positive 205%positive 206%positive 207%positive 208%positive 209%positive.
Definition ChainCaller : env := sig 777%Z (701%positive,Tint32).
Definition ChainBlocks := V293_tcb_function_blocks 201%positive 202%positive 203%positive 204%positive 205%positive 206%positive 207%positive 208%positive 209%positive.
Definition ChainAddresses := V293_tcb_function_addresses 201%positive 202%positive 203%positive 204%positive 205%positive 206%positive 207%positive 208%positive 209%positive.
Definition ChainInitial := ChainOldFields++ChainInputs++ChainLinks++ChainSaved++ChainTail++ChainSentinel.
Definition ChainCells := ChainInitial++ChainOldRecord.
Fixpoint ChainMemory (cells : list V293_record_cell) : mem :=
 match cells with []=>emp | ((b,i),tp,v)::tail=>
 merge (V293_encoded_memory b i true (encode_val tp v)) (ChainMemory tail) end.
Definition ChainEntryState M := V293_wstate ChainGE ChainLE M.
Definition ChainState M := V293_wstate ChainGE ChainCaller M.
Definition ChainFreed M := forall b tp k, In (b,tp) ChainAddresses -> k<typelen tp -> get M (b,Z.of_nat k)=None.
Definition ChainCode hi hc := V293_TCBInit_prefix 91%Z 108%Z 101%Z 102%Z 103%Z 104%Z 105%Z 106%Z 107%Z
 (V293_TCBInit_success_suffix hi hc).
Definition ChainRemainder := V293_tcb_init_record_remainder 301%positive 128%Z
 Vnull Vnull (Vint32 Int.zero) (Vint32 Int.zero) Vnull (Vint32 Int.zero).
Definition ChainSurvivors := ChainRemainder++
 [((405%positive,0%Z),Tptr V293_tcb_type,Vnull);
  ((406%positive,44%Z),Tptr V293_tcb_type,Vptr ChainNewTid)]++ChainSentinel.
Definition ChainFinalLinks := V293_pub_link_cells 208%positive 301%positive 128%Z
 401%positive 402%positive 403%positive 404%positive 301%positive 8%Z true 11
 (Vptr ChainOldTid) Vnull (Vptr ChainNewTid) 2 24 2 (Vptr ChainNewTid).
Definition ChainPost := V293_owned_task_records ChainUpdated **
 V293_rdy_raw_cells (tl ChainFinalLinks++ChainSurvivors) Atrue.
Definition ChainHookCells (second : bool) := V293_record_hook_cells
 201%positive 202%positive 203%positive 204%positive 205%positive 206%positive 207%positive 208%positive 209%positive
 405%positive 406%positive 301%positive 128%Z 11 Vnull Vnull (Vint32 Int.zero) (Vint32 Int.zero)
 Vnull (Vint32 Int.zero) Vnull (if second then Vptr ChainNewTid else Vnull) (ChainTail++ChainSentinel).
Definition ChainHooks P f hi hc ks enabled si ci (second : bool) :=
 V293_records_hook_return ChainUpdated P (if second then hc else hi) 301%positive 128%Z
 (if second then V293_tcb_second_hook_cont f hi hc ChainCaller ks else V293_tcb_first_hook_cont f hi hc ChainCaller ks)
 ChainGE ChainLE (fun _=>false) (false,nil,nil) (emp:osabst) (spec_done None) enabled si ci (ChainHookCells second).
Ltac ChainOutside :=
 repeat first [rewrite V293_encoded_memory_outside by
 (first [left;congruence | right;cbn [V293_byteval length encode_val typelen list_repeat inj_pointer inj_bytes encode_int List.map];lia])
 |rewrite map_merge_semp by reflexivity];reflexivity.
Ltac ChainApart b start count :=
 apply map_join_merge;apply map_disjoint;intros [other off];
 destruct (Pos.eq_dec other b) as [B|B];
 [subst other;destruct (Z_lt_dec off start) as [Low|Low];
 [left;apply V293_encoded_memory_outside;right;left;exact Low |
 destruct (Z_lt_dec off (start+count)) as [Inside|Outside];
 [right;left;ChainOutside |left;apply V293_encoded_memory_outside;right;right;
 cbn [V293_byteval length encode_val typelen list_repeat inj_pointer inj_bytes encode_int List.map];lia]] |
 left;apply V293_encoded_memory_outside;left;exact B].
Theorem ChainLiteralEntry : ChainEntryState (ChainMemory ChainCells) |= V293_rdy_raw_cells ChainCells Aemp.
Proof.
 unfold ChainEntryState,ChainCells,ChainInitial,ChainOldFields,ChainInputs,ChainLinks,ChainSaved,
  ChainTail,ChainSentinel,ChainOldRecord.
 cbn [app ChainMemory V293_rdy_raw_cells].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 128%Z true (encode_val (Tptr Tint32) (Vundef)));
 [ChainApart 301%positive 128%Z 4%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 178%Z true (encode_val (Tint8) (Vundef)));
 [ChainApart 301%positive 178%Z 1%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 176%Z true (encode_val (Tint8) (Vundef)));
 [ChainApart 301%positive 176%Z 1%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 177%Z true (encode_val (Tint8) (Vundef)));
 [ChainApart 301%positive 177%Z 1%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 172%Z true (encode_val (Tint32) (Vundef)));
 [ChainApart 301%positive 172%Z 4%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 132%Z true (encode_val (Tptr Tvoid) (Vundef)));
 [ChainApart 301%positive 132%Z 4%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 140%Z true (encode_val (Tint32) (Vundef)));
 [ChainApart 301%positive 140%Z 4%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 136%Z true (encode_val (Tptr Tint32) (Vundef)));
 [ChainApart 301%positive 136%Z 4%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 144%Z true (encode_val (Tint16) (Vundef)));
 [ChainApart 301%positive 144%Z 2%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 146%Z true (encode_val (Tint16) (Vundef)));
 [ChainApart 301%positive 146%Z 2%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 183%Z true (encode_val (Tint8) (Vundef)));
 [ChainApart 301%positive 183%Z 1%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 180%Z true (encode_val (Tint8) (Vundef)));
 [ChainApart 301%positive 180%Z 1%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 179%Z true (encode_val (Tint8) (Vundef)));
 [ChainApart 301%positive 179%Z 1%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 182%Z true (encode_val (Tint8) (Vundef)));
 [ChainApart 301%positive 182%Z 1%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 181%Z true (encode_val (Tint8) (Vundef)));
 [ChainApart 301%positive 181%Z 1%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 156%Z true (encode_val (Tcom_ptr 411%Z) (Vundef)));
 [ChainApart 301%positive 156%Z 4%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 164%Z true (encode_val (Tcom_ptr 412%Z) (Vundef)));
 [ChainApart 301%positive 164%Z 4%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 160%Z true (encode_val (Tptr Tvoid) (Vundef)));
 [ChainApart 301%positive 160%Z 4%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 208%positive 0%Z true (encode_val (Tptr V293_tcb_type) (Vundef)));
 [ChainApart 208%positive 0%Z 4%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 201%positive 0%Z true (encode_val (Tint8) (V293_byteval 11)));
 [ChainApart 201%positive 0%Z 1%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 202%positive 0%Z true (encode_val (Tptr Tint32) (Vnull)));
 [ChainApart 202%positive 0%Z 4%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 203%positive 0%Z true (encode_val (Tptr Tint32) (Vnull)));
 [ChainApart 203%positive 0%Z 4%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 204%positive 0%Z true (encode_val (Tint16) (Vint32 Int.zero)));
 [ChainApart 204%positive 0%Z 2%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 205%positive 0%Z true (encode_val (Tint32) (Vint32 Int.zero)));
 [ChainApart 205%positive 0%Z 4%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 206%positive 0%Z true (encode_val (Tptr Tvoid) (Vnull)));
 [ChainApart 206%positive 0%Z 4%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 207%positive 0%Z true (encode_val (Tint16) (Vint32 Int.zero)));
 [ChainApart 207%positive 0%Z 2%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 405%positive 0%Z true (encode_val (Tptr V293_tcb_type) (Vptr(301%positive,Int.repr 128))));
 [ChainApart 405%positive 0%Z 4%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 148%Z true (encode_val (Tcom_ptr 410%Z) (Vnull)));
 [ChainApart 301%positive 148%Z 4%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 209%positive 0%Z true (encode_val (Tint32) (Vint32 Int.zero)));
 [ChainApart 209%positive 0%Z 4%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 406%positive 44%Z true (encode_val (Tptr V293_tcb_type) (Vnull)));
 [ChainApart 406%positive 44%Z 4%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 152%Z true (encode_val (Tcom_ptr 410%Z) (Vnull)));
 [ChainApart 301%positive 152%Z 4%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 401%positive 0%Z true (encode_val (Tptr V293_tcb_type) (Vptr(301%positive,Int.repr 8))));
 [ChainApart 401%positive 0%Z 4%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 402%positive 0%Z true (encode_val (Tint8) (V293_byteval 2)));
 [ChainApart 402%positive 0%Z 1%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 403%positive 1%Z true (encode_val (Tint8) (V293_byteval 16)));
 [ChainApart 403%positive 1%Z 1%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 404%positive 0%Z true (encode_val (Tint8) (V293_byteval 1)));
 [ChainApart 404%positive 0%Z 1%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 32%Z true (encode_val (Tcom_ptr 410%Z) (Vnull)));
 [ChainApart 301%positive 32%Z 4%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 601%positive 0%Z true (encode_val (Tint32) (Vint32(Int.repr 77))));
 [ChainApart 601%positive 0%Z 4%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 58%Z true (encode_val (Tint8) (V293_byteval 12)));
 [ChainApart 301%positive 58%Z 1%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 60%Z true (encode_val (Tint8) (V293_byteval 1)));
 [ChainApart 301%positive 60%Z 1%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 59%Z true (encode_val (Tint8) (V293_byteval 4)));
 [ChainApart 301%positive 59%Z 1%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 62%Z true (encode_val (Tint8) (V293_byteval 2)));
 [ChainApart 301%positive 62%Z 1%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 61%Z true (encode_val (Tint8) (V293_byteval 16)));
 [ChainApart 301%positive 61%Z 1%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 40%Z true (encode_val (Tptr Tvoid) (Vnull)));
 [ChainApart 301%positive 40%Z 4%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 56%Z true (encode_val (Tint8) (V293_byteval 0)));
 [ChainApart 301%positive 56%Z 1%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 split;reflexivity.
Qed.
Lemma ChainEnvironment : V293_pub_env ChainGE ChainLE 108%Z 93%Z 94%Z 95%Z 96%Z
 208%positive 401%positive 402%positive 403%positive 404%positive.
Proof. unfold V293_pub_env,ChainGE,ChainLE,V293_tcb_function_env;repeat split;
 repeat first [rewrite map_get_set |rewrite map_get_set' by discriminate];reflexivity. Qed.
Lemma ChainOldOwned : forall R,
 V293_rdy_raw_cells ChainOldRecord R ==> V293_owned_task_records ChainTasks ** R.
Proof.
 intros R s Owned. apply V293_raw_cells_separate in Owned.
 assert (Held : s |= V293_owned_task_record ChainOldTid (Int.repr 12) rdy Vnull ** R).
 { eapply astar_mono;[apply (V293_raw_to_ready_record 301%positive 8%Z 12);lia |intros st HS;exact HS |exact Owned]. }
 change (s |= (V293_owned_task_record ChainOldTid (Int.repr 12) rdy Vnull ** Aemp) ** R).
 clear -Held. sep auto.
Qed.
Theorem ChainSpatialEntry : ChainEntryState (ChainMemory ChainCells) |=
 V293_rdy_raw_cells ChainInitial (V293_owned_task_records ChainTasks ** Atrue).
Proof.
 eapply V293_raw_cells_mono;[ | ].
 - intros st HS. apply ChainOldOwned in HS.
   eapply astar_mono;[intros s H;exact H |intros s H;exact I |exact HS].
 - rewrite <-V293_raw_cells_append. exact ChainLiteralEntry.
Qed.
Theorem ChainPrefix : forall P f hi hc ks enabled si ci, exists Mf,
 V293_local_steps P (curs(ChainCode hi hc),(kenil,kcall f (V293_TCBInit_function_body hi hc) ChainCaller ks))
 ((ChainGE,ChainLE,ChainMemory ChainCells),(fun _=>false),(enabled,si,ci))
 (curs(sfexec hi [Vptr ChainNewTid] [Tptr V293_tcb_type]),
  (kenil,V293_tcb_first_hook_cont f hi hc ChainCaller ks))
 ((ChainGE,ChainLE,Mf),(fun _=>false),(enabled,si,ci)) /\
 (ChainEntryState Mf |= V293_owned_task_records ChainUpdated ** V293_rdy_raw_cells (ChainHookCells false) Atrue).
Proof.
 intros P f hi hc ks enabled si ci.
 eapply (V293_TCBInit_prefix_to_record_hook ChainTasks P ks ChainGE ChainCaller (ChainMemory ChainCells)
 (fun _=>false) (false,nil,nil) (emp:osabst) (spec_done None) enabled si ci f hi hc
 201%positive 202%positive 203%positive 204%positive 205%positive 206%positive 207%positive 208%positive 209%positive
 405%positive 406%positive 301%positive 128%Z 11 Vnull Vnull (Vint32 Int.zero) (Vint32 Int.zero)
 Vnull (Vint32 Int.zero) Vundef Vnull (fun _=>Vundef) Vnull (ChainTail++ChainSentinel));
 try reflexivity;try lia;try (change (128+55<=4294967295)%Z;lia).
 - repeat split;reflexivity.
 - exact ChainSpatialEntry.
Qed.
Theorem ChainGoodCall : forall P f hi hc ks enabled si ci,
 ChainHooks P f hi hc ks enabled si ci false -> ChainHooks P f hi hc ks enabled si ci true -> exists Mf,
 V293_local_steps P (curs(ChainCode hi hc),(kenil,kcall f (V293_TCBInit_function_body hi hc) ChainCaller ks))
 ((ChainGE,ChainLE,ChainMemory ChainCells),(fun _=>false),(enabled,si,ci))
 (curs(sskip(Some(Vint32 Int.zero))),(kenil,ks)) ((ChainGE,ChainCaller,Mf),(fun _=>false),(enabled,si,ci)) /\
 (ChainState Mf |= ChainPost) /\ ChainFreed Mf.
Proof.
 intros P f hi hc ks enabled si ci Hook1 Hook2.
 eapply (V293_OS_TCBInit_prefix_return_records_under_hooks ChainTasks P f hi hc ChainCaller ks ChainGE
 (ChainMemory ChainCells) (fun _=>false) (false,nil,nil) (emp:osabst) (spec_done None) enabled si ci
 201%positive 202%positive 203%positive 204%positive 205%positive 206%positive 207%positive 208%positive 209%positive
 405%positive 406%positive 301%positive 128%Z 401%positive 402%positive 403%positive 404%positive
 301%positive 8%Z true 11 2 16 1 Vnull Vnull (Vint32 Int.zero) (Vint32 Int.zero) Vnull (Vint32 Int.zero)
 Vundef Vnull (fun _=>Vundef) Vnull Vnull Vnull ChainSentinel);
 try lia;try (change (128+55<=4294967295)%Z;lia);try (change (8+24<=4294967295)%Z;lia).
 - reflexivity.
 - reflexivity.
 - exact ChainEnvironment.
 - reflexivity.
 - repeat constructor;cbn;intuition congruence.
 - repeat split;reflexivity.
 - reflexivity.
 - intros t value Member. change (In (t,value)
    [(ChainOldTid,(Int.repr 12,rdy,Vnull));(ChainNewTid,(Int.repr 11,rdy,Vnull))]) in Member.
   destruct Member as [Same |[Same |Impossible]];[inversion Same;subst |inversion Same;subst |contradiction];
   cbn [ChainOldTid ChainNewTid fst V293_tcb_function_blocks In];intuition discriminate.
 - intros a tp v Member. cbn [V293_pub_link_cells tl app V293_prio_row ChainSentinel
   V293_tcb_init_record_remainder In] in Member.
   repeat destruct Member as [E |Member];try contradiction;inversion E;subst;
   cbn [fst V293_tcb_function_blocks In];intuition discriminate.
 - exact Hook1.
 - exact Hook2.
 - exact ChainSpatialEntry.
Qed.
Lemma ChainRecordsFrameSound : forall tasks R M,
 ChainState M |= V293_owned_task_records tasks ** R -> V293_task_records M tasks.
Proof.
 intros tasks R M Held. apply sat_split in Held.
 destruct Held as (m1&m2&o1&o2&JM&JO&Records&Other).
 pose proof (V293_owned_task_records_sound _ _ Records) as Sound.
 intros t priority status message Lookup.
 eapply V293_task_record_sub;[exists m2;exact JM |apply Sound;exact Lookup].
Qed.
Lemma ChainFinalRead : forall M a tp v,
 In (a,tp,v) (tl ChainFinalLinks++ChainSurvivors) -> rule_type_val_match tp v=true ->
 ChainState M |= ChainPost -> load tp M a=Some v.
Proof.
 intros M a tp v Member Valid Owned.
 change (load tp (getmem(ChainState M)) a=Some v).
 eapply V293_star_load_r;[ |exact Owned]. intros st Raw.
 eapply V293_rdy_raw_load;[exact Member |exact Valid |exact Raw].
Qed.
Definition ChainReads M : Prop :=
 load (Tptr V293_tcb_type) M (406%positive,44%Z)=Some(Vptr ChainNewTid) /\
 load (Tptr V293_tcb_type) M (405%positive,0%Z)=Some Vnull /\
 load (Tptr Tint32) M (301%positive,128%Z)=Some Vnull /\
 load (Tcom_ptr 410%Z) M (301%positive,148%Z)=Some(Vptr ChainOldTid) /\
 load (Tcom_ptr 410%Z) M (301%positive,152%Z)=Some Vnull /\
 load (Tptr V293_tcb_type) M (401%positive,0%Z)=Some(Vptr ChainNewTid) /\
 load (Tcom_ptr 410%Z) M (301%positive,32%Z)=Some(Vptr ChainNewTid) /\
 load Tint8 M (402%positive,0%Z)=Some(V293_byteval 2) /\
 load Tint8 M (403%positive,1%Z)=Some(V293_byteval 24) /\
 load Tint8 M (404%positive,0%Z)=Some(V293_byteval 2) /\
 load Tint32 M (601%positive,0%Z)=Some(Vint32(Int.repr 77)).
Lemma ChainGoodPostReads : forall M, ChainState M |= ChainPost -> ChainReads M.
Proof.
 intros M Owned. unfold ChainReads. repeat split;
 (eapply ChainFinalRead;[unfold ChainFinalLinks,ChainSurvivors,ChainRemainder,ChainSentinel,V293_pub_link_cells,V293_tcb_init_record_remainder;
  cbn [V293_prio_row In app tl];tauto |reflexivity |exact Owned]).
Qed.
Theorem ChainGoodSameMf : forall P f hi hc ks enabled si ci,
 ChainHooks P f hi hc ks enabled si ci false -> ChainHooks P f hi hc ks enabled si ci true -> exists Mf,
 V293_local_steps P (curs(ChainCode hi hc),(kenil,kcall f (V293_TCBInit_function_body hi hc) ChainCaller ks))
 ((ChainGE,ChainLE,ChainMemory ChainCells),(fun _=>false),(enabled,si,ci))
 (curs(sskip(Some(Vint32 Int.zero))),(kenil,ks)) ((ChainGE,ChainCaller,Mf),(fun _=>false),(enabled,si,ci)) /\
 (ChainState Mf |= ChainPost) /\ V293_task_records Mf ChainUpdated /\ ChainReads Mf /\ ChainFreed Mf.
Proof.
 intros P f hi hc ks enabled si ci H1 H2.
 destruct (ChainGoodCall P f hi hc ks enabled si ci H1 H2) as (Mf&Exec&Owned&Freed).
 exists Mf. split;[exact Exec | ]. split;[exact Owned | ].
 split;[eapply ChainRecordsFrameSound;exact Owned | ].
 split;[apply ChainGoodPostReads;exact Owned |exact Freed].
Qed.
(* An unconditional actual prefix reaches a genuinely absent Hook. This is
   not evidence for the conditional downstream execution. *)
Theorem ChainActualMissingHook : forall P f hi hc ks enabled si ci, P hi=None -> exists Mf,
 V293_local_steps P (curs(ChainCode hi hc),(kenil,kcall f (V293_TCBInit_function_body hi hc) ChainCaller ks))
 ((ChainGE,ChainLE,ChainMemory ChainCells),(fun _=>false),(enabled,si,ci))
 (curs(sfexec hi [Vptr ChainNewTid] [Tptr V293_tcb_type]),
  (kenil,V293_tcb_first_hook_cont f hi hc ChainCaller ks))
 ((ChainGE,ChainLE,Mf),(fun _=>false),(enabled,si,ci)) /\
 (ChainEntryState Mf |= V293_owned_task_records ChainUpdated ** V293_rdy_raw_cells (ChainHookCells false) Atrue) /\
 (forall ks' state', ~V293_local_steps P
  (curs(sfexec hi [Vptr ChainNewTid] [Tptr V293_tcb_type]),
   (kenil,V293_tcb_first_hook_cont f hi hc ChainCaller ks))
  ((ChainGE,ChainLE,Mf),(fun _=>false),(enabled,si,ci)) (curs(sskip None),(kenil,ks')) state').
Proof.
 intros P f hi hc ks enabled si ci Missing.
 destruct (ChainPrefix P f hi hc ks enabled si ci) as (Mf&Exec&Owned).
 exists Mf. split;[exact Exec | ]. split;[exact Owned | ].
 intros ks' state'. apply V293_missing_hook_cannot_return. exact Missing.
Qed.
Lemma ChainPrefixRecordsSound : forall tasks R M,
 ChainEntryState M |= V293_owned_task_records tasks ** R -> V293_task_records M tasks.
Proof.
 intros tasks R M Held. apply sat_split in Held.
 destruct Held as (m1&m2&o1&o2&JM&JO&Records&Other).
 pose proof (V293_owned_task_records_sound _ _ Records) as Sound.
 intros t priority status message Lookup.
 eapply V293_task_record_sub;[exists m2;exact JM |apply Sound;exact Lookup].
Qed.
Lemma ChainRecordPriority : forall tasks M p,
 p<13 -> V293_task_records M tasks ->
 get tasks ChainNewTid=Some(Int.repr(Z.of_nat p),rdy,Vnull) ->
 load Tint8 M (301%positive,178%Z)=Some(V293_byteval p).
Proof.
 intros tasks M p Range Sound Lookup. specialize (Sound _ _ _ _ Lookup).
 destruct Sound as (q&Qr&Priority&Fields&Status).
 assert (q=p) by (eapply V293_priority_repr_injective;[exact Qr |exact Range |symmetry;exact Priority]).
 subst q. exact (proj1 Fields).
Qed.
Theorem ChainPrefixExcludesWrong : forall P f hi hc ks enabled si ci, exists Mf,
 V293_local_steps P (curs(ChainCode hi hc),(kenil,kcall f (V293_TCBInit_function_body hi hc) ChainCaller ks))
 ((ChainGE,ChainLE,ChainMemory ChainCells),(fun _=>false),(enabled,si,ci))
 (curs(sfexec hi [Vptr ChainNewTid] [Tptr V293_tcb_type]),
  (kenil,V293_tcb_first_hook_cont f hi hc ChainCaller ks))
 ((ChainGE,ChainLE,Mf),(fun _=>false),(enabled,si,ci)) /\
 (ChainEntryState Mf |= V293_owned_task_records ChainUpdated ** V293_rdy_raw_cells (ChainHookCells false) Atrue) /\
 load Tint8 Mf (301%positive,178%Z)=Some(V293_byteval 11) /\
 ~ ChainEntryState Mf |= V293_owned_task_records (set ChainTasks ChainNewTid (Int.repr 10,rdy,Vnull)) ** Atrue.
Proof.
 intros P f hi hc ks enabled si ci.
 destruct (ChainPrefix P f hi hc ks enabled si ci) as (Mf&Exec&Owned).
 pose proof (ChainPrefixRecordsSound _ _ _ Owned) as Records.
 assert (Read : load Tint8 Mf (301%positive,178%Z)=Some(V293_byteval 11)).
 { eapply (ChainRecordPriority ChainUpdated Mf 11);[lia |exact Records |reflexivity]. }
 exists Mf. split;[exact Exec | ]. split;[exact Owned | ]. split;[exact Read | ].
 intro Bad. pose proof (ChainPrefixRecordsSound _ _ _ Bad) as Wrong.
 pose proof (ChainRecordPriority _ Mf 10 ltac:(lia) Wrong eq_refl) as Physical.
 rewrite Read in Physical. discriminate.
Qed.
Print Assumptions ChainLiteralEntry.
Print Assumptions ChainEnvironment.
Print Assumptions ChainOldOwned.
Print Assumptions ChainSpatialEntry.
Print Assumptions ChainPrefix.
Print Assumptions ChainGoodCall.
Print Assumptions ChainRecordsFrameSound.
Print Assumptions ChainFinalRead.
Print Assumptions ChainGoodPostReads.
Print Assumptions ChainGoodSameMf.
Print Assumptions ChainActualMissingHook.
Print Assumptions ChainPrefixRecordsSound.
Print Assumptions ChainRecordPriority.
Print Assumptions ChainPrefixExcludesWrong.
