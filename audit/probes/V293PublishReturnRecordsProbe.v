(* Independent literal publication followed by actual return/free; no Hook oracle. *)
Require Import CertiOS.framework.include_frm.
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
Import ListNotations.
Local Open Scope nat_scope.
Definition RetLinks : list V293_record_cell :=
 [((208%positive,0%Z),(Tptr V293_tcb_type),(Vptr(301%positive,Int.repr 128)));
  ((301%positive,148%Z),(Tcom_ptr 410%Z),(Vnull));
  ((301%positive,152%Z),(Tcom_ptr 410%Z),(Vnull));
  ((401%positive,0%Z),(Tptr V293_tcb_type),(Vptr(301%positive,Int.repr 8)));
  ((402%positive,0%Z),(Tint8),(V293_byteval 2));
  ((403%positive,1%Z),(Tint8),(V293_byteval 16));
  ((404%positive,0%Z),(Tint8),(V293_byteval 1));
  ((301%positive,32%Z),(Tcom_ptr 410%Z),(Vnull))].
Definition RetNewFields : list V293_record_cell :=
 [((301%positive,178%Z),(Tint8),(V293_byteval 11));
  ((301%positive,180%Z),(Tint8),(V293_byteval 1));
  ((301%positive,179%Z),(Tint8),(V293_byteval 3));
  ((301%positive,182%Z),(Tint8),(V293_byteval 2));
  ((301%positive,181%Z),(Tint8),(V293_byteval 8));
  ((301%positive,160%Z),(Tptr Tvoid),(Vnull));
  ((301%positive,176%Z),(Tint8),(V293_byteval 0))].
Definition RetOldFields : list V293_record_cell :=
 [((301%positive,58%Z),(Tint8),(V293_byteval 12));
  ((301%positive,60%Z),(Tint8),(V293_byteval 1));
  ((301%positive,59%Z),(Tint8),(V293_byteval 4));
  ((301%positive,62%Z),(Tint8),(V293_byteval 2));
  ((301%positive,61%Z),(Tint8),(V293_byteval 16));
  ((301%positive,40%Z),(Tptr Tvoid),(Vnull));
  ((301%positive,56%Z),(Tint8),(V293_byteval 0))].
Definition RetSentinel : list V293_record_cell :=
 [((601%positive,0%Z),(Tint32),(Vint32(Int.repr 77)))].
Definition RetOldTid : tid := (301%positive,Int.repr 8).
Definition RetNewTid : tid := (301%positive,Int.repr 128).
Definition RetTasks : TcbMod.map := sig RetOldTid (Int.repr 12,rdy,Vnull).
Definition RetUpdated : TcbMod.map := set RetTasks RetNewTid (Int.repr 11,rdy,Vnull).
Definition RetGE : env := set (set (set (set (emp:env)
 93%Z (401%positive,Tptr V293_tcb_type)) 94%Z (402%positive,Tint8))
 95%Z (403%positive,Tarray Tint8 2)) 96%Z (404%positive,Tint8).
Definition RetLE := V293_tcb_function_env 201%positive 202%positive 203%positive 204%positive 205%positive 206%positive 207%positive 208%positive 209%positive.
Definition RetCaller : env := sig 777%Z (701%positive,Tint32).
Definition RetBlocks := V293_tcb_function_blocks 201%positive 202%positive 203%positive 204%positive 205%positive 206%positive 207%positive 208%positive 209%positive.
Definition RetAddresses := V293_tcb_function_addresses 201%positive 202%positive 203%positive 204%positive 205%positive 206%positive 207%positive 208%positive 209%positive.
Definition RetOther : list V293_record_cell :=
 [((209%positive,0%Z),Tint32,Vint32 Int.zero);
  ((201%positive,0%Z),Tint8,V293_byteval 11);
  ((202%positive,0%Z),Tptr Tint32,Vnull);
  ((203%positive,0%Z),Tptr Tint32,Vnull);
  ((204%positive,0%Z),Tint16,Vint32 Int.zero);
  ((205%positive,0%Z),Tint32,Vint32 Int.zero);
  ((206%positive,0%Z),Tptr Tvoid,Vnull);
  ((207%positive,0%Z),Tint16,Vint32 Int.zero)].
Definition RetCells := RetLinks++RetNewFields++RetOldFields++RetOther++RetSentinel.
Fixpoint RetMemory (cells : list V293_record_cell) : mem :=
 match cells with []=>emp | ((b,i),tp,v)::tail=>
 merge (V293_encoded_memory b i true (encode_val tp v)) (RetMemory tail) end.
Definition RetEntryState M := V293_wstate RetGE RetLE M.
Definition RetState M := V293_wstate RetGE RetCaller M.
Definition RetFreed M := forall b tp k, In (b,tp) RetAddresses -> k<typelen tp -> get M (b,Z.of_nat k)=None.
Definition RetFinalLinks := V293_pub_link_cells 208%positive 301%positive 128%Z
 401%positive 402%positive 403%positive 404%positive 301%positive 8%Z true 11
 (Vptr RetOldTid) Vnull (Vptr RetNewTid) 2 24 2 (Vptr RetNewTid).
Definition RetPost := V293_owned_task_records RetUpdated **
 V293_rdy_raw_cells (tl RetFinalLinks++RetSentinel) Atrue.
Ltac RetOutside :=
 repeat first [rewrite V293_encoded_memory_outside by
 (first [left;congruence | right;cbn [V293_byteval length encode_val typelen list_repeat inj_pointer inj_bytes encode_int List.map];lia])
 |rewrite map_merge_semp by reflexivity];reflexivity.
Ltac RetApart b start count :=
 apply map_join_merge;apply map_disjoint;intros [other off];
 destruct (Pos.eq_dec other b) as [B|B];
 [subst other;destruct (Z_lt_dec off start) as [Low|Low];
 [left;apply V293_encoded_memory_outside;right;left;exact Low |
 destruct (Z_lt_dec off (start+count)) as [Inside|Outside];
 [right;left;RetOutside |left;apply V293_encoded_memory_outside;right;right;
 cbn [V293_byteval length encode_val typelen list_repeat inj_pointer inj_bytes encode_int List.map];lia]] |
 left;apply V293_encoded_memory_outside;left;exact B].
Theorem RetLiteralEntry : RetEntryState (RetMemory RetCells) |= V293_rdy_raw_cells RetCells Aemp.
Proof.
 unfold RetEntryState,RetCells,RetLinks,RetNewFields,RetOldFields,RetOther,RetSentinel.
 cbn [app RetMemory V293_rdy_raw_cells].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 208%positive 0%Z true (encode_val (Tptr V293_tcb_type) (Vptr(301%positive,Int.repr 128))));
 [RetApart 208%positive 0%Z 4%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 148%Z true (encode_val (Tcom_ptr 410%Z) (Vnull)));
 [RetApart 301%positive 148%Z 4%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 152%Z true (encode_val (Tcom_ptr 410%Z) (Vnull)));
 [RetApart 301%positive 152%Z 4%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 401%positive 0%Z true (encode_val (Tptr V293_tcb_type) (Vptr(301%positive,Int.repr 8))));
 [RetApart 401%positive 0%Z 4%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 402%positive 0%Z true (encode_val (Tint8) (V293_byteval 2)));
 [RetApart 402%positive 0%Z 1%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 403%positive 1%Z true (encode_val (Tint8) (V293_byteval 16)));
 [RetApart 403%positive 1%Z 1%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 404%positive 0%Z true (encode_val (Tint8) (V293_byteval 1)));
 [RetApart 404%positive 0%Z 1%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 32%Z true (encode_val (Tcom_ptr 410%Z) (Vnull)));
 [RetApart 301%positive 32%Z 4%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 178%Z true (encode_val (Tint8) (V293_byteval 11)));
 [RetApart 301%positive 178%Z 1%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 180%Z true (encode_val (Tint8) (V293_byteval 1)));
 [RetApart 301%positive 180%Z 1%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 179%Z true (encode_val (Tint8) (V293_byteval 3)));
 [RetApart 301%positive 179%Z 1%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 182%Z true (encode_val (Tint8) (V293_byteval 2)));
 [RetApart 301%positive 182%Z 1%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 181%Z true (encode_val (Tint8) (V293_byteval 8)));
 [RetApart 301%positive 181%Z 1%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 160%Z true (encode_val (Tptr Tvoid) (Vnull)));
 [RetApart 301%positive 160%Z 4%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 176%Z true (encode_val (Tint8) (V293_byteval 0)));
 [RetApart 301%positive 176%Z 1%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 58%Z true (encode_val (Tint8) (V293_byteval 12)));
 [RetApart 301%positive 58%Z 1%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 60%Z true (encode_val (Tint8) (V293_byteval 1)));
 [RetApart 301%positive 60%Z 1%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 59%Z true (encode_val (Tint8) (V293_byteval 4)));
 [RetApart 301%positive 59%Z 1%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 62%Z true (encode_val (Tint8) (V293_byteval 2)));
 [RetApart 301%positive 62%Z 1%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 61%Z true (encode_val (Tint8) (V293_byteval 16)));
 [RetApart 301%positive 61%Z 1%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 40%Z true (encode_val (Tptr Tvoid) (Vnull)));
 [RetApart 301%positive 40%Z 4%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 56%Z true (encode_val (Tint8) (V293_byteval 0)));
 [RetApart 301%positive 56%Z 1%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 209%positive 0%Z true (encode_val (Tint32) (Vint32 Int.zero)));
 [RetApart 209%positive 0%Z 4%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 201%positive 0%Z true (encode_val (Tint8) (V293_byteval 11)));
 [RetApart 201%positive 0%Z 1%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 202%positive 0%Z true (encode_val (Tptr Tint32) (Vnull)));
 [RetApart 202%positive 0%Z 4%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 203%positive 0%Z true (encode_val (Tptr Tint32) (Vnull)));
 [RetApart 203%positive 0%Z 4%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 204%positive 0%Z true (encode_val (Tint16) (Vint32 Int.zero)));
 [RetApart 204%positive 0%Z 2%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 205%positive 0%Z true (encode_val (Tint32) (Vint32 Int.zero)));
 [RetApart 205%positive 0%Z 4%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 206%positive 0%Z true (encode_val (Tptr Tvoid) (Vnull)));
 [RetApart 206%positive 0%Z 4%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 207%positive 0%Z true (encode_val (Tint16) (Vint32 Int.zero)));
 [RetApart 207%positive 0%Z 2%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 601%positive 0%Z true (encode_val (Tint32) (Vint32(Int.repr 77))));
 [RetApart 601%positive 0%Z 4%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 split;reflexivity.
Qed.
Lemma RetEnvironment : V293_pub_env RetGE RetLE 108%Z 93%Z 94%Z 95%Z 96%Z
 208%positive 401%positive 402%positive 403%positive 404%positive.
Proof. unfold V293_pub_env,RetGE,RetLE,V293_tcb_function_env;repeat split;
 repeat first [rewrite map_get_set |rewrite map_get_set' by discriminate];reflexivity. Qed.
Lemma RetNewOwned : forall R,
 V293_rdy_raw_cells RetNewFields R ==>
 V293_owned_task_record RetNewTid (Int.repr 11) rdy Vnull ** R.
Proof.
 intros R s Owned. apply V293_raw_cells_separate in Owned.
 eapply astar_mono;[apply (V293_raw_to_ready_record 301%positive 128%Z 11);lia |intros st HS;exact HS |exact Owned].
Qed.
Lemma RetOldOwned : forall R,
 V293_rdy_raw_cells RetOldFields R ==> V293_owned_task_records RetTasks ** R.
Proof.
 intros R s Owned. apply V293_raw_cells_separate in Owned.
 assert (Held : s |= V293_owned_task_record RetOldTid (Int.repr 12) rdy Vnull ** R).
 { eapply astar_mono;[apply (V293_raw_to_ready_record 301%positive 8%Z 12);lia |intros st HS;exact HS |exact Owned]. }
 change (s |= (V293_owned_task_record RetOldTid (Int.repr 12) rdy Vnull ** Aemp) ** R).
 clear -Held. sep auto.
Qed.
Theorem RetSpatialEntry : RetEntryState (RetMemory RetCells) |=
 V293_rdy_raw_cells RetLinks (V293_owned_task_records RetUpdated **
 V293_rdy_raw_cells (RetOther++RetSentinel) Atrue).
Proof.
 eapply V293_raw_cells_mono.
 - intros st HS.
   assert (Old : st |= V293_rdy_raw_cells RetNewFields
      (V293_owned_task_records RetTasks ** V293_rdy_raw_cells (RetOther++RetSentinel) Atrue)).
   { eapply V293_raw_cells_mono;[apply RetOldOwned |exact HS]. }
   apply RetNewOwned in Old.
   eapply V293_task_records_insert;[reflexivity |exact Old].
 - rewrite <-!V293_raw_cells_append.
   eapply V293_raw_cells_mono;[intros st HS;exact I |exact RetLiteralEntry].
Qed.
Theorem RetGoodCall : forall P f hi hc ks enabled si ci, exists Mf,
 V293_local_steps P (curs(sskip None),(kenil,V293_tcb_second_hook_cont f hi hc RetCaller ks))
 ((RetGE,RetLE,RetMemory RetCells),(fun _=>false),(enabled,si,ci))
 (curs(sskip(Some(Vint32 Int.zero))),(kenil,ks)) ((RetGE,RetCaller,Mf),(fun _=>false),(enabled,si,ci)) /\
 (RetState Mf |= RetPost) /\ RetFreed Mf.
Proof.
 intros P f hi hc ks enabled si ci.
 eapply (V293_OS_TCBInit_publication_return_preserves_records RetTasks P f hi hc RetCaller ks RetGE
 (RetMemory RetCells) (fun _=>false) (false,nil,nil) (emp:osabst) (spec_done None) enabled si ci
 201%positive 202%positive 203%positive 204%positive 205%positive 206%positive 207%positive 208%positive 209%positive
 301%positive 128%Z 401%positive 402%positive 403%positive 404%positive 301%positive 8%Z true
 11 2 16 1 Vnull Vnull Vnull (V293_byteval 11) Vnull Vnull (Vint32 Int.zero)
 (Vint32 Int.zero) Vnull (Vint32 Int.zero) (Vint32 Int.zero) RetSentinel);
 try lia;try (change (128+54<=4294967295)%Z;lia);try (change (8+24<=4294967295)%Z;lia).
 - reflexivity.
 - exact RetEnvironment.
 - repeat constructor;cbn;intuition congruence.
 - intros t value Member. change (In (t,value)
    [(RetOldTid,(Int.repr 12,rdy,Vnull));(RetNewTid,(Int.repr 11,rdy,Vnull))]) in Member.
   destruct Member as [Same |[Same |Impossible]];[inversion Same;subst |inversion Same;subst |contradiction];
   cbn [RetOldTid RetNewTid fst V293_tcb_function_blocks In];intuition discriminate.
 - intros a tp v Member. cbn [V293_pub_link_cells tl app V293_prio_row RetSentinel In] in Member.
   repeat destruct Member as [E |Member];try contradiction;inversion E;subst;
   cbn [fst V293_tcb_function_blocks In];intuition discriminate.
 - exact RetSpatialEntry.
Qed.
Print Assumptions RetGoodCall.

Lemma RetRecordsFrameSound : forall tasks R M,
 RetState M |= V293_owned_task_records tasks ** R -> V293_task_records M tasks.
Proof.
 intros tasks R M Held. apply sat_split in Held.
 destruct Held as (m1&m2&o1&o2&JM&JO&Records&Other).
 pose proof (V293_owned_task_records_sound _ _ Records) as Sound.
 intros t priority status message Lookup.
 eapply V293_task_record_sub;[exists m2;exact JM |apply Sound;exact Lookup].
Qed.
Lemma RetFinalRead : forall M a tp v,
 In (a,tp,v) (tl RetFinalLinks++RetSentinel) -> rule_type_val_match tp v=true ->
 RetState M |= RetPost -> load tp M a=Some v.
Proof.
 intros M a tp v Member Valid Owned.
 change (load tp (getmem(RetState M)) a=Some v).
 eapply V293_star_load_r;[ |exact Owned]. intros st Raw.
 eapply V293_rdy_raw_load;[exact Member |exact Valid |exact Raw].
Qed.
Definition RetReads M : Prop :=
 load (Tcom_ptr 410%Z) M (301%positive,148%Z)=Some(Vptr RetOldTid) /\
 load (Tcom_ptr 410%Z) M (301%positive,152%Z)=Some Vnull /\
 load (Tptr V293_tcb_type) M (401%positive,0%Z)=Some(Vptr RetNewTid) /\
 load (Tcom_ptr 410%Z) M (301%positive,32%Z)=Some(Vptr RetNewTid) /\
 load Tint8 M (402%positive,0%Z)=Some(V293_byteval 2) /\
 load Tint8 M (403%positive,1%Z)=Some(V293_byteval 24) /\
 load Tint8 M (404%positive,0%Z)=Some(V293_byteval 2) /\
 load Tint32 M (601%positive,0%Z)=Some(Vint32(Int.repr 77)).
Lemma RetGoodPostReads : forall M, RetState M |= RetPost -> RetReads M.
Proof.
 intros M Owned. unfold RetReads. repeat split;
 (eapply RetFinalRead;[unfold RetFinalLinks,RetSentinel,V293_pub_link_cells;
  cbn [V293_prio_row In app tl];tauto |reflexivity |exact Owned]).
Qed.
Theorem RetGoodSameMf : forall P f hi hc ks enabled si ci, exists Mf,
 V293_local_steps P (curs(sskip None),(kenil,V293_tcb_second_hook_cont f hi hc RetCaller ks))
 ((RetGE,RetLE,RetMemory RetCells),(fun _=>false),(enabled,si,ci))
 (curs(sskip(Some(Vint32 Int.zero))),(kenil,ks)) ((RetGE,RetCaller,Mf),(fun _=>false),(enabled,si,ci)) /\
 (RetState Mf |= RetPost) /\ V293_task_records Mf RetUpdated /\
 get RetUpdated RetOldTid=Some(Int.repr 12,rdy,Vnull) /\
 get RetUpdated RetNewTid=Some(Int.repr 11,rdy,Vnull) /\ RetReads Mf /\ RetFreed Mf.
Proof.
 intros P f hi hc ks enabled si ci.
 destruct (RetGoodCall P f hi hc ks enabled si ci) as (Mf&Exec&Owned&Freed).
 exists Mf. split;[exact Exec | ]. split;[exact Owned | ].
 split;[eapply RetRecordsFrameSound;exact Owned | ].
 split;[reflexivity | ]. split;[reflexivity | ]. split;[apply RetGoodPostReads;exact Owned |exact Freed].
Qed.
Theorem RetInitialLocal :
 load (Tptr V293_tcb_type) (RetMemory RetCells) (208%positive,0%Z)=Some(Vptr RetNewTid).
Proof.
 change (load (Tptr V293_tcb_type) (getmem(RetEntryState(RetMemory RetCells))) (208%positive,0%Z)=Some(Vptr RetNewTid)).
 eapply (V293_rdy_raw_load RetCells);[unfold RetCells,RetLinks,RetNewTid;cbn [In app];tauto
 |reflexivity |exact RetLiteralEntry].
Qed.
Theorem RetFreedLocalCannotSurvive : forall Mf R,
 RetFreed Mf -> ~ RetState Mf |= Amapsto (208%positive,0%Z) (Tptr V293_tcb_type) true (Vptr RetNewTid) ** R.
Proof.
 intros Mf R Freed Owned.
 pose proof (V293_tick_raw_owned_writable 208%positive (Tptr V293_tcb_type)
  (Vptr RetNewTid) R RetGE RetCaller Mf (fun _=>false) (false,nil,nil) (emp:osabst) (spec_done None) Owned) as W.
 destruct (W 0 ltac:(cbn;lia)) as [raw Full].
 pose proof (Freed 208%positive (Tptr V293_tcb_type) 0 ltac:(unfold RetAddresses,V293_tcb_function_addresses;cbn;tauto) ltac:(cbn;lia)) as Gone.
 change (get Mf (208%positive,0%Z)=None) in Gone. change (get Mf (208%positive,0%Z)=Some(true,raw)) in Full. rewrite Gone in Full. discriminate.
Qed.
Print Assumptions RetGoodSameMf.
Print Assumptions RetFreedLocalCannotSurvive.
Theorem RetActualNoLocal : forall P f hi hc ks enabled si ci, exists Mf,
 V293_local_steps P (curs(sskip None),(kenil,V293_tcb_second_hook_cont f hi hc RetCaller ks))
 ((RetGE,RetLE,RetMemory RetCells),(fun _=>false),(enabled,si,ci))
 (curs(sskip(Some(Vint32 Int.zero))),(kenil,ks)) ((RetGE,RetCaller,Mf),(fun _=>false),(enabled,si,ci)) /\
 (RetState Mf |= RetPost) /\ RetReads Mf /\ RetFreed Mf /\
 (forall R, ~ RetState Mf |= Amapsto (208%positive,0%Z) (Tptr V293_tcb_type) true (Vptr RetNewTid) ** R).
Proof.
 intros P f hi hc ks enabled si ci.
 destruct (RetGoodSameMf P f hi hc ks enabled si ci) as (Mf&Exec&Owned&Records&Old&New&Reads&Freed).
 exists Mf. split;[exact Exec | ]. split;[exact Owned | ]. split;[exact Reads | ].
 split;[exact Freed | ]. intro R. apply RetFreedLocalCannotSurvive. exact Freed.
Qed.
Print Assumptions RetActualNoLocal.
