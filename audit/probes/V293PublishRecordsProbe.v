(* Literal nonempty-head publication; same block, two ready records. *)
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
Import ListNotations.
Local Open Scope nat_scope.
Definition PubLinks : list V293_record_cell :=
 [((201%positive,0%Z),(Tptr V293_tcb_type),(Vptr(301%positive,Int.repr 128)));
  ((301%positive,148%Z),(Tcom_ptr 410%Z),(Vnull));
  ((301%positive,152%Z),(Tcom_ptr 410%Z),(Vnull));
  ((401%positive,0%Z),(Tptr V293_tcb_type),(Vptr(301%positive,Int.repr 8)));
  ((402%positive,0%Z),(Tint8),(V293_byteval 2));
  ((403%positive,1%Z),(Tint8),(V293_byteval 16));
  ((404%positive,0%Z),(Tint8),(V293_byteval 1));
  ((301%positive,32%Z),(Tcom_ptr 410%Z),(Vnull))].
Definition PubNewFields : list V293_record_cell :=
 [((301%positive,178%Z),(Tint8),(V293_byteval 11));
  ((301%positive,180%Z),(Tint8),(V293_byteval 1));
  ((301%positive,179%Z),(Tint8),(V293_byteval 3));
  ((301%positive,182%Z),(Tint8),(V293_byteval 2));
  ((301%positive,181%Z),(Tint8),(V293_byteval 8));
  ((301%positive,160%Z),(Tptr Tvoid),(Vnull));
  ((301%positive,176%Z),(Tint8),(V293_byteval 0))].
Definition PubOldFields : list V293_record_cell :=
 [((301%positive,58%Z),(Tint8),(V293_byteval 12));
  ((301%positive,60%Z),(Tint8),(V293_byteval 1));
  ((301%positive,59%Z),(Tint8),(V293_byteval 4));
  ((301%positive,62%Z),(Tint8),(V293_byteval 2));
  ((301%positive,61%Z),(Tint8),(V293_byteval 16));
  ((301%positive,40%Z),(Tptr Tvoid),(Vnull));
  ((301%positive,56%Z),(Tint8),(V293_byteval 0))].
Definition PubSentinel : list V293_record_cell :=
 [((601%positive,0%Z),(Tint32),(Vint32(Int.repr 77)))].
Definition PubOldTid : tid := (301%positive,Int.repr 8).
Definition PubNewTid : tid := (301%positive,Int.repr 128).
Definition PubTasks : TcbMod.map := sig PubOldTid (Int.repr 12,rdy,Vnull).
Definition PubUpdated : TcbMod.map := set PubTasks PubNewTid (Int.repr 11,rdy,Vnull).
Definition PubGE : env := set (set (set (set (emp:env)
 102%Z (401%positive,Tptr V293_tcb_type)) 103%Z (402%positive,Tint8))
 104%Z (403%positive,Tarray Tint8 2)) 105%Z (404%positive,Tint8).
Definition PubLE : env := sig 101%Z (201%positive,Tptr V293_tcb_type).
Definition PubCode := V293_TCB_publish 101%Z 102%Z 103%Z 104%Z 105%Z.
Definition PubCells := PubLinks++PubNewFields++PubOldFields++PubSentinel.
Fixpoint PubMemory (cells : list V293_record_cell) : mem :=
 match cells with []=>emp | ((b,i),tp,v)::tail=>
 merge (V293_encoded_memory b i true (encode_val tp v)) (PubMemory tail) end.
Definition PubState M := V293_wstate PubGE PubLE M.
Definition PubFinalLinks := V293_pub_link_cells 201%positive 301%positive 128%Z
 401%positive 402%positive 403%positive 404%positive 301%positive 8%Z true 11
 (Vptr PubOldTid) Vnull (Vptr PubNewTid) 2 24 2 (Vptr PubNewTid).
Definition PubPost := V293_owned_task_records PubUpdated **
 V293_rdy_raw_cells PubFinalLinks (V293_rdy_raw_cells PubSentinel Aemp).
Ltac PubOutside :=
 repeat first [rewrite V293_encoded_memory_outside by
 (first [left;congruence | right;cbn [V293_byteval length encode_val typelen list_repeat inj_pointer inj_bytes encode_int List.map];lia])
 |rewrite map_merge_semp by reflexivity];reflexivity.
Ltac PubApart b start count :=
 apply map_join_merge;apply map_disjoint;intros [other off];
 destruct (Pos.eq_dec other b) as [B|B];
 [subst other;destruct (Z_lt_dec off start) as [Low|Low];
 [left;apply V293_encoded_memory_outside;right;left;exact Low |
 destruct (Z_lt_dec off (start+count)) as [Inside|Outside];
 [right;left;PubOutside |left;apply V293_encoded_memory_outside;right;right;
 cbn [V293_byteval length encode_val typelen list_repeat inj_pointer inj_bytes encode_int List.map];lia]] |
 left;apply V293_encoded_memory_outside;left;exact B].
Theorem PubLiteralEntry : PubState (PubMemory PubCells) |= V293_rdy_raw_cells PubCells Aemp.
Proof.
 unfold PubState,PubCells,PubLinks,PubNewFields,PubOldFields,PubSentinel.
 cbn [app PubMemory V293_rdy_raw_cells].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 201%positive 0%Z true (encode_val (Tptr V293_tcb_type) (Vptr(301%positive,Int.repr 128))));
 [PubApart 201%positive 0%Z 4%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 148%Z true (encode_val (Tcom_ptr 410%Z) (Vnull)));
 [PubApart 301%positive 148%Z 4%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 152%Z true (encode_val (Tcom_ptr 410%Z) (Vnull)));
 [PubApart 301%positive 152%Z 4%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 401%positive 0%Z true (encode_val (Tptr V293_tcb_type) (Vptr(301%positive,Int.repr 8))));
 [PubApart 401%positive 0%Z 4%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 402%positive 0%Z true (encode_val (Tint8) (V293_byteval 2)));
 [PubApart 402%positive 0%Z 1%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 403%positive 1%Z true (encode_val (Tint8) (V293_byteval 16)));
 [PubApart 403%positive 1%Z 1%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 404%positive 0%Z true (encode_val (Tint8) (V293_byteval 1)));
 [PubApart 404%positive 0%Z 1%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 32%Z true (encode_val (Tcom_ptr 410%Z) (Vnull)));
 [PubApart 301%positive 32%Z 4%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 178%Z true (encode_val (Tint8) (V293_byteval 11)));
 [PubApart 301%positive 178%Z 1%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 180%Z true (encode_val (Tint8) (V293_byteval 1)));
 [PubApart 301%positive 180%Z 1%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 179%Z true (encode_val (Tint8) (V293_byteval 3)));
 [PubApart 301%positive 179%Z 1%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 182%Z true (encode_val (Tint8) (V293_byteval 2)));
 [PubApart 301%positive 182%Z 1%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 181%Z true (encode_val (Tint8) (V293_byteval 8)));
 [PubApart 301%positive 181%Z 1%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 160%Z true (encode_val (Tptr Tvoid) (Vnull)));
 [PubApart 301%positive 160%Z 4%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 176%Z true (encode_val (Tint8) (V293_byteval 0)));
 [PubApart 301%positive 176%Z 1%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 58%Z true (encode_val (Tint8) (V293_byteval 12)));
 [PubApart 301%positive 58%Z 1%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 60%Z true (encode_val (Tint8) (V293_byteval 1)));
 [PubApart 301%positive 60%Z 1%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 59%Z true (encode_val (Tint8) (V293_byteval 4)));
 [PubApart 301%positive 59%Z 1%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 62%Z true (encode_val (Tint8) (V293_byteval 2)));
 [PubApart 301%positive 62%Z 1%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 61%Z true (encode_val (Tint8) (V293_byteval 16)));
 [PubApart 301%positive 61%Z 1%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 40%Z true (encode_val (Tptr Tvoid) (Vnull)));
 [PubApart 301%positive 40%Z 4%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 56%Z true (encode_val (Tint8) (V293_byteval 0)));
 [PubApart 301%positive 56%Z 1%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 601%positive 0%Z true (encode_val (Tint32) (Vint32(Int.repr 77))));
 [PubApart 601%positive 0%Z 4%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 split;reflexivity.
Qed.
Lemma PubEnvironment : V293_pub_env PubGE PubLE 101%Z 102%Z 103%Z 104%Z 105%Z
 201%positive 401%positive 402%positive 403%positive 404%positive.
Proof. unfold V293_pub_env,PubGE,PubLE;repeat split;
 repeat first [rewrite map_get_set |rewrite map_get_set' by discriminate];reflexivity. Qed.
Lemma PubNewOwned : forall R,
 V293_rdy_raw_cells PubNewFields R ==>
 V293_owned_task_record PubNewTid (Int.repr 11) rdy Vnull ** R.
Proof.
 intros R s Owned. apply V293_raw_cells_separate in Owned.
 eapply astar_mono;[apply (V293_raw_to_ready_record 301%positive 128%Z 11);lia |intros st HS;exact HS |exact Owned].
Qed.
Lemma PubOldOwned : forall R,
 V293_rdy_raw_cells PubOldFields R ==> V293_owned_task_records PubTasks ** R.
Proof.
 intros R s Owned. apply V293_raw_cells_separate in Owned.
 assert (Held : s |= V293_owned_task_record PubOldTid (Int.repr 12) rdy Vnull ** R).
 { eapply astar_mono;[apply (V293_raw_to_ready_record 301%positive 8%Z 12);lia |intros st HS;exact HS |exact Owned]. }
 change (s |= (V293_owned_task_record PubOldTid (Int.repr 12) rdy Vnull ** Aemp) ** R).
 clear -Held. sep auto.
Qed.
Theorem PubSpatialEntry : PubState (PubMemory PubCells) |=
 V293_rdy_raw_cells PubLinks (V293_owned_task_records PubUpdated ** V293_rdy_raw_cells PubSentinel Aemp).
Proof.
 eapply V293_raw_cells_mono.
 - intros st HS.
   assert (Old : st |= V293_rdy_raw_cells PubNewFields
      (V293_owned_task_records PubTasks ** V293_rdy_raw_cells PubSentinel Aemp)).
   { eapply V293_raw_cells_mono;[apply PubOldOwned |exact HS]. }
   apply PubNewOwned in Old.
   eapply V293_task_records_insert;[reflexivity |exact Old].
 - rewrite <-!V293_raw_cells_append. apply PubLiteralEntry.
Qed.
Theorem PubGoodCall : forall P ks enabled si ci, exists Mf,
 V293_local_steps P (curs PubCode,(kenil,ks))
 ((PubGE,PubLE,PubMemory PubCells),(fun _=>false),(enabled,si,ci))
 (curs(srete(econst32 Int.zero)),(kenil,ks)) ((PubGE,PubLE,Mf),(fun _=>false),(enabled,si,ci)) /\
 PubState Mf |= PubPost.
Proof.
 intros P ks enabled si ci.
 eapply (V293_OS_TCBInit_publication_preserves_records PubTasks P ks PubGE PubLE
 (PubMemory PubCells) (fun _=>false) (false,nil,nil) (emp:osabst) (spec_done None)
 (V293_rdy_raw_cells PubSentinel Aemp) enabled si ci
 101%Z 102%Z 103%Z 104%Z 105%Z 201%positive 301%positive 128%Z
 401%positive 402%positive 403%positive 404%positive 301%positive 8%Z true
 11 2 16 1 Vnull Vnull Vnull);try lia;try (change (128+54<=4294967295)%Z;lia);
 try (change (8+24<=4294967295)%Z;lia).
 - reflexivity.
 - exact PubEnvironment.
 - exact PubSpatialEntry.
Qed.
Print Assumptions PubGoodCall.

Lemma PubRecordsFrameSound : forall tasks R M,
 PubState M |= V293_owned_task_records tasks ** R -> V293_task_records M tasks.
Proof.
 intros tasks R M Held. apply sat_split in Held.
 destruct Held as (m1&m2&o1&o2&JM&JO&Records&Other).
 pose proof (V293_owned_task_records_sound _ _ Records) as Sound.
 intros t priority status message Lookup.
 eapply V293_task_record_sub;[exists m2;exact JM |apply Sound;exact Lookup].
Qed.
Lemma PubFinalRead : forall M a tp v,
 In (a,tp,v) (PubFinalLinks++PubSentinel) -> rule_type_val_match tp v=true ->
 PubState M |= PubPost -> load tp M a=Some v.
Proof.
 intros M a tp v Member Valid Owned.
 change (load tp (getmem(PubState M)) a=Some v).
 eapply V293_star_load_r;[ |exact Owned]. intros st Raw.
 rewrite <-V293_raw_cells_append in Raw.
 eapply V293_rdy_raw_load;[exact Member |exact Valid |exact Raw].
Qed.
Definition PubReads M : Prop :=
 load (Tcom_ptr 410%Z) M (301%positive,148%Z)=Some(Vptr PubOldTid) /\
 load (Tcom_ptr 410%Z) M (301%positive,152%Z)=Some Vnull /\
 load (Tptr V293_tcb_type) M (401%positive,0%Z)=Some(Vptr PubNewTid) /\
 load (Tcom_ptr 410%Z) M (301%positive,32%Z)=Some(Vptr PubNewTid) /\
 load Tint8 M (402%positive,0%Z)=Some(V293_byteval 2) /\
 load Tint8 M (403%positive,1%Z)=Some(V293_byteval 24) /\
 load Tint8 M (404%positive,0%Z)=Some(V293_byteval 2) /\
 load Tint32 M (601%positive,0%Z)=Some(Vint32(Int.repr 77)).
Lemma PubGoodPostReads : forall M, PubState M |= PubPost -> PubReads M.
Proof.
 intros M Owned. unfold PubReads. repeat split;
 (eapply PubFinalRead;[unfold PubFinalLinks,PubSentinel,V293_pub_link_cells;
  cbn [V293_prio_row In app];tauto |reflexivity |exact Owned]).
Qed.
Theorem PubGoodSameMf : forall P ks enabled si ci, exists Mf,
 V293_local_steps P (curs PubCode,(kenil,ks))
 ((PubGE,PubLE,PubMemory PubCells),(fun _=>false),(enabled,si,ci))
 (curs(srete(econst32 Int.zero)),(kenil,ks)) ((PubGE,PubLE,Mf),(fun _=>false),(enabled,si,ci)) /\
 (PubState Mf |= PubPost) /\ V293_task_records Mf PubUpdated /\
 get PubUpdated PubOldTid=Some(Int.repr 12,rdy,Vnull) /\
 get PubUpdated PubNewTid=Some(Int.repr 11,rdy,Vnull) /\ PubReads Mf.
Proof.
 intros P ks enabled si ci. destruct (PubGoodCall P ks enabled si ci) as (Mf&Exec&Owned).
 exists Mf. split;[exact Exec | ]. split;[exact Owned | ].
 split;[eapply PubRecordsFrameSound;exact Owned | ].
 split;[reflexivity | ]. split;[reflexivity |apply PubGoodPostReads;exact Owned].
Qed.
Theorem PubInitialHeadAndBack :
 load (Tptr V293_tcb_type) (PubMemory PubCells) (401%positive,0%Z)=Some(Vptr PubOldTid) /\
 load (Tcom_ptr 410%Z) (PubMemory PubCells) (301%positive,32%Z)=Some Vnull.
Proof.
 split.
 - change (load (Tptr V293_tcb_type) (getmem(PubState(PubMemory PubCells))) (401%positive,0%Z)=Some(Vptr PubOldTid)).
   eapply (V293_rdy_raw_load PubCells);[unfold PubCells,PubLinks,PubOldTid;cbn [In app];tauto
   |reflexivity |exact PubLiteralEntry].
 - change (load (Tcom_ptr 410%Z) (getmem(PubState(PubMemory PubCells))) (301%positive,32%Z)=Some Vnull).
 (eapply (V293_rdy_raw_load PubCells);[unfold PubCells,PubLinks,PubOldTid;cbn [In app];tauto
 |reflexivity |exact PubLiteralEntry]).
Qed.
(* Both candidate back-pointer assertions refer to this one actual execution. *)
Theorem PubBadBackPointer : forall P ks enabled si ci, exists Mf,
 V293_local_steps P (curs PubCode,(kenil,ks))
 ((PubGE,PubLE,PubMemory PubCells),(fun _=>false),(enabled,si,ci))
 (curs(srete(econst32 Int.zero)),(kenil,ks)) ((PubGE,PubLE,Mf),(fun _=>false),(enabled,si,ci)) /\
 (PubState Mf |= PubPost) /\
 load (Tcom_ptr 410%Z) Mf (301%positive,32%Z)=Some(Vptr PubNewTid) /\
 ~ PubState Mf |= Amapsto (301%positive,32%Z) (Tcom_ptr 410%Z) true Vnull ** Atrue.
Proof.
 intros P ks enabled si ci. destruct (PubGoodCall P ks enabled si ci) as (Mf&Exec&Owned).
 exists Mf. split;[exact Exec | ]. split;[exact Owned | ].
 assert (Read : load (Tcom_ptr 410%Z) Mf (301%positive,32%Z)=Some(Vptr PubNewTid)).
 { eapply PubFinalRead;[unfold PubFinalLinks,V293_pub_link_cells;cbn [In app];tauto
 |reflexivity |exact Owned]. }
 split;[exact Read | ]. intro Bad.
 assert (Wrong : load (Tcom_ptr 410%Z) Mf (301%positive,32%Z)=Some Vnull).
 { change (load (Tcom_ptr 410%Z) (getmem(PubState Mf)) (301%positive,32%Z)=Some Vnull).
   eapply V293_star_load_l;[ |exact Bad]. intros st Cell.
   eapply mapstoval_load;[reflexivity |exact (proj1 Cell)]. }
 rewrite Read in Wrong. discriminate.
Qed.
Print Assumptions PubLiteralEntry.
Print Assumptions PubEnvironment.
Print Assumptions PubSpatialEntry.
Print Assumptions PubRecordsFrameSound.
Print Assumptions PubFinalRead.
Print Assumptions PubGoodPostReads.
Print Assumptions PubGoodSameMf.
Print Assumptions PubInitialHeadAndBack.
Print Assumptions PubBadBackPointer.
