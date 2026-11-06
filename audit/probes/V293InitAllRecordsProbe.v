(* Real eighteen initializer stores; two spatial records share block 301.
   The task-map extension below is not an abstract publication transition. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.certiucos.v293.code.V293OSTCBInit.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitFields.
Require Import CertiOS.certiucos.v293.proofs.V293InitAllRecords.
Require Import CertiOS.certiucos.v293.proofs.V293StartRecord.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293InitTCBClear.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewWitness.
Require Import CertiOS.certiucos.v293.proofs.V293NullBytes.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.
Definition AllOldFields : list V293_record_cell :=
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
Definition AllInputs : list V293_record_cell :=
 [((201%positive,0%Z),(Tptr V293_tcb_type),(Vptr(301%positive,Int.repr 128)));
  ((202%positive,0%Z),(Tint8),(V293_byteval 11));
  ((203%positive,0%Z),(Tptr Tint32),(Vnull));
  ((204%positive,0%Z),(Tptr Tint32),(Vnull));
  ((205%positive,0%Z),(Tint16),(Vint32 Int.zero));
  ((206%positive,0%Z),(Tint32),(Vint32(Int.repr 128)));
  ((207%positive,0%Z),(Tptr Tvoid),(Vnull));
  ((208%positive,0%Z),(Tint16),(Vint32 Int.zero))].
Definition AllExisting : list V293_record_cell :=
 [((301%positive,58%Z),(Tint8),(V293_byteval 12));
  ((301%positive,60%Z),(Tint8),(V293_byteval 1));
  ((301%positive,59%Z),(Tint8),(V293_byteval 4));
  ((301%positive,62%Z),(Tint8),(V293_byteval 2));
  ((301%positive,61%Z),(Tint8),(V293_byteval 16));
  ((301%positive,40%Z),(Tptr Tvoid),(Vnull));
  ((301%positive,56%Z),(Tint8),(V293_byteval 0))].
Definition AllSentinel : list V293_record_cell :=
 [((601%positive,0%Z),(Tint32),(Vint32(Int.repr 77)))].
Definition AllCells := AllOldFields++AllInputs++AllExisting++AllSentinel.
Definition AllOldTid : tid := (301%positive,Int.repr 8).
Definition AllNewTid : tid := (301%positive,Int.repr 128).
Definition AllTasks q : TcbMod.map := sig AllOldTid (Int.repr (Z.of_nat q),rdy,Vnull).
Definition AllUpdated q := set (AllTasks q) AllNewTid (Int.repr 11,rdy,Vnull).
Definition AllLE : env :=
 set (set (set (set (set (set (set (set (emp:env)
 101%Z (201%positive,Tptr V293_tcb_type)) 102%Z (202%positive,Tint8))
 103%Z (203%positive,Tptr Tint32)) 104%Z (204%positive,Tptr Tint32))
 105%Z (205%positive,Tint16)) 106%Z (206%positive,Tint32))
 107%Z (207%positive,Tptr Tvoid)) 108%Z (208%positive,Tint16).
Fixpoint AllMemory (cells : list V293_record_cell) : mem :=
 match cells with []=>emp | ((b,i),tp,v)::tail=>
 merge (V293_encoded_memory b i true (encode_val tp v)) (AllMemory tail) end.
Definition AllState M := V293_wstate (emp:env) AllLE M.
Definition AllCode := V293_TCBInit_fields 101%Z 102%Z 103%Z 104%Z 105%Z 106%Z 107%Z 108%Z.
Definition AllNewFields := V293_tcb_init_final_fields 301%positive 128%Z 11
 Vnull Vnull (Vint32 Int.zero) (Vint32(Int.repr 128)) Vnull (Vint32 Int.zero).
Definition AllRemaining := V293_tcb_init_record_remainder 301%positive 128%Z
 Vnull Vnull (Vint32 Int.zero) (Vint32(Int.repr 128)) Vnull (Vint32 Int.zero).
Definition AllPost q := V293_owned_task_records (AllUpdated q) **
 V293_rdy_raw_cells AllRemaining (V293_rdy_raw_cells AllInputs (V293_rdy_raw_cells AllSentinel Aemp)).
Ltac AllOutside :=
 repeat first [rewrite V293_encoded_memory_outside by
 (first [left;congruence | right;cbn [V293_byteval length encode_val typelen list_repeat inj_pointer inj_bytes encode_int List.map];lia])
 |rewrite map_merge_semp by reflexivity];reflexivity.
Ltac AllApart b start count :=
 apply map_join_merge;apply map_disjoint;intros [other off];
 destruct (Pos.eq_dec other b) as [B|B];
 [subst other;destruct (Z_lt_dec off start) as [Low|Low];
 [left;apply V293_encoded_memory_outside;right;left;exact Low |
 destruct (Z_lt_dec off (start+count)) as [Inside|Outside];
 [right;left;AllOutside |left;apply V293_encoded_memory_outside;right;right;
 cbn [V293_byteval length encode_val typelen list_repeat inj_pointer inj_bytes encode_int List.map];lia]] |
 left;apply V293_encoded_memory_outside;left;exact B].
Theorem AllLiteralEntry : AllState (AllMemory AllCells) |= V293_rdy_raw_cells AllCells Aemp.
Proof.
 unfold AllState,AllCells,AllOldFields,AllInputs,AllExisting,AllSentinel.
 cbn [app AllMemory V293_rdy_raw_cells].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 128%Z true (encode_val (Tptr Tint32) (Vundef)));
 [AllApart 301%positive 128%Z 4%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 178%Z true (encode_val (Tint8) (Vundef)));
 [AllApart 301%positive 178%Z 1%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 176%Z true (encode_val (Tint8) (Vundef)));
 [AllApart 301%positive 176%Z 1%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 177%Z true (encode_val (Tint8) (Vundef)));
 [AllApart 301%positive 177%Z 1%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 172%Z true (encode_val (Tint32) (Vundef)));
 [AllApart 301%positive 172%Z 4%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 132%Z true (encode_val (Tptr Tvoid) (Vundef)));
 [AllApart 301%positive 132%Z 4%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 140%Z true (encode_val (Tint32) (Vundef)));
 [AllApart 301%positive 140%Z 4%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 136%Z true (encode_val (Tptr Tint32) (Vundef)));
 [AllApart 301%positive 136%Z 4%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 144%Z true (encode_val (Tint16) (Vundef)));
 [AllApart 301%positive 144%Z 2%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 146%Z true (encode_val (Tint16) (Vundef)));
 [AllApart 301%positive 146%Z 2%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 183%Z true (encode_val (Tint8) (Vundef)));
 [AllApart 301%positive 183%Z 1%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 180%Z true (encode_val (Tint8) (Vundef)));
 [AllApart 301%positive 180%Z 1%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 179%Z true (encode_val (Tint8) (Vundef)));
 [AllApart 301%positive 179%Z 1%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 182%Z true (encode_val (Tint8) (Vundef)));
 [AllApart 301%positive 182%Z 1%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 181%Z true (encode_val (Tint8) (Vundef)));
 [AllApart 301%positive 181%Z 1%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 156%Z true (encode_val (Tcom_ptr 411%Z) (Vundef)));
 [AllApart 301%positive 156%Z 4%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 164%Z true (encode_val (Tcom_ptr 412%Z) (Vundef)));
 [AllApart 301%positive 164%Z 4%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 160%Z true (encode_val (Tptr Tvoid) (Vundef)));
 [AllApart 301%positive 160%Z 4%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 201%positive 0%Z true (encode_val (Tptr V293_tcb_type) (Vptr(301%positive,Int.repr 128))));
 [AllApart 201%positive 0%Z 4%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 202%positive 0%Z true (encode_val (Tint8) (V293_byteval 11)));
 [AllApart 202%positive 0%Z 1%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 203%positive 0%Z true (encode_val (Tptr Tint32) (Vnull)));
 [AllApart 203%positive 0%Z 4%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 204%positive 0%Z true (encode_val (Tptr Tint32) (Vnull)));
 [AllApart 204%positive 0%Z 4%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 205%positive 0%Z true (encode_val (Tint16) (Vint32 Int.zero)));
 [AllApart 205%positive 0%Z 2%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 206%positive 0%Z true (encode_val (Tint32) (Vint32(Int.repr 128))));
 [AllApart 206%positive 0%Z 4%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 207%positive 0%Z true (encode_val (Tptr Tvoid) (Vnull)));
 [AllApart 207%positive 0%Z 4%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 208%positive 0%Z true (encode_val (Tint16) (Vint32 Int.zero)));
 [AllApart 208%positive 0%Z 2%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 58%Z true (encode_val (Tint8) (V293_byteval 12)));
 [AllApart 301%positive 58%Z 1%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 60%Z true (encode_val (Tint8) (V293_byteval 1)));
 [AllApart 301%positive 60%Z 1%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 59%Z true (encode_val (Tint8) (V293_byteval 4)));
 [AllApart 301%positive 59%Z 1%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 62%Z true (encode_val (Tint8) (V293_byteval 2)));
 [AllApart 301%positive 62%Z 1%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 61%Z true (encode_val (Tint8) (V293_byteval 16)));
 [AllApart 301%positive 61%Z 1%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 40%Z true (encode_val (Tptr Tvoid) (Vnull)));
 [AllApart 301%positive 40%Z 4%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 56%Z true (encode_val (Tint8) (V293_byteval 0)));
 [AllApart 301%positive 56%Z 1%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 601%positive 0%Z true (encode_val (Tint32) (Vint32(Int.repr 77))));
 [AllApart 601%positive 0%Z 4%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 split;reflexivity.
Qed.
Lemma AllEnvironment : V293_tcb_init_env AllLE 101%Z 102%Z 103%Z 104%Z 105%Z 106%Z 107%Z 108%Z
 201%positive 202%positive 203%positive 204%positive 205%positive 206%positive 207%positive 208%positive.
Proof. unfold V293_tcb_init_env,AllLE;repeat split;
 repeat first [rewrite map_get_set |rewrite map_get_set' by discriminate];reflexivity. Qed.
Lemma AllValues : V293_tcb_init_values_valid Vnull Vnull (Vint32 Int.zero)
 (Vint32(Int.repr 128)) Vnull (Vint32 Int.zero).
Proof. repeat split;reflexivity. Qed.
Theorem AllFresh : forall q, get (AllTasks q) AllNewTid=None.
Proof. intro q. reflexivity. Qed.
Theorem AllExistingOwned : forall R,
 V293_rdy_raw_cells AllExisting R ==> V293_owned_task_records (AllTasks 12) ** R.
Proof.
 intros R s Owned.
 assert (Types : Forall (fun cell => let '(_,tp,v):=cell in rule_type_val_match tp v=true) AllExisting)
 by (repeat constructor).
 apply (V293_raw_record_ownership _ _ Types) in Owned.
 assert (Held : s |= V293_owned_task_record AllOldTid (Int.repr 12) rdy Vnull ** R).
 { eapply astar_mono;[ |intros st HS;exact HS |exact Owned].
 intros st HS. exists 12. exists 0. apply astar_l_apure_intro;[exact HS |repeat split;try reflexivity;lia]. }
 change (s |= (V293_owned_task_record AllOldTid (Int.repr 12) rdy Vnull ** Aemp) ** R).
 clear -Held. sep auto.
Qed.
Theorem AllGoodCall : forall P ks, exists Mf,
 cstepstar P (curs AllCode,(kenil,ks)) ((emp:env),AllLE,AllMemory AllCells)
 (curs(sskip None),(kenil,ks)) ((emp:env),AllLE,Mf) /\ AllState Mf |= AllPost 12.
Proof.
 intros P ks.
 eapply (V293_OS_TCBInit_fields_extend_records (AllTasks 12) P ks (emp:env) AllLE
 (AllMemory AllCells) (fun _=>false) (false,nil,nil) (emp:osabst) (spec_done None)
 (V293_rdy_raw_cells AllSentinel Aemp)
 101%Z 102%Z 103%Z 104%Z 105%Z 106%Z 107%Z 108%Z
 201%positive 202%positive 203%positive 204%positive 205%positive 206%positive 207%positive 208%positive
 301%positive 128%Z 11 Vnull Vnull (Vint32 Int.zero) (Vint32(Int.repr 128)) Vnull (Vint32 Int.zero)
 (fun _=>Vundef));try (change (128+55<=4294967295)%Z;lia);try lia.
 - apply AllFresh.
 - exact AllEnvironment.
 - exact AllValues.
 - change (AllState (AllMemory AllCells) |= V293_rdy_raw_cells (AllOldFields++AllInputs)
     (V293_owned_task_records (AllTasks 12) ** V293_rdy_raw_cells AllSentinel Aemp)).
   eapply V293_raw_cells_mono;[apply AllExistingOwned | ].
   rewrite <-!V293_raw_cells_append. unfold AllCells. rewrite <-!app_assoc. apply AllLiteralEntry.
Qed.
Print Assumptions AllGoodCall.

(* This execution does not assume either candidate task-map postcondition. *)
Theorem AllRawCall : forall P ks, exists Mf,
 cstepstar P (curs AllCode,(kenil,ks)) ((emp:env),AllLE,AllMemory AllCells)
 (curs(sskip None),(kenil,ks)) ((emp:env),AllLE,Mf) /\
 AllState Mf |= V293_rdy_raw_cells (AllNewFields++AllInputs++AllExisting++AllSentinel) Aemp.
Proof.
 intros P ks.
 eapply (V293_OS_TCBInit_fields_execution P ks (emp:env) AllLE
 (AllMemory AllCells) (fun _=>false) (false,nil,nil) (emp:osabst) (spec_done None)
 (V293_rdy_raw_cells (AllExisting++AllSentinel) Aemp)
 101%Z 102%Z 103%Z 104%Z 105%Z 106%Z 107%Z 108%Z
 201%positive 202%positive 203%positive 204%positive 205%positive 206%positive 207%positive 208%positive
 301%positive 128%Z 11 Vnull Vnull (Vint32 Int.zero) (Vint32(Int.repr 128)) Vnull (Vint32 Int.zero)
 (fun _=>Vundef));try (change (128+55<=4294967295)%Z;lia);try lia.
 - exact AllEnvironment.
 - exact AllValues.
 - rewrite <-!V293_raw_cells_append. apply AllLiteralEntry.
Qed.
Theorem AllMapOnlyFactor : forall t, t<>AllOldTid ->
 get (AllUpdated 12) t=get (AllUpdated 11) t.
Proof.
 intros t Different. unfold AllUpdated.
 destruct (tidspec.beq t AllNewTid) eqn:New.
 - apply tidspec.beq_true_eq in New. subst t. rewrite !map_get_set. reflexivity.
 - apply tidspec.beq_false_neq in New. rewrite !map_get_set' by congruence.
   unfold AllTasks. rewrite !map_get_sig' by congruence. reflexivity.
Qed.
Theorem AllMapLookups :
 get (AllUpdated 12) AllOldTid=Some(Int.repr 12,rdy,Vnull) /\
 get (AllUpdated 11) AllOldTid=Some(Int.repr 11,rdy,Vnull) /\
 get (AllUpdated 12) AllNewTid=Some(Int.repr 11,rdy,Vnull) /\
 get (AllUpdated 11) AllNewTid=Some(Int.repr 11,rdy,Vnull).
Proof. repeat split;reflexivity. Qed.
Lemma AllRecordsFrameSound : forall tasks R M,
 AllState M |= V293_owned_task_records tasks ** R -> V293_task_records M tasks.
Proof.
 intros tasks R M Held. apply sat_split in Held.
 destruct Held as (m1&m2&o1&o2&JM&JO&Records&Other).
 pose proof (V293_owned_task_records_sound _ _ Records) as Sound.
 intros t priority status message Lookup.
 eapply V293_task_record_sub;[exists m2;exact JM |apply Sound;exact Lookup].
Qed.
Theorem AllBadCall : forall P ks, exists Mf,
 cstepstar P (curs AllCode,(kenil,ks)) ((emp:env),AllLE,AllMemory AllCells)
 (curs(sskip None),(kenil,ks)) ((emp:env),AllLE,Mf) /\
 load Tint8 Mf (301%positive,58%Z)=Some(V293_byteval 12) /\
 ~ AllState Mf |= V293_owned_task_records (AllUpdated 11) ** Atrue.
Proof.
 intros P ks. destruct (AllRawCall P ks) as (Mf&Exec&Raw). exists Mf.
 split;[exact Exec | ].
 assert (Read : load Tint8 Mf (301%positive,58%Z)=Some(V293_byteval 12)).
 { change (load Tint8 (getmem (AllState Mf)) (301%positive,58%Z)=Some(V293_byteval 12)).
 eapply V293_rdy_raw_load;[ |reflexivity |exact Raw].
 unfold AllNewFields,AllInputs,AllExisting,AllSentinel,V293_tcb_init_final_fields.
 cbn [In app];tauto. }
 split;[exact Read | ]. intro Bad.
 pose proof (AllRecordsFrameSound _ _ _ Bad) as Sound.
 assert (Lookup : get (AllUpdated 11) AllOldTid=Some(Int.repr 11,rdy,Vnull)) by reflexivity.
 specialize (Sound _ _ _ _ Lookup).
 destruct Sound as (p&Range&Priority&Fields&Status).
 assert (p=11) by (eapply V293_priority_repr_injective;[exact Range |lia |symmetry;exact Priority]).
 subst p. destruct Fields as (Physical&Rest).
 change (load Tint8 Mf (301%positive,58%Z)=Some(V293_byteval 11)) in Physical.
 rewrite Read in Physical. discriminate.
Qed.
Theorem AllGoodSameMf : forall P ks, exists Mf,
 cstepstar P (curs AllCode,(kenil,ks)) ((emp:env),AllLE,AllMemory AllCells)
 (curs(sskip None),(kenil,ks)) ((emp:env),AllLE,Mf) /\
 (AllState Mf |= AllPost 12) /\ V293_task_records Mf (AllUpdated 12) /\
 get (AllUpdated 12) AllOldTid=Some(Int.repr 12,rdy,Vnull) /\
 get (AllUpdated 12) AllNewTid=Some(Int.repr 11,rdy,Vnull) /\
 load Tint32 Mf (601%positive,0%Z)=Some(Vint32(Int.repr 77)).
Proof.
 intros P ks. destruct (AllGoodCall P ks) as (Mf&Exec&Owned). exists Mf.
 split;[exact Exec | ]. split;[exact Owned | ].
 split;[eapply AllRecordsFrameSound;exact Owned | ].
 split;[reflexivity | ]. split;[reflexivity | ].
 change (load Tint32 (getmem(AllState Mf)) (601%positive,0%Z)=Some(Vint32(Int.repr 77))).
 eapply V293_star_load_r;[ |exact Owned]. intros st Raw.
 rewrite <-!V293_raw_cells_append in Raw.
 eapply V293_rdy_raw_load;[ |reflexivity |exact Raw].
 unfold AllRemaining,AllInputs,AllSentinel,V293_tcb_init_record_remainder.
 cbn [In app];tauto.
Qed.
Print Assumptions AllLiteralEntry.
Print Assumptions AllRawCall.
Print Assumptions AllMapOnlyFactor.
Print Assumptions AllMapLookups.
Print Assumptions AllRecordsFrameSound.
Print Assumptions AllBadCall.
Print Assumptions AllGoodSameMf.
