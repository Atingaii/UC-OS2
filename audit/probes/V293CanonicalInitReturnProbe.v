(* Full priority table plus allocated old task record; the prefix is unconditional,
   but the downstream return still requires both original CPU hook contracts.
   The single-slot counterexample rejects an input gate only. *)
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
Import ListNotations.
Local Open Scope nat_scope.
Definition CIROldFields : list V293_record_cell :=
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
Definition CIRInputs : list V293_record_cell :=
 [((208%positive,0%Z),Tptr V293_tcb_type,Vundef);
  ((201%positive,0%Z),Tint8,V293_byteval 11);
  ((202%positive,0%Z),Tptr Tint32,Vnull);
  ((203%positive,0%Z),Tptr Tint32,Vnull);
  ((204%positive,0%Z),Tint16,Vint32 Int.zero);
  ((205%positive,0%Z),Tint32,Vint32 Int.zero);
  ((206%positive,0%Z),Tptr Tvoid,Vnull);
  ((207%positive,0%Z),Tint16,Vint32 Int.zero)].
Definition CIRLinks : list V293_record_cell :=
 [((405%positive,0%Z),Tptr V293_tcb_type,Vptr(301%positive,Int.repr 128));
  ((301%positive,148%Z),Tcom_ptr 410%Z,Vnull)].
Definition CIRSaved : list V293_record_cell :=
 [((209%positive,0%Z),Tint32,Vint32 Int.zero);
  ((406%positive,44%Z),Tptr V293_tcb_type,Vnull)].
Definition CIRTail : list V293_record_cell :=
 [((301%positive,152%Z),Tcom_ptr 410%Z,Vnull);
  ((401%positive,0%Z),Tptr V293_tcb_type,Vptr(301%positive,Int.repr 8));
  ((402%positive,0%Z),Tint8,V293_byteval 2);
  ((403%positive,1%Z),Tint8,V293_byteval 16);
  ((404%positive,0%Z),Tint8,V293_byteval 1);
  ((301%positive,32%Z),Tcom_ptr 410%Z,Vnull)].
Definition CIROldRecord : list V293_record_cell :=
 [((301%positive,58%Z),(Tint8),(V293_byteval 12));
  ((301%positive,60%Z),(Tint8),(V293_byteval 1));
  ((301%positive,59%Z),(Tint8),(V293_byteval 4));
  ((301%positive,62%Z),(Tint8),(V293_byteval 2));
  ((301%positive,61%Z),(Tint8),(V293_byteval 16));
  ((301%positive,40%Z),(Tptr Tvoid),(Vnull));
  ((301%positive,56%Z),(Tint8),(V293_byteval 0))].
Definition CIRSentinel : list V293_record_cell :=
 [((601%positive,0%Z),(Tint32),(Vint32(Int.repr 77)))].
Definition CIROldTid : tid := (301%positive,Int.repr 8).
Definition CIRNewTid : tid := (301%positive,Int.repr 128).
Definition CIRTasks : TcbMod.map := sig CIROldTid (Int.repr 12,rdy,Vnull).
Definition CIRUpdated : TcbMod.map := set CIRTasks CIRNewTid (Int.repr 11,rdy,Vnull).
Definition CIRGE : env := set (set (set (set (set (set (emp:env)
 91%Z (405%positive,Tptr V293_tcb_type)) 92%Z (406%positive,Tarray(Tptr V293_tcb_type) 13))
 93%Z (401%positive,Tptr V293_tcb_type)) 94%Z (402%positive,Tint8))
 95%Z (403%positive,Tarray Tint8 2)) 96%Z (404%positive,Tint8).
Definition CIRLE := V293_tcb_function_env 201%positive 202%positive 203%positive 204%positive 205%positive 206%positive 207%positive 208%positive 209%positive.
Definition CIRCaller : env := sig 777%Z (701%positive,Tint32).
Definition CIRBlocks := V293_tcb_function_blocks 201%positive 202%positive 203%positive 204%positive 205%positive 206%positive 207%positive 208%positive 209%positive.
Definition CIRAddresses := V293_tcb_function_addresses 201%positive 202%positive 203%positive 204%positive 205%positive 206%positive 207%positive 208%positive 209%positive.
Definition CIRPositive := update_nth_val 12 (repeat Vnull 13) (Vptr CIROldTid).
Definition CIRNegative := update_nth_val 0 CIRPositive (Vptr CIROldTid).
Definition CIREntries (bad:bool) := if bad then CIRNegative else CIRPositive.
Definition CIRHole bad := V293_priority_hole (CIREntries bad) 406%positive 0%Z 11.
Definition CIRInitial bad := CIROldFields++CIRInputs++CIRLinks++CIRSaved++CIRTail++CIRHole bad++CIRSentinel.
Definition CIRCells bad := CIRInitial bad++CIROldRecord.
Fixpoint CIRMemory (cells : list V293_record_cell) : mem :=
 match cells with []=>emp | ((b,i),tp,v)::tail=>
 merge (V293_encoded_memory b i true (encode_val tp v)) (CIRMemory tail) end.
Definition CIREntryState M := V293_wstate CIRGE CIRLE M.
Definition CIRState M := V293_wstate CIRGE CIRCaller M.
Definition CIRFreed M := forall b tp k, In (b,tp) CIRAddresses -> k<typelen tp -> get M (b,Z.of_nat k)=None.
Definition CIRCode hi hc := V293_TCBInit_prefix 91%Z 108%Z 101%Z 102%Z 103%Z 104%Z 105%Z 106%Z 107%Z
 (V293_TCBInit_success_suffix hi hc).
Definition CIRRemainder := V293_tcb_init_record_remainder 301%positive 128%Z
 Vnull Vnull (Vint32 Int.zero) (Vint32 Int.zero) Vnull (Vint32 Int.zero).
Definition CIRSurvivors := CIRRemainder++
 [((405%positive,0%Z),Tptr V293_tcb_type,Vnull);
  ((406%positive,44%Z),Tptr V293_tcb_type,Vptr CIRNewTid)]++CIRHole false++CIRSentinel.
Definition CIRFinalLinks := V293_pub_link_cells 208%positive 301%positive 128%Z
 401%positive 402%positive 403%positive 404%positive 301%positive 8%Z true 11
 (Vptr CIROldTid) Vnull (Vptr CIRNewTid) 2 24 2 (Vptr CIRNewTid).
Definition CIRPost := V293_owned_task_records CIRUpdated **
 V293_rdy_raw_cells (tl CIRFinalLinks++CIRSurvivors) Atrue.
Definition CIRHookCells (second : bool) := V293_record_hook_cells
 201%positive 202%positive 203%positive 204%positive 205%positive 206%positive 207%positive 208%positive 209%positive
 405%positive 406%positive 301%positive 128%Z 11 Vnull Vnull (Vint32 Int.zero) (Vint32 Int.zero)
 Vnull (Vint32 Int.zero) Vnull (if second then Vptr CIRNewTid else Vnull) (CIRTail++CIRHole false++CIRSentinel).
Definition CIRHooks P f hi hc ks enabled si ci (second : bool) :=
 V293_records_hook_return CIRUpdated P (if second then hc else hi) 301%positive 128%Z
 (if second then V293_tcb_second_hook_cont f hi hc CIRCaller ks else V293_tcb_first_hook_cont f hi hc CIRCaller ks)
 CIRGE CIRLE (fun _=>false) (false,nil,nil) (emp:osabst) (spec_done None) enabled si ci (CIRHookCells second).
Ltac CIROutside :=
 repeat first [rewrite V293_encoded_memory_outside by
 (first [left;congruence | right;cbn [V293_byteval length encode_val typelen list_repeat inj_pointer inj_bytes encode_int List.map];lia])
 |rewrite map_merge_semp by reflexivity];reflexivity.
Ltac CIRApart b start count :=
 apply map_join_merge;apply map_disjoint;intros [other off];
 destruct (Pos.eq_dec other b) as [B|B];
 [subst other;destruct (Z_lt_dec off start) as [Low|Low];
 [left;apply V293_encoded_memory_outside;right;left;exact Low |
 destruct (Z_lt_dec off (start+count)) as [Inside|Outside];
 [right;left;CIROutside |left;apply V293_encoded_memory_outside;right;right;
 cbn [V293_byteval length encode_val typelen list_repeat inj_pointer inj_bytes encode_int List.map];lia]] |
 left;apply V293_encoded_memory_outside;left;exact B].
Ltac CIRLiteral :=
 repeat match goal with
 | |- V293_wstate _ _ (merge (V293_encoded_memory ?b ?off true (encode_val ?tp ?v)) _) |= _ =>
   let count:=eval cbv in (Z.of_nat(typelen tp)) in
   eapply V293_wstate_star with (m1:=V293_encoded_memory b off true (encode_val tp v));
   [ CIRApart b off count | split;[apply V293_encoded_memory_mapsto |reflexivity] | ]
 end;split;reflexivity.
Theorem CIRLiteralEntry : forall bad, CIREntryState (CIRMemory (CIRCells bad)) |= V293_rdy_raw_cells (CIRCells bad) Aemp.
Proof.
 intro bad. destruct bad;
 unfold CIREntryState,CIRCells,CIRInitial,CIROldFields,CIRInputs,CIRLinks,CIRSaved,
  CIRTail,CIRSentinel,CIROldRecord,CIRHole,CIREntries,CIRNegative,CIRPositive,CIROldTid.
 all: cbn [app CIRMemory V293_rdy_raw_cells V293_priority_hole V293_priority_cells repeat update_nth_val].
 all: CIRLiteral.
Qed.
Lemma CIREnvironment : V293_pub_env CIRGE CIRLE 108%Z 93%Z 94%Z 95%Z 96%Z
 208%positive 401%positive 402%positive 403%positive 404%positive.
Proof. unfold V293_pub_env,CIRGE,CIRLE,V293_tcb_function_env;repeat split;
 repeat first [rewrite map_get_set |rewrite map_get_set' by discriminate];reflexivity. Qed.
Lemma CIROldOwned : forall R,
 V293_rdy_raw_cells CIROldRecord R ==> V293_owned_task_records CIRTasks ** R.
Proof.
 intros R s Owned. apply V293_raw_cells_separate in Owned.
 assert (Held : s |= V293_owned_task_record CIROldTid (Int.repr 12) rdy Vnull ** R).
 { eapply astar_mono;[apply (V293_raw_to_ready_record 301%positive 8%Z 12);lia |intros st HS;exact HS |exact Owned]. }
 change (s |= (V293_owned_task_record CIROldTid (Int.repr 12) rdy Vnull ** Aemp) ** R).
 clear -Held. sep auto.
Qed.
Theorem CIRSpatialEntry : CIREntryState (CIRMemory (CIRCells false)) |=
 V293_rdy_raw_cells (CIRInitial false) (V293_owned_task_records CIRTasks ** Atrue).
Proof.
 eapply V293_raw_cells_mono;[ | ].
 - intros st HS. apply CIROldOwned in HS.
   eapply astar_mono;[intros s H;exact H |intros s H;exact I |exact HS].
 - rewrite <-V293_raw_cells_append. exact (CIRLiteralEntry false).
Qed.
Theorem CIRPrefix : forall P f hi hc ks enabled si ci, exists Mf,
 V293_local_steps P (curs(CIRCode hi hc),(kenil,kcall f (V293_TCBInit_function_body hi hc) CIRCaller ks))
 ((CIRGE,CIRLE,CIRMemory (CIRCells false)),(fun _=>false),(enabled,si,ci))
 (curs(sfexec hi [Vptr CIRNewTid] [Tptr V293_tcb_type]),
  (kenil,V293_tcb_first_hook_cont f hi hc CIRCaller ks))
 ((CIRGE,CIRLE,Mf),(fun _=>false),(enabled,si,ci)) /\
 (CIREntryState Mf |= V293_owned_task_records CIRUpdated ** V293_rdy_raw_cells (CIRHookCells false) Atrue).
Proof.
 intros P f hi hc ks enabled si ci.
 eapply (V293_TCBInit_prefix_to_record_hook CIRTasks P ks CIRGE CIRCaller (CIRMemory (CIRCells false))
 (fun _=>false) (false,nil,nil) (emp:osabst) (spec_done None) enabled si ci f hi hc
 201%positive 202%positive 203%positive 204%positive 205%positive 206%positive 207%positive 208%positive 209%positive
 405%positive 406%positive 301%positive 128%Z 11 Vnull Vnull (Vint32 Int.zero) (Vint32 Int.zero)
 Vnull (Vint32 Int.zero) Vundef Vnull (fun _=>Vundef) Vnull (CIRTail++CIRHole false++CIRSentinel));
 try reflexivity;try lia;try (change (128+55<=4294967295)%Z;lia).
 - repeat split;reflexivity.
 - exact CIRSpatialEntry.
Qed.
Lemma CIRPositiveCanonical : V293_init_priority_table CIRPositive CIRTasks.
Proof.
 assert (H:V293_init_priority_table CIRPositive
  (set (emp:TcbMod.map) CIROldTid (Int.repr 12,rdy,Vnull))).
 { apply V293_init_priority_insert;[apply V293_init_priority_empty |lia |reflexivity |reflexivity]. }
 change (V293_init_priority_table CIRPositive (sig CIROldTid (Int.repr 12,rdy,Vnull))).
 rewrite <- map_set_emp;exact H.
Qed.
Lemma CIRNegativeOldAccepted : V293_priority_table CIRNegative CIRTasks.
Proof.
 split;[reflexivity | ]. intros t pri status message Lookup.
 unfold CIRTasks in Lookup. destruct (tidspec.beq t CIROldTid) eqn:E.
 - apply tidspec.beq_true_eq in E;subst t. rewrite map_get_sig in Lookup.
   inversion Lookup;subst. exists 12. repeat split;try lia;reflexivity.
 - apply tidspec.beq_false_neq in E. rewrite map_get_sig' in Lookup by congruence;discriminate.
Qed.
Lemma CIRNegativeCanonicalRejected : ~V293_init_priority_table CIRNegative CIRTasks.
Proof.
 intro H. destruct (proj1(V293_init_priority_pointer_exact CIRNegative CIRTasks 0 CIROldTid H ltac:(lia)) eq_refl)
 as (st&msg&Lookup). change (Some(Int.repr 12,rdy,Vnull)=Some(Int.repr 0,st,msg)) in Lookup;discriminate.
Qed.
Lemma CIRSingleSlotOnly : forall p, p<>0 -> nth p CIRNegative Vnull=nth p CIRPositive Vnull.
Proof. intros p Different;apply V293_init_priority_nth_other;exact Different. Qed.
Definition CIRJoint := V293_owned_priority_table 406%positive
 (update_nth_val 11 CIRPositive (Vptr CIRNewTid)) **
 (V293_owned_task_records CIRUpdated ** V293_rdy_raw_cells
 (tl CIRFinalLinks++CIRRemainder++((405%positive,0%Z),Tptr V293_tcb_type,Vnull)::CIRSentinel) Atrue).
Theorem CIRGoodCall : forall P f hi hc ks enabled si ci,
 CIRHooks P f hi hc ks enabled si ci false -> CIRHooks P f hi hc ks enabled si ci true -> exists Mf,
 V293_local_steps P (curs(CIRCode hi hc),(kenil,kcall f (V293_TCBInit_function_body hi hc) CIRCaller ks))
 ((CIRGE,CIRLE,CIRMemory (CIRCells false)),(fun _=>false),(enabled,si,ci))
 (curs(sskip(Some(Vint32 Int.zero))),(kenil,ks)) ((CIRGE,CIRCaller,Mf),(fun _=>false),(enabled,si,ci)) /\
 (CIRState Mf |= CIRPost) /\ CIRFreed Mf /\
 V293_init_priority_table (update_nth_val 11 CIRPositive (Vptr CIRNewTid)) CIRUpdated /\
 (CIRState Mf |= CIRJoint).
Proof.
 intros P f hi hc ks enabled si ci Hook1 Hook2.
 eapply (V293_OS_TCBInit_canonical_return_under_hooks CIRPositive CIRTasks P f hi hc CIRCaller ks CIRGE
 (CIRMemory (CIRCells false)) (fun _=>false) (false,nil,nil) (emp:osabst) (spec_done None) enabled si ci
 201%positive 202%positive 203%positive 204%positive 205%positive 206%positive 207%positive 208%positive 209%positive
 405%positive 406%positive 301%positive 128%Z 401%positive 402%positive 403%positive 404%positive
 301%positive 8%Z true 11 2 16 1 Vnull Vnull (Vint32 Int.zero) (Vint32 Int.zero) Vnull (Vint32 Int.zero)
 Vundef Vnull (fun _=>Vundef) Vnull Vnull CIRSentinel);
 try lia;try (change (128+55<=4294967295)%Z;lia);try (change (8+24<=4294967295)%Z;lia).
 - exact CIRPositiveCanonical.
 - reflexivity.
 - reflexivity.
 - reflexivity.
 - exact CIREnvironment.
 - reflexivity.
 - repeat constructor;cbn;intuition congruence.
 - repeat split;reflexivity.
 - reflexivity.
 - intros t value Member. change (In (t,value)
    [(CIROldTid,(Int.repr 12,rdy,Vnull));(CIRNewTid,(Int.repr 11,rdy,Vnull))]) in Member.
   destruct Member as [Same |[Same |Impossible]];[inversion Same;subst |inversion Same;subst |contradiction];
   cbn [CIROldTid CIRNewTid fst V293_tcb_function_blocks In];intuition discriminate.
 - intros a tp v Member. cbn [V293_pub_link_cells tl app V293_prio_row CIRSentinel CIRPositive CIREntries CIRHole
   V293_priority_hole V293_priority_cells update_nth_val repeat
   V293_tcb_init_record_remainder In] in Member.
   repeat destruct Member as [E |Member];try contradiction;inversion E;subst;
   cbn [fst V293_tcb_function_blocks In];intuition discriminate.
 - exact Hook1.
 - exact Hook2.
 - exact CIRSpatialEntry.
Qed.

(* This control proves physical entry identity outside the four-byte slot;
   it does not execute either CPU hook or the downstream bad-input path. *)
Lemma CIRPhysicalOutside : forall b off,
 b<>406%positive \/ (off<0)%Z \/ (4<=off)%Z ->
 get (CIRMemory (CIRCells true)) (b,off)=get (CIRMemory (CIRCells false)) (b,off).
Proof.
 intros b off Outside.
 assert (Good:get (V293_encoded_memory 406%positive 0%Z true
   (encode_val (Tptr V293_tcb_type) Vnull)) (b,off)=None).
 { apply V293_encoded_memory_outside;exact Outside. }
 assert (Bad:get (V293_encoded_memory 406%positive 0%Z true
   (encode_val (Tptr V293_tcb_type) (Vptr CIROldTid))) (b,off)=None).
 { apply V293_encoded_memory_outside;exact Outside. }
 assert (MergePoint:forall m1 m1' m2 m2':mem,
   get m1 (b,off)=get m1' (b,off) -> get m2 (b,off)=get m2' (b,off) ->
   get (merge m1 m2) (b,off)=get (merge m1' m2') (b,off)).
 { intros m1 m1' m2 m2' E1 E2. rewrite !map_merge_semp by reflexivity.
   rewrite E1,E2;reflexivity. }
 assert (Extend:forall head m1 m2:mem, get m1 (b,off)=get m2 (b,off) ->
   get (merge head m1) (b,off)=get (merge head m2) (b,off)).
 { intros;apply MergePoint;[reflexivity |assumption]. }
 unfold CIRCells,CIRInitial,CIROldFields,CIRInputs,CIRLinks,CIRSaved,CIRTail,CIRSentinel,
 CIROldRecord,CIRHole,CIREntries,CIRNegative,CIRPositive.
 cbn [app CIRMemory V293_priority_hole V293_priority_cells repeat update_nth_val].
 repeat apply Extend. apply MergePoint;[rewrite Good,Bad;reflexivity |reflexivity].
Qed.
Lemma CIRJointReads : forall M, CIRState M |= CIRJoint ->
 V293_table_loads V293_tcb_type M 406%positive
  (update_nth_val 11 CIRPositive (Vptr CIRNewTid)) /\
 V293_task_records M CIRUpdated.
Proof.
 intros M Held. split.
 - eapply V293_full_priority_table_loads;[reflexivity |exact Held].
 - assert (Records:CIRState M |= V293_owned_task_records CIRUpdated **
    (V293_owned_priority_table 406%positive (update_nth_val 11 CIRPositive (Vptr CIRNewTid)) **
     V293_rdy_raw_cells
      (tl CIRFinalLinks++CIRRemainder++((405%positive,0%Z),Tptr V293_tcb_type,Vnull)::CIRSentinel) Atrue)).
   { unfold CIRJoint in Held;clear -Held;sep auto. }
   apply sat_split in Records. destruct Records as (m1&m2&o1&o2&JM&JO&Owned&Other).
   pose proof (V293_owned_task_records_sound _ _ Owned) as Sound.
   intros t priority status message Lookup.
   eapply V293_task_record_sub;[exists m2;exact JM |apply Sound;exact Lookup].
Qed.
Lemma CIRJointCanary : forall M, CIRState M |= CIRJoint ->
 load Tint32 M (601%positive,0%Z)=Some(Vint32(Int.repr 77)).
Proof.
 intros M Held. change (load Tint32 (getmem(CIRState M)) (601%positive,0%Z)=Some(Vint32(Int.repr 77))).
 eapply V293_star_load_r;[ |exact Held]. intros st Inner.
 eapply V293_star_load_r;[ |exact Inner]. intros st' Raw.
 eapply V293_rdy_raw_load;[ |reflexivity |exact Raw].
 unfold CIRFinalLinks,CIRRemainder,CIRSentinel,V293_pub_link_cells,V293_tcb_init_record_remainder.
 cbn [V293_prio_row In app tl];tauto.
Qed.
