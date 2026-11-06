(* Only the unaccessed row0 byte differs. Both physical entries reuse the
   same canonical table and TCB records; rejection is an input gate only. *)
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
Require Import CertiOS.certiucos.v293.proofs.V293InitReadyPayload.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyTaskInvariant.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordInvariant.
Require Import Coq.Sorting.Permutation.
Import ListNotations.
Local Open Scope nat_scope.

Definition IRPRow (bad:bool) : V293_record_cell :=
 ((403%positive,0%Z),Tint8,V293_byteval(if bad then 1 else 0)).
Definition IRPFrame bad := IRPRow bad::CIRSentinel.
Definition IRPInitial bad := CIROldFields++CIRInputs++CIRLinks++CIRSaved++CIRTail++CIRHole false++IRPFrame bad.
Definition IRPCells bad := IRPRow bad::CIRCells false.
Definition IRPPost := V293_owned_task_records CIRUpdated ** V293_rdy_raw_cells
 (tl CIRFinalLinks++CIRRemainder++
 [((405%positive,0%Z),Tptr V293_tcb_type,Vnull);
  ((406%positive,44%Z),Tptr V293_tcb_type,Vptr CIRNewTid)]++CIRHole false++IRPFrame false) Atrue.
Definition IRPRest :=
 [((301%positive,148%Z),Tcom_ptr 410%Z,Vptr CIROldTid);
  ((301%positive,152%Z),Tcom_ptr 410%Z,Vnull);
  ((401%positive,0%Z),Tptr V293_tcb_type,Vptr CIRNewTid);
  ((404%positive,0%Z),Tint8,V293_byteval 2);
  ((301%positive,32%Z),Tcom_ptr 410%Z,Vptr CIRNewTid)]++
 CIRRemainder++((405%positive,0%Z),Tptr V293_tcb_type,Vnull)::CIRSentinel.
Definition IRPJoint := V293_ready_payload 403%positive 402%positive 406%positive CIRUpdated **
 V293_rdy_raw_cells IRPRest Atrue.
Definition IRPHookCells (second:bool) := V293_record_hook_cells
 201%positive 202%positive 203%positive 204%positive 205%positive 206%positive 207%positive 208%positive 209%positive
 405%positive 406%positive 301%positive 128%Z 11 Vnull Vnull (Vint32 Int.zero) (Vint32 Int.zero)
 Vnull (Vint32 Int.zero) Vnull (if second then Vptr CIRNewTid else Vnull)
 (CIRTail++CIRHole false++IRPFrame false).
Definition IRPHooks P f hi hc ks enabled si ci (second:bool) :=
 V293_records_hook_return CIRUpdated P (if second then hc else hi) 301%positive 128%Z
 (if second then V293_tcb_second_hook_cont f hi hc CIRCaller ks else V293_tcb_first_hook_cont f hi hc CIRCaller ks)
 CIRGE CIRLE (fun _=>false) (false,nil,nil) (emp:osabst) (spec_done None) enabled si ci (IRPHookCells second).
Lemma IRPPositiveBitmap : V293_bitmap_tasks 0 16 CIRTasks.
Proof.
 assert(Empty:V293_bitmap_tasks 0 0 (emp:TcbMod.map)).
 { intros p Bound. unfold V293_bitmap_ready. rewrite !Nat.bits_0.
   split;[intuition discriminate |intros(t&msg&Lookup);discriminate]. }
 pose proof(V293_init_bitmap_insert 0 0 (emp:TcbMod.map) CIROldTid 12 ltac:(lia) eq_refl Empty)as Insert.
 change(V293_bitmap_tasks 0 16 (set (emp:TcbMod.map) CIROldTid (Int.repr 12,rdy,Vnull)))in Insert.
 unfold CIRTasks. rewrite <-map_set_emp. exact Insert.
Qed.
Lemma IRPNegativeBitmapRejected : ~V293_bitmap_tasks 1 16 CIRTasks.
Proof.
 intro Bitmap. assert(Bit:V293_bitmap_ready 1 16 0)by(left;split;[lia |reflexivity]).
 destruct(proj1(Bitmap 0 ltac:(lia))Bit)as(t&msg&Lookup).
 unfold CIRTasks in Lookup. destruct(tidspec.beq t CIROldTid)eqn:E.
 - apply tidspec.beq_true_eq in E;subst t. rewrite map_get_sig in Lookup;discriminate.
 - apply tidspec.beq_false_neq in E. rewrite map_get_sig' in Lookup by congruence;discriminate.
Qed.
Theorem IRPLiteralEntry : forall bad, CIREntryState(CIRMemory(IRPCells bad)) |=
 V293_rdy_raw_cells(IRPCells bad) Aemp.
Proof.
 intro bad;destruct bad;unfold CIREntryState,IRPCells,IRPRow;
 cbn[CIRMemory V293_rdy_raw_cells].
 all: eapply V293_wstate_star with
  (m1:=V293_encoded_memory 403%positive 0%Z true (encode_val Tint8 (V293_byteval _))).
 all: try(split;[apply V293_encoded_memory_mapsto |reflexivity]).
 all: try exact(CIRLiteralEntry false).
 all: unfold CIRCells,CIRInitial,CIROldFields,CIRInputs,CIRLinks,CIRSaved,CIRTail,CIRSentinel,
  CIROldRecord,CIRHole,CIREntries,CIRPositive,CIROldTid.
 all: cbn[app CIRMemory V293_priority_hole V293_priority_cells repeat update_nth_val].
 all: CIRApart 403%positive 0%Z 1%Z.
Qed.
Theorem IRPSpatialEntry : forall bad, CIREntryState(CIRMemory(IRPCells bad)) |=
 V293_rdy_raw_cells(IRPInitial bad)(V293_owned_task_records CIRTasks ** Atrue).
Proof.
 intro bad. eapply V293_raw_cells_mono.
 - intros st HS. apply CIROldOwned in HS.
   eapply astar_mono;[intros s H;exact H |intros s H;exact I |exact HS].
 - rewrite <-V293_raw_cells_append. eapply V293_raw_cells_permutation;[ |exact(IRPLiteralEntry bad)].
   unfold IRPCells,CIRCells,CIRInitial,IRPInitial,IRPFrame.
   repeat rewrite <-app_assoc. apply Permutation_sym.
   change(Permutation
    ((CIROldFields++CIRInputs++CIRLinks++CIRSaved++CIRTail++CIRHole false)++
     IRPRow bad::(CIRSentinel++CIROldRecord))
    (IRPRow bad::((CIROldFields++CIRInputs++CIRLinks++CIRSaved++CIRTail++CIRHole false)++
     (CIRSentinel++CIROldRecord)))).
   apply Permutation_sym,Permutation_middle.
Qed.

Theorem IRPPrefix : forall bad P f hi hc ks enabled si ci, exists Mf,
 V293_local_steps P (curs(CIRCode hi hc),(kenil,kcall f (V293_TCBInit_function_body hi hc) CIRCaller ks))
 ((CIRGE,CIRLE,CIRMemory (IRPCells bad)),(fun _=>false),(enabled,si,ci))
 (curs(sfexec hi [Vptr CIRNewTid] [Tptr V293_tcb_type]),
  (kenil,V293_tcb_first_hook_cont f hi hc CIRCaller ks))
 ((CIRGE,CIRLE,Mf),(fun _=>false),(enabled,si,ci)) /\
 (CIREntryState Mf |= V293_owned_task_records CIRUpdated ** V293_rdy_raw_cells (V293_record_hook_cells
 201%positive 202%positive 203%positive 204%positive 205%positive 206%positive 207%positive 208%positive 209%positive
 405%positive 406%positive 301%positive 128%Z 11 Vnull Vnull (Vint32 Int.zero) (Vint32 Int.zero)
 Vnull (Vint32 Int.zero) Vnull Vnull (CIRTail++CIRHole false++IRPFrame bad)) Atrue).
Proof.
 intros bad P f hi hc ks enabled si ci.
 eapply (V293_TCBInit_prefix_to_record_hook CIRTasks P ks CIRGE CIRCaller (CIRMemory (IRPCells bad))
 (fun _=>false) (false,nil,nil) (emp:osabst) (spec_done None) enabled si ci f hi hc
 201%positive 202%positive 203%positive 204%positive 205%positive 206%positive 207%positive 208%positive 209%positive
 405%positive 406%positive 301%positive 128%Z 11 Vnull Vnull (Vint32 Int.zero) (Vint32 Int.zero)
 Vnull (Vint32 Int.zero) Vundef Vnull (fun _=>Vundef) Vnull (CIRTail++CIRHole false++IRPFrame bad));
 try reflexivity;try lia;try (change (128+55<=4294967295)%Z;lia).
 - repeat split;reflexivity.
 - exact (IRPSpatialEntry bad).
Qed.

Theorem IRPGoodCall : forall P f hi hc ks enabled si ci,
 IRPHooks P f hi hc ks enabled si ci false -> IRPHooks P f hi hc ks enabled si ci true -> exists Mf,
 V293_local_steps P (curs(CIRCode hi hc),(kenil,kcall f (V293_TCBInit_function_body hi hc) CIRCaller ks))
 ((CIRGE,CIRLE,CIRMemory (IRPCells false)),(fun _=>false),(enabled,si,ci))
 (curs(sskip(Some(Vint32 Int.zero))),(kenil,ks)) ((CIRGE,CIRCaller,Mf),(fun _=>false),(enabled,si,ci)) /\
 (CIRState Mf |= IRPPost) /\ CIRFreed Mf /\
 V293_init_priority_table (update_nth_val 11 CIRPositive (Vptr CIRNewTid)) CIRUpdated /\
 (CIRState Mf |= IRPJoint).
Proof.
 intros P f hi hc ks enabled si ci Hook1 Hook2.
 eapply (V293_OS_TCBInit_ready_return_under_hooks CIRPositive CIRTasks 0 16 P f hi hc CIRCaller ks CIRGE
 (CIRMemory (IRPCells false)) (fun _=>false) (false,nil,nil) (emp:osabst) (spec_done None) enabled si ci
 201%positive 202%positive 203%positive 204%positive 205%positive 206%positive 207%positive 208%positive 209%positive
 405%positive 406%positive 301%positive 128%Z 401%positive 402%positive 403%positive 404%positive
 301%positive 8%Z true 11 1 Vnull Vnull (Vint32 Int.zero) (Vint32 Int.zero) Vnull (Vint32 Int.zero)
 Vundef Vnull (fun _=>Vundef) Vnull Vnull CIRSentinel);
 try lia;try (change (128+55<=4294967295)%Z;lia);try (change (8+24<=4294967295)%Z;lia).
 - exact IRPPositiveBitmap.
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
 - intros a tp v Member. cbn [V293_pub_link_cells tl app V293_prio_row V293_init_other_row CIRSentinel CIRPositive CIREntries CIRHole
   V293_priority_hole V293_priority_cells update_nth_val repeat
   V293_tcb_init_record_remainder In] in Member.
   repeat destruct Member as [E |Member];try contradiction;inversion E;subst;
   cbn [fst V293_tcb_function_blocks In];intuition discriminate.
 - exact Hook1.
 - exact Hook2.
 - exact (IRPSpatialEntry false).
Qed.

Lemma IRPPhysicalOutside : forall b off,
 b<>403%positive \/ (off<0)%Z \/ (1<=off)%Z ->
 get(CIRMemory(IRPCells true))(b,off)=get(CIRMemory(IRPCells false))(b,off).
Proof.
 intros b off Outside. unfold IRPCells,IRPRow. cbn[CIRMemory].
 rewrite !map_merge_semp by reflexivity.
 rewrite !V293_encoded_memory_outside by exact Outside. reflexivity.
Qed.
Lemma IRPJointReads : forall M, CIRState M |= IRPJoint ->
 V293_task_records M CIRUpdated /\
 exists lo hi entries, V293_ready_rel lo hi entries CIRUpdated /\
 V293_ready_loads M 403%positive 402%positive 406%positive lo hi entries.
Proof.
 intros M Held. unfold IRPJoint,V293_ready_payload in Held.
 split.
 - assert(Records:CIRState M |= V293_owned_task_records CIRUpdated ** Atrue)by(clear -Held;sep auto).
   apply sat_split in Records. destruct Records as(m1&m2&o1&o2&JM&JO&Owned&Other).
   pose proof(V293_owned_task_records_sound _ _ Owned)as Sound.
   intros t priority status message Lookup.
   eapply V293_task_record_sub;[exists m2;exact JM |apply Sound;exact Lookup].
 - assert(Ready:CIRState M |= V293_ready_owned 403%positive 402%positive 406%positive CIRUpdated ** Atrue)
    by(clear -Held;sep auto).
   exact(V293_ready_owned_observation 403%positive 402%positive 406%positive _ _ _ Ready).
Qed.
Lemma IRPBitmapReads : forall M, CIRState M |= IRPPost ->
 load Tint8 M(403%positive,0%Z)=Some(V293_byteval 0) /\
 load Tint8 M(403%positive,1%Z)=Some(V293_byteval 24) /\
 load Tint8 M(402%positive,0%Z)=Some(V293_byteval 2).
Proof.
 intros M Held.
 assert(Read:forall a v, rule_type_val_match Tint8 v=true -> In(a,Tint8,v)
  (tl CIRFinalLinks++CIRRemainder++
  [((405%positive,0%Z),Tptr V293_tcb_type,Vnull);
   ((406%positive,44%Z),Tptr V293_tcb_type,Vptr CIRNewTid)]++CIRHole false++IRPFrame false) ->
  load Tint8 M a=Some v).
 { intros a v Typed Member. change(load Tint8(getmem(CIRState M))a=Some v).
   eapply V293_star_load_r;[ |exact Held]. intros st Raw.
   eapply V293_rdy_raw_load;[exact Member |exact Typed |exact Raw]. }
 repeat split;apply Read;try reflexivity;
 unfold CIRFinalLinks,CIRRemainder,IRPFrame,IRPRow,CIRSentinel,CIRHole,CIREntries,CIRPositive,V293_pub_link_cells,V293_tcb_init_record_remainder;
 cbn[V293_prio_row In app tl V293_priority_hole V293_priority_cells update_nth_val repeat];tauto.
Qed.
Lemma IRPJointCanary : forall M, CIRState M |= IRPJoint ->
 load Tint32 M(601%positive,0%Z)=Some(Vint32(Int.repr 77)).
Proof.
 intros M Held. change(load Tint32(getmem(CIRState M))(601%positive,0%Z)=Some(Vint32(Int.repr 77))).
 eapply V293_star_load_r;[ |exact Held]. intros st Raw.
 eapply V293_rdy_raw_load;[ |reflexivity |exact Raw].
 unfold IRPRest,CIRRemainder,CIRSentinel,V293_tcb_init_record_remainder. cbn[In app];tauto.
Qed.

Lemma IRPChangedByte : forall bad,
 load Tint8(CIRMemory(IRPCells bad))(403%positive,0%Z)=
 Some(V293_byteval(if bad then 1 else 0)).
Proof.
 intro bad. assert(Typed:rule_type_val_match Tint8 (V293_byteval(if bad then 1 else 0))=true)
 by(destruct bad;reflexivity). change(load Tint8(getmem(CIREntryState(CIRMemory(IRPCells bad))))
 (403%positive,0%Z)=Some(V293_byteval(if bad then 1 else 0))).
 eapply V293_rdy_raw_load with(cells:=IRPCells bad)(R:=Aemp);[left;reflexivity |exact Typed |exact(IRPLiteralEntry bad)].
Qed.
