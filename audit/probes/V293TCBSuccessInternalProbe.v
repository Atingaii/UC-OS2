(* Independent literal bytes and environments, local fixture names.
   No dependency on any historical probe. *)
Require Import CertiOS.certiucos.v293.proofs.V293TCBSuccessInternal.
Require Import CertiOS.certiucos.v293.proofs.V293TCBHookCall.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.certiucos.v293.proofs.V293TCBEmptyInternal.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
(* Independent literal resources and actual Success call-site entries; no old probe imports. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.certiucos.v293.proofs.V293TCBFieldsHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TCBSuccessHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TCBPriorityHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitPrefix.
Require Import CertiOS.certiucos.v293.code.V293OSTCBInitFunction.
Require Import CertiOS.certiucos.v293.code.V293OSTCBInitPrefix.
Require Import CertiOS.certiucos.v293.code.V293OSTCBPublish.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitFields.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293InitTCBClear.
Require Import CertiOS.certiucos.v293.proofs.V293StartRecord.
Require Import CertiOS.certiucos.v293.proofs.V293NullBytes.
Require Import CertiOS.certiucos.v293.proofs.V293InitAllRecords.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewWitness.
Require Import CertiOS.certiucos.v293.code.V293OSTCBInit.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List Coq.Sorting.Permutation Lia.
Import ListNotations.
Local Open Scope nat_scope.
Definition SuccessOld : list V293_record_cell :=
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
Definition SuccessInputs pc : list V293_record_cell :=
 [((201%positive,0%Z),(Tptr V293_tcb_type),(pc));
  ((202%positive,0%Z),(Tint8),(V293_byteval 11));
  ((203%positive,0%Z),(Tptr Tint32),(Vnull));
  ((204%positive,0%Z),(Tptr Tint32),(Vnull));
  ((205%positive,0%Z),(Tint16),(Vint32 Int.zero));
  ((206%positive,0%Z),(Tint32),(Vint32(Int.repr 128)));
  ((207%positive,0%Z),(Tptr Tvoid),(Vnull));
  ((208%positive,0%Z),(Tint16),(Vint32 Int.zero))].
Definition SuccessFinal : list V293_record_cell :=
 [((301%positive,128%Z),(Tptr Tint32),(Vnull));
  ((301%positive,178%Z),(Tint8),(V293_byteval 11));
  ((301%positive,176%Z),(Tint8),(Vint32 Int.zero));
  ((301%positive,177%Z),(Tint8),(Vint32 Int.zero));
  ((301%positive,172%Z),(Tint32),(Vint32 Int.zero));
  ((301%positive,132%Z),(Tptr Tvoid),(Vnull));
  ((301%positive,140%Z),(Tint32),(Vint32(Int.repr 128)));
  ((301%positive,136%Z),(Tptr Tint32),(Vnull));
  ((301%positive,144%Z),(Tint16),(Vint32 Int.zero));
  ((301%positive,146%Z),(Tint16),(Vint32 Int.zero));
  ((301%positive,183%Z),(Tint8),(Vint32 Int.zero));
  ((301%positive,180%Z),(Tint8),(V293_byteval 1));
  ((301%positive,179%Z),(Tint8),(V293_byteval 3));
  ((301%positive,182%Z),(Tint8),(V293_byteval 2));
  ((301%positive,181%Z),(Tint8),(V293_byteval 8));
  ((301%positive,156%Z),(Tcom_ptr 411%Z),(Vnull));
  ((301%positive,164%Z),(Tcom_ptr 412%Z),(Vnull));
  ((301%positive,160%Z),(Tptr Tvoid),(Vnull))].
Require Import CertiOS.certiucos.v293.proofs.V293TCBLinkedHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TCBPublishHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TCBPublish.
Definition SuccessGE : env := set (set (set (set (set (set (sig OSTCBCur (402%positive,Tptr Tvoid))
 91%Z (210%positive,Tptr V293_tcb_type)) 92%Z (211%positive,Tarray (Tptr V293_tcb_type) 13))
 93%Z (212%positive,Tptr V293_tcb_type)) 94%Z (213%positive,Tint8))
 95%Z (214%positive,Tarray Tint8 2)) 96%Z (215%positive,Tint8).
Definition SuccessLE : env :=
 set (set (set (set (set (set (set (set (set (emp:env)
 108%Z (201%positive,Tptr V293_tcb_type)) 101%Z (202%positive,Tint8))
 102%Z (203%positive,Tptr Tint32)) 103%Z (204%positive,Tptr Tint32))
 104%Z (205%positive,Tint16)) 105%Z (206%positive,Tint32))
 106%Z (207%positive,Tptr Tvoid)) 107%Z (208%positive,Tint16)) 109%Z (209%positive,Tint32).
Definition SuccessTid : tid := (301%positive,Int.repr 8).
Definition SuccessBytes b permission tp v := V293_encoded_memory b 0 permission (encode_val tp v).
Definition SuccessCurrent := SuccessBytes 402%positive false (Tptr Tvoid) (Vptr SuccessTid).
Definition SuccessSentinel := SuccessBytes 601%positive true Tint8 (Vint32(Int.repr 77)).
Fixpoint SuccessMemory (cells : list V293_record_cell) : mem :=
 match cells with []=>emp | ((b,i),tp,v)::tail=>
 merge (V293_encoded_memory b i true (encode_val tp v)) (SuccessMemory tail) end.
Definition SuccessHead := Vptr(301%positive,Int.repr 128).
Definition SuccessNext := Vptr(301%positive,Int.repr 384).
Definition SuccessOldHead (present:bool) := if present then Vptr(301%positive,Int.repr 256) else Vnull.
Definition SuccessExtra (present:bool) : list V293_record_cell :=
 [((301%positive,152%Z),Tcom_ptr 410%Z,Vundef);
  ((212%positive,0%Z),Tptr V293_tcb_type,SuccessOldHead present);
  ((213%positive,0%Z),Tint8,V293_byteval 1);
  ((214%positive,1%Z),Tint8,V293_byteval 129);
  ((215%positive,0%Z),Tint8,V293_byteval 254)] ++
 if present then [((301%positive,280%Z),Tcom_ptr 410%Z,Vundef)] else [].
Definition SuccessPreCells : list V293_record_cell :=
 ((211%positive,44%Z),Tptr V293_tcb_type,Vundef)::
 ((209%positive,0%Z),Tint32,Vundef)::
 (SuccessOld++SuccessInputs Vundef++
 [((210%positive,0%Z),Tptr V293_tcb_type,SuccessHead);
  ((301%positive,148%Z),Tcom_ptr 410%Z,SuccessNext)]).
Definition SuccessResidual : list V293_record_cell :=
 [((211%positive,44%Z),Tptr V293_tcb_type,SuccessHead);
  ((209%positive,0%Z),Tint32,Vint32 Int.zero);
  ((301%positive,128%Z),Tptr Tint32,Vnull);
  ((301%positive,178%Z),Tint8,V293_byteval 11);
  ((301%positive,176%Z),Tint8,Vint32 Int.zero);
  ((301%positive,177%Z),Tint8,Vint32 Int.zero);
  ((301%positive,172%Z),Tint32,Vint32 Int.zero);
  ((301%positive,132%Z),Tptr Tvoid,Vnull);
  ((301%positive,140%Z),Tint32,Vint32(Int.repr 128));
  ((301%positive,136%Z),Tptr Tint32,Vnull);
  ((301%positive,144%Z),Tint16,Vint32 Int.zero);
  ((301%positive,146%Z),Tint16,Vint32 Int.zero);
  ((301%positive,183%Z),Tint8,Vint32 Int.zero);
  ((301%positive,179%Z),Tint8,V293_byteval 3);
  ((301%positive,156%Z),Tcom_ptr 411%Z,Vnull);
  ((301%positive,164%Z),Tcom_ptr 412%Z,Vnull);
  ((301%positive,160%Z),Tptr Tvoid,Vnull)] ++ tl(SuccessInputs SuccessHead) ++
 [((210%positive,0%Z),Tptr V293_tcb_type,SuccessNext)].
Definition SuccessPublished (present:bool) : list V293_record_cell :=
 [((201%positive,0%Z),Tptr V293_tcb_type,SuccessHead);
  ((301%positive,148%Z),Tcom_ptr 410%Z,SuccessOldHead present);
  ((301%positive,152%Z),Tcom_ptr 410%Z,Vnull);
  ((301%positive,180%Z),Tint8,V293_byteval 1);
  ((301%positive,182%Z),Tint8,V293_byteval 2);
  ((301%positive,181%Z),Tint8,V293_byteval 8);
  ((212%positive,0%Z),Tptr V293_tcb_type,SuccessHead);
  ((213%positive,0%Z),Tint8,V293_byteval 3);
  ((214%positive,1%Z),Tint8,V293_byteval 137);
  ((215%positive,0%Z),Tint8,V293_byteval 255)] ++
 if present then [((301%positive,280%Z),Tcom_ptr 410%Z,SuccessHead)] else [].
Definition SuccessCells (initialized present:bool) :=
 if initialized then SuccessPublished present++SuccessResidual else SuccessPreCells++SuccessExtra present.
Definition SuccessWhole initialized present := merge(SuccessMemory(SuccessCells initialized present))(merge SuccessCurrent SuccessSentinel).
Definition SuccessState M cs : RstateOP :=
 (SuccessGE,SuccessLE,M,(fun _=>false),(false,[],cs),(emp:osabst),spec_done None).
Definition SuccessR := CurTid SuccessTid ** LINV V293_witness_li SuccessTid [] **
 Amapsto(601%positive,0%Z) Tint8 true(Vint32(Int.repr 77)).
Definition SuccessFieldBindings := V293_tcb_fields_bindings 108%Z 101%Z 102%Z 103%Z 104%Z 105%Z 106%Z 107%Z
 201%positive 202%positive 203%positive 204%positive 205%positive 206%positive 207%positive 208%positive.
Definition SuccessBindings := SuccessFieldBindings ** V293_tcb_success_extra 210%positive 209%positive.
Definition SuccessPubBindings := V293_pub_bindings 108%Z 93%Z 94%Z 95%Z 96%Z 201%positive 212%positive 213%positive 214%positive 215%positive.
Definition SuccessFrame cs := OS[(fun _=>false),false,[],cs] **
 (SuccessBindings ** (V293_tcb_table_binding 211%positive ** (SuccessPubBindings ** SuccessR))).
Definition SuccessLiteral initialized present cs := <||spec_done None||> ** V293_rdy_raw_cells(SuccessCells initialized present)(SuccessFrame cs).
Definition SuccessExtension present := V293_rdy_raw_cells(SuccessExtra present)(SuccessPubBindings ** SuccessR).
Definition SuccessPre present cs := <||spec_done None||> ** V293_rdy_raw_cells SuccessPreCells
 (OS[(fun _=>false),false,[],cs] ** (SuccessBindings ** (V293_tcb_table_binding 211%positive ** SuccessExtension present))).
Definition SuccessPost present cs : retasrt :=
 V293_link_return_post 211%positive 210%positive 209%positive 201%positive 202%positive 203%positive 204%positive
 205%positive 206%positive 207%positive 208%positive 301%positive 128%Z 11
 Vnull Vnull (Vint32 Int.zero) (Vint32(Int.repr 128)) Vnull (Vint32 Int.zero) SuccessNext
 212%positive 213%positive 214%positive 215%positive 301%positive 256%Z present 1 129 254 SuccessR
 (spec_done None)(fun _=>false)[]cs.
Lemma SuccessStar : forall m1 m2 m cs p q,
 join m1 m2 m -> SuccessState m1 cs |= p -> SuccessState m2 cs |= q ->
 SuccessState m cs |= p ** q.
Proof.
 intros. apply sat_split'. exists m1. exists m2.
 exists(emp:osabst). exists(emp:osabst).
 split;[exact H | ]. split;[apply map_join_emp | ]. split;assumption.
Qed.
Lemma SuccessCurrentSpatial : forall cs, SuccessState SuccessCurrent cs |= CurTid SuccessTid.
Proof.
 intro cs. exists Tvoid. exists 402%positive.
 eapply SuccessStar with (m1:=emp) (m2:=SuccessCurrent).
 - apply map_join_comm;apply map_join_emp.
 - exists 402%positive. split;[vm_compute;reflexivity | ]. repeat split;reflexivity.
 - split;[apply V293_encoded_memory_mapsto|reflexivity].
Qed.
Lemma SuccessLInvSpatial : forall cs, SuccessState emp cs |= LINV V293_witness_li SuccessTid [].
Proof.
 intro cs. unfold LINV. apply astar_comm. apply astar_l_apure_intro.
 - split;reflexivity.
 - apply V293_witness_li_good.
Qed.
Ltac SuccessFrameApart b :=
 apply map_join_merge;apply map_disjoint;intros [other offset];
 destruct(Pos.eq_dec other b);[subst other;right;left|left];
 unfold SuccessCurrent,SuccessSentinel,SuccessBytes;
 repeat first [rewrite map_merge_semp by reflexivity |
 rewrite V293_encoded_memory_outside by (left;congruence)];reflexivity.
Lemma SuccessRSpatial : forall cs,
 SuccessState (merge SuccessCurrent SuccessSentinel) cs |= SuccessR.
Proof.
 intro cs. unfold SuccessR.
 eapply SuccessStar with (m1:=SuccessCurrent) (m2:=SuccessSentinel).
 - SuccessFrameApart 402%positive.
 - apply SuccessCurrentSpatial.
 - eapply SuccessStar with (m1:=emp) (m2:=SuccessSentinel).
   + apply map_join_comm;apply map_join_emp.
   + apply SuccessLInvSpatial.
   + split;[apply V293_encoded_memory_mapsto|reflexivity].
Qed.
Lemma SuccessRGood : GoodFrm SuccessR.
Proof. cbn [SuccessR CurTid LINV V293_witness_li GoodFrm]. repeat split;exact I. Qed.
Lemma SuccessRCurLINV : SuccessR ==> CurLINV V293_witness_li SuccessTid.
Proof.
 intros s HS. unfold CurLINV. exists([]:list logicvar).
 unfold SuccessR in HS. clear -HS. sep auto.
Qed.
Lemma SuccessFieldBindingsSpatial : forall cs, SuccessState emp cs |= SuccessFieldBindings.
Proof.
 intro cs. unfold SuccessFieldBindings,V293_tcb_fields_bindings. repeat split.
 - exists 201%positive. split;[vm_compute;reflexivity | ]. repeat split;reflexivity.
 - exists 202%positive. split;[vm_compute;reflexivity | ]. repeat split;reflexivity.
 - exists 203%positive. split;[vm_compute;reflexivity | ]. repeat split;reflexivity.
 - exists 204%positive. split;[vm_compute;reflexivity | ]. repeat split;reflexivity.
 - exists 205%positive. split;[vm_compute;reflexivity | ]. repeat split;reflexivity.
 - exists 206%positive. split;[vm_compute;reflexivity | ]. repeat split;reflexivity.
 - exists 207%positive. split;[vm_compute;reflexivity | ]. repeat split;reflexivity.
 - exists 208%positive. split;[vm_compute;reflexivity | ]. repeat split;reflexivity.
Qed.
Lemma SuccessBindingsSpatial : forall cs, SuccessState emp cs |= SuccessBindings.
Proof.
 intro cs. unfold SuccessBindings. eapply SuccessStar with (m1:=emp) (m2:=emp).
 - apply map_join_emp.
 - apply SuccessFieldBindingsSpatial.
 - unfold V293_tcb_success_extra. repeat split.
   + exists 209%positive. split;[vm_compute;reflexivity| ]. repeat split;reflexivity.
   + exists 210%positive. split;[vm_compute;reflexivity| ]. repeat split;reflexivity.
   + intros [v H]. vm_compute in H. discriminate H.
Qed.
Ltac SuccessOutside :=
 repeat first [rewrite V293_encoded_memory_outside by
 (first [left;congruence | right;rewrite ?encode_val_length;cbn [V293_byteval length encode_val typelen list_repeat inj_pointer inj_bytes encode_int List.map];lia])
 |rewrite map_merge_semp by reflexivity];reflexivity.
Ltac SuccessApart b start count :=
 apply map_join_merge;apply map_disjoint;intros [other off];
 destruct (Pos.eq_dec other b) as [B|B];
 [subst other;destruct (Z_lt_dec off start) as [Low|Low];
 [left;apply V293_encoded_memory_outside;right;left;exact Low |
 destruct (Z_lt_dec off (start+count)) as [Inside|Outside];
 [right;left;SuccessOutside |left;apply V293_encoded_memory_outside;right;right;
 rewrite ?encode_val_length;cbn [V293_byteval length encode_val typelen list_repeat inj_pointer inj_bytes encode_int List.map];lia]] |
 left;apply V293_encoded_memory_outside;left;exact B].

Lemma SuccessTableSpatial : forall cs, SuccessState emp cs |= V293_tcb_table_binding 211%positive.
Proof.
 intro cs. unfold V293_tcb_table_binding. repeat split.
 - exists 211%positive. split;[vm_compute;reflexivity| ]. repeat split;reflexivity.
 - intros [v H]. vm_compute in H. discriminate H.
Qed.
Lemma SuccessPubBindingsSpatial : forall cs, SuccessState emp cs |= SuccessPubBindings.
Proof.
 intro cs. unfold SuccessPubBindings,V293_pub_bindings. repeat split.
 - exists 201%positive. split;[vm_compute;reflexivity| ]. repeat split;reflexivity.
 - intros [v H]. vm_compute in H. discriminate H.
 - exists 212%positive. split;[vm_compute;reflexivity| ]. repeat split;reflexivity.
 - intros [v H]. vm_compute in H. discriminate H.
 - exists 213%positive. split;[vm_compute;reflexivity| ]. repeat split;reflexivity.
 - intros [v H]. vm_compute in H. discriminate H.
 - exists 214%positive. split;[vm_compute;reflexivity| ]. repeat split;reflexivity.
 - intros [v H]. vm_compute in H. discriminate H.
 - exists 215%positive. split;[vm_compute;reflexivity| ]. repeat split;reflexivity.
Qed.

Ltac SuccessRawTactic :=
 lazymatch goal with
 | |- SuccessState (merge (V293_encoded_memory ?b ?off true (encode_val ?tp ?v)) ?tail) ?cs |= _ =>
   let bytes := eval cbv in (Z.of_nat(typelen tp)) in
   eapply SuccessStar with(m1:=V293_encoded_memory b off true(encode_val tp v));
   [SuccessApart b off bytes|split;[apply V293_encoded_memory_mapsto|reflexivity]|SuccessRawTactic]
 | |- SuccessState emp _ |= Aemp => split;reflexivity
 end.
Theorem SuccessRawLiteral : forall initialized present cs,
 SuccessState(SuccessMemory(SuccessCells initialized present))cs |= V293_rdy_raw_cells(SuccessCells initialized present)Aemp.
Proof.
 intros initialized present cs. destruct initialized,present;
 unfold SuccessCells,SuccessPublished,SuccessResidual,SuccessPreCells,SuccessExtra,SuccessOldHead,
 SuccessOld,SuccessInputs,SuccessHead,SuccessNext;
 cbn [app tl SuccessMemory V293_rdy_raw_cells];SuccessRawTactic.
Qed.
Theorem SuccessLiteralEntry : forall initialized present cs,
 SuccessState(SuccessWhole initialized present)cs |= SuccessLiteral initialized present cs.
Proof.
 intros initialized present cs. unfold SuccessLiteral.
 eapply SuccessStar with(m1:=emp)(m2:=SuccessWhole initialized present).
 - apply map_join_comm;apply map_join_emp.
 - split;[reflexivity| ]. split;reflexivity.
 - apply V293_raw_cells_join. unfold SuccessWhole.
   eapply SuccessStar with(m1:=SuccessMemory(SuccessCells initialized present))(m2:=merge SuccessCurrent SuccessSentinel).
   + apply map_join_merge;apply map_disjoint;intros[b off].
     destruct(Pos.eq_dec b 402%positive);[subst b;left| ].
     * destruct initialized,present;unfold SuccessCells,SuccessPublished,SuccessResidual,SuccessPreCells,SuccessExtra,SuccessOld,SuccessInputs;cbn[app tl SuccessMemory];SuccessOutside.
     * destruct(Pos.eq_dec b 601%positive);[subst b;left|right;left].
       -- destruct initialized,present;unfold SuccessCells,SuccessPublished,SuccessResidual,SuccessPreCells,SuccessExtra,SuccessOld,SuccessInputs;cbn[app tl SuccessMemory];SuccessOutside.
       -- unfold SuccessCurrent,SuccessSentinel,SuccessBytes. rewrite map_merge_semp by reflexivity.
          rewrite !V293_encoded_memory_outside by(left;congruence). reflexivity.
   + apply SuccessRawLiteral.
   + unfold SuccessFrame. eapply SuccessStar with(m1:=emp)(m2:=merge SuccessCurrent SuccessSentinel).
     * apply map_join_comm;apply map_join_emp.
     * repeat(eapply SuccessStar with(m1:=emp)(m2:=emp);
       [apply map_join_emp|split;[reflexivity|split;reflexivity]| ]).
       split;[reflexivity|split;reflexivity].
     * eapply SuccessStar with(m1:=emp)(m2:=merge SuccessCurrent SuccessSentinel).
       -- apply map_join_comm;apply map_join_emp.
       -- apply SuccessBindingsSpatial.
       -- eapply SuccessStar with(m1:=emp)(m2:=merge SuccessCurrent SuccessSentinel).
          ++ apply map_join_comm;apply map_join_emp.
          ++ apply SuccessTableSpatial.
          ++ eapply SuccessStar with(m1:=emp)(m2:=merge SuccessCurrent SuccessSentinel).
             ** apply map_join_comm;apply map_join_emp.
             ** apply SuccessPubBindingsSpatial.
             ** apply SuccessRSpatial.
Qed.
Theorem SuccessInitialView : forall present cs, SuccessLiteral false present cs ==> SuccessPre present cs.
Proof.
 intros present cs. unfold SuccessLiteral,SuccessPre,SuccessCells,SuccessFrame,SuccessExtension.
 apply astar_mono;[intros s H;exact H| ].
 rewrite V293_raw_cells_append. apply V293_raw_cells_mono. intros s HS.
 assert(H : s |= V293_rdy_raw_cells(SuccessExtra present)
 ((OS[(fun _=>false),false,[],cs] ** (SuccessBindings ** V293_tcb_table_binding 211%positive)) ** (SuccessPubBindings ** SuccessR))).
 { eapply V293_raw_cells_mono;[ |exact HS]. intros st Hst. clear -Hst. sep auto. }
 apply V293_raw_cells_move_frame in H. clear -H. sep auto.
Qed.
Theorem SuccessInitialEntry : forall present cs,
 SuccessState(SuccessWhole false present)cs |= SuccessPre present cs.
Proof. intros. apply SuccessInitialView. apply SuccessLiteralEntry. Qed.

Theorem SuccessPostView : forall present cs result s,
 (s |= SuccessPost present cs result) <->
 (s |= [|result=Some(Vint32 Int.zero)|] ** SuccessLiteral true present cs).
Proof.
 intros present cs result s. unfold SuccessPost,V293_link_return_post,V293_pub_return_post,
 V293_pub_hstate,V293_link_residual_frame.
 change ((s |= [|result=Some(Vint32 Int.zero)|] ** (<||spec_done None||> **
 V293_rdy_raw_cells(SuccessPublished present)
 (OS[(fun _=>false),false,[],cs] ** (SuccessPubBindings **
 V293_rdy_raw_cells SuccessResidual(SuccessBindings ** (V293_tcb_table_binding 211%positive ** SuccessR)))))) <->
 (s |= [|result=Some(Vint32 Int.zero)|] ** SuccessLiteral true present cs)).
 unfold SuccessLiteral,SuccessCells,SuccessFrame. rewrite V293_raw_cells_append.
 split;intro HS.
 - eapply astar_mono;[intros st H;exact H| |exact HS].
   apply astar_mono;[intros st H;exact H| ];apply V293_raw_cells_mono;intros st H.
   assert(K : st |= (OS[(fun _=>false),false,[],cs] ** SuccessPubBindings) **
   V293_rdy_raw_cells SuccessResidual(SuccessBindings ** (V293_tcb_table_binding 211%positive ** SuccessR))).
   { clear -H. sep auto. }
   apply V293_raw_cells_unmove_frame in K.
   eapply V293_raw_cells_mono;[ |exact K]. intros st1 H1. clear -H1. sep auto.
 - eapply astar_mono;[intros st H;exact H| |exact HS].
   apply astar_mono;[intros st H;exact H| ];apply V293_raw_cells_mono;intros st H.
   assert(K : st |= V293_rdy_raw_cells SuccessResidual
   ((OS[(fun _=>false),false,[],cs] ** SuccessPubBindings) ** (SuccessBindings ** (V293_tcb_table_binding 211%positive ** SuccessR)))).
   { eapply V293_raw_cells_mono;[ |exact H]. intros st1 H1. clear -H1. sep auto. }
   apply V293_raw_cells_move_frame in K. clear -K. sep auto.
Qed.
Theorem SuccessFinalEntry : forall present cs,
 SuccessState(SuccessWhole true present)cs |= SuccessPost present cs(Some(Vint32 Int.zero)).
Proof.
 intros. apply SuccessPostView. apply astar_l_apure_intro;[apply SuccessLiteralEntry|reflexivity].
Qed.

Lemma SuccessRFun : GoodFunAsrt SuccessR.
Proof.
 cbn [SuccessR CurTid LINV V293_witness_li Agvarmapsto Agvarenv' Aptrmapsto GoodFunAsrt].
 repeat split;exact I.
Qed.
Definition SuccessOwned slot present := V293_hook_owned_cells 211%positive slot 210%positive 301%positive 128%Z 11
 Vnull Vnull(Vint32 Int.zero)(Vint32(Int.repr 128))Vnull(Vint32 Int.zero) SuccessNext
 212%positive 213%positive 214%positive 215%positive 301%positive 256%Z present Vundef 1 129 254 Vundef.
Definition SuccessResource slot present cs := V293_hook_resource(SuccessOwned slot present) SuccessR
 (spec_done None)(fun _=>false)[]cs.
Definition SuccessResourceGood slot present cs := V293_hook_resource_good(SuccessOwned slot present)SuccessR
 (spec_done None)(fun _=>false)[]cs SuccessRFun.
Definition SuccessFpre slot present cs := V293_hook_fpre SuccessHead SuccessTid(SuccessResource slot present cs)(SuccessResourceGood slot present cs).
Definition SuccessFpost slot present cs := V293_hook_fpost SuccessHead SuccessTid(SuccessResource slot present cs)(SuccessResourceGood slot present cs).


Definition SuccessDeclaredSpec present cs : funspec := fun f =>
 if Z.eq_dec f 501%Z then Some(SuccessFpre Vundef present cs,SuccessFpost Vundef present cs,(Tvoid,[Tptr V293_tcb_type]))
 else if Z.eq_dec f 502%Z then Some(SuccessFpre SuccessHead present cs,SuccessFpost SuccessHead present cs,(Tvoid,[Tptr V293_tcb_type]))
 else None.
Theorem SuccessInitLookup : forall present cs,
 SuccessDeclaredSpec present cs 501%Z=Some(SuccessFpre Vundef present cs,SuccessFpost Vundef present cs,(Tvoid,[Tptr V293_tcb_type])).
Proof. intros. unfold SuccessDeclaredSpec. destruct(Z.eq_dec 501%Z 501%Z);[reflexivity|contradiction]. Qed.
Theorem SuccessCreateLookup : forall present cs,
 SuccessDeclaredSpec present cs 502%Z=Some(SuccessFpre SuccessHead present cs,SuccessFpost SuccessHead present cs,(Tvoid,[Tptr V293_tcb_type])).
Proof.
 intros. unfold SuccessDeclaredSpec. destruct(Z.eq_dec 502%Z 501%Z);[discriminate| ].
 destruct(Z.eq_dec 502%Z 502%Z);[reflexivity|contradiction].
Qed.

Lemma SuccessDomain : eq_dom_env SuccessLE (getlenvdom V293_tcb_internal_declarations).
Proof.
 unfold eq_dom_env. intros x tp.
 destruct (Z.eq_dec x 109%Z) as [E109|E109].
 { subst x. cbn [V293_tcb_internal_declarations V293_TCBInit_parameters V293_TCBInit_locals revlcons getlenvdom].
   unfold SuccessLE. repeat rewrite map_get_set' by congruence. rewrite map_get_set.
   split.
   + intro H. repeat destruct H as [H|H];try discriminate;try contradiction;
     inversion H;subst;eexists;reflexivity.
   + intros [b H]. inversion H;subst. cbn. tauto. }
 destruct (Z.eq_dec x 108%Z) as [E108|E108].
 { subst x. cbn [V293_tcb_internal_declarations V293_TCBInit_parameters V293_TCBInit_locals revlcons getlenvdom].
   unfold SuccessLE. repeat rewrite map_get_set' by congruence. rewrite map_get_set.
   split.
   + intro H. repeat destruct H as [H|H];try discriminate;try contradiction;
     inversion H;subst;eexists;reflexivity.
   + intros [b H]. inversion H;subst. cbn. tauto. }
 destruct (Z.eq_dec x 101%Z) as [E101|E101].
 { subst x. cbn [V293_tcb_internal_declarations V293_TCBInit_parameters V293_TCBInit_locals revlcons getlenvdom].
   unfold SuccessLE. repeat rewrite map_get_set' by congruence. rewrite map_get_set.
   split.
   + intro H. repeat destruct H as [H|H];try discriminate;try contradiction;
     inversion H;subst;eexists;reflexivity.
   + intros [b H]. inversion H;subst. cbn. tauto. }
 destruct (Z.eq_dec x 102%Z) as [E102|E102].
 { subst x. cbn [V293_tcb_internal_declarations V293_TCBInit_parameters V293_TCBInit_locals revlcons getlenvdom].
   unfold SuccessLE. repeat rewrite map_get_set' by congruence. rewrite map_get_set.
   split.
   + intro H. repeat destruct H as [H|H];try discriminate;try contradiction;
     inversion H;subst;eexists;reflexivity.
   + intros [b H]. inversion H;subst. cbn. tauto. }
 destruct (Z.eq_dec x 103%Z) as [E103|E103].
 { subst x. cbn [V293_tcb_internal_declarations V293_TCBInit_parameters V293_TCBInit_locals revlcons getlenvdom].
   unfold SuccessLE. repeat rewrite map_get_set' by congruence. rewrite map_get_set.
   split.
   + intro H. repeat destruct H as [H|H];try discriminate;try contradiction;
     inversion H;subst;eexists;reflexivity.
   + intros [b H]. inversion H;subst. cbn. tauto. }
 destruct (Z.eq_dec x 104%Z) as [E104|E104].
 { subst x. cbn [V293_tcb_internal_declarations V293_TCBInit_parameters V293_TCBInit_locals revlcons getlenvdom].
   unfold SuccessLE. repeat rewrite map_get_set' by congruence. rewrite map_get_set.
   split.
   + intro H. repeat destruct H as [H|H];try discriminate;try contradiction;
     inversion H;subst;eexists;reflexivity.
   + intros [b H]. inversion H;subst. cbn. tauto. }
 destruct (Z.eq_dec x 105%Z) as [E105|E105].
 { subst x. cbn [V293_tcb_internal_declarations V293_TCBInit_parameters V293_TCBInit_locals revlcons getlenvdom].
   unfold SuccessLE. repeat rewrite map_get_set' by congruence. rewrite map_get_set.
   split.
   + intro H. repeat destruct H as [H|H];try discriminate;try contradiction;
     inversion H;subst;eexists;reflexivity.
   + intros [b H]. inversion H;subst. cbn. tauto. }
 destruct (Z.eq_dec x 106%Z) as [E106|E106].
 { subst x. cbn [V293_tcb_internal_declarations V293_TCBInit_parameters V293_TCBInit_locals revlcons getlenvdom].
   unfold SuccessLE. repeat rewrite map_get_set' by congruence. rewrite map_get_set.
   split.
   + intro H. repeat destruct H as [H|H];try discriminate;try contradiction;
     inversion H;subst;eexists;reflexivity.
   + intros [b H]. inversion H;subst. cbn. tauto. }
 destruct (Z.eq_dec x 107%Z) as [E107|E107].
 { subst x. cbn [V293_tcb_internal_declarations V293_TCBInit_parameters V293_TCBInit_locals revlcons getlenvdom].
   unfold SuccessLE. repeat rewrite map_get_set' by congruence. rewrite map_get_set.
   split.
   + intro H. repeat destruct H as [H|H];try discriminate;try contradiction;
     inversion H;subst;eexists;reflexivity.
   + intros [b H]. inversion H;subst. cbn. tauto. }
 unfold SuccessLE. repeat rewrite map_get_set' by congruence. rewrite map_emp_get.
 cbn [V293_tcb_internal_declarations V293_TCBInit_parameters V293_TCBInit_locals revlcons getlenvdom].
 split.
 - intro H. repeat destruct H as [H|H];try contradiction;inversion H;congruence.
 - intros [b H]. discriminate.
Qed.

Definition SuccessArguments : vallist :=
 [Vint32(Int.repr 11); Vnull; Vnull; Vint32 Int.zero; Vint32(Int.repr 128); Vnull; Vint32 Int.zero].
Definition SuccessInternalFpre present cs := V293_tcb_success_fpre 211%positive Vundef 210%positive 301%positive 128%Z (fun _=>Vundef) 11 Vnull Vnull (Vint32 Int.zero) (Vint32(Int.repr 128)) Vnull (Vint32 Int.zero) SuccessNext 212%positive 213%positive 214%positive 215%positive 301%positive 256%Z present Vundef 1 129 254 Vundef SuccessR (spec_done None)(fun _=>false)[]cs SuccessRFun.
Definition SuccessInternalFpost present cs := V293_tcb_success_fpost 211%positive 210%positive 301%positive 128%Z 11 Vnull Vnull (Vint32 Int.zero) (Vint32(Int.repr 128)) Vnull (Vint32 Int.zero) SuccessNext 212%positive 213%positive 214%positive 215%positive 301%positive 256%Z present 1 129 254 SuccessR (spec_done None)(fun _=>false)[]cs SuccessRFun.
Definition SuccessProgram : progunit := fun f =>
 if Z.eq_dec f 900%Z then Some(V293_TCBInit_function 501%Z 502%Z) else None.
Definition SuccessBuilderPre present cs :=
 V293_tcb_internal_pre_cells (V293_byteval 11) Vnull Vnull (Vint32 Int.zero)
 (Vint32(Int.repr 128)) Vnull (Vint32 Int.zero) **
 getasrt(SuccessInternalFpre present cs SuccessArguments [] SuccessTid) ** V293_tcb_internal_domain.
Definition SuccessBuilderPost present cs : retasrt := fun result=>
 V293_tcb_internal_post_cells **
 getasrt(SuccessInternalFpost present cs SuccessArguments result [] SuccessTid) ** V293_tcb_internal_domain.
Theorem SuccessConstructorsNonvacuous : forall present cs,
 BuildPreI SuccessProgram 900%Z (rev SuccessArguments) [] (SuccessInternalFpre present cs) SuccessTid=
 Some(SuccessBuilderPre present cs) /\
 BuildRetI SuccessProgram 900%Z (rev SuccessArguments) [] (SuccessInternalFpost present cs) SuccessTid=
 Some(SuccessBuilderPost present cs).
Proof. intros. split;reflexivity. Qed.
Theorem SuccessGoodIInhabited : GoodI V293_shared_inv V293_scheduler V293_witness_li.
Proof. exact V293_shared_good. Qed.

Definition SuccessLocals pc cpu := V293_tcb_success_local_cells
 209%positive 201%positive 202%positive 203%positive 204%positive 205%positive 206%positive 207%positive 208%positive
 11 Vnull Vnull (Vint32 Int.zero) (Vint32(Int.repr 128)) Vnull (Vint32 Int.zero) pc cpu.
Definition SuccessLocalBindings := V293_tcb_success_local_bindings
 209%positive 201%positive 202%positive 203%positive 204%positive 205%positive 206%positive 207%positive 208%positive.
Definition SuccessGlobals := V293_tcb_success_global_bindings
 211%positive 210%positive 212%positive 213%positive 214%positive 215%positive.
Definition SuccessExternalCells present := V293_tcb_success_pre_owned
 211%positive Vundef 210%positive 301%positive 128%Z (fun _=>Vundef) SuccessNext
 212%positive 213%positive 214%positive 215%positive 301%positive 256%Z present 11 Vundef 1 129 254 Vundef.
Lemma SuccessEntryPartition : forall present,
 Permutation(SuccessCells false present)(SuccessLocals Vundef Vundef ++ SuccessExternalCells present).
Proof.
 intros present. destruct present;
 unfold SuccessCells,SuccessLocals,SuccessExternalCells,SuccessPreCells,SuccessExtra,SuccessOld,SuccessInputs,
 SuccessOldHead,SuccessHead,V293_tcb_success_local_cells,V293_tcb_success_pre_owned,V293_tcb_init_old_fields,
 V293_tcb_prefix_links,V293_link_extra,SuccessNext;cbn [app tl];vm_compute;V293_link_permute.
Qed.
Lemma SuccessLiteralBuilderResources : forall present cs,
 SuccessLiteral false present cs ==>
 V293_tcb_internal_pre_cells (V293_byteval 11) Vnull Vnull (Vint32 Int.zero)
 (Vint32(Int.repr 128)) Vnull (Vint32 Int.zero) **
 V293_tcb_success_external 211%positive 210%positive 212%positive 213%positive 214%positive 215%positive
 (SuccessExternalCells present) SuccessR (spec_done None)(fun _=>false)[]cs.
Proof.
 intros present cs s H. unfold SuccessLiteral,SuccessFrame in H.
 eapply astar_mono in H;[ |intros st HS;exact HS| ].
 2: { apply V293_link_cells_permutation. apply SuccessEntryPartition. }
 assert(K:s |= <||spec_done None||> ** V293_rdy_raw_cells
 (SuccessLocals Vundef Vundef ++ SuccessExternalCells present)
 (SuccessLocalBindings ** (OS[(fun _=>false),false,[],cs] ** (SuccessGlobals ** SuccessR)))).
 { eapply astar_mono;[intros st HS;exact HS| |exact H]. apply V293_raw_cells_mono.
   intros st HS.
   assert(B:st |= V293_hook_bindings 211%positive 210%positive 209%positive 201%positive
    202%positive 203%positive 204%positive 205%positive 206%positive 207%positive 208%positive
    212%positive 213%positive 214%positive 215%positive ** (OS[(fun _=>false),false,[],cs] ** SuccessR)).
   { unfold V293_hook_bindings,SuccessBindings,SuccessFieldBindings,SuccessPubBindings in *. clear -HS. sep auto. }
   eapply astar_mono in B;[ |apply V293_tcb_success_return_bindings|intros st1 H1;exact H1].
   unfold SuccessLocalBindings,SuccessGlobals. clear -B. sep auto. }
 assert(Factored:s |= <||spec_done None||> **
 (V293_rdy_raw_cells(SuccessLocals Vundef Vundef)SuccessLocalBindings **
 V293_rdy_raw_cells(SuccessExternalCells present)(OS[(fun _=>false),false,[],cs] ** (SuccessGlobals ** SuccessR)))).
 { eapply astar_mono;[intros st HS;exact HS| |exact K]. intros st HS.
   apply V293_hook_cells_factor. exact HS. }
 eapply astar_mono in Factored;[ |intros st HS;exact HS| ].
 2: { apply astar_mono;[ |intros st HS;exact HS]. unfold SuccessLocals,SuccessLocalBindings.
      apply V293_tcb_success_internal_prepack. }
 unfold V293_tcb_success_external,V293_hook_resource,SuccessGlobals.
 clear -Factored. sep auto.
Qed.
Theorem SuccessLiteralBuilderEntry : forall present cs,
 SuccessState(SuccessWhole false present)cs |= SuccessBuilderPre present cs.
Proof.
 intros present cs. unfold SuccessBuilderPre.
 change (SuccessState(SuccessWhole false present)cs |=
 V293_tcb_internal_pre_cells (V293_byteval 11) Vnull Vnull (Vint32 Int.zero)
 (Vint32(Int.repr 128)) Vnull (Vint32 Int.zero) **
 ([|SuccessArguments=V293_tcb_success_arguments 11 Vnull Vnull (Vint32 Int.zero)
 (Vint32(Int.repr 128)) Vnull (Vint32 Int.zero)|] **
 V293_tcb_success_external 211%positive 210%positive 212%positive 213%positive 214%positive 215%positive
 (SuccessExternalCells present) SuccessR (spec_done None)(fun _=>false)[]cs) ** V293_tcb_internal_domain).
 assert(H:SuccessState(SuccessWhole false present)cs |=
 (V293_tcb_internal_pre_cells (V293_byteval 11) Vnull Vnull (Vint32 Int.zero)
 (Vint32(Int.repr 128)) Vnull (Vint32 Int.zero) **
 V293_tcb_success_external 211%positive 210%positive 212%positive 213%positive 214%positive 215%positive
 (SuccessExternalCells present) SuccessR (spec_done None)(fun _=>false)[]cs) ** V293_tcb_internal_domain).
 { apply astar_comm. unfold V293_tcb_internal_domain. apply astar_l_adomlenv_intro.
   - apply SuccessLiteralBuilderResources. apply SuccessLiteralEntry.
   - exact SuccessDomain. }
 assert(E:SuccessArguments=V293_tcb_success_arguments 11 Vnull Vnull (Vint32 Int.zero)
 (Vint32(Int.repr 128)) Vnull (Vint32 Int.zero)) by reflexivity.
 clear -H E. sep auto.
Qed.


(* Concrete, inhabited GoodI and finite two-entry Hook specification table. *)
Theorem SuccessContractChecked : forall present cs,
 InfRules (SuccessDeclaredSpec present cs) V293_scheduler V293_witness_li V293_shared_inv
 (SuccessBuilderPost present cs) Afalse (SuccessBuilderPre present cs)
 (V293_TCBInit_function_body 501%Z 502%Z) Afalse SuccessTid.
Proof.
 intros present cs.
 eapply V293_OS_TCBInit_success_internal_contract
 with (P:=SuccessProgram) (f:=900%Z) (vl:=rev SuccessArguments) (lg:=[])
 (Hfun:=SuccessRFun) (old:=fun _=>Vundef) (oldprev:=Vundef) (oldback:=Vundef)
 (slot:=Vundef) (table:=211%positive) (bg:=210%positive) (bt:=301%positive)
 (base:=128%Z) (p:=11) (top:=Vnull) (bottom:=Vnull) (identity:=Vint32 Int.zero)
 (size:=Vint32(Int.repr 128)) (ext:=Vnull) (options:=Vint32 Int.zero) (next:=SuccessNext)
 (bh:=212%positive) (bgrp:=213%positive) (br:=214%positive) (bn:=215%positive)
 (oldblock:=301%positive) (oldbase:=256%Z) (present:=present) (g:=1) (row:=129) (n:=254)
 (aop:=spec_done None) (isr:=fun _=>false) (is:=[]) (cs:=cs).
 - apply SuccessGoodIInhabited.
 - lia.
 - lia.
 - unfold Int.max_unsigned,Int.modulus,Int.wordsize;cbn;lia.
 - lia.
 - unfold Int.max_unsigned,Int.modulus,Int.wordsize;cbn;lia.
 - repeat split;reflexivity.
 - reflexivity.
 - lia.
 - lia.
 - lia.
 - apply SuccessRGood.
 - apply SuccessRCurLINV.
 - apply SuccessInitLookup.
 - apply SuccessCreateLookup.
 - reflexivity.
 - symmetry;apply (proj1(SuccessConstructorsNonvacuous present cs)).
 - symmetry;apply (proj2(SuccessConstructorsNonvacuous present cs)).
Qed.
Theorem SuccessLiteralBuilderReturn : forall present cs,
 SuccessState(SuccessWhole true present)cs |= SuccessBuilderPost present cs(Some(Vint32 Int.zero)).
Proof.
 intros present cs. unfold SuccessBuilderPost.
 change (SuccessState(SuccessWhole true present)cs |=
 V293_tcb_internal_post_cells ** ([|Some(Vint32 Int.zero)=Some(Vint32 Int.zero)|] **
 V293_tcb_success_external 211%positive 210%positive 212%positive 213%positive 214%positive 215%positive
 (V293_tcb_success_post_owned 211%positive 210%positive 301%positive 128%Z 11
 Vnull Vnull (Vint32 Int.zero) (Vint32(Int.repr 128)) Vnull (Vint32 Int.zero) SuccessNext
 212%positive 213%positive 214%positive 215%positive 301%positive 256%Z present 1 129 254)
 SuccessR (spec_done None)(fun _=>false)[]cs) ** V293_tcb_internal_domain).
 apply astar_assoc_elim. apply astar_comm. unfold V293_tcb_internal_domain. apply astar_l_adomlenv_intro.
 - eapply V293_tcb_success_internal_exit. apply SuccessFinalEntry.
 - apply SuccessDomain.
Qed.
Lemma SuccessBuilderPostCode : forall s present cs result,
 s |= SuccessBuilderPost present cs result -> result=Some(Vint32 Int.zero).
Proof.
 intros s present cs result H. unfold SuccessBuilderPost,SuccessInternalFpost,V293_tcb_success_fpost in H.
 cbn [getasrt] in H. sep normal in H. sep destruct H. sep auto.
Qed.
Theorem SuccessBuilderReject66 : forall s present cs,
 ~s |= SuccessBuilderPost present cs (Some(Vint32(Int.repr 66))).
Proof. intros s present cs H. pose proof(SuccessBuilderPostCode _ _ _ _ H). discriminate. Qed.
Theorem SuccessBuilderRejectNone : forall s present cs,
 ~s |= SuccessBuilderPost present cs None.
Proof. intros s present cs H. pose proof(SuccessBuilderPostCode _ _ _ _ H). discriminate. Qed.
Theorem SuccessEmptyArgumentsRejected : forall present cs,
 BuildPreI SuccessProgram 900%Z [] [] (SuccessInternalFpre present cs) SuccessTid=None.
Proof. reflexivity. Qed.
Definition SuccessFinalExternalCells present := V293_tcb_success_post_owned
 211%positive 210%positive 301%positive 128%Z 11
 Vnull Vnull (Vint32 Int.zero) (Vint32(Int.repr 128)) Vnull (Vint32 Int.zero) SuccessNext
 212%positive 213%positive 214%positive 215%positive 301%positive 256%Z present 1 129 254.
Theorem SuccessBuilderPostLoad : forall present cs result s a tp v,
 s |= SuccessBuilderPost present cs result -> In(a,tp,v)(SuccessFinalExternalCells present) ->
 rule_type_val_match tp v=true -> load tp(getmem s)a=Some v.
Proof.
 intros present cs result s a tp v HS Member Valid.
 unfold SuccessBuilderPost,SuccessInternalFpost,V293_tcb_success_fpost in HS.
 cbn [getasrt] in HS.
 eapply V293_star_load_r;[ |exact HS]. intros st H.
 eapply V293_star_load_l;[ |exact H]. intros st1 H1.
 eapply V293_star_load_r;[ |exact H1]. intros st2 H2.
 unfold V293_tcb_success_external,V293_hook_resource in H2.
 eapply V293_star_load_r;[ |exact H2]. intros st3 H3.
 eapply V293_rdy_raw_load;[exact Member|exact Valid|exact H3].
Qed.
Theorem SuccessBuilderFreeHeadRead : forall present cs result s,
 s |= SuccessBuilderPost present cs result ->
 load (Tptr V293_tcb_type)(getmem s)(210%positive,0%Z)=Some SuccessNext.
Proof.
 intros present cs result s HS. eapply SuccessBuilderPostLoad;[exact HS| |reflexivity].
 destruct present;unfold SuccessFinalExternalCells,V293_tcb_success_post_owned,
 V293_pub_cells;cbn [app tl];simpl;tauto.
Qed.
Theorem SuccessBuilderCounterRead : forall present cs result s,
 s |= SuccessBuilderPost present cs result ->
 load Tint8(getmem s)(215%positive,0%Z)=Some(V293_byteval 255).
Proof.
 intros present cs result s HS. eapply SuccessBuilderPostLoad;[exact HS| |reflexivity].
 destruct present;unfold SuccessFinalExternalCells,V293_tcb_success_post_owned,
 V293_pub_cells;cbn [app tl];simpl;tauto.
Qed.
Theorem SuccessBuilderOldBacklinkRead : forall cs result s,
 s |= SuccessBuilderPost true cs result ->
 load(Tcom_ptr 410%Z)(getmem s)(301%positive,280%Z)=Some SuccessHead.
Proof.
 intros cs result s HS. eapply SuccessBuilderPostLoad;[exact HS| |reflexivity].
 unfold SuccessFinalExternalCells,V293_tcb_success_post_owned,V293_pub_cells,SuccessHead;
 cbn [app tl];simpl;tauto.
Qed.

(* The argument check rejects a typed but different priority, not just []. *)
Theorem SuccessWrongPriorityRejected : forall s present cs,
 ~s |= getasrt(SuccessInternalFpre present cs
 [V293_byteval 12;Vnull;Vnull;Vint32 Int.zero;Vint32(Int.repr 128);Vnull;Vint32 Int.zero]
 [] SuccessTid).
Proof.
 intros s present cs H. unfold SuccessInternalFpre,V293_tcb_success_fpre in H.
 cbn [getasrt] in H. apply astar_l_apure_elim in H. destruct H as [Args _].
 unfold V293_tcb_success_arguments,V293_byteval in Args. vm_compute in Args. discriminate.
Qed.
Theorem SuccessBuilderSentinelRead : forall present cs result s,
 s |= SuccessBuilderPost present cs result ->
 load Tint8(getmem s)(601%positive,0%Z)=Some(Vint32(Int.repr 77)).
Proof.
 intros present cs result s HS.
 unfold SuccessBuilderPost,SuccessInternalFpost,V293_tcb_success_fpost in HS.
 cbn [getasrt] in HS.
 eapply V293_star_load_r;[ |exact HS]. intros st H.
 eapply V293_star_load_l;[ |exact H]. intros st1 H1.
 eapply V293_star_load_r;[ |exact H1]. intros st2 H2.
 unfold V293_tcb_success_external,V293_hook_resource in H2.
 eapply V293_star_load_r;[ |exact H2]. intros st3 H3.
 apply V293_raw_cells_separate in H3.
 eapply V293_star_load_r;[ |exact H3]. intros st4 H4.
 assert(S:st4 |= Amapsto(601%positive,0%Z) Tint8 true(Vint32(Int.repr 77)) ** Atrue).
 { unfold SuccessR in H4. clear -H4. sep auto. }
 eapply V293_star_load_l;[ |exact S]. intros st5 H5.
 destruct H5 as [Points Empty].
 eapply CertiOS.tactics.hoareforward.symbolic_lemmas.mapstoval_load;[reflexivity|exact Points].
Qed.
