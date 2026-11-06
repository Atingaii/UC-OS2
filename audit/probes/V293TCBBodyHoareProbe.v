(* Independent literal fixtures copied with local names, not imported from old probes. *)
Require Import CertiOS.certiucos.v293.proofs.V293TCBBodyHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TCBEmptyHoare.
(* Independent literal resources and actual Body call-site entries; no old probe imports. *)
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
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.
Definition BodyOld : list V293_record_cell :=
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
Definition BodyInputs pc : list V293_record_cell :=
 [((201%positive,0%Z),(Tptr V293_tcb_type),(pc));
  ((202%positive,0%Z),(Tint8),(V293_byteval 11));
  ((203%positive,0%Z),(Tptr Tint32),(Vnull));
  ((204%positive,0%Z),(Tptr Tint32),(Vnull));
  ((205%positive,0%Z),(Tint16),(Vint32 Int.zero));
  ((206%positive,0%Z),(Tint32),(Vint32(Int.repr 128)));
  ((207%positive,0%Z),(Tptr Tvoid),(Vnull));
  ((208%positive,0%Z),(Tint16),(Vint32 Int.zero))].
Definition BodyFinal : list V293_record_cell :=
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
Definition BodyGE : env := set (set (set (set (set (set (sig OSTCBCur (402%positive,Tptr Tvoid))
 91%Z (210%positive,Tptr V293_tcb_type)) 92%Z (211%positive,Tarray (Tptr V293_tcb_type) 13))
 93%Z (212%positive,Tptr V293_tcb_type)) 94%Z (213%positive,Tint8))
 95%Z (214%positive,Tarray Tint8 2)) 96%Z (215%positive,Tint8).
Definition BodyLE : env :=
 set (set (set (set (set (set (set (set (set (emp:env)
 108%Z (201%positive,Tptr V293_tcb_type)) 101%Z (202%positive,Tint8))
 102%Z (203%positive,Tptr Tint32)) 103%Z (204%positive,Tptr Tint32))
 104%Z (205%positive,Tint16)) 105%Z (206%positive,Tint32))
 106%Z (207%positive,Tptr Tvoid)) 107%Z (208%positive,Tint16)) 109%Z (209%positive,Tint32).
Definition BodyTid : tid := (301%positive,Int.repr 8).
Definition BodyBytes b permission tp v := V293_encoded_memory b 0 permission (encode_val tp v).
Definition BodyCurrent := BodyBytes 402%positive false (Tptr Tvoid) (Vptr BodyTid).
Definition BodySentinel := BodyBytes 601%positive true Tint8 (Vint32(Int.repr 77)).
Fixpoint BodyMemory (cells : list V293_record_cell) : mem :=
 match cells with []=>emp | ((b,i),tp,v)::tail=>
 merge (V293_encoded_memory b i true (encode_val tp v)) (BodyMemory tail) end.
Definition BodyHead := Vptr(301%positive,Int.repr 128).
Definition BodyNext := Vptr(301%positive,Int.repr 384).
Definition BodyOldHead (present:bool) := if present then Vptr(301%positive,Int.repr 256) else Vnull.
Definition BodyExtra (present:bool) : list V293_record_cell :=
 [((301%positive,152%Z),Tcom_ptr 410%Z,Vundef);
  ((212%positive,0%Z),Tptr V293_tcb_type,BodyOldHead present);
  ((213%positive,0%Z),Tint8,V293_byteval 1);
  ((214%positive,1%Z),Tint8,V293_byteval 129);
  ((215%positive,0%Z),Tint8,V293_byteval 254)] ++
 if present then [((301%positive,280%Z),Tcom_ptr 410%Z,Vundef)] else [].
Definition BodyPreCells : list V293_record_cell :=
 ((211%positive,44%Z),Tptr V293_tcb_type,Vundef)::
 ((209%positive,0%Z),Tint32,Vundef)::
 (BodyOld++BodyInputs Vundef++
 [((210%positive,0%Z),Tptr V293_tcb_type,BodyHead);
  ((301%positive,148%Z),Tcom_ptr 410%Z,BodyNext)]).
Definition BodyResidual : list V293_record_cell :=
 [((211%positive,44%Z),Tptr V293_tcb_type,BodyHead);
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
  ((301%positive,160%Z),Tptr Tvoid,Vnull)] ++ tl(BodyInputs BodyHead) ++
 [((210%positive,0%Z),Tptr V293_tcb_type,BodyNext)].
Definition BodyPublished (present:bool) : list V293_record_cell :=
 [((201%positive,0%Z),Tptr V293_tcb_type,BodyHead);
  ((301%positive,148%Z),Tcom_ptr 410%Z,BodyOldHead present);
  ((301%positive,152%Z),Tcom_ptr 410%Z,Vnull);
  ((301%positive,180%Z),Tint8,V293_byteval 1);
  ((301%positive,182%Z),Tint8,V293_byteval 2);
  ((301%positive,181%Z),Tint8,V293_byteval 8);
  ((212%positive,0%Z),Tptr V293_tcb_type,BodyHead);
  ((213%positive,0%Z),Tint8,V293_byteval 3);
  ((214%positive,1%Z),Tint8,V293_byteval 137);
  ((215%positive,0%Z),Tint8,V293_byteval 255)] ++
 if present then [((301%positive,280%Z),Tcom_ptr 410%Z,BodyHead)] else [].
Definition BodyCells (initialized present:bool) :=
 if initialized then BodyPublished present++BodyResidual else BodyPreCells++BodyExtra present.
Definition BodyWhole initialized present := merge(BodyMemory(BodyCells initialized present))(merge BodyCurrent BodySentinel).
Definition BodyState M cs : RstateOP :=
 (BodyGE,BodyLE,M,(fun _=>false),(false,[],cs),(emp:osabst),spec_done None).
Definition BodyR := CurTid BodyTid ** LINV V293_witness_li BodyTid [] **
 Amapsto(601%positive,0%Z) Tint8 true(Vint32(Int.repr 77)).
Definition BodyFieldBindings := V293_tcb_fields_bindings 108%Z 101%Z 102%Z 103%Z 104%Z 105%Z 106%Z 107%Z
 201%positive 202%positive 203%positive 204%positive 205%positive 206%positive 207%positive 208%positive.
Definition BodyBindings := BodyFieldBindings ** V293_tcb_success_extra 210%positive 209%positive.
Definition BodyPubBindings := V293_pub_bindings 108%Z 93%Z 94%Z 95%Z 96%Z 201%positive 212%positive 213%positive 214%positive 215%positive.
Definition BodyFrame cs := OS[(fun _=>false),false,[],cs] **
 (BodyBindings ** (V293_tcb_table_binding 211%positive ** (BodyPubBindings ** BodyR))).
Definition BodyLiteral initialized present cs := <||spec_done None||> ** V293_rdy_raw_cells(BodyCells initialized present)(BodyFrame cs).
Definition BodyExtension present := V293_rdy_raw_cells(BodyExtra present)(BodyPubBindings ** BodyR).
Definition BodyPre present cs := <||spec_done None||> ** V293_rdy_raw_cells BodyPreCells
 (OS[(fun _=>false),false,[],cs] ** (BodyBindings ** (V293_tcb_table_binding 211%positive ** BodyExtension present))).
Definition BodyPost present cs : retasrt :=
 V293_link_return_post 211%positive 210%positive 209%positive 201%positive 202%positive 203%positive 204%positive
 205%positive 206%positive 207%positive 208%positive 301%positive 128%Z 11
 Vnull Vnull (Vint32 Int.zero) (Vint32(Int.repr 128)) Vnull (Vint32 Int.zero) BodyNext
 212%positive 213%positive 214%positive 215%positive 301%positive 256%Z present 1 129 254 BodyR
 (spec_done None)(fun _=>false)[]cs.
Lemma BodyStar : forall m1 m2 m cs p q,
 join m1 m2 m -> BodyState m1 cs |= p -> BodyState m2 cs |= q ->
 BodyState m cs |= p ** q.
Proof.
 intros. apply sat_split'. exists m1. exists m2.
 exists(emp:osabst). exists(emp:osabst).
 split;[exact H | ]. split;[apply map_join_emp | ]. split;assumption.
Qed.
Lemma BodyCurrentSpatial : forall cs, BodyState BodyCurrent cs |= CurTid BodyTid.
Proof.
 intro cs. exists Tvoid. exists 402%positive.
 eapply BodyStar with (m1:=emp) (m2:=BodyCurrent).
 - apply map_join_comm;apply map_join_emp.
 - exists 402%positive. split;[vm_compute;reflexivity | ]. repeat split;reflexivity.
 - split;[apply V293_encoded_memory_mapsto|reflexivity].
Qed.
Lemma BodyLInvSpatial : forall cs, BodyState emp cs |= LINV V293_witness_li BodyTid [].
Proof.
 intro cs. unfold LINV. apply astar_comm. apply astar_l_apure_intro.
 - split;reflexivity.
 - apply V293_witness_li_good.
Qed.
Ltac BodyFrameApart b :=
 apply map_join_merge;apply map_disjoint;intros [other offset];
 destruct(Pos.eq_dec other b);[subst other;right;left|left];
 unfold BodyCurrent,BodySentinel,BodyBytes;
 repeat first [rewrite map_merge_semp by reflexivity |
 rewrite V293_encoded_memory_outside by (left;congruence)];reflexivity.
Lemma BodyRSpatial : forall cs,
 BodyState (merge BodyCurrent BodySentinel) cs |= BodyR.
Proof.
 intro cs. unfold BodyR.
 eapply BodyStar with (m1:=BodyCurrent) (m2:=BodySentinel).
 - BodyFrameApart 402%positive.
 - apply BodyCurrentSpatial.
 - eapply BodyStar with (m1:=emp) (m2:=BodySentinel).
   + apply map_join_comm;apply map_join_emp.
   + apply BodyLInvSpatial.
   + split;[apply V293_encoded_memory_mapsto|reflexivity].
Qed.
Lemma BodyRGood : GoodFrm BodyR.
Proof. cbn [BodyR CurTid LINV V293_witness_li GoodFrm]. repeat split;exact I. Qed.
Lemma BodyRCurLINV : BodyR ==> CurLINV V293_witness_li BodyTid.
Proof.
 intros s HS. unfold CurLINV. exists([]:list logicvar).
 unfold BodyR in HS. clear -HS. sep auto.
Qed.
Lemma BodyFieldBindingsSpatial : forall cs, BodyState emp cs |= BodyFieldBindings.
Proof.
 intro cs. unfold BodyFieldBindings,V293_tcb_fields_bindings. repeat split.
 - exists 201%positive. split;[vm_compute;reflexivity | ]. repeat split;reflexivity.
 - exists 202%positive. split;[vm_compute;reflexivity | ]. repeat split;reflexivity.
 - exists 203%positive. split;[vm_compute;reflexivity | ]. repeat split;reflexivity.
 - exists 204%positive. split;[vm_compute;reflexivity | ]. repeat split;reflexivity.
 - exists 205%positive. split;[vm_compute;reflexivity | ]. repeat split;reflexivity.
 - exists 206%positive. split;[vm_compute;reflexivity | ]. repeat split;reflexivity.
 - exists 207%positive. split;[vm_compute;reflexivity | ]. repeat split;reflexivity.
 - exists 208%positive. split;[vm_compute;reflexivity | ]. repeat split;reflexivity.
Qed.
Lemma BodyBindingsSpatial : forall cs, BodyState emp cs |= BodyBindings.
Proof.
 intro cs. unfold BodyBindings. eapply BodyStar with (m1:=emp) (m2:=emp).
 - apply map_join_emp.
 - apply BodyFieldBindingsSpatial.
 - unfold V293_tcb_success_extra. repeat split.
   + exists 209%positive. split;[vm_compute;reflexivity| ]. repeat split;reflexivity.
   + exists 210%positive. split;[vm_compute;reflexivity| ]. repeat split;reflexivity.
   + intros [v H]. vm_compute in H. discriminate H.
Qed.
Ltac BodyOutside :=
 repeat first [rewrite V293_encoded_memory_outside by
 (first [left;congruence | right;rewrite ?encode_val_length;cbn [V293_byteval length encode_val typelen list_repeat inj_pointer inj_bytes encode_int List.map];lia])
 |rewrite map_merge_semp by reflexivity];reflexivity.
Ltac BodyApart b start count :=
 apply map_join_merge;apply map_disjoint;intros [other off];
 destruct (Pos.eq_dec other b) as [B|B];
 [subst other;destruct (Z_lt_dec off start) as [Low|Low];
 [left;apply V293_encoded_memory_outside;right;left;exact Low |
 destruct (Z_lt_dec off (start+count)) as [Inside|Outside];
 [right;left;BodyOutside |left;apply V293_encoded_memory_outside;right;right;
 rewrite ?encode_val_length;cbn [V293_byteval length encode_val typelen list_repeat inj_pointer inj_bytes encode_int List.map];lia]] |
 left;apply V293_encoded_memory_outside;left;exact B].

Lemma BodyTableSpatial : forall cs, BodyState emp cs |= V293_tcb_table_binding 211%positive.
Proof.
 intro cs. unfold V293_tcb_table_binding. repeat split.
 - exists 211%positive. split;[vm_compute;reflexivity| ]. repeat split;reflexivity.
 - intros [v H]. vm_compute in H. discriminate H.
Qed.
Lemma BodyPubBindingsSpatial : forall cs, BodyState emp cs |= BodyPubBindings.
Proof.
 intro cs. unfold BodyPubBindings,V293_pub_bindings. repeat split.
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

Ltac BodyRawTactic :=
 lazymatch goal with
 | |- BodyState (merge (V293_encoded_memory ?b ?off true (encode_val ?tp ?v)) ?tail) ?cs |= _ =>
   let bytes := eval cbv in (Z.of_nat(typelen tp)) in
   eapply BodyStar with(m1:=V293_encoded_memory b off true(encode_val tp v));
   [BodyApart b off bytes|split;[apply V293_encoded_memory_mapsto|reflexivity]|BodyRawTactic]
 | |- BodyState emp _ |= Aemp => split;reflexivity
 end.
Theorem BodyRawLiteral : forall initialized present cs,
 BodyState(BodyMemory(BodyCells initialized present))cs |= V293_rdy_raw_cells(BodyCells initialized present)Aemp.
Proof.
 intros initialized present cs. destruct initialized,present;
 unfold BodyCells,BodyPublished,BodyResidual,BodyPreCells,BodyExtra,BodyOldHead,
 BodyOld,BodyInputs,BodyHead,BodyNext;
 cbn [app tl BodyMemory V293_rdy_raw_cells];BodyRawTactic.
Qed.
Theorem BodyLiteralEntry : forall initialized present cs,
 BodyState(BodyWhole initialized present)cs |= BodyLiteral initialized present cs.
Proof.
 intros initialized present cs. unfold BodyLiteral.
 eapply BodyStar with(m1:=emp)(m2:=BodyWhole initialized present).
 - apply map_join_comm;apply map_join_emp.
 - split;[reflexivity| ]. split;reflexivity.
 - apply V293_raw_cells_join. unfold BodyWhole.
   eapply BodyStar with(m1:=BodyMemory(BodyCells initialized present))(m2:=merge BodyCurrent BodySentinel).
   + apply map_join_merge;apply map_disjoint;intros[b off].
     destruct(Pos.eq_dec b 402%positive);[subst b;left| ].
     * destruct initialized,present;unfold BodyCells,BodyPublished,BodyResidual,BodyPreCells,BodyExtra,BodyOld,BodyInputs;cbn[app tl BodyMemory];BodyOutside.
     * destruct(Pos.eq_dec b 601%positive);[subst b;left|right;left].
       -- destruct initialized,present;unfold BodyCells,BodyPublished,BodyResidual,BodyPreCells,BodyExtra,BodyOld,BodyInputs;cbn[app tl BodyMemory];BodyOutside.
       -- unfold BodyCurrent,BodySentinel,BodyBytes. rewrite map_merge_semp by reflexivity.
          rewrite !V293_encoded_memory_outside by(left;congruence). reflexivity.
   + apply BodyRawLiteral.
   + unfold BodyFrame. eapply BodyStar with(m1:=emp)(m2:=merge BodyCurrent BodySentinel).
     * apply map_join_comm;apply map_join_emp.
     * repeat(eapply BodyStar with(m1:=emp)(m2:=emp);
       [apply map_join_emp|split;[reflexivity|split;reflexivity]| ]).
       split;[reflexivity|split;reflexivity].
     * eapply BodyStar with(m1:=emp)(m2:=merge BodyCurrent BodySentinel).
       -- apply map_join_comm;apply map_join_emp.
       -- apply BodyBindingsSpatial.
       -- eapply BodyStar with(m1:=emp)(m2:=merge BodyCurrent BodySentinel).
          ++ apply map_join_comm;apply map_join_emp.
          ++ apply BodyTableSpatial.
          ++ eapply BodyStar with(m1:=emp)(m2:=merge BodyCurrent BodySentinel).
             ** apply map_join_comm;apply map_join_emp.
             ** apply BodyPubBindingsSpatial.
             ** apply BodyRSpatial.
Qed.
Theorem BodyInitialView : forall present cs, BodyLiteral false present cs ==> BodyPre present cs.
Proof.
 intros present cs. unfold BodyLiteral,BodyPre,BodyCells,BodyFrame,BodyExtension.
 apply astar_mono;[intros s H;exact H| ].
 rewrite V293_raw_cells_append. apply V293_raw_cells_mono. intros s HS.
 assert(H : s |= V293_rdy_raw_cells(BodyExtra present)
 ((OS[(fun _=>false),false,[],cs] ** (BodyBindings ** V293_tcb_table_binding 211%positive)) ** (BodyPubBindings ** BodyR))).
 { eapply V293_raw_cells_mono;[ |exact HS]. intros st Hst. clear -Hst. sep auto. }
 apply V293_raw_cells_move_frame in H. clear -H. sep auto.
Qed.
Theorem BodyInitialEntry : forall present cs,
 BodyState(BodyWhole false present)cs |= BodyPre present cs.
Proof. intros. apply BodyInitialView. apply BodyLiteralEntry. Qed.

Theorem BodyPostView : forall present cs result s,
 (s |= BodyPost present cs result) <->
 (s |= [|result=Some(Vint32 Int.zero)|] ** BodyLiteral true present cs).
Proof.
 intros present cs result s. unfold BodyPost,V293_link_return_post,V293_pub_return_post,
 V293_pub_hstate,V293_link_residual_frame.
 change ((s |= [|result=Some(Vint32 Int.zero)|] ** (<||spec_done None||> **
 V293_rdy_raw_cells(BodyPublished present)
 (OS[(fun _=>false),false,[],cs] ** (BodyPubBindings **
 V293_rdy_raw_cells BodyResidual(BodyBindings ** (V293_tcb_table_binding 211%positive ** BodyR)))))) <->
 (s |= [|result=Some(Vint32 Int.zero)|] ** BodyLiteral true present cs)).
 unfold BodyLiteral,BodyCells,BodyFrame. rewrite V293_raw_cells_append.
 split;intro HS.
 - eapply astar_mono;[intros st H;exact H| |exact HS].
   apply astar_mono;[intros st H;exact H| ];apply V293_raw_cells_mono;intros st H.
   assert(K : st |= (OS[(fun _=>false),false,[],cs] ** BodyPubBindings) **
   V293_rdy_raw_cells BodyResidual(BodyBindings ** (V293_tcb_table_binding 211%positive ** BodyR))).
   { clear -H. sep auto. }
   apply V293_raw_cells_unmove_frame in K.
   eapply V293_raw_cells_mono;[ |exact K]. intros st1 H1. clear -H1. sep auto.
 - eapply astar_mono;[intros st H;exact H| |exact HS].
   apply astar_mono;[intros st H;exact H| ];apply V293_raw_cells_mono;intros st H.
   assert(K : st |= V293_rdy_raw_cells BodyResidual
   ((OS[(fun _=>false),false,[],cs] ** BodyPubBindings) ** (BodyBindings ** (V293_tcb_table_binding 211%positive ** BodyR)))).
   { eapply V293_raw_cells_mono;[ |exact H]. intros st1 H1. clear -H1. sep auto. }
   apply V293_raw_cells_move_frame in K. clear -K. sep auto.
Qed.
Theorem BodyFinalEntry : forall present cs,
 BodyState(BodyWhole true present)cs |= BodyPost present cs(Some(Vint32 Int.zero)).
Proof.
 intros. apply BodyPostView. apply astar_l_apure_intro;[apply BodyLiteralEntry|reflexivity].
Qed.
Definition BodyHookState slot present cs :=
 V293_tcb_table_state 211%positive slot 210%positive 209%positive 201%positive 202%positive 203%positive 204%positive
 205%positive 206%positive 207%positive 208%positive 301%positive 128%Z 11
 Vnull Vnull(Vint32 Int.zero)(Vint32(Int.repr 128))Vnull(Vint32 Int.zero)
 BodyFinal BodyHead(Vint32 Int.zero)BodyNext BodyNext(BodyExtension present)(spec_done None)(fun _=>false)[]cs.
Definition BodyPriorBodyChecked : forall Spec sd I hi hc present cs,
 InfRules Spec sd V293_witness_li I(BodyPost present cs)Afalse
 (BodyHookState Vundef present cs)(scall hi[evar 108%Z])(BodyHookState Vundef present cs)BodyTid ->
 InfRules Spec sd V293_witness_li I(BodyPost present cs)Afalse
 (BodyHookState BodyHead present cs)(scall hc[evar 108%Z])(BodyHookState BodyHead present cs)BodyTid ->
 InfRules Spec sd V293_witness_li I(BodyPost present cs)Afalse
 (BodyPre present cs)(V293_TCBInit_function_body hi hc)Afalse BodyTid.
Proof.
 intros Spec sd I hi hc present cs InitHook CreateHook.
 exact(V293_OS_TCBInit_linked_body_hoare Spec sd V293_witness_li I BodyTid hi hc Vundef(fun _=>Vundef)Vundef Vundef
 211%positive 210%positive 209%positive 201%positive 202%positive 203%positive 204%positive 205%positive 206%positive 207%positive 208%positive 301%positive 128%Z 11 Vnull Vnull (Vint32 Int.zero) (Vint32(Int.repr 128)) Vnull (Vint32 Int.zero) BodyNext 212%positive 213%positive 214%positive 215%positive 301%positive 256%Z present Vundef 1 129 254 Vundef BodyR (spec_done None)(fun _=>false)[]cs
 ltac:(lia)ltac:(lia)ltac:(unfold Int.max_unsigned,Int.modulus,Int.wordsize;cbn;lia)
 ltac:(lia)ltac:(unfold Int.max_unsigned,Int.modulus,Int.wordsize;cbn;lia)
 ltac:(repeat split;reflexivity)ltac:(reflexivity)ltac:(lia)ltac:(lia)ltac:(lia)
 BodyRGood BodyRCurLINV InitHook CreateHook).
Qed.
Theorem BodyPostRaw : forall present cs result s,
 s |= BodyPost present cs result ->
 s |= V293_rdy_raw_cells(BodyCells true present)(BodyFrame cs) ** Atrue.
Proof.
 intros present cs result s HS. apply BodyPostView in HS.
 unfold BodyLiteral in HS. clear -HS. sep auto.
Qed.
Theorem BodyPostLoad : forall present cs result s a tp v,
 s |= BodyPost present cs result -> In(a,tp,v)(BodyCells true present) ->
 rule_type_val_match tp v=true -> load tp(getmem s)a=Some v.
Proof.
 intros present cs result s a tp v HS Member Valid.
 apply BodyPostRaw in HS. eapply V293_star_load_l;[ |exact HS].
 intros st H. eapply V293_rdy_raw_load;eassumption.
Qed.
Theorem BodyPriorityRead : forall present cs result s, s |= BodyPost present cs result ->
 load (Tint8)(getmem s)(301%positive,178%Z)=Some(V293_byteval 11).
Proof.
 intros present cs result s HS. eapply BodyPostLoad;[exact HS| | ].
 - destruct present;unfold BodyCells,BodyPublished,BodyResidual,BodyInputs;cbn[app tl];simpl;tauto.
 - destruct present;reflexivity.
Qed.
Theorem BodySlotRead : forall present cs result s, s |= BodyPost present cs result ->
 load (Tptr V293_tcb_type)(getmem s)(211%positive,44%Z)=Some(BodyHead).
Proof.
 intros present cs result s HS. eapply BodyPostLoad;[exact HS| | ].
 - destruct present;unfold BodyCells,BodyPublished,BodyResidual,BodyInputs;cbn[app tl];simpl;tauto.
 - destruct present;reflexivity.
Qed.
Theorem BodyFreeHeadRead : forall present cs result s, s |= BodyPost present cs result ->
 load (Tptr V293_tcb_type)(getmem s)(210%positive,0%Z)=Some(BodyNext).
Proof.
 intros present cs result s HS. eapply BodyPostLoad;[exact HS| | ].
 - destruct present;unfold BodyCells,BodyPublished,BodyResidual,BodyInputs;cbn[app tl];simpl;tauto.
 - destruct present;reflexivity.
Qed.
Theorem BodyNextRead : forall present cs result s, s |= BodyPost present cs result ->
 load (Tcom_ptr 410%Z)(getmem s)(301%positive,148%Z)=Some(BodyOldHead present).
Proof.
 intros present cs result s HS. eapply BodyPostLoad;[exact HS| | ].
 - destruct present;unfold BodyCells,BodyPublished,BodyResidual,BodyInputs;cbn[app tl];simpl;tauto.
 - destruct present;reflexivity.
Qed.
Theorem BodyPrevRead : forall present cs result s, s |= BodyPost present cs result ->
 load (Tcom_ptr 410%Z)(getmem s)(301%positive,152%Z)=Some(Vnull).
Proof.
 intros present cs result s HS. eapply BodyPostLoad;[exact HS| | ].
 - destruct present;unfold BodyCells,BodyPublished,BodyResidual,BodyInputs;cbn[app tl];simpl;tauto.
 - destruct present;reflexivity.
Qed.
Theorem BodyHeadRead : forall present cs result s, s |= BodyPost present cs result ->
 load (Tptr V293_tcb_type)(getmem s)(212%positive,0%Z)=Some(BodyHead).
Proof.
 intros present cs result s HS. eapply BodyPostLoad;[exact HS| | ].
 - destruct present;unfold BodyCells,BodyPublished,BodyResidual,BodyInputs;cbn[app tl];simpl;tauto.
 - destruct present;reflexivity.
Qed.
Theorem BodyGroupRead : forall present cs result s, s |= BodyPost present cs result ->
 load (Tint8)(getmem s)(213%positive,0%Z)=Some(V293_byteval 3).
Proof.
 intros present cs result s HS. eapply BodyPostLoad;[exact HS| | ].
 - destruct present;unfold BodyCells,BodyPublished,BodyResidual,BodyInputs;cbn[app tl];simpl;tauto.
 - destruct present;reflexivity.
Qed.
Theorem BodyRowRead : forall present cs result s, s |= BodyPost present cs result ->
 load (Tint8)(getmem s)(214%positive,1%Z)=Some(V293_byteval 137).
Proof.
 intros present cs result s HS. eapply BodyPostLoad;[exact HS| | ].
 - destruct present;unfold BodyCells,BodyPublished,BodyResidual,BodyInputs;cbn[app tl];simpl;tauto.
 - destruct present;reflexivity.
Qed.
Theorem BodyCounterRead : forall present cs result s, s |= BodyPost present cs result ->
 load (Tint8)(getmem s)(215%positive,0%Z)=Some(V293_byteval 255).
Proof.
 intros present cs result s HS. eapply BodyPostLoad;[exact HS| | ].
 - destruct present;unfold BodyCells,BodyPublished,BodyResidual,BodyInputs;cbn[app tl];simpl;tauto.
 - destruct present;reflexivity.
Qed.
Theorem BodySizeRead : forall present cs result s, s |= BodyPost present cs result ->
 load (Tint32)(getmem s)(301%positive,140%Z)=Some(Vint32(Int.repr 128)).
Proof.
 intros present cs result s HS. eapply BodyPostLoad;[exact HS| | ].
 - destruct present;unfold BodyCells,BodyPublished,BodyResidual,BodyInputs;cbn[app tl];simpl;tauto.
 - destruct present;reflexivity.
Qed.
Theorem BodyOldBacklinkRead : forall cs result s, s |= BodyPost true cs result ->
 load(Tcom_ptr 410%Z)(getmem s)(301%positive,280%Z)=Some BodyHead.
Proof.
 intros cs result s HS. eapply BodyPostLoad;[exact HS| |reflexivity].
 unfold BodyCells,BodyPublished;cbn[app]. do 10 right;left;reflexivity.
Qed.
Theorem BodyWrongFreeHead : forall present cs result s, s |= BodyPost present cs result ->
 load(Tptr V293_tcb_type)(getmem s)(210%positive,0%Z)<>Some BodyHead.
Proof. intros. rewrite(BodyFreeHeadRead _ _ _ _ H). unfold BodyNext,BodyHead. intro E. inversion E. Qed.
Theorem BodyReturnedZero : forall present cs result s, s |= BodyPost present cs result -> result=Some(Vint32 Int.zero).
Proof.
 intros present cs result s HS. apply BodyPostView in HS. apply astar_l_apure_elim in HS. tauto.
Qed.
Theorem BodyCoreSize : forall present,
 length(BodyCells false present)=(if present then 36 else 35) /\
 length(BodyCells true present)=(if present then 36 else 35) /\
 fold_right(fun cell count=>typelen(snd(fst cell))+count)0(BodyCells false present)=(if present then 100 else 96) /\
 fold_right(fun cell count=>typelen(snd(fst cell))+count)0(BodyCells true present)=(if present then 100 else 96).
Proof. destruct present;repeat split;reflexivity. Qed.

Require Import CertiOS.certiucos.v293.proofs.V293TCBHookCall.

Lemma BodyRFun : GoodFunAsrt BodyR.
Proof.
 cbn [BodyR CurTid LINV V293_witness_li Agvarmapsto Agvarenv' Aptrmapsto GoodFunAsrt].
 repeat split;exact I.
Qed.
Definition BodyOwned slot present := V293_hook_owned_cells 211%positive slot 210%positive 301%positive 128%Z 11
 Vnull Vnull(Vint32 Int.zero)(Vint32(Int.repr 128))Vnull(Vint32 Int.zero) BodyNext
 212%positive 213%positive 214%positive 215%positive 301%positive 256%Z present Vundef 1 129 254 Vundef.
Definition BodyResource slot present cs := V293_hook_resource(BodyOwned slot present) BodyR
 (spec_done None)(fun _=>false)[]cs.
Definition BodyResourceGood slot present cs := V293_hook_resource_good(BodyOwned slot present)BodyR
 (spec_done None)(fun _=>false)[]cs BodyRFun.
Definition BodyFpre slot present cs := V293_hook_fpre BodyHead BodyTid(BodyResource slot present cs)(BodyResourceGood slot present cs).
Definition BodyFpost slot present cs := V293_hook_fpost BodyHead BodyTid(BodyResource slot present cs)(BodyResourceGood slot present cs).

Definition BodyBodyChecked : forall Spec sd I hi hc present cs,
 Spec hi=Some(BodyFpre Vundef present cs,BodyFpost Vundef present cs,(Tvoid,[Tptr V293_tcb_type])) ->
 Spec hc=Some(BodyFpre BodyHead present cs,BodyFpost BodyHead present cs,(Tvoid,[Tptr V293_tcb_type])) ->
 InfRules Spec sd V293_witness_li I(BodyPost present cs)Afalse
 (BodyPre present cs)(V293_TCBInit_function_body hi hc)Afalse BodyTid.
Proof.
 intros Spec sd I hi hc present cs InitLookup CreateLookup.
 exact(V293_OS_TCBInit_hook_calls_body_hoare Spec sd V293_witness_li I BodyTid hi hc Vundef(fun _=>Vundef)Vundef Vundef
 211%positive 210%positive 209%positive 201%positive 202%positive 203%positive 204%positive 205%positive 206%positive 207%positive 208%positive 301%positive 128%Z 11 Vnull Vnull (Vint32 Int.zero) (Vint32(Int.repr 128)) Vnull (Vint32 Int.zero) BodyNext 212%positive 213%positive 214%positive 215%positive 301%positive 256%Z present Vundef 1 129 254 Vundef BodyR (spec_done None)(fun _=>false)[]cs
 ltac:(lia)ltac:(lia)ltac:(unfold Int.max_unsigned,Int.modulus,Int.wordsize;cbn;lia)
 ltac:(lia)ltac:(unfold Int.max_unsigned,Int.modulus,Int.wordsize;cbn;lia)
 ltac:(repeat split;reflexivity)ltac:(reflexivity)ltac:(lia)ltac:(lia)ltac:(lia)
 BodyRGood BodyRCurLINV BodyRFun InitLookup CreateLookup).
Qed.
(* This finite table witnesses lookup consistency ONLY. No Body body is supplied. *)
Definition BodyDeclaredSpec present cs : funspec := fun f =>
 if Z.eq_dec f 501%Z then Some(BodyFpre Vundef present cs,BodyFpost Vundef present cs,(Tvoid,[Tptr V293_tcb_type]))
 else if Z.eq_dec f 502%Z then Some(BodyFpre BodyHead present cs,BodyFpost BodyHead present cs,(Tvoid,[Tptr V293_tcb_type]))
 else None.
Theorem BodyInitLookup : forall present cs,
 BodyDeclaredSpec present cs 501%Z=Some(BodyFpre Vundef present cs,BodyFpost Vundef present cs,(Tvoid,[Tptr V293_tcb_type])).
Proof. intros. unfold BodyDeclaredSpec. destruct(Z.eq_dec 501%Z 501%Z);[reflexivity|contradiction]. Qed.
Theorem BodyCreateLookup : forall present cs,
 BodyDeclaredSpec present cs 502%Z=Some(BodyFpre BodyHead present cs,BodyFpost BodyHead present cs,(Tvoid,[Tptr V293_tcb_type])).
Proof.
 intros. unfold BodyDeclaredSpec. destruct(Z.eq_dec 502%Z 501%Z);[discriminate| ].
 destruct(Z.eq_dec 502%Z 502%Z);[reflexivity|contradiction].
Qed.
Theorem BodyBodyUnderDeclaredContracts : forall sd I present cs,
 InfRules(BodyDeclaredSpec present cs)sd V293_witness_li I(BodyPost present cs)Afalse
 (BodyPre present cs)(V293_TCBInit_function_body 501%Z 502%Z)Afalse BodyTid.
Proof. intros. apply BodyBodyChecked;[apply BodyInitLookup|apply BodyCreateLookup]. Qed.

Definition BodyEmptyGE : env := BodyGE.
Definition BodyEmptyLE : env := BodyLE.
Definition BodyEmptyTid : tid := (301%positive,Int.repr 8).
Definition BodyEmptyBytes b permission tp v := V293_encoded_memory b 0 permission (encode_val tp v).
Definition BodyEmptyCPU := BodyEmptyBytes 209%positive true Tint32 Vundef.
Definition BodyEmptyPointer := BodyEmptyBytes 201%positive true (Tptr V293_tcb_type) Vundef.
Definition BodyEmptyFree := BodyEmptyBytes 210%positive false (Tptr V293_tcb_type) Vnull.
Definition BodyEmptyCurrent := BodyEmptyBytes 402%positive false (Tptr Tvoid) (Vptr BodyEmptyTid).
Definition BodyEmptySentinel := BodyEmptyBytes 601%positive true Tint8 (Vint32(Int.repr 77)).
Definition BodyEmptyMemory := merge BodyEmptyCPU (merge BodyEmptyPointer
 (merge BodyEmptyFree (merge BodyEmptyCurrent BodyEmptySentinel))).
Definition BodyEmptyState M cs : RstateOP :=
 (BodyEmptyGE,BodyEmptyLE,M,(fun _=>false),(false,[],cs),(emp:osabst),spec_done None).
Definition BodyEmptyR := CurTid BodyEmptyTid ** LINV V293_witness_li BodyEmptyTid [] **
 Amapsto (601%positive,0%Z) Tint8 true (Vint32(Int.repr 77)).

Lemma BodyEmptyStar : forall m1 m2 m cs p q,
 join m1 m2 m -> BodyEmptyState m1 cs |= p -> BodyEmptyState m2 cs |= q ->
 BodyEmptyState m cs |= p ** q.
Proof.
 intros. apply sat_split'. exists m1. exists m2.
 exists(emp:osabst). exists(emp:osabst).
 split;[exact H | ]. split;[apply map_join_emp | ]. split;assumption.
Qed.
Lemma BodyEmptyBindings : forall cs, BodyEmptyState emp cs |=
 V293_tcb_empty_bindings 210%positive 201%positive 209%positive.
Proof.
 intro cs. unfold V293_tcb_empty_bindings. repeat split.
 - exists 201%positive. split;[vm_compute;reflexivity | ]. repeat split;reflexivity.
 - exists 209%positive. split;[vm_compute;reflexivity | ]. repeat split;reflexivity.
 - exists 210%positive. split;[vm_compute;reflexivity | ]. repeat split;reflexivity.
 - intros [v H]. vm_compute in H. discriminate H.
Qed.
Lemma BodyEmptyCurrentSpatial : forall cs, BodyEmptyState BodyEmptyCurrent cs |= CurTid BodyEmptyTid.
Proof.
 intro cs. exists Tvoid. exists 402%positive.
 eapply BodyEmptyStar with (m1:=emp) (m2:=BodyEmptyCurrent).
 - apply map_join_comm;apply map_join_emp.
 - exists 402%positive. split;[vm_compute;reflexivity | ]. repeat split;reflexivity.
 - split;[apply V293_encoded_memory_mapsto|reflexivity].
Qed.
Lemma BodyEmptyLInvSpatial : forall cs, BodyEmptyState emp cs |= LINV V293_witness_li BodyEmptyTid [].
Proof.
 intro cs. unfold LINV. apply astar_comm. apply astar_l_apure_intro.
 - split;reflexivity.
 - apply V293_witness_li_good.
Qed.
Ltac BodyEmptyApart b :=
 apply map_join_merge;apply map_disjoint;intros [other offset];
 destruct(Pos.eq_dec other b);[subst other;right;left|left];
 unfold BodyEmptyCPU,BodyEmptyPointer,BodyEmptyFree,BodyEmptyCurrent,BodyEmptySentinel,BodyEmptyBytes;
 repeat first [rewrite map_merge_semp by reflexivity |
 rewrite V293_encoded_memory_outside by (left;congruence)];reflexivity.
Lemma BodyEmptyRSpatial : forall cs,
 BodyEmptyState (merge BodyEmptyCurrent BodyEmptySentinel) cs |= BodyEmptyR.
Proof.
 intro cs. unfold BodyEmptyR.
 eapply BodyEmptyStar with (m1:=BodyEmptyCurrent) (m2:=BodyEmptySentinel).
 - BodyEmptyApart 402%positive.
 - apply BodyEmptyCurrentSpatial.
 - eapply BodyEmptyStar with (m1:=emp) (m2:=BodyEmptySentinel).
   + apply map_join_comm;apply map_join_emp.
   + apply BodyEmptyLInvSpatial.
   + split;[apply V293_encoded_memory_mapsto|reflexivity].
Qed.
Lemma BodyEmptyRGood : GoodFrm BodyEmptyR.
Proof. cbn [BodyEmptyR CurTid LINV V293_witness_li GoodFrm]. repeat split;exact I. Qed.
Lemma BodyEmptyRCurLINV : BodyEmptyR ==> CurLINV V293_witness_li BodyEmptyTid.
Proof.
 intros s HS. unfold CurLINV. exists([]:list logicvar).
 unfold BodyEmptyR in HS. clear -HS. sep auto.
Qed.
Theorem BodyEmptyLiteralEntry : forall cs,
 BodyEmptyState BodyEmptyMemory cs |=
 V293_tcb_empty_state 210%positive 201%positive 209%positive Vundef Vundef BodyEmptyR
 (spec_done None) (fun _=>false) [] cs.
Proof.
 intro cs. unfold V293_tcb_empty_state,V293_tcb_empty_resources.
 eapply BodyEmptyStar with (m1:=emp) (m2:=BodyEmptyMemory).
 - apply map_join_comm;apply map_join_emp.
 - split;[reflexivity | ]. split;reflexivity.
 - eapply BodyEmptyStar with (m1:=emp) (m2:=BodyEmptyMemory).
   + apply map_join_comm;apply map_join_emp.
   + repeat (eapply BodyEmptyStar with (m1:=emp) (m2:=emp);
       [apply map_join_emp|split;[reflexivity|split;reflexivity] | ]).
     split;[reflexivity | ]. split;reflexivity.
   + eapply BodyEmptyStar with (m1:=emp) (m2:=BodyEmptyMemory).
     * apply map_join_comm;apply map_join_emp.
     * apply BodyEmptyBindings.
     * assert (Ordered:BodyEmptyState BodyEmptyMemory cs |=
        Amapsto (209%positive,0%Z) Tint32 true Vundef **
        (Amapsto (201%positive,0%Z) (Tptr V293_tcb_type) true Vundef **
        (Amapsto (210%positive,0%Z) (Tptr V293_tcb_type) false Vnull ** BodyEmptyR))).
       { unfold BodyEmptyMemory.
         eapply BodyEmptyStar with (m1:=BodyEmptyCPU)
          (m2:=merge BodyEmptyPointer (merge BodyEmptyFree (merge BodyEmptyCurrent BodyEmptySentinel))).
         - BodyEmptyApart 209%positive.
         - split;[apply V293_encoded_memory_mapsto|reflexivity].
         - eapply BodyEmptyStar with (m1:=BodyEmptyPointer)
            (m2:=merge BodyEmptyFree (merge BodyEmptyCurrent BodyEmptySentinel)).
           + BodyEmptyApart 201%positive.
           + split;[apply V293_encoded_memory_mapsto|reflexivity].
           + eapply BodyEmptyStar with (m1:=BodyEmptyFree) (m2:=merge BodyEmptyCurrent BodyEmptySentinel).
             * BodyEmptyApart 210%positive.
             * split;[apply V293_encoded_memory_mapsto|reflexivity].
             * apply BodyEmptyRSpatial. }
       clear -Ordered. sep auto.
Qed.

Definition BodyEmptyBodyChecked : forall Spec sd I hi hc cs,
 InfRules Spec sd V293_witness_li I
 (fun result => [|result=Some(Vint32(Int.repr 66))|] **
  V293_tcb_empty_state 210%positive 201%positive 209%positive Vnull (Vint32 Int.zero)
   BodyEmptyR (spec_done None) (fun _=>false) [] cs) Afalse
 (V293_tcb_empty_state 210%positive 201%positive 209%positive Vundef Vundef
  BodyEmptyR (spec_done None) (fun _=>false) [] cs)
 (V293_TCBInit_function_body hi hc) Afalse BodyEmptyTid.
Proof. intros. apply V293_OS_TCBInit_empty_body_hoare;[apply BodyEmptyRGood|apply BodyEmptyRCurLINV]. Qed.
Definition BodyEmptyNoHookSpec : funspec := fun _=>None.
Theorem BodyEmptyBodyNoHook : forall sd I hi hc cs,
 InfRules BodyEmptyNoHookSpec sd V293_witness_li I
 (V293_tcb_empty_post 210%positive 201%positive 209%positive BodyEmptyR
  (spec_done None) (fun _=>false) [] cs) Afalse
 (V293_tcb_empty_state 210%positive 201%positive 209%positive Vundef Vundef
  BodyEmptyR (spec_done None) (fun _=>false) [] cs)
 (V293_TCBInit_function_body hi hc) Afalse BodyEmptyTid.
Proof. intros. apply BodyEmptyBodyChecked. Qed.
Theorem BodyEmptyPostRejectZero : forall s cs,
 ~s |= V293_tcb_empty_post 210%positive 201%positive 209%positive BodyEmptyR
 (spec_done None) (fun _=>false) [] cs (Some(Vint32 Int.zero)).
Proof.
 intros s cs H. apply astar_l_apure_elim in H. destruct H as [Bad _]. discriminate Bad.
Qed.
(* Semantic exclusion of the success guard, not a claim about executing it. *)
Theorem BodyEmptyGuardNotTrue : forall bf bp bc cpu R aop isr is cs s,
 s |= V293_tcb_empty_state bf bp bc Vnull cpu R aop isr is cs ->
 ~s |= Aistrue(eunop oppsite(V293_task_prio_null_test(evar 108%Z))).
Proof.
 intros bf bp bc cpu R aop isr is cs s HS [v [V B]].
 destruct (V293_tcb_empty_guard_eval _ _ _ _ _ _ _ _ _ _ HS) as [Z _].
 rewrite Z in V. inversion V;subst v. discriminate B.
Qed.

(* The two entries share identifiers, addresses, GE/LE, task and sentinel;
   they do NOT claim identical ownership/footprints or global reachability. *)
Definition BodyEmptyPre cs :=
 V293_tcb_empty_state 210%positive 201%positive 209%positive Vundef Vundef
 BodyEmptyR (spec_done None)(fun _=>false)[]cs.
Definition BodyEmptyReturn cs :=
 V293_tcb_empty_state 210%positive 201%positive 209%positive Vnull (Vint32 Int.zero)
 BodyEmptyR (spec_done None)(fun _=>false)[]cs.
Definition BodyCombinedPre present cs := BodyEmptyPre cs \\// BodyPre present cs.
Definition BodyCombinedPost present cs := V293_tcb_body_post (BodyEmptyReturn cs)
 (BodyPost present cs (Some(Vint32 Int.zero))).
Theorem BodyEmptyJointEntry : forall present cs,
 BodyState BodyEmptyMemory cs |= BodyCombinedPre present cs.
Proof. intros. left. apply BodyEmptyLiteralEntry. Qed.
Theorem BodyNonemptyJointEntry : forall present cs,
 BodyState(BodyWhole false present)cs |= BodyCombinedPre present cs.
Proof. intros. right. apply BodyInitialEntry. Qed.
Theorem BodySharedEnvironments : forall M cs,
 getgenv(BodyEmptyState M cs)=getgenv(BodyState M cs) /\
 getlenv(BodyEmptyState M cs)=getlenv(BodyState M cs).
Proof. intros. split;reflexivity. Qed.
Theorem BodyCombinedChecked : forall Spec sd I hi hc present cs,
 Spec hi=Some(BodyFpre Vundef present cs,BodyFpost Vundef present cs,(Tvoid,[Tptr V293_tcb_type])) ->
 Spec hc=Some(BodyFpre BodyHead present cs,BodyFpost BodyHead present cs,(Tvoid,[Tptr V293_tcb_type])) ->
 InfRules Spec sd V293_witness_li I(BodyCombinedPost present cs)Afalse
 (BodyCombinedPre present cs)(V293_TCBInit_function_body hi hc)Afalse BodyTid.
Proof.
 intros Spec sd I hi hc present cs InitLookup CreateLookup.
 exact(V293_OS_TCBInit_body_hoare Spec sd V293_witness_li I BodyTid hi hc Vundef(fun _=>Vundef)Vundef Vundef
 211%positive 210%positive 209%positive 201%positive 202%positive 203%positive 204%positive 205%positive 206%positive 207%positive 208%positive 301%positive 128%Z 11 Vnull Vnull (Vint32 Int.zero) (Vint32(Int.repr 128)) Vnull (Vint32 Int.zero) BodyNext 212%positive 213%positive 214%positive 215%positive 301%positive 256%Z present Vundef 1 129 254 Vundef BodyR BodyEmptyR (spec_done None)(fun _=>false)[]cs
 ltac:(lia)ltac:(lia)ltac:(unfold Int.max_unsigned,Int.modulus,Int.wordsize;cbn;lia)
 ltac:(lia)ltac:(unfold Int.max_unsigned,Int.modulus,Int.wordsize;cbn;lia)
 ltac:(repeat split;reflexivity)ltac:(reflexivity)ltac:(lia)ltac:(lia)ltac:(lia)
 BodyRGood BodyRCurLINV BodyEmptyRGood BodyEmptyRCurLINV BodyRFun InitLookup CreateLookup).
Qed.
Theorem BodyCombinedDeclaredContracts : forall sd I present cs,
 InfRules(BodyDeclaredSpec present cs)sd V293_witness_li I(BodyCombinedPost present cs)Afalse
 (BodyCombinedPre present cs)(V293_TCBInit_function_body 501%Z 502%Z)Afalse BodyTid.
Proof. intros. apply BodyCombinedChecked;[apply BodyInitLookup|apply BodyCreateLookup]. Qed.
Theorem BodyEmptyReturnExact : forall present cs s,
 (s |= BodyCombinedPost present cs (Some(Vint32(Int.repr 66)))) <-> s |= BodyEmptyReturn cs.
Proof. intros. apply V293_tcb_body_post_empty. Qed.
Theorem BodyReadyReturnExact : forall present cs s,
 (s |= BodyCombinedPost present cs (Some(Vint32 Int.zero))) <->
 s |= BodyPost present cs (Some(Vint32 Int.zero)).
Proof. intros. apply V293_tcb_body_post_ready. Qed.
Theorem BodyRejectsVoid : forall present cs s,
 ~(s |= BodyCombinedPost present cs None).
Proof. intros. apply V293_tcb_body_post_no_void. Qed.
Theorem BodyRejectsWrongCode : forall present cs s,
 ~(s |= BodyCombinedPost present cs (Some(Vint32(Int.repr 65)))).
Proof. intros. apply V293_tcb_body_post_no_other;discriminate. Qed.
