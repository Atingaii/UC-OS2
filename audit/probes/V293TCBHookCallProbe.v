(* Independent literal resources and actual Hook call-site entries; no old probe imports. *)
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
Definition HookOld : list V293_record_cell :=
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
Definition HookInputs pc : list V293_record_cell :=
 [((201%positive,0%Z),(Tptr V293_tcb_type),(pc));
  ((202%positive,0%Z),(Tint8),(V293_byteval 11));
  ((203%positive,0%Z),(Tptr Tint32),(Vnull));
  ((204%positive,0%Z),(Tptr Tint32),(Vnull));
  ((205%positive,0%Z),(Tint16),(Vint32 Int.zero));
  ((206%positive,0%Z),(Tint32),(Vint32(Int.repr 128)));
  ((207%positive,0%Z),(Tptr Tvoid),(Vnull));
  ((208%positive,0%Z),(Tint16),(Vint32 Int.zero))].
Definition HookFinal : list V293_record_cell :=
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
Definition HookGE : env := set (set (set (set (set (set (sig OSTCBCur (402%positive,Tptr Tvoid))
 91%Z (210%positive,Tptr V293_tcb_type)) 92%Z (211%positive,Tarray (Tptr V293_tcb_type) 13))
 93%Z (212%positive,Tptr V293_tcb_type)) 94%Z (213%positive,Tint8))
 95%Z (214%positive,Tarray Tint8 2)) 96%Z (215%positive,Tint8).
Definition HookLE : env :=
 set (set (set (set (set (set (set (set (set (emp:env)
 108%Z (201%positive,Tptr V293_tcb_type)) 101%Z (202%positive,Tint8))
 102%Z (203%positive,Tptr Tint32)) 103%Z (204%positive,Tptr Tint32))
 104%Z (205%positive,Tint16)) 105%Z (206%positive,Tint32))
 106%Z (207%positive,Tptr Tvoid)) 107%Z (208%positive,Tint16)) 109%Z (209%positive,Tint32).
Definition HookTid : tid := (301%positive,Int.repr 8).
Definition HookBytes b permission tp v := V293_encoded_memory b 0 permission (encode_val tp v).
Definition HookCurrent := HookBytes 402%positive false (Tptr Tvoid) (Vptr HookTid).
Definition HookSentinel := HookBytes 601%positive true Tint8 (Vint32(Int.repr 77)).
Fixpoint HookMemory (cells : list V293_record_cell) : mem :=
 match cells with []=>emp | ((b,i),tp,v)::tail=>
 merge (V293_encoded_memory b i true (encode_val tp v)) (HookMemory tail) end.
Definition HookHead := Vptr(301%positive,Int.repr 128).
Definition HookNext := Vptr(301%positive,Int.repr 384).
Definition HookOldHead (present:bool) := if present then Vptr(301%positive,Int.repr 256) else Vnull.
Definition HookExtra (present:bool) : list V293_record_cell :=
 [((301%positive,152%Z),Tcom_ptr 410%Z,Vundef);
  ((212%positive,0%Z),Tptr V293_tcb_type,HookOldHead present);
  ((213%positive,0%Z),Tint8,V293_byteval 1);
  ((214%positive,1%Z),Tint8,V293_byteval 129);
  ((215%positive,0%Z),Tint8,V293_byteval 254)] ++
 if present then [((301%positive,280%Z),Tcom_ptr 410%Z,Vundef)] else [].
Definition HookPreCells : list V293_record_cell :=
 ((211%positive,44%Z),Tptr V293_tcb_type,Vundef)::
 ((209%positive,0%Z),Tint32,Vundef)::
 (HookOld++HookInputs Vundef++
 [((210%positive,0%Z),Tptr V293_tcb_type,HookHead);
  ((301%positive,148%Z),Tcom_ptr 410%Z,HookNext)]).
Definition HookResidual : list V293_record_cell :=
 [((211%positive,44%Z),Tptr V293_tcb_type,HookHead);
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
  ((301%positive,160%Z),Tptr Tvoid,Vnull)] ++ tl(HookInputs HookHead) ++
 [((210%positive,0%Z),Tptr V293_tcb_type,HookNext)].
Definition HookPublished (present:bool) : list V293_record_cell :=
 [((201%positive,0%Z),Tptr V293_tcb_type,HookHead);
  ((301%positive,148%Z),Tcom_ptr 410%Z,HookOldHead present);
  ((301%positive,152%Z),Tcom_ptr 410%Z,Vnull);
  ((301%positive,180%Z),Tint8,V293_byteval 1);
  ((301%positive,182%Z),Tint8,V293_byteval 2);
  ((301%positive,181%Z),Tint8,V293_byteval 8);
  ((212%positive,0%Z),Tptr V293_tcb_type,HookHead);
  ((213%positive,0%Z),Tint8,V293_byteval 3);
  ((214%positive,1%Z),Tint8,V293_byteval 137);
  ((215%positive,0%Z),Tint8,V293_byteval 255)] ++
 if present then [((301%positive,280%Z),Tcom_ptr 410%Z,HookHead)] else [].
Definition HookCells (initialized present:bool) :=
 if initialized then HookPublished present++HookResidual else HookPreCells++HookExtra present.
Definition HookWhole initialized present := merge(HookMemory(HookCells initialized present))(merge HookCurrent HookSentinel).
Definition HookState M cs : RstateOP :=
 (HookGE,HookLE,M,(fun _=>false),(false,[],cs),(emp:osabst),spec_done None).
Definition HookR := CurTid HookTid ** LINV V293_witness_li HookTid [] **
 Amapsto(601%positive,0%Z) Tint8 true(Vint32(Int.repr 77)).
Definition HookFieldBindings := V293_tcb_fields_bindings 108%Z 101%Z 102%Z 103%Z 104%Z 105%Z 106%Z 107%Z
 201%positive 202%positive 203%positive 204%positive 205%positive 206%positive 207%positive 208%positive.
Definition HookBindings := HookFieldBindings ** V293_tcb_success_extra 210%positive 209%positive.
Definition HookPubBindings := V293_pub_bindings 108%Z 93%Z 94%Z 95%Z 96%Z 201%positive 212%positive 213%positive 214%positive 215%positive.
Definition HookFrame cs := OS[(fun _=>false),false,[],cs] **
 (HookBindings ** (V293_tcb_table_binding 211%positive ** (HookPubBindings ** HookR))).
Definition HookLiteral initialized present cs := <||spec_done None||> ** V293_rdy_raw_cells(HookCells initialized present)(HookFrame cs).
Definition HookExtension present := V293_rdy_raw_cells(HookExtra present)(HookPubBindings ** HookR).
Definition HookPre present cs := <||spec_done None||> ** V293_rdy_raw_cells HookPreCells
 (OS[(fun _=>false),false,[],cs] ** (HookBindings ** (V293_tcb_table_binding 211%positive ** HookExtension present))).
Definition HookPost present cs : retasrt :=
 V293_link_return_post 211%positive 210%positive 209%positive 201%positive 202%positive 203%positive 204%positive
 205%positive 206%positive 207%positive 208%positive 301%positive 128%Z 11
 Vnull Vnull (Vint32 Int.zero) (Vint32(Int.repr 128)) Vnull (Vint32 Int.zero) HookNext
 212%positive 213%positive 214%positive 215%positive 301%positive 256%Z present 1 129 254 HookR
 (spec_done None)(fun _=>false)[]cs.
Lemma HookStar : forall m1 m2 m cs p q,
 join m1 m2 m -> HookState m1 cs |= p -> HookState m2 cs |= q ->
 HookState m cs |= p ** q.
Proof.
 intros. apply sat_split'. exists m1. exists m2.
 exists(emp:osabst). exists(emp:osabst).
 split;[exact H | ]. split;[apply map_join_emp | ]. split;assumption.
Qed.
Lemma HookCurrentSpatial : forall cs, HookState HookCurrent cs |= CurTid HookTid.
Proof.
 intro cs. exists Tvoid. exists 402%positive.
 eapply HookStar with (m1:=emp) (m2:=HookCurrent).
 - apply map_join_comm;apply map_join_emp.
 - exists 402%positive. split;[vm_compute;reflexivity | ]. repeat split;reflexivity.
 - split;[apply V293_encoded_memory_mapsto|reflexivity].
Qed.
Lemma HookLInvSpatial : forall cs, HookState emp cs |= LINV V293_witness_li HookTid [].
Proof.
 intro cs. unfold LINV. apply astar_comm. apply astar_l_apure_intro.
 - split;reflexivity.
 - apply V293_witness_li_good.
Qed.
Ltac HookFrameApart b :=
 apply map_join_merge;apply map_disjoint;intros [other offset];
 destruct(Pos.eq_dec other b);[subst other;right;left|left];
 unfold HookCurrent,HookSentinel,HookBytes;
 repeat first [rewrite map_merge_semp by reflexivity |
 rewrite V293_encoded_memory_outside by (left;congruence)];reflexivity.
Lemma HookRSpatial : forall cs,
 HookState (merge HookCurrent HookSentinel) cs |= HookR.
Proof.
 intro cs. unfold HookR.
 eapply HookStar with (m1:=HookCurrent) (m2:=HookSentinel).
 - HookFrameApart 402%positive.
 - apply HookCurrentSpatial.
 - eapply HookStar with (m1:=emp) (m2:=HookSentinel).
   + apply map_join_comm;apply map_join_emp.
   + apply HookLInvSpatial.
   + split;[apply V293_encoded_memory_mapsto|reflexivity].
Qed.
Lemma HookRGood : GoodFrm HookR.
Proof. cbn [HookR CurTid LINV V293_witness_li GoodFrm]. repeat split;exact I. Qed.
Lemma HookRCurLINV : HookR ==> CurLINV V293_witness_li HookTid.
Proof.
 intros s HS. unfold CurLINV. exists([]:list logicvar).
 unfold HookR in HS. clear -HS. sep auto.
Qed.
Lemma HookFieldBindingsSpatial : forall cs, HookState emp cs |= HookFieldBindings.
Proof.
 intro cs. unfold HookFieldBindings,V293_tcb_fields_bindings. repeat split.
 - exists 201%positive. split;[vm_compute;reflexivity | ]. repeat split;reflexivity.
 - exists 202%positive. split;[vm_compute;reflexivity | ]. repeat split;reflexivity.
 - exists 203%positive. split;[vm_compute;reflexivity | ]. repeat split;reflexivity.
 - exists 204%positive. split;[vm_compute;reflexivity | ]. repeat split;reflexivity.
 - exists 205%positive. split;[vm_compute;reflexivity | ]. repeat split;reflexivity.
 - exists 206%positive. split;[vm_compute;reflexivity | ]. repeat split;reflexivity.
 - exists 207%positive. split;[vm_compute;reflexivity | ]. repeat split;reflexivity.
 - exists 208%positive. split;[vm_compute;reflexivity | ]. repeat split;reflexivity.
Qed.
Lemma HookBindingsSpatial : forall cs, HookState emp cs |= HookBindings.
Proof.
 intro cs. unfold HookBindings. eapply HookStar with (m1:=emp) (m2:=emp).
 - apply map_join_emp.
 - apply HookFieldBindingsSpatial.
 - unfold V293_tcb_success_extra. repeat split.
   + exists 209%positive. split;[vm_compute;reflexivity| ]. repeat split;reflexivity.
   + exists 210%positive. split;[vm_compute;reflexivity| ]. repeat split;reflexivity.
   + intros [v H]. vm_compute in H. discriminate H.
Qed.
Ltac HookOutside :=
 repeat first [rewrite V293_encoded_memory_outside by
 (first [left;congruence | right;rewrite ?encode_val_length;cbn [V293_byteval length encode_val typelen list_repeat inj_pointer inj_bytes encode_int List.map];lia])
 |rewrite map_merge_semp by reflexivity];reflexivity.
Ltac HookApart b start count :=
 apply map_join_merge;apply map_disjoint;intros [other off];
 destruct (Pos.eq_dec other b) as [B|B];
 [subst other;destruct (Z_lt_dec off start) as [Low|Low];
 [left;apply V293_encoded_memory_outside;right;left;exact Low |
 destruct (Z_lt_dec off (start+count)) as [Inside|Outside];
 [right;left;HookOutside |left;apply V293_encoded_memory_outside;right;right;
 rewrite ?encode_val_length;cbn [V293_byteval length encode_val typelen list_repeat inj_pointer inj_bytes encode_int List.map];lia]] |
 left;apply V293_encoded_memory_outside;left;exact B].

Lemma HookTableSpatial : forall cs, HookState emp cs |= V293_tcb_table_binding 211%positive.
Proof.
 intro cs. unfold V293_tcb_table_binding. repeat split.
 - exists 211%positive. split;[vm_compute;reflexivity| ]. repeat split;reflexivity.
 - intros [v H]. vm_compute in H. discriminate H.
Qed.
Lemma HookPubBindingsSpatial : forall cs, HookState emp cs |= HookPubBindings.
Proof.
 intro cs. unfold HookPubBindings,V293_pub_bindings. repeat split.
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

Ltac HookRawTactic :=
 lazymatch goal with
 | |- HookState (merge (V293_encoded_memory ?b ?off true (encode_val ?tp ?v)) ?tail) ?cs |= _ =>
   let bytes := eval cbv in (Z.of_nat(typelen tp)) in
   eapply HookStar with(m1:=V293_encoded_memory b off true(encode_val tp v));
   [HookApart b off bytes|split;[apply V293_encoded_memory_mapsto|reflexivity]|HookRawTactic]
 | |- HookState emp _ |= Aemp => split;reflexivity
 end.
Theorem HookRawLiteral : forall initialized present cs,
 HookState(HookMemory(HookCells initialized present))cs |= V293_rdy_raw_cells(HookCells initialized present)Aemp.
Proof.
 intros initialized present cs. destruct initialized,present;
 unfold HookCells,HookPublished,HookResidual,HookPreCells,HookExtra,HookOldHead,
 HookOld,HookInputs,HookHead,HookNext;
 cbn [app tl HookMemory V293_rdy_raw_cells];HookRawTactic.
Qed.
Theorem HookLiteralEntry : forall initialized present cs,
 HookState(HookWhole initialized present)cs |= HookLiteral initialized present cs.
Proof.
 intros initialized present cs. unfold HookLiteral.
 eapply HookStar with(m1:=emp)(m2:=HookWhole initialized present).
 - apply map_join_comm;apply map_join_emp.
 - split;[reflexivity| ]. split;reflexivity.
 - apply V293_raw_cells_join. unfold HookWhole.
   eapply HookStar with(m1:=HookMemory(HookCells initialized present))(m2:=merge HookCurrent HookSentinel).
   + apply map_join_merge;apply map_disjoint;intros[b off].
     destruct(Pos.eq_dec b 402%positive);[subst b;left| ].
     * destruct initialized,present;unfold HookCells,HookPublished,HookResidual,HookPreCells,HookExtra,HookOld,HookInputs;cbn[app tl HookMemory];HookOutside.
     * destruct(Pos.eq_dec b 601%positive);[subst b;left|right;left].
       -- destruct initialized,present;unfold HookCells,HookPublished,HookResidual,HookPreCells,HookExtra,HookOld,HookInputs;cbn[app tl HookMemory];HookOutside.
       -- unfold HookCurrent,HookSentinel,HookBytes. rewrite map_merge_semp by reflexivity.
          rewrite !V293_encoded_memory_outside by(left;congruence). reflexivity.
   + apply HookRawLiteral.
   + unfold HookFrame. eapply HookStar with(m1:=emp)(m2:=merge HookCurrent HookSentinel).
     * apply map_join_comm;apply map_join_emp.
     * repeat(eapply HookStar with(m1:=emp)(m2:=emp);
       [apply map_join_emp|split;[reflexivity|split;reflexivity]| ]).
       split;[reflexivity|split;reflexivity].
     * eapply HookStar with(m1:=emp)(m2:=merge HookCurrent HookSentinel).
       -- apply map_join_comm;apply map_join_emp.
       -- apply HookBindingsSpatial.
       -- eapply HookStar with(m1:=emp)(m2:=merge HookCurrent HookSentinel).
          ++ apply map_join_comm;apply map_join_emp.
          ++ apply HookTableSpatial.
          ++ eapply HookStar with(m1:=emp)(m2:=merge HookCurrent HookSentinel).
             ** apply map_join_comm;apply map_join_emp.
             ** apply HookPubBindingsSpatial.
             ** apply HookRSpatial.
Qed.
Theorem HookInitialView : forall present cs, HookLiteral false present cs ==> HookPre present cs.
Proof.
 intros present cs. unfold HookLiteral,HookPre,HookCells,HookFrame,HookExtension.
 apply astar_mono;[intros s H;exact H| ].
 rewrite V293_raw_cells_append. apply V293_raw_cells_mono. intros s HS.
 assert(H : s |= V293_rdy_raw_cells(HookExtra present)
 ((OS[(fun _=>false),false,[],cs] ** (HookBindings ** V293_tcb_table_binding 211%positive)) ** (HookPubBindings ** HookR))).
 { eapply V293_raw_cells_mono;[ |exact HS]. intros st Hst. clear -Hst. sep auto. }
 apply V293_raw_cells_move_frame in H. clear -H. sep auto.
Qed.
Theorem HookInitialEntry : forall present cs,
 HookState(HookWhole false present)cs |= HookPre present cs.
Proof. intros. apply HookInitialView. apply HookLiteralEntry. Qed.

Theorem HookPostView : forall present cs result s,
 (s |= HookPost present cs result) <->
 (s |= [|result=Some(Vint32 Int.zero)|] ** HookLiteral true present cs).
Proof.
 intros present cs result s. unfold HookPost,V293_link_return_post,V293_pub_return_post,
 V293_pub_hstate,V293_link_residual_frame.
 change ((s |= [|result=Some(Vint32 Int.zero)|] ** (<||spec_done None||> **
 V293_rdy_raw_cells(HookPublished present)
 (OS[(fun _=>false),false,[],cs] ** (HookPubBindings **
 V293_rdy_raw_cells HookResidual(HookBindings ** (V293_tcb_table_binding 211%positive ** HookR)))))) <->
 (s |= [|result=Some(Vint32 Int.zero)|] ** HookLiteral true present cs)).
 unfold HookLiteral,HookCells,HookFrame. rewrite V293_raw_cells_append.
 split;intro HS.
 - eapply astar_mono;[intros st H;exact H| |exact HS].
   apply astar_mono;[intros st H;exact H| ];apply V293_raw_cells_mono;intros st H.
   assert(K : st |= (OS[(fun _=>false),false,[],cs] ** HookPubBindings) **
   V293_rdy_raw_cells HookResidual(HookBindings ** (V293_tcb_table_binding 211%positive ** HookR))).
   { clear -H. sep auto. }
   apply V293_raw_cells_unmove_frame in K.
   eapply V293_raw_cells_mono;[ |exact K]. intros st1 H1. clear -H1. sep auto.
 - eapply astar_mono;[intros st H;exact H| |exact HS].
   apply astar_mono;[intros st H;exact H| ];apply V293_raw_cells_mono;intros st H.
   assert(K : st |= V293_rdy_raw_cells HookResidual
   ((OS[(fun _=>false),false,[],cs] ** HookPubBindings) ** (HookBindings ** (V293_tcb_table_binding 211%positive ** HookR)))).
   { eapply V293_raw_cells_mono;[ |exact H]. intros st1 H1. clear -H1. sep auto. }
   apply V293_raw_cells_move_frame in K. clear -K. sep auto.
Qed.
Theorem HookFinalEntry : forall present cs,
 HookState(HookWhole true present)cs |= HookPost present cs(Some(Vint32 Int.zero)).
Proof.
 intros. apply HookPostView. apply astar_l_apure_intro;[apply HookLiteralEntry|reflexivity].
Qed.
Definition HookHookState slot present cs :=
 V293_tcb_table_state 211%positive slot 210%positive 209%positive 201%positive 202%positive 203%positive 204%positive
 205%positive 206%positive 207%positive 208%positive 301%positive 128%Z 11
 Vnull Vnull(Vint32 Int.zero)(Vint32(Int.repr 128))Vnull(Vint32 Int.zero)
 HookFinal HookHead(Vint32 Int.zero)HookNext HookNext(HookExtension present)(spec_done None)(fun _=>false)[]cs.
Definition HookPriorBodyChecked : forall Spec sd I hi hc present cs,
 InfRules Spec sd V293_witness_li I(HookPost present cs)Afalse
 (HookHookState Vundef present cs)(scall hi[evar 108%Z])(HookHookState Vundef present cs)HookTid ->
 InfRules Spec sd V293_witness_li I(HookPost present cs)Afalse
 (HookHookState HookHead present cs)(scall hc[evar 108%Z])(HookHookState HookHead present cs)HookTid ->
 InfRules Spec sd V293_witness_li I(HookPost present cs)Afalse
 (HookPre present cs)(V293_TCBInit_function_body hi hc)Afalse HookTid.
Proof.
 intros Spec sd I hi hc present cs InitHook CreateHook.
 exact(V293_OS_TCBInit_linked_body_hoare Spec sd V293_witness_li I HookTid hi hc Vundef(fun _=>Vundef)Vundef Vundef
 211%positive 210%positive 209%positive 201%positive 202%positive 203%positive 204%positive 205%positive 206%positive 207%positive 208%positive 301%positive 128%Z 11 Vnull Vnull (Vint32 Int.zero) (Vint32(Int.repr 128)) Vnull (Vint32 Int.zero) HookNext 212%positive 213%positive 214%positive 215%positive 301%positive 256%Z present Vundef 1 129 254 Vundef HookR (spec_done None)(fun _=>false)[]cs
 ltac:(lia)ltac:(lia)ltac:(unfold Int.max_unsigned,Int.modulus,Int.wordsize;cbn;lia)
 ltac:(lia)ltac:(unfold Int.max_unsigned,Int.modulus,Int.wordsize;cbn;lia)
 ltac:(repeat split;reflexivity)ltac:(reflexivity)ltac:(lia)ltac:(lia)ltac:(lia)
 HookRGood HookRCurLINV InitHook CreateHook).
Qed.
Theorem HookPostRaw : forall present cs result s,
 s |= HookPost present cs result ->
 s |= V293_rdy_raw_cells(HookCells true present)(HookFrame cs) ** Atrue.
Proof.
 intros present cs result s HS. apply HookPostView in HS.
 unfold HookLiteral in HS. clear -HS. sep auto.
Qed.
Theorem HookPostLoad : forall present cs result s a tp v,
 s |= HookPost present cs result -> In(a,tp,v)(HookCells true present) ->
 rule_type_val_match tp v=true -> load tp(getmem s)a=Some v.
Proof.
 intros present cs result s a tp v HS Member Valid.
 apply HookPostRaw in HS. eapply V293_star_load_l;[ |exact HS].
 intros st H. eapply V293_rdy_raw_load;eassumption.
Qed.
Theorem HookPriorityRead : forall present cs result s, s |= HookPost present cs result ->
 load (Tint8)(getmem s)(301%positive,178%Z)=Some(V293_byteval 11).
Proof.
 intros present cs result s HS. eapply HookPostLoad;[exact HS| | ].
 - destruct present;unfold HookCells,HookPublished,HookResidual,HookInputs;cbn[app tl];simpl;tauto.
 - destruct present;reflexivity.
Qed.
Theorem HookSlotRead : forall present cs result s, s |= HookPost present cs result ->
 load (Tptr V293_tcb_type)(getmem s)(211%positive,44%Z)=Some(HookHead).
Proof.
 intros present cs result s HS. eapply HookPostLoad;[exact HS| | ].
 - destruct present;unfold HookCells,HookPublished,HookResidual,HookInputs;cbn[app tl];simpl;tauto.
 - destruct present;reflexivity.
Qed.
Theorem HookFreeHeadRead : forall present cs result s, s |= HookPost present cs result ->
 load (Tptr V293_tcb_type)(getmem s)(210%positive,0%Z)=Some(HookNext).
Proof.
 intros present cs result s HS. eapply HookPostLoad;[exact HS| | ].
 - destruct present;unfold HookCells,HookPublished,HookResidual,HookInputs;cbn[app tl];simpl;tauto.
 - destruct present;reflexivity.
Qed.
Theorem HookNextRead : forall present cs result s, s |= HookPost present cs result ->
 load (Tcom_ptr 410%Z)(getmem s)(301%positive,148%Z)=Some(HookOldHead present).
Proof.
 intros present cs result s HS. eapply HookPostLoad;[exact HS| | ].
 - destruct present;unfold HookCells,HookPublished,HookResidual,HookInputs;cbn[app tl];simpl;tauto.
 - destruct present;reflexivity.
Qed.
Theorem HookPrevRead : forall present cs result s, s |= HookPost present cs result ->
 load (Tcom_ptr 410%Z)(getmem s)(301%positive,152%Z)=Some(Vnull).
Proof.
 intros present cs result s HS. eapply HookPostLoad;[exact HS| | ].
 - destruct present;unfold HookCells,HookPublished,HookResidual,HookInputs;cbn[app tl];simpl;tauto.
 - destruct present;reflexivity.
Qed.
Theorem HookHeadRead : forall present cs result s, s |= HookPost present cs result ->
 load (Tptr V293_tcb_type)(getmem s)(212%positive,0%Z)=Some(HookHead).
Proof.
 intros present cs result s HS. eapply HookPostLoad;[exact HS| | ].
 - destruct present;unfold HookCells,HookPublished,HookResidual,HookInputs;cbn[app tl];simpl;tauto.
 - destruct present;reflexivity.
Qed.
Theorem HookGroupRead : forall present cs result s, s |= HookPost present cs result ->
 load (Tint8)(getmem s)(213%positive,0%Z)=Some(V293_byteval 3).
Proof.
 intros present cs result s HS. eapply HookPostLoad;[exact HS| | ].
 - destruct present;unfold HookCells,HookPublished,HookResidual,HookInputs;cbn[app tl];simpl;tauto.
 - destruct present;reflexivity.
Qed.
Theorem HookRowRead : forall present cs result s, s |= HookPost present cs result ->
 load (Tint8)(getmem s)(214%positive,1%Z)=Some(V293_byteval 137).
Proof.
 intros present cs result s HS. eapply HookPostLoad;[exact HS| | ].
 - destruct present;unfold HookCells,HookPublished,HookResidual,HookInputs;cbn[app tl];simpl;tauto.
 - destruct present;reflexivity.
Qed.
Theorem HookCounterRead : forall present cs result s, s |= HookPost present cs result ->
 load (Tint8)(getmem s)(215%positive,0%Z)=Some(V293_byteval 255).
Proof.
 intros present cs result s HS. eapply HookPostLoad;[exact HS| | ].
 - destruct present;unfold HookCells,HookPublished,HookResidual,HookInputs;cbn[app tl];simpl;tauto.
 - destruct present;reflexivity.
Qed.
Theorem HookSizeRead : forall present cs result s, s |= HookPost present cs result ->
 load (Tint32)(getmem s)(301%positive,140%Z)=Some(Vint32(Int.repr 128)).
Proof.
 intros present cs result s HS. eapply HookPostLoad;[exact HS| | ].
 - destruct present;unfold HookCells,HookPublished,HookResidual,HookInputs;cbn[app tl];simpl;tauto.
 - destruct present;reflexivity.
Qed.
Theorem HookOldBacklinkRead : forall cs result s, s |= HookPost true cs result ->
 load(Tcom_ptr 410%Z)(getmem s)(301%positive,280%Z)=Some HookHead.
Proof.
 intros cs result s HS. eapply HookPostLoad;[exact HS| |reflexivity].
 unfold HookCells,HookPublished;cbn[app]. do 10 right;left;reflexivity.
Qed.
Theorem HookWrongFreeHead : forall present cs result s, s |= HookPost present cs result ->
 load(Tptr V293_tcb_type)(getmem s)(210%positive,0%Z)<>Some HookHead.
Proof. intros. rewrite(HookFreeHeadRead _ _ _ _ H). unfold HookNext,HookHead. intro E. inversion E. Qed.
Theorem HookReturnedZero : forall present cs result s, s |= HookPost present cs result -> result=Some(Vint32 Int.zero).
Proof.
 intros present cs result s HS. apply HookPostView in HS. apply astar_l_apure_elim in HS. tauto.
Qed.
Theorem HookCoreSize : forall present,
 length(HookCells false present)=(if present then 36 else 35) /\
 length(HookCells true present)=(if present then 36 else 35) /\
 fold_right(fun cell count=>typelen(snd(fst cell))+count)0(HookCells false present)=(if present then 100 else 96) /\
 fold_right(fun cell count=>typelen(snd(fst cell))+count)0(HookCells true present)=(if present then 100 else 96).
Proof. destruct present;repeat split;reflexivity. Qed.

Require Import CertiOS.certiucos.v293.proofs.V293TCBHookCall.

Lemma HookRFun : GoodFunAsrt HookR.
Proof.
 cbn [HookR CurTid LINV V293_witness_li Agvarmapsto Agvarenv' Aptrmapsto GoodFunAsrt].
 repeat split;exact I.
Qed.
Definition HookOwned slot present := V293_hook_owned_cells 211%positive slot 210%positive 301%positive 128%Z 11
 Vnull Vnull(Vint32 Int.zero)(Vint32(Int.repr 128))Vnull(Vint32 Int.zero) HookNext
 212%positive 213%positive 214%positive 215%positive 301%positive 256%Z present Vundef 1 129 254 Vundef.
Definition HookResource slot present cs := V293_hook_resource(HookOwned slot present) HookR
 (spec_done None)(fun _=>false)[]cs.
Definition HookResourceGood slot present cs := V293_hook_resource_good(HookOwned slot present)HookR
 (spec_done None)(fun _=>false)[]cs HookRFun.
Definition HookFpre slot present cs := V293_hook_fpre HookHead HookTid(HookResource slot present cs)(HookResourceGood slot present cs).
Definition HookFpost slot present cs := V293_hook_fpost HookHead HookTid(HookResource slot present cs)(HookResourceGood slot present cs).

Definition HookBodyChecked : forall Spec sd I hi hc present cs,
 Spec hi=Some(HookFpre Vundef present cs,HookFpost Vundef present cs,(Tvoid,[Tptr V293_tcb_type])) ->
 Spec hc=Some(HookFpre HookHead present cs,HookFpost HookHead present cs,(Tvoid,[Tptr V293_tcb_type])) ->
 InfRules Spec sd V293_witness_li I(HookPost present cs)Afalse
 (HookPre present cs)(V293_TCBInit_function_body hi hc)Afalse HookTid.
Proof.
 intros Spec sd I hi hc present cs InitLookup CreateLookup.
 exact(V293_OS_TCBInit_hook_calls_body_hoare Spec sd V293_witness_li I HookTid hi hc Vundef(fun _=>Vundef)Vundef Vundef
 211%positive 210%positive 209%positive 201%positive 202%positive 203%positive 204%positive 205%positive 206%positive 207%positive 208%positive 301%positive 128%Z 11 Vnull Vnull (Vint32 Int.zero) (Vint32(Int.repr 128)) Vnull (Vint32 Int.zero) HookNext 212%positive 213%positive 214%positive 215%positive 301%positive 256%Z present Vundef 1 129 254 Vundef HookR (spec_done None)(fun _=>false)[]cs
 ltac:(lia)ltac:(lia)ltac:(unfold Int.max_unsigned,Int.modulus,Int.wordsize;cbn;lia)
 ltac:(lia)ltac:(unfold Int.max_unsigned,Int.modulus,Int.wordsize;cbn;lia)
 ltac:(repeat split;reflexivity)ltac:(reflexivity)ltac:(lia)ltac:(lia)ltac:(lia)
 HookRGood HookRCurLINV HookRFun InitLookup CreateLookup).
Qed.
Definition HookAtCallCore (written:bool) : list V293_record_cell :=
 ((211%positive,44%Z),Tptr V293_tcb_type,if written then HookHead else Vundef)::
 ((209%positive,0%Z),Tint32,Vint32 Int.zero)::
 (HookFinal++HookInputs HookHead++
 [((210%positive,0%Z),Tptr V293_tcb_type,HookNext);
  ((301%positive,148%Z),Tcom_ptr 410%Z,HookNext)]).
Definition HookAtCallCells written present := HookAtCallCore written++HookExtra present.
Definition HookAtCallWhole written present := merge(HookMemory(HookAtCallCells written present))(merge HookCurrent HookSentinel).
Definition HookAtCallLiteral written present cs := <||spec_done None||> **
 V293_rdy_raw_cells(HookAtCallCells written present)(HookFrame cs).
Theorem HookAtCallRawLiteral : forall written present cs,
 HookState(HookMemory(HookAtCallCells written present))cs |= V293_rdy_raw_cells(HookAtCallCells written present)Aemp.
Proof.
 intros written present cs. destruct written,present;
 unfold HookAtCallCells,HookAtCallCore,HookExtra,HookOldHead,
 HookFinal,HookInputs,HookHead,HookNext;
 cbn [app tl HookMemory V293_rdy_raw_cells];HookRawTactic.
Qed.
Theorem HookAtCallLiteralEntry : forall written present cs,
 HookState(HookAtCallWhole written present)cs |= HookAtCallLiteral written present cs.
Proof.
 intros written present cs. unfold HookLiteral.
 eapply HookStar with(m1:=emp)(m2:=HookAtCallWhole written present).
 - apply map_join_comm;apply map_join_emp.
 - split;[reflexivity| ]. split;reflexivity.
 - apply V293_raw_cells_join. unfold HookAtCallWhole.
   eapply HookStar with(m1:=HookMemory(HookAtCallCells written present))(m2:=merge HookCurrent HookSentinel).
   + apply map_join_merge;apply map_disjoint;intros[b off].
     destruct(Pos.eq_dec b 402%positive);[subst b;left| ].
     * destruct written,present;unfold HookAtCallCells,HookAtCallCore,HookExtra,HookFinal,HookInputs;cbn[app tl HookMemory];HookOutside.
     * destruct(Pos.eq_dec b 601%positive);[subst b;left|right;left].
       -- destruct written,present;unfold HookAtCallCells,HookAtCallCore,HookExtra,HookFinal,HookInputs;cbn[app tl HookMemory];HookOutside.
       -- unfold HookCurrent,HookSentinel,HookBytes. rewrite map_merge_semp by reflexivity.
          rewrite !V293_encoded_memory_outside by(left;congruence). reflexivity.
   + apply HookAtCallRawLiteral.
   + unfold HookFrame. eapply HookStar with(m1:=emp)(m2:=merge HookCurrent HookSentinel).
     * apply map_join_comm;apply map_join_emp.
     * repeat(eapply HookStar with(m1:=emp)(m2:=emp);
       [apply map_join_emp|split;[reflexivity|split;reflexivity]| ]).
       split;[reflexivity|split;reflexivity].
     * eapply HookStar with(m1:=emp)(m2:=merge HookCurrent HookSentinel).
       -- apply map_join_comm;apply map_join_emp.
       -- apply HookBindingsSpatial.
       -- eapply HookStar with(m1:=emp)(m2:=merge HookCurrent HookSentinel).
          ++ apply map_join_comm;apply map_join_emp.
          ++ apply HookTableSpatial.
          ++ eapply HookStar with(m1:=emp)(m2:=merge HookCurrent HookSentinel).
             ** apply map_join_comm;apply map_join_emp.
             ** apply HookPubBindingsSpatial.
             ** apply HookRSpatial.
Qed.

Theorem HookAtCallView : forall written present cs,
 HookAtCallLiteral written present cs ==> HookHookState(if written then HookHead else Vundef)present cs.
Proof.
 intros written present cs. unfold HookAtCallLiteral,HookHookState,V293_tcb_table_state,HookAtCallCells,HookFrame,HookExtension.
 change (<||spec_done None||> ** V293_rdy_raw_cells (HookAtCallCore written++HookExtra present)(HookFrame cs) ==>
 <||spec_done None||> ** V293_rdy_raw_cells (HookAtCallCore written)
 (OS[(fun _=>false),false,[],cs] ** (HookBindings ** (V293_tcb_table_binding 211%positive ** HookExtension present)))).
 unfold HookFrame,HookExtension. apply astar_mono;[intros s H;exact H| ].
 rewrite V293_raw_cells_append. apply V293_raw_cells_mono. intros s HS.
 assert(H:s |= V293_rdy_raw_cells(HookExtra present)
 ((OS[(fun _=>false),false,[],cs] ** (HookBindings ** V293_tcb_table_binding 211%positive)) ** (HookPubBindings ** HookR))).
 { eapply V293_raw_cells_mono;[ |exact HS]. intros st Hst. clear -Hst. sep auto. }
 apply V293_raw_cells_move_frame in H. clear -H. sep auto.
Qed.
Theorem HookAtCallEntry : forall written present cs,
 HookState(HookAtCallWhole written present)cs |= HookHookState(if written then HookHead else Vundef)present cs.
Proof. intros. apply HookAtCallView. apply HookAtCallLiteralEntry. Qed.
Theorem HookArgumentRead : forall slot present cs s,
 s |= HookHookState slot present cs ->
 s |= Rvl[evar 108%Z]@[Tptr V293_tcb_type]==[HookHead].
Proof. intros slot present cs s HS. eapply V293_tcb_hook_argument;exact HS. Qed.
Theorem HookCallSiteChecked : forall Spec sd I r ri f slot present cs,
 Spec f=Some(HookFpre slot present cs,HookFpost slot present cs,(Tvoid,[Tptr V293_tcb_type])) ->
 InfRules Spec sd V293_witness_li I r ri (HookHookState slot present cs)
 (scall f[evar 108%Z])(HookHookState slot present cs)HookTid.
Proof.
 intros. eapply V293_tcb_hook_call;[exact HookRCurLINV|exact H].
Qed.
Theorem HookArgumentNotNext : forall slot present cs s,
 s |= HookHookState slot present cs ->
 ~(s |= Rvl[evar 108%Z]@[Tptr V293_tcb_type]==[HookNext]).
Proof.
 intros slot present cs s HS Wrong. pose proof(HookArgumentRead slot present cs s HS) as Right.
 cbn [sat evalexprlist] in Right,Wrong. destruct Right as [R _],Wrong as [W _].
 rewrite R in W. vm_compute in W. discriminate W.
Qed.
Theorem HookPreRejectsWrongPointer : forall slot present cs s,
 ~(s |= getasrt(HookFpre slot present cs [HookNext][]HookTid)).
Proof.
 intros slot present cs s HS. cbn [HookFpre V293_hook_fpre getasrt] in HS.
 apply astar_l_apure_elim in HS. destruct HS as [[Eq _] _]. vm_compute in Eq. discriminate Eq.
Qed.
Theorem HookPostRejectsValueReturn : forall slot present cs s,
 ~(s |= getasrt(HookFpost slot present cs [HookHead](Some(Vint32 Int.zero))[]HookTid)).
Proof.
 intros slot present cs s HS. cbn [HookFpost V293_hook_fpost getasrt] in HS.
 apply astar_l_apure_elim in HS. destruct HS as [[_ [_ Eq]] _]. discriminate Eq.
Qed.
Theorem HookFootprint : forall slot present,
 length(HookOwned slot present)=(if present then 27 else 26) /\
 length(V293_hook_local_cells 209%positive 201%positive 202%positive 203%positive 204%positive 205%positive
 206%positive 207%positive 208%positive 301%positive 128%Z 11
 Vnull Vnull(Vint32 Int.zero)(Vint32(Int.repr 128))Vnull(Vint32 Int.zero))=9.
Proof. intros slot present. destruct present;vm_compute;split;reflexivity. Qed.
(* This finite table witnesses lookup consistency ONLY. No Hook body is supplied. *)
Definition HookDeclaredSpec present cs : funspec := fun f =>
 if Z.eq_dec f 501%Z then Some(HookFpre Vundef present cs,HookFpost Vundef present cs,(Tvoid,[Tptr V293_tcb_type]))
 else if Z.eq_dec f 502%Z then Some(HookFpre HookHead present cs,HookFpost HookHead present cs,(Tvoid,[Tptr V293_tcb_type]))
 else None.
Theorem HookInitLookup : forall present cs,
 HookDeclaredSpec present cs 501%Z=Some(HookFpre Vundef present cs,HookFpost Vundef present cs,(Tvoid,[Tptr V293_tcb_type])).
Proof. intros. unfold HookDeclaredSpec. destruct(Z.eq_dec 501%Z 501%Z);[reflexivity|contradiction]. Qed.
Theorem HookCreateLookup : forall present cs,
 HookDeclaredSpec present cs 502%Z=Some(HookFpre HookHead present cs,HookFpost HookHead present cs,(Tvoid,[Tptr V293_tcb_type])).
Proof.
 intros. unfold HookDeclaredSpec. destruct(Z.eq_dec 502%Z 501%Z);[discriminate| ].
 destruct(Z.eq_dec 502%Z 502%Z);[reflexivity|contradiction].
Qed.
Theorem HookBodyUnderDeclaredContracts : forall sd I present cs,
 InfRules(HookDeclaredSpec present cs)sd V293_witness_li I(HookPost present cs)Afalse
 (HookPre present cs)(V293_TCBInit_function_body 501%Z 502%Z)Afalse HookTid.
Proof. intros. apply HookBodyChecked;[apply HookInitLookup|apply HookCreateLookup]. Qed.
