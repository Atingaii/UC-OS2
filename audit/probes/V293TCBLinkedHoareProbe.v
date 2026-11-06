(* Independent literal full-body resources, no old probe dependency; TWO Hooks remain open. *)
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
Definition LinkOld : list V293_record_cell :=
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
Definition LinkInputs pc : list V293_record_cell :=
 [((201%positive,0%Z),(Tptr V293_tcb_type),(pc));
  ((202%positive,0%Z),(Tint8),(V293_byteval 11));
  ((203%positive,0%Z),(Tptr Tint32),(Vnull));
  ((204%positive,0%Z),(Tptr Tint32),(Vnull));
  ((205%positive,0%Z),(Tint16),(Vint32 Int.zero));
  ((206%positive,0%Z),(Tint32),(Vint32(Int.repr 128)));
  ((207%positive,0%Z),(Tptr Tvoid),(Vnull));
  ((208%positive,0%Z),(Tint16),(Vint32 Int.zero))].
Definition LinkFinal : list V293_record_cell :=
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
Definition LinkGE : env := set (set (set (set (set (set (sig OSTCBCur (402%positive,Tptr Tvoid))
 91%Z (210%positive,Tptr V293_tcb_type)) 92%Z (211%positive,Tarray (Tptr V293_tcb_type) 13))
 93%Z (212%positive,Tptr V293_tcb_type)) 94%Z (213%positive,Tint8))
 95%Z (214%positive,Tarray Tint8 2)) 96%Z (215%positive,Tint8).
Definition LinkLE : env :=
 set (set (set (set (set (set (set (set (set (emp:env)
 108%Z (201%positive,Tptr V293_tcb_type)) 101%Z (202%positive,Tint8))
 102%Z (203%positive,Tptr Tint32)) 103%Z (204%positive,Tptr Tint32))
 104%Z (205%positive,Tint16)) 105%Z (206%positive,Tint32))
 106%Z (207%positive,Tptr Tvoid)) 107%Z (208%positive,Tint16)) 109%Z (209%positive,Tint32).
Definition LinkTid : tid := (301%positive,Int.repr 8).
Definition LinkBytes b permission tp v := V293_encoded_memory b 0 permission (encode_val tp v).
Definition LinkCurrent := LinkBytes 402%positive false (Tptr Tvoid) (Vptr LinkTid).
Definition LinkSentinel := LinkBytes 601%positive true Tint8 (Vint32(Int.repr 77)).
Fixpoint LinkMemory (cells : list V293_record_cell) : mem :=
 match cells with []=>emp | ((b,i),tp,v)::tail=>
 merge (V293_encoded_memory b i true (encode_val tp v)) (LinkMemory tail) end.
Definition LinkHead := Vptr(301%positive,Int.repr 128).
Definition LinkNext := Vptr(301%positive,Int.repr 384).
Definition LinkOldHead (present:bool) := if present then Vptr(301%positive,Int.repr 256) else Vnull.
Definition LinkExtra (present:bool) : list V293_record_cell :=
 [((301%positive,152%Z),Tcom_ptr 410%Z,Vundef);
  ((212%positive,0%Z),Tptr V293_tcb_type,LinkOldHead present);
  ((213%positive,0%Z),Tint8,V293_byteval 1);
  ((214%positive,1%Z),Tint8,V293_byteval 129);
  ((215%positive,0%Z),Tint8,V293_byteval 254)] ++
 if present then [((301%positive,280%Z),Tcom_ptr 410%Z,Vundef)] else [].
Definition LinkPreCells : list V293_record_cell :=
 ((211%positive,44%Z),Tptr V293_tcb_type,Vundef)::
 ((209%positive,0%Z),Tint32,Vundef)::
 (LinkOld++LinkInputs Vundef++
 [((210%positive,0%Z),Tptr V293_tcb_type,LinkHead);
  ((301%positive,148%Z),Tcom_ptr 410%Z,LinkNext)]).
Definition LinkResidual : list V293_record_cell :=
 [((211%positive,44%Z),Tptr V293_tcb_type,LinkHead);
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
  ((301%positive,160%Z),Tptr Tvoid,Vnull)] ++ tl(LinkInputs LinkHead) ++
 [((210%positive,0%Z),Tptr V293_tcb_type,LinkNext)].
Definition LinkPublished (present:bool) : list V293_record_cell :=
 [((201%positive,0%Z),Tptr V293_tcb_type,LinkHead);
  ((301%positive,148%Z),Tcom_ptr 410%Z,LinkOldHead present);
  ((301%positive,152%Z),Tcom_ptr 410%Z,Vnull);
  ((301%positive,180%Z),Tint8,V293_byteval 1);
  ((301%positive,182%Z),Tint8,V293_byteval 2);
  ((301%positive,181%Z),Tint8,V293_byteval 8);
  ((212%positive,0%Z),Tptr V293_tcb_type,LinkHead);
  ((213%positive,0%Z),Tint8,V293_byteval 3);
  ((214%positive,1%Z),Tint8,V293_byteval 137);
  ((215%positive,0%Z),Tint8,V293_byteval 255)] ++
 if present then [((301%positive,280%Z),Tcom_ptr 410%Z,LinkHead)] else [].
Definition LinkCells (initialized present:bool) :=
 if initialized then LinkPublished present++LinkResidual else LinkPreCells++LinkExtra present.
Definition LinkWhole initialized present := merge(LinkMemory(LinkCells initialized present))(merge LinkCurrent LinkSentinel).
Definition LinkState M cs : RstateOP :=
 (LinkGE,LinkLE,M,(fun _=>false),(false,[],cs),(emp:osabst),spec_done None).
Definition LinkR := CurTid LinkTid ** LINV V293_witness_li LinkTid [] **
 Amapsto(601%positive,0%Z) Tint8 true(Vint32(Int.repr 77)).
Definition LinkFieldBindings := V293_tcb_fields_bindings 108%Z 101%Z 102%Z 103%Z 104%Z 105%Z 106%Z 107%Z
 201%positive 202%positive 203%positive 204%positive 205%positive 206%positive 207%positive 208%positive.
Definition LinkBindings := LinkFieldBindings ** V293_tcb_success_extra 210%positive 209%positive.
Definition LinkPubBindings := V293_pub_bindings 108%Z 93%Z 94%Z 95%Z 96%Z 201%positive 212%positive 213%positive 214%positive 215%positive.
Definition LinkFrame cs := OS[(fun _=>false),false,[],cs] **
 (LinkBindings ** (V293_tcb_table_binding 211%positive ** (LinkPubBindings ** LinkR))).
Definition LinkLiteral initialized present cs := <||spec_done None||> ** V293_rdy_raw_cells(LinkCells initialized present)(LinkFrame cs).
Definition LinkExtension present := V293_rdy_raw_cells(LinkExtra present)(LinkPubBindings ** LinkR).
Definition LinkPre present cs := <||spec_done None||> ** V293_rdy_raw_cells LinkPreCells
 (OS[(fun _=>false),false,[],cs] ** (LinkBindings ** (V293_tcb_table_binding 211%positive ** LinkExtension present))).
Definition LinkPost present cs : retasrt :=
 V293_link_return_post 211%positive 210%positive 209%positive 201%positive 202%positive 203%positive 204%positive
 205%positive 206%positive 207%positive 208%positive 301%positive 128%Z 11
 Vnull Vnull (Vint32 Int.zero) (Vint32(Int.repr 128)) Vnull (Vint32 Int.zero) LinkNext
 212%positive 213%positive 214%positive 215%positive 301%positive 256%Z present 1 129 254 LinkR
 (spec_done None)(fun _=>false)[]cs.
Lemma LinkStar : forall m1 m2 m cs p q,
 join m1 m2 m -> LinkState m1 cs |= p -> LinkState m2 cs |= q ->
 LinkState m cs |= p ** q.
Proof.
 intros. apply sat_split'. exists m1. exists m2.
 exists(emp:osabst). exists(emp:osabst).
 split;[exact H | ]. split;[apply map_join_emp | ]. split;assumption.
Qed.
Lemma LinkCurrentSpatial : forall cs, LinkState LinkCurrent cs |= CurTid LinkTid.
Proof.
 intro cs. exists Tvoid. exists 402%positive.
 eapply LinkStar with (m1:=emp) (m2:=LinkCurrent).
 - apply map_join_comm;apply map_join_emp.
 - exists 402%positive. split;[vm_compute;reflexivity | ]. repeat split;reflexivity.
 - split;[apply V293_encoded_memory_mapsto|reflexivity].
Qed.
Lemma LinkLInvSpatial : forall cs, LinkState emp cs |= LINV V293_witness_li LinkTid [].
Proof.
 intro cs. unfold LINV. apply astar_comm. apply astar_l_apure_intro.
 - split;reflexivity.
 - apply V293_witness_li_good.
Qed.
Ltac LinkFrameApart b :=
 apply map_join_merge;apply map_disjoint;intros [other offset];
 destruct(Pos.eq_dec other b);[subst other;right;left|left];
 unfold LinkCurrent,LinkSentinel,LinkBytes;
 repeat first [rewrite map_merge_semp by reflexivity |
 rewrite V293_encoded_memory_outside by (left;congruence)];reflexivity.
Lemma LinkRSpatial : forall cs,
 LinkState (merge LinkCurrent LinkSentinel) cs |= LinkR.
Proof.
 intro cs. unfold LinkR.
 eapply LinkStar with (m1:=LinkCurrent) (m2:=LinkSentinel).
 - LinkFrameApart 402%positive.
 - apply LinkCurrentSpatial.
 - eapply LinkStar with (m1:=emp) (m2:=LinkSentinel).
   + apply map_join_comm;apply map_join_emp.
   + apply LinkLInvSpatial.
   + split;[apply V293_encoded_memory_mapsto|reflexivity].
Qed.
Lemma LinkRGood : GoodFrm LinkR.
Proof. cbn [LinkR CurTid LINV V293_witness_li GoodFrm]. repeat split;exact I. Qed.
Lemma LinkRCurLINV : LinkR ==> CurLINV V293_witness_li LinkTid.
Proof.
 intros s HS. unfold CurLINV. exists([]:list logicvar).
 unfold LinkR in HS. clear -HS. sep auto.
Qed.
Lemma LinkFieldBindingsSpatial : forall cs, LinkState emp cs |= LinkFieldBindings.
Proof.
 intro cs. unfold LinkFieldBindings,V293_tcb_fields_bindings. repeat split.
 - exists 201%positive. split;[vm_compute;reflexivity | ]. repeat split;reflexivity.
 - exists 202%positive. split;[vm_compute;reflexivity | ]. repeat split;reflexivity.
 - exists 203%positive. split;[vm_compute;reflexivity | ]. repeat split;reflexivity.
 - exists 204%positive. split;[vm_compute;reflexivity | ]. repeat split;reflexivity.
 - exists 205%positive. split;[vm_compute;reflexivity | ]. repeat split;reflexivity.
 - exists 206%positive. split;[vm_compute;reflexivity | ]. repeat split;reflexivity.
 - exists 207%positive. split;[vm_compute;reflexivity | ]. repeat split;reflexivity.
 - exists 208%positive. split;[vm_compute;reflexivity | ]. repeat split;reflexivity.
Qed.
Lemma LinkBindingsSpatial : forall cs, LinkState emp cs |= LinkBindings.
Proof.
 intro cs. unfold LinkBindings. eapply LinkStar with (m1:=emp) (m2:=emp).
 - apply map_join_emp.
 - apply LinkFieldBindingsSpatial.
 - unfold V293_tcb_success_extra. repeat split.
   + exists 209%positive. split;[vm_compute;reflexivity| ]. repeat split;reflexivity.
   + exists 210%positive. split;[vm_compute;reflexivity| ]. repeat split;reflexivity.
   + intros [v H]. vm_compute in H. discriminate H.
Qed.
Ltac LinkOutside :=
 repeat first [rewrite V293_encoded_memory_outside by
 (first [left;congruence | right;rewrite ?encode_val_length;cbn [V293_byteval length encode_val typelen list_repeat inj_pointer inj_bytes encode_int List.map];lia])
 |rewrite map_merge_semp by reflexivity];reflexivity.
Ltac LinkApart b start count :=
 apply map_join_merge;apply map_disjoint;intros [other off];
 destruct (Pos.eq_dec other b) as [B|B];
 [subst other;destruct (Z_lt_dec off start) as [Low|Low];
 [left;apply V293_encoded_memory_outside;right;left;exact Low |
 destruct (Z_lt_dec off (start+count)) as [Inside|Outside];
 [right;left;LinkOutside |left;apply V293_encoded_memory_outside;right;right;
 rewrite ?encode_val_length;cbn [V293_byteval length encode_val typelen list_repeat inj_pointer inj_bytes encode_int List.map];lia]] |
 left;apply V293_encoded_memory_outside;left;exact B].

Lemma LinkTableSpatial : forall cs, LinkState emp cs |= V293_tcb_table_binding 211%positive.
Proof.
 intro cs. unfold V293_tcb_table_binding. repeat split.
 - exists 211%positive. split;[vm_compute;reflexivity| ]. repeat split;reflexivity.
 - intros [v H]. vm_compute in H. discriminate H.
Qed.
Lemma LinkPubBindingsSpatial : forall cs, LinkState emp cs |= LinkPubBindings.
Proof.
 intro cs. unfold LinkPubBindings,V293_pub_bindings. repeat split.
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

Ltac LinkRawTactic :=
 lazymatch goal with
 | |- LinkState (merge (V293_encoded_memory ?b ?off true (encode_val ?tp ?v)) ?tail) ?cs |= _ =>
   let bytes := eval cbv in (Z.of_nat(typelen tp)) in
   eapply LinkStar with(m1:=V293_encoded_memory b off true(encode_val tp v));
   [LinkApart b off bytes|split;[apply V293_encoded_memory_mapsto|reflexivity]|LinkRawTactic]
 | |- LinkState emp _ |= Aemp => split;reflexivity
 end.
Theorem LinkRawLiteral : forall initialized present cs,
 LinkState(LinkMemory(LinkCells initialized present))cs |= V293_rdy_raw_cells(LinkCells initialized present)Aemp.
Proof.
 intros initialized present cs. destruct initialized,present;
 unfold LinkCells,LinkPublished,LinkResidual,LinkPreCells,LinkExtra,LinkOldHead,
 LinkOld,LinkInputs,LinkHead,LinkNext;
 cbn [app tl LinkMemory V293_rdy_raw_cells];LinkRawTactic.
Qed.
Theorem LinkLiteralEntry : forall initialized present cs,
 LinkState(LinkWhole initialized present)cs |= LinkLiteral initialized present cs.
Proof.
 intros initialized present cs. unfold LinkLiteral.
 eapply LinkStar with(m1:=emp)(m2:=LinkWhole initialized present).
 - apply map_join_comm;apply map_join_emp.
 - split;[reflexivity| ]. split;reflexivity.
 - apply V293_raw_cells_join. unfold LinkWhole.
   eapply LinkStar with(m1:=LinkMemory(LinkCells initialized present))(m2:=merge LinkCurrent LinkSentinel).
   + apply map_join_merge;apply map_disjoint;intros[b off].
     destruct(Pos.eq_dec b 402%positive);[subst b;left| ].
     * destruct initialized,present;unfold LinkCells,LinkPublished,LinkResidual,LinkPreCells,LinkExtra,LinkOld,LinkInputs;cbn[app tl LinkMemory];LinkOutside.
     * destruct(Pos.eq_dec b 601%positive);[subst b;left|right;left].
       -- destruct initialized,present;unfold LinkCells,LinkPublished,LinkResidual,LinkPreCells,LinkExtra,LinkOld,LinkInputs;cbn[app tl LinkMemory];LinkOutside.
       -- unfold LinkCurrent,LinkSentinel,LinkBytes. rewrite map_merge_semp by reflexivity.
          rewrite !V293_encoded_memory_outside by(left;congruence). reflexivity.
   + apply LinkRawLiteral.
   + unfold LinkFrame. eapply LinkStar with(m1:=emp)(m2:=merge LinkCurrent LinkSentinel).
     * apply map_join_comm;apply map_join_emp.
     * repeat(eapply LinkStar with(m1:=emp)(m2:=emp);
       [apply map_join_emp|split;[reflexivity|split;reflexivity]| ]).
       split;[reflexivity|split;reflexivity].
     * eapply LinkStar with(m1:=emp)(m2:=merge LinkCurrent LinkSentinel).
       -- apply map_join_comm;apply map_join_emp.
       -- apply LinkBindingsSpatial.
       -- eapply LinkStar with(m1:=emp)(m2:=merge LinkCurrent LinkSentinel).
          ++ apply map_join_comm;apply map_join_emp.
          ++ apply LinkTableSpatial.
          ++ eapply LinkStar with(m1:=emp)(m2:=merge LinkCurrent LinkSentinel).
             ** apply map_join_comm;apply map_join_emp.
             ** apply LinkPubBindingsSpatial.
             ** apply LinkRSpatial.
Qed.
Theorem LinkInitialView : forall present cs, LinkLiteral false present cs ==> LinkPre present cs.
Proof.
 intros present cs. unfold LinkLiteral,LinkPre,LinkCells,LinkFrame,LinkExtension.
 apply astar_mono;[intros s H;exact H| ].
 rewrite V293_raw_cells_append. apply V293_raw_cells_mono. intros s HS.
 assert(H : s |= V293_rdy_raw_cells(LinkExtra present)
 ((OS[(fun _=>false),false,[],cs] ** (LinkBindings ** V293_tcb_table_binding 211%positive)) ** (LinkPubBindings ** LinkR))).
 { eapply V293_raw_cells_mono;[ |exact HS]. intros st Hst. clear -Hst. sep auto. }
 apply V293_raw_cells_move_frame in H. clear -H. sep auto.
Qed.
Theorem LinkInitialEntry : forall present cs,
 LinkState(LinkWhole false present)cs |= LinkPre present cs.
Proof. intros. apply LinkInitialView. apply LinkLiteralEntry. Qed.

Theorem LinkPostView : forall present cs result s,
 (s |= LinkPost present cs result) <->
 (s |= [|result=Some(Vint32 Int.zero)|] ** LinkLiteral true present cs).
Proof.
 intros present cs result s. unfold LinkPost,V293_link_return_post,V293_pub_return_post,
 V293_pub_hstate,V293_link_residual_frame.
 change ((s |= [|result=Some(Vint32 Int.zero)|] ** (<||spec_done None||> **
 V293_rdy_raw_cells(LinkPublished present)
 (OS[(fun _=>false),false,[],cs] ** (LinkPubBindings **
 V293_rdy_raw_cells LinkResidual(LinkBindings ** (V293_tcb_table_binding 211%positive ** LinkR)))))) <->
 (s |= [|result=Some(Vint32 Int.zero)|] ** LinkLiteral true present cs)).
 unfold LinkLiteral,LinkCells,LinkFrame. rewrite V293_raw_cells_append.
 split;intro HS.
 - eapply astar_mono;[intros st H;exact H| |exact HS].
   apply astar_mono;[intros st H;exact H| ];apply V293_raw_cells_mono;intros st H.
   assert(K : st |= (OS[(fun _=>false),false,[],cs] ** LinkPubBindings) **
   V293_rdy_raw_cells LinkResidual(LinkBindings ** (V293_tcb_table_binding 211%positive ** LinkR))).
   { clear -H. sep auto. }
   apply V293_raw_cells_unmove_frame in K.
   eapply V293_raw_cells_mono;[ |exact K]. intros st1 H1. clear -H1. sep auto.
 - eapply astar_mono;[intros st H;exact H| |exact HS].
   apply astar_mono;[intros st H;exact H| ];apply V293_raw_cells_mono;intros st H.
   assert(K : st |= V293_rdy_raw_cells LinkResidual
   ((OS[(fun _=>false),false,[],cs] ** LinkPubBindings) ** (LinkBindings ** (V293_tcb_table_binding 211%positive ** LinkR)))).
   { eapply V293_raw_cells_mono;[ |exact H]. intros st1 H1. clear -H1. sep auto. }
   apply V293_raw_cells_move_frame in K. clear -K. sep auto.
Qed.
Theorem LinkFinalEntry : forall present cs,
 LinkState(LinkWhole true present)cs |= LinkPost present cs(Some(Vint32 Int.zero)).
Proof.
 intros. apply LinkPostView. apply astar_l_apure_intro;[apply LinkLiteralEntry|reflexivity].
Qed.
Definition LinkHookState slot present cs :=
 V293_tcb_table_state 211%positive slot 210%positive 209%positive 201%positive 202%positive 203%positive 204%positive
 205%positive 206%positive 207%positive 208%positive 301%positive 128%Z 11
 Vnull Vnull(Vint32 Int.zero)(Vint32(Int.repr 128))Vnull(Vint32 Int.zero)
 LinkFinal LinkHead(Vint32 Int.zero)LinkNext LinkNext(LinkExtension present)(spec_done None)(fun _=>false)[]cs.
Definition LinkBodyChecked : forall Spec sd I hi hc present cs,
 InfRules Spec sd V293_witness_li I(LinkPost present cs)Afalse
 (LinkHookState Vundef present cs)(scall hi[evar 108%Z])(LinkHookState Vundef present cs)LinkTid ->
 InfRules Spec sd V293_witness_li I(LinkPost present cs)Afalse
 (LinkHookState LinkHead present cs)(scall hc[evar 108%Z])(LinkHookState LinkHead present cs)LinkTid ->
 InfRules Spec sd V293_witness_li I(LinkPost present cs)Afalse
 (LinkPre present cs)(V293_TCBInit_function_body hi hc)Afalse LinkTid.
Proof.
 intros Spec sd I hi hc present cs InitHook CreateHook.
 exact(V293_OS_TCBInit_linked_body_hoare Spec sd V293_witness_li I LinkTid hi hc Vundef(fun _=>Vundef)Vundef Vundef
 211%positive 210%positive 209%positive 201%positive 202%positive 203%positive 204%positive 205%positive 206%positive 207%positive 208%positive 301%positive 128%Z 11 Vnull Vnull (Vint32 Int.zero) (Vint32(Int.repr 128)) Vnull (Vint32 Int.zero) LinkNext 212%positive 213%positive 214%positive 215%positive 301%positive 256%Z present Vundef 1 129 254 Vundef LinkR (spec_done None)(fun _=>false)[]cs
 ltac:(lia)ltac:(lia)ltac:(unfold Int.max_unsigned,Int.modulus,Int.wordsize;cbn;lia)
 ltac:(lia)ltac:(unfold Int.max_unsigned,Int.modulus,Int.wordsize;cbn;lia)
 ltac:(repeat split;reflexivity)ltac:(reflexivity)ltac:(lia)ltac:(lia)ltac:(lia)
 LinkRGood LinkRCurLINV InitHook CreateHook).
Qed.
Theorem LinkPostRaw : forall present cs result s,
 s |= LinkPost present cs result ->
 s |= V293_rdy_raw_cells(LinkCells true present)(LinkFrame cs) ** Atrue.
Proof.
 intros present cs result s HS. apply LinkPostView in HS.
 unfold LinkLiteral in HS. clear -HS. sep auto.
Qed.
Theorem LinkPostLoad : forall present cs result s a tp v,
 s |= LinkPost present cs result -> In(a,tp,v)(LinkCells true present) ->
 rule_type_val_match tp v=true -> load tp(getmem s)a=Some v.
Proof.
 intros present cs result s a tp v HS Member Valid.
 apply LinkPostRaw in HS. eapply V293_star_load_l;[ |exact HS].
 intros st H. eapply V293_rdy_raw_load;eassumption.
Qed.
Theorem LinkPriorityRead : forall present cs result s, s |= LinkPost present cs result ->
 load (Tint8)(getmem s)(301%positive,178%Z)=Some(V293_byteval 11).
Proof.
 intros present cs result s HS. eapply LinkPostLoad;[exact HS| | ].
 - destruct present;unfold LinkCells,LinkPublished,LinkResidual,LinkInputs;cbn[app tl];simpl;tauto.
 - destruct present;reflexivity.
Qed.
Theorem LinkSlotRead : forall present cs result s, s |= LinkPost present cs result ->
 load (Tptr V293_tcb_type)(getmem s)(211%positive,44%Z)=Some(LinkHead).
Proof.
 intros present cs result s HS. eapply LinkPostLoad;[exact HS| | ].
 - destruct present;unfold LinkCells,LinkPublished,LinkResidual,LinkInputs;cbn[app tl];simpl;tauto.
 - destruct present;reflexivity.
Qed.
Theorem LinkFreeHeadRead : forall present cs result s, s |= LinkPost present cs result ->
 load (Tptr V293_tcb_type)(getmem s)(210%positive,0%Z)=Some(LinkNext).
Proof.
 intros present cs result s HS. eapply LinkPostLoad;[exact HS| | ].
 - destruct present;unfold LinkCells,LinkPublished,LinkResidual,LinkInputs;cbn[app tl];simpl;tauto.
 - destruct present;reflexivity.
Qed.
Theorem LinkNextRead : forall present cs result s, s |= LinkPost present cs result ->
 load (Tcom_ptr 410%Z)(getmem s)(301%positive,148%Z)=Some(LinkOldHead present).
Proof.
 intros present cs result s HS. eapply LinkPostLoad;[exact HS| | ].
 - destruct present;unfold LinkCells,LinkPublished,LinkResidual,LinkInputs;cbn[app tl];simpl;tauto.
 - destruct present;reflexivity.
Qed.
Theorem LinkPrevRead : forall present cs result s, s |= LinkPost present cs result ->
 load (Tcom_ptr 410%Z)(getmem s)(301%positive,152%Z)=Some(Vnull).
Proof.
 intros present cs result s HS. eapply LinkPostLoad;[exact HS| | ].
 - destruct present;unfold LinkCells,LinkPublished,LinkResidual,LinkInputs;cbn[app tl];simpl;tauto.
 - destruct present;reflexivity.
Qed.
Theorem LinkHeadRead : forall present cs result s, s |= LinkPost present cs result ->
 load (Tptr V293_tcb_type)(getmem s)(212%positive,0%Z)=Some(LinkHead).
Proof.
 intros present cs result s HS. eapply LinkPostLoad;[exact HS| | ].
 - destruct present;unfold LinkCells,LinkPublished,LinkResidual,LinkInputs;cbn[app tl];simpl;tauto.
 - destruct present;reflexivity.
Qed.
Theorem LinkGroupRead : forall present cs result s, s |= LinkPost present cs result ->
 load (Tint8)(getmem s)(213%positive,0%Z)=Some(V293_byteval 3).
Proof.
 intros present cs result s HS. eapply LinkPostLoad;[exact HS| | ].
 - destruct present;unfold LinkCells,LinkPublished,LinkResidual,LinkInputs;cbn[app tl];simpl;tauto.
 - destruct present;reflexivity.
Qed.
Theorem LinkRowRead : forall present cs result s, s |= LinkPost present cs result ->
 load (Tint8)(getmem s)(214%positive,1%Z)=Some(V293_byteval 137).
Proof.
 intros present cs result s HS. eapply LinkPostLoad;[exact HS| | ].
 - destruct present;unfold LinkCells,LinkPublished,LinkResidual,LinkInputs;cbn[app tl];simpl;tauto.
 - destruct present;reflexivity.
Qed.
Theorem LinkCounterRead : forall present cs result s, s |= LinkPost present cs result ->
 load (Tint8)(getmem s)(215%positive,0%Z)=Some(V293_byteval 255).
Proof.
 intros present cs result s HS. eapply LinkPostLoad;[exact HS| | ].
 - destruct present;unfold LinkCells,LinkPublished,LinkResidual,LinkInputs;cbn[app tl];simpl;tauto.
 - destruct present;reflexivity.
Qed.
Theorem LinkSizeRead : forall present cs result s, s |= LinkPost present cs result ->
 load (Tint32)(getmem s)(301%positive,140%Z)=Some(Vint32(Int.repr 128)).
Proof.
 intros present cs result s HS. eapply LinkPostLoad;[exact HS| | ].
 - destruct present;unfold LinkCells,LinkPublished,LinkResidual,LinkInputs;cbn[app tl];simpl;tauto.
 - destruct present;reflexivity.
Qed.
Theorem LinkOldBacklinkRead : forall cs result s, s |= LinkPost true cs result ->
 load(Tcom_ptr 410%Z)(getmem s)(301%positive,280%Z)=Some LinkHead.
Proof.
 intros cs result s HS. eapply LinkPostLoad;[exact HS| |reflexivity].
 unfold LinkCells,LinkPublished;cbn[app]. do 10 right;left;reflexivity.
Qed.
Theorem LinkWrongFreeHead : forall present cs result s, s |= LinkPost present cs result ->
 load(Tptr V293_tcb_type)(getmem s)(210%positive,0%Z)<>Some LinkHead.
Proof. intros. rewrite(LinkFreeHeadRead _ _ _ _ H). unfold LinkNext,LinkHead. intro E. inversion E. Qed.
Theorem LinkReturnedZero : forall present cs result s, s |= LinkPost present cs result -> result=Some(Vint32 Int.zero).
Proof.
 intros present cs result s HS. apply LinkPostView in HS. apply astar_l_apure_elim in HS. tauto.
Qed.
Theorem LinkCoreSize : forall present,
 length(LinkCells false present)=(if present then 36 else 35) /\
 length(LinkCells true present)=(if present then 36 else 35) /\
 fold_right(fun cell count=>typelen(snd(fst cell))+count)0(LinkCells false present)=(if present then 100 else 96) /\
 fold_right(fun cell count=>typelen(snd(fst cell))+count)0(LinkCells true present)=(if present then 100 else 96).
Proof. destruct present;repeat split;reflexivity. Qed.
