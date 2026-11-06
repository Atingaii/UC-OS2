(* Independent literal entry for real between-Hooks Hoare and split body contracts.
   No old probe import; no Hook or global startup invariant is instantiated. *)
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
Definition PriorityOld : list V293_record_cell :=
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
Definition PriorityInputs pc : list V293_record_cell :=
 [((201%positive,0%Z),(Tptr V293_tcb_type),(pc));
  ((202%positive,0%Z),(Tint8),(V293_byteval 11));
  ((203%positive,0%Z),(Tptr Tint32),(Vnull));
  ((204%positive,0%Z),(Tptr Tint32),(Vnull));
  ((205%positive,0%Z),(Tint16),(Vint32 Int.zero));
  ((206%positive,0%Z),(Tint32),(Vint32(Int.repr 128)));
  ((207%positive,0%Z),(Tptr Tvoid),(Vnull));
  ((208%positive,0%Z),(Tint16),(Vint32 Int.zero))].
Definition PriorityFinal : list V293_record_cell :=
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
Definition PriorityGE : env := set (set (sig OSTCBCur (402%positive,Tptr Tvoid)) 91%Z (210%positive,Tptr V293_tcb_type)) 92%Z (211%positive,Tarray (Tptr V293_tcb_type) 13).
Definition PriorityLE : env :=
 set (set (set (set (set (set (set (set (set (emp:env)
 108%Z (201%positive,Tptr V293_tcb_type)) 101%Z (202%positive,Tint8))
 102%Z (203%positive,Tptr Tint32)) 103%Z (204%positive,Tptr Tint32))
 104%Z (205%positive,Tint16)) 105%Z (206%positive,Tint32))
 106%Z (207%positive,Tptr Tvoid)) 107%Z (208%positive,Tint16)) 109%Z (209%positive,Tint32).
Definition PriorityTid : tid := (301%positive,Int.repr 8).
Definition PriorityBytes b permission tp v := V293_encoded_memory b 0 permission (encode_val tp v).
Definition PriorityCurrent := PriorityBytes 402%positive false (Tptr Tvoid) (Vptr PriorityTid).
Definition PrioritySentinel := PriorityBytes 601%positive true Tint8 (Vint32(Int.repr 77)).
Fixpoint PriorityMemory (cells : list V293_record_cell) : mem :=
 match cells with []=>emp | ((b,i),tp,v)::tail=>
 merge (V293_encoded_memory b i true (encode_val tp v)) (PriorityMemory tail) end.
Definition PriorityHead := Vptr(301%positive,Int.repr 128).
Definition PriorityNext := Vptr(301%positive,Int.repr 256).
Definition PriorityCells (initialized : bool) pc cpu slot :=
 ((211%positive,44%Z),Tptr V293_tcb_type,slot)::
 ((209%positive,0%Z),Tint32,cpu)::
 ((if initialized then PriorityFinal else PriorityOld)++PriorityInputs pc++
 [((210%positive,0%Z),Tptr V293_tcb_type,if initialized then PriorityNext else PriorityHead);
  ((301%positive,148%Z),Tcom_ptr 410%Z,PriorityNext)]).
Definition PriorityFinalCells := PriorityCells true PriorityHead (Vint32 Int.zero) PriorityHead.
Definition PriorityWhole initialized pc cpu slot := merge (PriorityMemory (PriorityCells initialized pc cpu slot)) (merge PriorityCurrent PrioritySentinel).
Definition PriorityState M cs : RstateOP :=
 (PriorityGE,PriorityLE,M,(fun _=>false),(false,[],cs),(emp:osabst),spec_done None).
Definition PriorityR := CurTid PriorityTid ** LINV V293_witness_li PriorityTid [] **
 Amapsto (601%positive,0%Z) Tint8 true (Vint32(Int.repr 77)).
Definition PriorityFieldBindings := V293_tcb_fields_bindings 108%Z 101%Z 102%Z 103%Z 104%Z 105%Z 106%Z 107%Z
 201%positive 202%positive 203%positive 204%positive 205%positive 206%positive 207%positive 208%positive.
Definition PriorityBindings := PriorityFieldBindings ** V293_tcb_success_extra 210%positive 209%positive.
Definition PriorityFrame cs := OS[(fun _=>false),false,[],cs] **
 (PriorityBindings ** (V293_tcb_table_binding 211%positive ** PriorityR)).
Definition PriorityPre initialized pc cpu slot cs := <||spec_done None||> ** V293_rdy_raw_cells (PriorityCells initialized pc cpu slot) (PriorityFrame cs).
Definition PriorityPost cs := <||spec_done None||> ** V293_rdy_raw_cells PriorityFinalCells (PriorityFrame cs).
Definition PriorityCode := sseq (sprim encrit)
 (sseq (sassign (earrayelem(evar 92%Z)(evar 101%Z)) (evar 108%Z)) (sprim excrit)).
Lemma PriorityStar : forall m1 m2 m cs p q,
 join m1 m2 m -> PriorityState m1 cs |= p -> PriorityState m2 cs |= q ->
 PriorityState m cs |= p ** q.
Proof.
 intros. apply sat_split'. exists m1. exists m2.
 exists(emp:osabst). exists(emp:osabst).
 split;[exact H | ]. split;[apply map_join_emp | ]. split;assumption.
Qed.
Lemma PriorityCurrentSpatial : forall cs, PriorityState PriorityCurrent cs |= CurTid PriorityTid.
Proof.
 intro cs. exists Tvoid. exists 402%positive.
 eapply PriorityStar with (m1:=emp) (m2:=PriorityCurrent).
 - apply map_join_comm;apply map_join_emp.
 - exists 402%positive. split;[vm_compute;reflexivity | ]. repeat split;reflexivity.
 - split;[apply V293_encoded_memory_mapsto|reflexivity].
Qed.
Lemma PriorityLInvSpatial : forall cs, PriorityState emp cs |= LINV V293_witness_li PriorityTid [].
Proof.
 intro cs. unfold LINV. apply astar_comm. apply astar_l_apure_intro.
 - split;reflexivity.
 - apply V293_witness_li_good.
Qed.
Ltac PriorityFrameApart b :=
 apply map_join_merge;apply map_disjoint;intros [other offset];
 destruct(Pos.eq_dec other b);[subst other;right;left|left];
 unfold PriorityCurrent,PrioritySentinel,PriorityBytes;
 repeat first [rewrite map_merge_semp by reflexivity |
 rewrite V293_encoded_memory_outside by (left;congruence)];reflexivity.
Lemma PriorityRSpatial : forall cs,
 PriorityState (merge PriorityCurrent PrioritySentinel) cs |= PriorityR.
Proof.
 intro cs. unfold PriorityR.
 eapply PriorityStar with (m1:=PriorityCurrent) (m2:=PrioritySentinel).
 - PriorityFrameApart 402%positive.
 - apply PriorityCurrentSpatial.
 - eapply PriorityStar with (m1:=emp) (m2:=PrioritySentinel).
   + apply map_join_comm;apply map_join_emp.
   + apply PriorityLInvSpatial.
   + split;[apply V293_encoded_memory_mapsto|reflexivity].
Qed.
Lemma PriorityRGood : GoodFrm PriorityR.
Proof. cbn [PriorityR CurTid LINV V293_witness_li GoodFrm]. repeat split;exact I. Qed.
Lemma PriorityRCurLINV : PriorityR ==> CurLINV V293_witness_li PriorityTid.
Proof.
 intros s HS. unfold CurLINV. exists([]:list logicvar).
 unfold PriorityR in HS. clear -HS. sep auto.
Qed.
Lemma PriorityFieldBindingsSpatial : forall cs, PriorityState emp cs |= PriorityFieldBindings.
Proof.
 intro cs. unfold PriorityFieldBindings,V293_tcb_fields_bindings. repeat split.
 - exists 201%positive. split;[vm_compute;reflexivity | ]. repeat split;reflexivity.
 - exists 202%positive. split;[vm_compute;reflexivity | ]. repeat split;reflexivity.
 - exists 203%positive. split;[vm_compute;reflexivity | ]. repeat split;reflexivity.
 - exists 204%positive. split;[vm_compute;reflexivity | ]. repeat split;reflexivity.
 - exists 205%positive. split;[vm_compute;reflexivity | ]. repeat split;reflexivity.
 - exists 206%positive. split;[vm_compute;reflexivity | ]. repeat split;reflexivity.
 - exists 207%positive. split;[vm_compute;reflexivity | ]. repeat split;reflexivity.
 - exists 208%positive. split;[vm_compute;reflexivity | ]. repeat split;reflexivity.
Qed.
Lemma PriorityBindingsSpatial : forall cs, PriorityState emp cs |= PriorityBindings.
Proof.
 intro cs. unfold PriorityBindings. eapply PriorityStar with (m1:=emp) (m2:=emp).
 - apply map_join_emp.
 - apply PriorityFieldBindingsSpatial.
 - unfold V293_tcb_success_extra. repeat split.
   + exists 209%positive. split;[vm_compute;reflexivity| ]. repeat split;reflexivity.
   + exists 210%positive. split;[vm_compute;reflexivity| ]. repeat split;reflexivity.
   + intros [v H]. vm_compute in H. discriminate H.
Qed.
Ltac PriorityOutside :=
 repeat first [rewrite V293_encoded_memory_outside by
 (first [left;congruence | right;rewrite ?encode_val_length;cbn [V293_byteval length encode_val typelen list_repeat inj_pointer inj_bytes encode_int List.map];lia])
 |rewrite map_merge_semp by reflexivity];reflexivity.
Ltac PriorityApart b start count :=
 apply map_join_merge;apply map_disjoint;intros [other off];
 destruct (Pos.eq_dec other b) as [B|B];
 [subst other;destruct (Z_lt_dec off start) as [Low|Low];
 [left;apply V293_encoded_memory_outside;right;left;exact Low |
 destruct (Z_lt_dec off (start+count)) as [Inside|Outside];
 [right;left;PriorityOutside |left;apply V293_encoded_memory_outside;right;right;
 rewrite ?encode_val_length;cbn [V293_byteval length encode_val typelen list_repeat inj_pointer inj_bytes encode_int List.map];lia]] |
 left;apply V293_encoded_memory_outside;left;exact B].

Lemma PriorityTableSpatial : forall cs, PriorityState emp cs |= V293_tcb_table_binding 211%positive.
Proof.
 intro cs. unfold V293_tcb_table_binding. repeat split.
 - exists 211%positive. split;[vm_compute;reflexivity| ]. repeat split;reflexivity.
 - intros [v H]. vm_compute in H. discriminate H.
Qed.
Theorem PriorityRawLiteral : forall initialized pc cpu slot cs,
 PriorityState (PriorityMemory (PriorityCells initialized pc cpu slot)) cs |=
 V293_rdy_raw_cells (PriorityCells initialized pc cpu slot) Aemp.
Proof.
 intros initialized pc cpu slot cs. destruct initialized;
 unfold PriorityCells,PriorityOld,PriorityFinal,PriorityInputs,PriorityHead,PriorityNext;
 cbn [app PriorityMemory V293_rdy_raw_cells].
 - eapply PriorityStar with (m1:=V293_encoded_memory 211%positive 44%Z true (encode_val (Tptr V293_tcb_type) slot));
   [PriorityApart 211%positive 44%Z 4%Z|split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
   eapply PriorityStar with (m1:=V293_encoded_memory 209%positive 0%Z true (encode_val Tint32 cpu));
   [PriorityApart 209%positive 0%Z 4%Z|split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
   eapply PriorityStar with (m1:=V293_encoded_memory 301%positive 128%Z true (encode_val (Tptr Tint32) (Vnull)));
   [PriorityApart 301%positive 128%Z 4%Z|split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
   eapply PriorityStar with (m1:=V293_encoded_memory 301%positive 178%Z true (encode_val (Tint8) (V293_byteval 11)));
   [PriorityApart 301%positive 178%Z 1%Z|split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
   eapply PriorityStar with (m1:=V293_encoded_memory 301%positive 176%Z true (encode_val (Tint8) (Vint32 Int.zero)));
   [PriorityApart 301%positive 176%Z 1%Z|split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
   eapply PriorityStar with (m1:=V293_encoded_memory 301%positive 177%Z true (encode_val (Tint8) (Vint32 Int.zero)));
   [PriorityApart 301%positive 177%Z 1%Z|split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
   eapply PriorityStar with (m1:=V293_encoded_memory 301%positive 172%Z true (encode_val (Tint32) (Vint32 Int.zero)));
   [PriorityApart 301%positive 172%Z 4%Z|split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
   eapply PriorityStar with (m1:=V293_encoded_memory 301%positive 132%Z true (encode_val (Tptr Tvoid) (Vnull)));
   [PriorityApart 301%positive 132%Z 4%Z|split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
   eapply PriorityStar with (m1:=V293_encoded_memory 301%positive 140%Z true (encode_val (Tint32) (Vint32(Int.repr 128))));
   [PriorityApart 301%positive 140%Z 4%Z|split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
   eapply PriorityStar with (m1:=V293_encoded_memory 301%positive 136%Z true (encode_val (Tptr Tint32) (Vnull)));
   [PriorityApart 301%positive 136%Z 4%Z|split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
   eapply PriorityStar with (m1:=V293_encoded_memory 301%positive 144%Z true (encode_val (Tint16) (Vint32 Int.zero)));
   [PriorityApart 301%positive 144%Z 2%Z|split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
   eapply PriorityStar with (m1:=V293_encoded_memory 301%positive 146%Z true (encode_val (Tint16) (Vint32 Int.zero)));
   [PriorityApart 301%positive 146%Z 2%Z|split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
   eapply PriorityStar with (m1:=V293_encoded_memory 301%positive 183%Z true (encode_val (Tint8) (Vint32 Int.zero)));
   [PriorityApart 301%positive 183%Z 1%Z|split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
   eapply PriorityStar with (m1:=V293_encoded_memory 301%positive 180%Z true (encode_val (Tint8) (V293_byteval 1)));
   [PriorityApart 301%positive 180%Z 1%Z|split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
   eapply PriorityStar with (m1:=V293_encoded_memory 301%positive 179%Z true (encode_val (Tint8) (V293_byteval 3)));
   [PriorityApart 301%positive 179%Z 1%Z|split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
   eapply PriorityStar with (m1:=V293_encoded_memory 301%positive 182%Z true (encode_val (Tint8) (V293_byteval 2)));
   [PriorityApart 301%positive 182%Z 1%Z|split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
   eapply PriorityStar with (m1:=V293_encoded_memory 301%positive 181%Z true (encode_val (Tint8) (V293_byteval 8)));
   [PriorityApart 301%positive 181%Z 1%Z|split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
   eapply PriorityStar with (m1:=V293_encoded_memory 301%positive 156%Z true (encode_val (Tcom_ptr 411%Z) (Vnull)));
   [PriorityApart 301%positive 156%Z 4%Z|split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
   eapply PriorityStar with (m1:=V293_encoded_memory 301%positive 164%Z true (encode_val (Tcom_ptr 412%Z) (Vnull)));
   [PriorityApart 301%positive 164%Z 4%Z|split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
   eapply PriorityStar with (m1:=V293_encoded_memory 301%positive 160%Z true (encode_val (Tptr Tvoid) (Vnull)));
   [PriorityApart 301%positive 160%Z 4%Z|split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
   eapply PriorityStar with (m1:=V293_encoded_memory 201%positive 0%Z true (encode_val (Tptr V293_tcb_type) (pc)));
   [PriorityApart 201%positive 0%Z 4%Z|split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
   eapply PriorityStar with (m1:=V293_encoded_memory 202%positive 0%Z true (encode_val (Tint8) (V293_byteval 11)));
   [PriorityApart 202%positive 0%Z 1%Z|split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
   eapply PriorityStar with (m1:=V293_encoded_memory 203%positive 0%Z true (encode_val (Tptr Tint32) (Vnull)));
   [PriorityApart 203%positive 0%Z 4%Z|split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
   eapply PriorityStar with (m1:=V293_encoded_memory 204%positive 0%Z true (encode_val (Tptr Tint32) (Vnull)));
   [PriorityApart 204%positive 0%Z 4%Z|split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
   eapply PriorityStar with (m1:=V293_encoded_memory 205%positive 0%Z true (encode_val (Tint16) (Vint32 Int.zero)));
   [PriorityApart 205%positive 0%Z 2%Z|split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
   eapply PriorityStar with (m1:=V293_encoded_memory 206%positive 0%Z true (encode_val (Tint32) (Vint32(Int.repr 128))));
   [PriorityApart 206%positive 0%Z 4%Z|split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
   eapply PriorityStar with (m1:=V293_encoded_memory 207%positive 0%Z true (encode_val (Tptr Tvoid) (Vnull)));
   [PriorityApart 207%positive 0%Z 4%Z|split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
   eapply PriorityStar with (m1:=V293_encoded_memory 208%positive 0%Z true (encode_val (Tint16) (Vint32 Int.zero)));
   [PriorityApart 208%positive 0%Z 2%Z|split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
   eapply PriorityStar with (m1:=V293_encoded_memory 210%positive 0%Z true (encode_val (Tptr V293_tcb_type) (Vptr(301%positive,Int.repr 256))));
   [PriorityApart 210%positive 0%Z 4%Z|split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
   eapply PriorityStar with (m1:=V293_encoded_memory 301%positive 148%Z true (encode_val (Tcom_ptr 410%Z) (Vptr(301%positive,Int.repr 256))));
   [PriorityApart 301%positive 148%Z 4%Z|split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
   split;reflexivity.
 - eapply PriorityStar with (m1:=V293_encoded_memory 211%positive 44%Z true (encode_val (Tptr V293_tcb_type) slot));
   [PriorityApart 211%positive 44%Z 4%Z|split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
   eapply PriorityStar with (m1:=V293_encoded_memory 209%positive 0%Z true (encode_val Tint32 cpu));
   [PriorityApart 209%positive 0%Z 4%Z|split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
   eapply PriorityStar with (m1:=V293_encoded_memory 301%positive 128%Z true (encode_val (Tptr Tint32) (Vundef)));
   [PriorityApart 301%positive 128%Z 4%Z|split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
   eapply PriorityStar with (m1:=V293_encoded_memory 301%positive 178%Z true (encode_val (Tint8) (Vundef)));
   [PriorityApart 301%positive 178%Z 1%Z|split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
   eapply PriorityStar with (m1:=V293_encoded_memory 301%positive 176%Z true (encode_val (Tint8) (Vundef)));
   [PriorityApart 301%positive 176%Z 1%Z|split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
   eapply PriorityStar with (m1:=V293_encoded_memory 301%positive 177%Z true (encode_val (Tint8) (Vundef)));
   [PriorityApart 301%positive 177%Z 1%Z|split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
   eapply PriorityStar with (m1:=V293_encoded_memory 301%positive 172%Z true (encode_val (Tint32) (Vundef)));
   [PriorityApart 301%positive 172%Z 4%Z|split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
   eapply PriorityStar with (m1:=V293_encoded_memory 301%positive 132%Z true (encode_val (Tptr Tvoid) (Vundef)));
   [PriorityApart 301%positive 132%Z 4%Z|split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
   eapply PriorityStar with (m1:=V293_encoded_memory 301%positive 140%Z true (encode_val (Tint32) (Vundef)));
   [PriorityApart 301%positive 140%Z 4%Z|split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
   eapply PriorityStar with (m1:=V293_encoded_memory 301%positive 136%Z true (encode_val (Tptr Tint32) (Vundef)));
   [PriorityApart 301%positive 136%Z 4%Z|split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
   eapply PriorityStar with (m1:=V293_encoded_memory 301%positive 144%Z true (encode_val (Tint16) (Vundef)));
   [PriorityApart 301%positive 144%Z 2%Z|split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
   eapply PriorityStar with (m1:=V293_encoded_memory 301%positive 146%Z true (encode_val (Tint16) (Vundef)));
   [PriorityApart 301%positive 146%Z 2%Z|split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
   eapply PriorityStar with (m1:=V293_encoded_memory 301%positive 183%Z true (encode_val (Tint8) (Vundef)));
   [PriorityApart 301%positive 183%Z 1%Z|split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
   eapply PriorityStar with (m1:=V293_encoded_memory 301%positive 180%Z true (encode_val (Tint8) (Vundef)));
   [PriorityApart 301%positive 180%Z 1%Z|split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
   eapply PriorityStar with (m1:=V293_encoded_memory 301%positive 179%Z true (encode_val (Tint8) (Vundef)));
   [PriorityApart 301%positive 179%Z 1%Z|split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
   eapply PriorityStar with (m1:=V293_encoded_memory 301%positive 182%Z true (encode_val (Tint8) (Vundef)));
   [PriorityApart 301%positive 182%Z 1%Z|split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
   eapply PriorityStar with (m1:=V293_encoded_memory 301%positive 181%Z true (encode_val (Tint8) (Vundef)));
   [PriorityApart 301%positive 181%Z 1%Z|split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
   eapply PriorityStar with (m1:=V293_encoded_memory 301%positive 156%Z true (encode_val (Tcom_ptr 411%Z) (Vundef)));
   [PriorityApart 301%positive 156%Z 4%Z|split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
   eapply PriorityStar with (m1:=V293_encoded_memory 301%positive 164%Z true (encode_val (Tcom_ptr 412%Z) (Vundef)));
   [PriorityApart 301%positive 164%Z 4%Z|split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
   eapply PriorityStar with (m1:=V293_encoded_memory 301%positive 160%Z true (encode_val (Tptr Tvoid) (Vundef)));
   [PriorityApart 301%positive 160%Z 4%Z|split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
   eapply PriorityStar with (m1:=V293_encoded_memory 201%positive 0%Z true (encode_val (Tptr V293_tcb_type) (pc)));
   [PriorityApart 201%positive 0%Z 4%Z|split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
   eapply PriorityStar with (m1:=V293_encoded_memory 202%positive 0%Z true (encode_val (Tint8) (V293_byteval 11)));
   [PriorityApart 202%positive 0%Z 1%Z|split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
   eapply PriorityStar with (m1:=V293_encoded_memory 203%positive 0%Z true (encode_val (Tptr Tint32) (Vnull)));
   [PriorityApart 203%positive 0%Z 4%Z|split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
   eapply PriorityStar with (m1:=V293_encoded_memory 204%positive 0%Z true (encode_val (Tptr Tint32) (Vnull)));
   [PriorityApart 204%positive 0%Z 4%Z|split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
   eapply PriorityStar with (m1:=V293_encoded_memory 205%positive 0%Z true (encode_val (Tint16) (Vint32 Int.zero)));
   [PriorityApart 205%positive 0%Z 2%Z|split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
   eapply PriorityStar with (m1:=V293_encoded_memory 206%positive 0%Z true (encode_val (Tint32) (Vint32(Int.repr 128))));
   [PriorityApart 206%positive 0%Z 4%Z|split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
   eapply PriorityStar with (m1:=V293_encoded_memory 207%positive 0%Z true (encode_val (Tptr Tvoid) (Vnull)));
   [PriorityApart 207%positive 0%Z 4%Z|split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
   eapply PriorityStar with (m1:=V293_encoded_memory 208%positive 0%Z true (encode_val (Tint16) (Vint32 Int.zero)));
   [PriorityApart 208%positive 0%Z 2%Z|split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
   eapply PriorityStar with (m1:=V293_encoded_memory 210%positive 0%Z true (encode_val (Tptr V293_tcb_type) (Vptr(301%positive,Int.repr 128))));
   [PriorityApart 210%positive 0%Z 4%Z|split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
   eapply PriorityStar with (m1:=V293_encoded_memory 301%positive 148%Z true (encode_val (Tcom_ptr 410%Z) (Vptr(301%positive,Int.repr 256))));
   [PriorityApart 301%positive 148%Z 4%Z|split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
   split;reflexivity.
Qed.
Theorem PriorityLiteralEntry : forall initialized pc cpu slot cs,
 PriorityState (PriorityWhole initialized pc cpu slot) cs |= PriorityPre initialized pc cpu slot cs.
Proof.
 intros initialized pc cpu slot cs. unfold PriorityPre.
 eapply PriorityStar with (m1:=emp) (m2:=PriorityWhole initialized pc cpu slot).
 - apply map_join_comm;apply map_join_emp.
 - split;[reflexivity| ]. split;reflexivity.
 - apply V293_raw_cells_join. unfold PriorityWhole.
   eapply PriorityStar with (m1:=PriorityMemory (PriorityCells initialized pc cpu slot)) (m2:=merge PriorityCurrent PrioritySentinel).
   + apply map_join_merge;apply map_disjoint;intros [b off].
     destruct (Pos.eq_dec b 402%positive);[subst b;left| ].
     * destruct initialized;unfold PriorityCells,PriorityOld,PriorityFinal,PriorityInputs;cbn [app PriorityMemory];PriorityOutside.
     * destruct (Pos.eq_dec b 601%positive);[subst b;left|right;left].
       -- destruct initialized;unfold PriorityCells,PriorityOld,PriorityFinal,PriorityInputs;cbn [app PriorityMemory];PriorityOutside.
       -- unfold PriorityCurrent,PrioritySentinel,PriorityBytes.
          rewrite map_merge_semp by reflexivity.
          rewrite !V293_encoded_memory_outside by (left;congruence). reflexivity.
   + apply PriorityRawLiteral.
   + unfold PriorityFrame. eapply PriorityStar with (m1:=emp) (m2:=merge PriorityCurrent PrioritySentinel).
     * apply map_join_comm;apply map_join_emp.
     * repeat (eapply PriorityStar with (m1:=emp) (m2:=emp);
        [apply map_join_emp|split;[reflexivity|split;reflexivity]| ]).
       split;[reflexivity|split;reflexivity].
     * eapply PriorityStar with (m1:=emp) (m2:=merge PriorityCurrent PrioritySentinel).
       -- apply map_join_comm;apply map_join_emp.
       -- apply PriorityBindingsSpatial.
       -- eapply PriorityStar with (m1:=emp) (m2:=merge PriorityCurrent PrioritySentinel).
          ++ apply map_join_comm;apply map_join_emp.
          ++ apply PriorityTableSpatial.
          ++ apply PriorityRSpatial.
Qed.

Definition PriorityChecked : forall Spec sd I r ri cs,
 InfRules Spec sd V293_witness_li I r ri
 (PriorityPre true PriorityHead (Vint32 Int.zero) Vundef cs) PriorityCode (PriorityPost cs) PriorityTid.
Proof.
 intros. exact (V293_OS_TCBInit_priority_bracket_hoare Spec sd V293_witness_li I r ri PriorityTid (spec_done None) PriorityR
 211%positive Vundef 210%positive 209%positive 201%positive 202%positive 203%positive 204%positive 205%positive 206%positive 207%positive 208%positive 301%positive 128%Z 11 Vnull Vnull (Vint32 Int.zero) (Vint32(Int.repr 128)) Vnull (Vint32 Int.zero) (Vint32 Int.zero) PriorityNext PriorityNext (fun _=>false) [] cs
 ltac:(lia) PriorityRGood PriorityRCurLINV).
Qed.
Definition PriorityBodyChecked : forall Spec sd I r ri hi hc cs,
 InfRules Spec sd V293_witness_li I r ri
 (PriorityPre true PriorityHead (Vint32 Int.zero) Vundef cs)
 (scall hi [evar 108%Z]) (PriorityPre true PriorityHead (Vint32 Int.zero) Vundef cs) PriorityTid ->
 InfRules Spec sd V293_witness_li I r ri (PriorityPost cs)
 (scall hc [evar 108%Z]) (PriorityPost cs) PriorityTid ->
 InfRules Spec sd V293_witness_li I r ri (PriorityPost cs)
 (V293_TCB_publish 108%Z 93%Z 94%Z 95%Z 96%Z) Afalse PriorityTid ->
 InfRules Spec sd V293_witness_li I r ri
 (PriorityPre false Vundef Vundef Vundef cs) (V293_TCBInit_function_body hi hc) Afalse PriorityTid.
Proof.
 intros Spec sd I r ri hi hc cs InitHook CreateHook Publish.
 exact (V293_OS_TCBInit_nonempty_body_split_hoare Spec sd V293_witness_li I r ri PriorityTid hi hc (spec_done None) PriorityR
 211%positive Vundef 210%positive 209%positive 201%positive 202%positive 203%positive 204%positive 205%positive 206%positive 207%positive 208%positive 301%positive 128%Z 11 Vnull Vnull (Vint32 Int.zero) (Vint32(Int.repr 128)) Vnull (Vint32 Int.zero) (fun _=>Vundef) Vundef Vundef PriorityNext (fun _=>false) [] cs
 ltac:(lia) ltac:(lia) ltac:(unfold Int.max_unsigned,Int.modulus,Int.wordsize;cbn;lia)
 ltac:(repeat split;reflexivity) ltac:(reflexivity) PriorityRGood PriorityRCurLINV InitHook CreateHook Publish).
Qed.
Theorem PrioritySlotRead : forall s cs, s |= PriorityPost cs ->
 load (Tptr V293_tcb_type) (getmem s) (211%positive,44%Z)=Some PriorityHead.
Proof.
 intros s cs HS. unfold PriorityPost in HS. eapply V293_star_load_r;[ |exact HS]. intros st Owned.
 eapply (V293_rdy_raw_load PriorityFinalCells _ _ _ _ st);
 [left;reflexivity|reflexivity|exact Owned].
Qed.
Theorem PriorityWrongSlotRead : forall s cs, s |= PriorityPost cs ->
 load (Tptr V293_tcb_type) (getmem s) (211%positive,44%Z)<>Some Vnull.
Proof. intros s cs HS. rewrite (PrioritySlotRead _ _ HS). discriminate. Qed.
Theorem PriorityFreeHeadPreserved : forall s cs, s |= PriorityPost cs ->
 load (Tptr V293_tcb_type) (getmem s) (210%positive,0%Z)=Some PriorityNext.
Proof.
 intros s cs HS. unfold PriorityPost in HS. eapply V293_star_load_r;[ |exact HS]. intros st Owned.
 eapply (V293_rdy_raw_load PriorityFinalCells _ _ _ _ st);
 [do 28 right;left;reflexivity|reflexivity|exact Owned].
Qed.
Theorem PriorityInitialEntry : forall cs,
 PriorityState (PriorityWhole false Vundef Vundef Vundef) cs |= PriorityPre false Vundef Vundef Vundef cs.
Proof. apply PriorityLiteralEntry. Qed.
Theorem PriorityBetweenHooksEntry : forall cs,
 PriorityState (PriorityWhole true PriorityHead (Vint32 Int.zero) Vundef) cs |=
 PriorityPre true PriorityHead (Vint32 Int.zero) Vundef cs.
Proof. apply PriorityLiteralEntry. Qed.
Theorem PriorityCoreSize : length (PriorityCells false Vundef Vundef Vundef)=30 /\
 fold_right (fun cell count=>typelen(snd(fst cell))+count) 0 (PriorityCells false Vundef Vundef Vundef)=85.
Proof. split;reflexivity. Qed.
