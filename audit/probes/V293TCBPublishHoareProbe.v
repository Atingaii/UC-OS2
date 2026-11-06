(* Independent joint entry for publication and return; no old probe imports. *)
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
Require Import CertiOS.certiucos.v293.proofs.V293TCBPublishHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TCBPublish.

Definition PubGE : env := set (set (set (set (sig OSTCBCur (402%positive,Tptr Tvoid))
 93%Z (210%positive,Tptr V293_tcb_type)) 94%Z (211%positive,Tint8))
 95%Z (212%positive,Tarray Tint8 2)) 96%Z (213%positive,Tint8).
Definition PubLE : env := sig 108%Z (201%positive,Tptr V293_tcb_type).
Definition PubTid : tid := (301%positive,Int.repr 8).
Definition PubBytes b permission tp v := V293_encoded_memory b 0 permission (encode_val tp v).
Definition PubCurrent := PubBytes 402%positive false (Tptr Tvoid) (Vptr PubTid).
Definition PubSentinel := PubBytes 601%positive true Tint8 (Vint32(Int.repr 77)).
Fixpoint PubMemory (cells:list V293_record_cell) : mem :=
 match cells with []=>emp | ((b,i),tp,v)::tail=>
 merge(V293_encoded_memory b i true(encode_val tp v))(PubMemory tail) end.
Definition PubNew := Vptr(301%positive,Int.repr 128).
Definition PubOld (present:bool) := if present then Vptr(301%positive,Int.repr 256) else Vnull.
Definition PubCells (initialized present:bool) : list V293_record_cell :=
 [((201%positive,0%Z),Tptr V293_tcb_type,PubNew);
  ((301%positive,148%Z),Tcom_ptr 410%Z,if initialized then PubOld present else Vundef);
  ((301%positive,152%Z),Tcom_ptr 410%Z,if initialized then Vnull else Vundef);
  ((301%positive,180%Z),Tint8,V293_byteval 1);
  ((301%positive,182%Z),Tint8,V293_byteval 2);
  ((301%positive,181%Z),Tint8,V293_byteval 8);
  ((210%positive,0%Z),Tptr V293_tcb_type,if initialized then PubNew else PubOld present);
  ((211%positive,0%Z),Tint8,V293_byteval(if initialized then 3 else 1));
  ((212%positive,1%Z),Tint8,V293_byteval(if initialized then 137 else 129));
  ((213%positive,0%Z),Tint8,V293_byteval(if initialized then 255 else 254))] ++
 if present then [((301%positive,280%Z),Tcom_ptr 410%Z,if initialized then PubNew else Vundef)] else [].
Definition PubWhole initialized present := merge(PubMemory(PubCells initialized present))(merge PubCurrent PubSentinel).
Definition PubState M cs : RstateOP :=
 (PubGE,PubLE,M,(fun _=>false),(false,[],cs),(emp:osabst),spec_done None).
Definition PubR := CurTid PubTid ** LINV V293_witness_li PubTid [] **
 Amapsto(601%positive,0%Z) Tint8 true(Vint32(Int.repr 77)).
Definition PubBindings := V293_pub_bindings 108%Z 93%Z 94%Z 95%Z 96%Z
 201%positive 210%positive 211%positive 212%positive 213%positive.
Definition PubFrame cs := OS[(fun _=>false),false,[],cs] ** (PubBindings ** PubR).
Definition PubPre present cs := <||spec_done None||> ** V293_rdy_raw_cells(PubCells false present)(PubFrame cs).
Definition PubFinal present cs := <||spec_done None||> ** V293_rdy_raw_cells(PubCells true present)(PubFrame cs).
Definition PubPost present cs : retasrt := fun result=>[|result=Some(Vint32 Int.zero)|] ** PubFinal present cs.
Definition PubCode := V293_TCB_publish 108%Z 93%Z 94%Z 95%Z 96%Z.
Lemma PubStar : forall m1 m2 m cs p q,
 join m1 m2 m -> PubState m1 cs |= p -> PubState m2 cs |= q ->
 PubState m cs |= p ** q.
Proof.
 intros. apply sat_split'. exists m1. exists m2.
 exists(emp:osabst). exists(emp:osabst).
 split;[exact H | ]. split;[apply map_join_emp | ]. split;assumption.
Qed.
Lemma PubCurrentSpatial : forall cs, PubState PubCurrent cs |= CurTid PubTid.
Proof.
 intro cs. exists Tvoid. exists 402%positive.
 eapply PubStar with (m1:=emp) (m2:=PubCurrent).
 - apply map_join_comm;apply map_join_emp.
 - exists 402%positive. split;[vm_compute;reflexivity | ]. repeat split;reflexivity.
 - split;[apply V293_encoded_memory_mapsto|reflexivity].
Qed.
Lemma PubLInvSpatial : forall cs, PubState emp cs |= LINV V293_witness_li PubTid [].
Proof.
 intro cs. unfold LINV. apply astar_comm. apply astar_l_apure_intro.
 - split;reflexivity.
 - apply V293_witness_li_good.
Qed.
Ltac PubFrameApart b :=
 apply map_join_merge;apply map_disjoint;intros [other offset];
 destruct(Pos.eq_dec other b);[subst other;right;left|left];
 unfold PubCurrent,PubSentinel,PubBytes;
 repeat first [rewrite map_merge_semp by reflexivity |
 rewrite V293_encoded_memory_outside by (left;congruence)];reflexivity.
Lemma PubRSpatial : forall cs,
 PubState (merge PubCurrent PubSentinel) cs |= PubR.
Proof.
 intro cs. unfold PubR.
 eapply PubStar with (m1:=PubCurrent) (m2:=PubSentinel).
 - PubFrameApart 402%positive.
 - apply PubCurrentSpatial.
 - eapply PubStar with (m1:=emp) (m2:=PubSentinel).
   + apply map_join_comm;apply map_join_emp.
   + apply PubLInvSpatial.
   + split;[apply V293_encoded_memory_mapsto|reflexivity].
Qed.
Lemma PubRGood : GoodFrm PubR.
Proof. cbn [PubR CurTid LINV V293_witness_li GoodFrm]. repeat split;exact I. Qed.
Lemma PubRCurLINV : PubR ==> CurLINV V293_witness_li PubTid.
Proof.
 intros s HS. unfold CurLINV. exists([]:list logicvar).
 unfold PubR in HS. clear -HS. sep auto.
Qed.

Lemma PubBindingsSpatial : forall cs, PubState emp cs |= PubBindings.
Proof.
 intro cs. unfold PubBindings,V293_pub_bindings. repeat split.
 - exists 201%positive. split;[vm_compute;reflexivity| ]. repeat split;reflexivity.
 - intros [v H]. vm_compute in H. discriminate H.
 - exists 210%positive. split;[vm_compute;reflexivity| ]. repeat split;reflexivity.
 - intros [v H]. vm_compute in H. discriminate H.
 - exists 211%positive. split;[vm_compute;reflexivity| ]. repeat split;reflexivity.
 - intros [v H]. vm_compute in H. discriminate H.
 - exists 212%positive. split;[vm_compute;reflexivity| ]. repeat split;reflexivity.
 - intros [v H]. vm_compute in H. discriminate H.
 - exists 213%positive. split;[vm_compute;reflexivity| ]. repeat split;reflexivity.
Qed.
Ltac PubOutside :=
 repeat first [rewrite V293_encoded_memory_outside by
 (first [left;congruence | right;rewrite ?encode_val_length;cbn [V293_byteval length encode_val typelen list_repeat inj_pointer inj_bytes encode_int List.map];lia])
 |rewrite map_merge_semp by reflexivity];reflexivity.
Ltac PubApart b start count :=
 apply map_join_merge;apply map_disjoint;intros [other off];
 destruct (Pos.eq_dec other b) as [B|B];
 [subst other;destruct (Z_lt_dec off start) as [Low|Low];
 [left;apply V293_encoded_memory_outside;right;left;exact Low |
 destruct (Z_lt_dec off (start+count)) as [Inside|Outside];
 [right;left;PubOutside |left;apply V293_encoded_memory_outside;right;right;
 rewrite ?encode_val_length;cbn [V293_byteval length encode_val typelen list_repeat inj_pointer inj_bytes encode_int List.map];lia]] |
 left;apply V293_encoded_memory_outside;left;exact B].


Theorem PubRawLiteral : forall initialized present cs,
 PubState (PubMemory(PubCells initialized present)) cs |= V293_rdy_raw_cells(PubCells initialized present) Aemp.
Proof.
 intros initialized present cs. destruct initialized,present;
 unfold PubCells,PubNew,PubOld;cbn [app PubMemory V293_rdy_raw_cells].
 - eapply PubStar with(m1:=V293_encoded_memory 201%positive 0%Z true(encode_val (Tptr V293_tcb_type) (Vptr(301%positive,Int.repr 128))));
   [PubApart 201%positive 0%Z 4%Z|split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
   eapply PubStar with(m1:=V293_encoded_memory 301%positive 148%Z true(encode_val (Tcom_ptr 410%Z) (Vptr(301%positive,Int.repr 256))));
   [PubApart 301%positive 148%Z 4%Z|split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
   eapply PubStar with(m1:=V293_encoded_memory 301%positive 152%Z true(encode_val (Tcom_ptr 410%Z) (Vnull)));
   [PubApart 301%positive 152%Z 4%Z|split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
   eapply PubStar with(m1:=V293_encoded_memory 301%positive 180%Z true(encode_val (Tint8) (V293_byteval 1)));
   [PubApart 301%positive 180%Z 1%Z|split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
   eapply PubStar with(m1:=V293_encoded_memory 301%positive 182%Z true(encode_val (Tint8) (V293_byteval 2)));
   [PubApart 301%positive 182%Z 1%Z|split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
   eapply PubStar with(m1:=V293_encoded_memory 301%positive 181%Z true(encode_val (Tint8) (V293_byteval 8)));
   [PubApart 301%positive 181%Z 1%Z|split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
   eapply PubStar with(m1:=V293_encoded_memory 210%positive 0%Z true(encode_val (Tptr V293_tcb_type) (Vptr(301%positive,Int.repr 128))));
   [PubApart 210%positive 0%Z 4%Z|split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
   eapply PubStar with(m1:=V293_encoded_memory 211%positive 0%Z true(encode_val (Tint8) (V293_byteval 3)));
   [PubApart 211%positive 0%Z 1%Z|split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
   eapply PubStar with(m1:=V293_encoded_memory 212%positive 1%Z true(encode_val (Tint8) (V293_byteval 137)));
   [PubApart 212%positive 1%Z 1%Z|split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
   eapply PubStar with(m1:=V293_encoded_memory 213%positive 0%Z true(encode_val (Tint8) (V293_byteval 255)));
   [PubApart 213%positive 0%Z 1%Z|split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
   eapply PubStar with(m1:=V293_encoded_memory 301%positive 280%Z true(encode_val (Tcom_ptr 410%Z) (Vptr(301%positive,Int.repr 128))));
   [PubApart 301%positive 280%Z 4%Z|split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
   split;reflexivity.
 - eapply PubStar with(m1:=V293_encoded_memory 201%positive 0%Z true(encode_val (Tptr V293_tcb_type) (Vptr(301%positive,Int.repr 128))));
   [PubApart 201%positive 0%Z 4%Z|split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
   eapply PubStar with(m1:=V293_encoded_memory 301%positive 148%Z true(encode_val (Tcom_ptr 410%Z) (Vnull)));
   [PubApart 301%positive 148%Z 4%Z|split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
   eapply PubStar with(m1:=V293_encoded_memory 301%positive 152%Z true(encode_val (Tcom_ptr 410%Z) (Vnull)));
   [PubApart 301%positive 152%Z 4%Z|split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
   eapply PubStar with(m1:=V293_encoded_memory 301%positive 180%Z true(encode_val (Tint8) (V293_byteval 1)));
   [PubApart 301%positive 180%Z 1%Z|split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
   eapply PubStar with(m1:=V293_encoded_memory 301%positive 182%Z true(encode_val (Tint8) (V293_byteval 2)));
   [PubApart 301%positive 182%Z 1%Z|split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
   eapply PubStar with(m1:=V293_encoded_memory 301%positive 181%Z true(encode_val (Tint8) (V293_byteval 8)));
   [PubApart 301%positive 181%Z 1%Z|split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
   eapply PubStar with(m1:=V293_encoded_memory 210%positive 0%Z true(encode_val (Tptr V293_tcb_type) (Vptr(301%positive,Int.repr 128))));
   [PubApart 210%positive 0%Z 4%Z|split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
   eapply PubStar with(m1:=V293_encoded_memory 211%positive 0%Z true(encode_val (Tint8) (V293_byteval 3)));
   [PubApart 211%positive 0%Z 1%Z|split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
   eapply PubStar with(m1:=V293_encoded_memory 212%positive 1%Z true(encode_val (Tint8) (V293_byteval 137)));
   [PubApart 212%positive 1%Z 1%Z|split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
   eapply PubStar with(m1:=V293_encoded_memory 213%positive 0%Z true(encode_val (Tint8) (V293_byteval 255)));
   [PubApart 213%positive 0%Z 1%Z|split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
   split;reflexivity.
 - eapply PubStar with(m1:=V293_encoded_memory 201%positive 0%Z true(encode_val (Tptr V293_tcb_type) (Vptr(301%positive,Int.repr 128))));
   [PubApart 201%positive 0%Z 4%Z|split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
   eapply PubStar with(m1:=V293_encoded_memory 301%positive 148%Z true(encode_val (Tcom_ptr 410%Z) (Vundef)));
   [PubApart 301%positive 148%Z 4%Z|split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
   eapply PubStar with(m1:=V293_encoded_memory 301%positive 152%Z true(encode_val (Tcom_ptr 410%Z) (Vundef)));
   [PubApart 301%positive 152%Z 4%Z|split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
   eapply PubStar with(m1:=V293_encoded_memory 301%positive 180%Z true(encode_val (Tint8) (V293_byteval 1)));
   [PubApart 301%positive 180%Z 1%Z|split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
   eapply PubStar with(m1:=V293_encoded_memory 301%positive 182%Z true(encode_val (Tint8) (V293_byteval 2)));
   [PubApart 301%positive 182%Z 1%Z|split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
   eapply PubStar with(m1:=V293_encoded_memory 301%positive 181%Z true(encode_val (Tint8) (V293_byteval 8)));
   [PubApart 301%positive 181%Z 1%Z|split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
   eapply PubStar with(m1:=V293_encoded_memory 210%positive 0%Z true(encode_val (Tptr V293_tcb_type) (Vptr(301%positive,Int.repr 256))));
   [PubApart 210%positive 0%Z 4%Z|split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
   eapply PubStar with(m1:=V293_encoded_memory 211%positive 0%Z true(encode_val (Tint8) (V293_byteval 1)));
   [PubApart 211%positive 0%Z 1%Z|split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
   eapply PubStar with(m1:=V293_encoded_memory 212%positive 1%Z true(encode_val (Tint8) (V293_byteval 129)));
   [PubApart 212%positive 1%Z 1%Z|split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
   eapply PubStar with(m1:=V293_encoded_memory 213%positive 0%Z true(encode_val (Tint8) (V293_byteval 254)));
   [PubApart 213%positive 0%Z 1%Z|split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
   eapply PubStar with(m1:=V293_encoded_memory 301%positive 280%Z true(encode_val (Tcom_ptr 410%Z) (Vundef)));
   [PubApart 301%positive 280%Z 4%Z|split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
   split;reflexivity.
 - eapply PubStar with(m1:=V293_encoded_memory 201%positive 0%Z true(encode_val (Tptr V293_tcb_type) (Vptr(301%positive,Int.repr 128))));
   [PubApart 201%positive 0%Z 4%Z|split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
   eapply PubStar with(m1:=V293_encoded_memory 301%positive 148%Z true(encode_val (Tcom_ptr 410%Z) (Vundef)));
   [PubApart 301%positive 148%Z 4%Z|split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
   eapply PubStar with(m1:=V293_encoded_memory 301%positive 152%Z true(encode_val (Tcom_ptr 410%Z) (Vundef)));
   [PubApart 301%positive 152%Z 4%Z|split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
   eapply PubStar with(m1:=V293_encoded_memory 301%positive 180%Z true(encode_val (Tint8) (V293_byteval 1)));
   [PubApart 301%positive 180%Z 1%Z|split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
   eapply PubStar with(m1:=V293_encoded_memory 301%positive 182%Z true(encode_val (Tint8) (V293_byteval 2)));
   [PubApart 301%positive 182%Z 1%Z|split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
   eapply PubStar with(m1:=V293_encoded_memory 301%positive 181%Z true(encode_val (Tint8) (V293_byteval 8)));
   [PubApart 301%positive 181%Z 1%Z|split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
   eapply PubStar with(m1:=V293_encoded_memory 210%positive 0%Z true(encode_val (Tptr V293_tcb_type) (Vnull)));
   [PubApart 210%positive 0%Z 4%Z|split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
   eapply PubStar with(m1:=V293_encoded_memory 211%positive 0%Z true(encode_val (Tint8) (V293_byteval 1)));
   [PubApart 211%positive 0%Z 1%Z|split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
   eapply PubStar with(m1:=V293_encoded_memory 212%positive 1%Z true(encode_val (Tint8) (V293_byteval 129)));
   [PubApart 212%positive 1%Z 1%Z|split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
   eapply PubStar with(m1:=V293_encoded_memory 213%positive 0%Z true(encode_val (Tint8) (V293_byteval 254)));
   [PubApart 213%positive 0%Z 1%Z|split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
   split;reflexivity.
Qed.

Theorem PubLiteralEntry : forall initialized present cs,
 PubState(PubWhole initialized present) cs |=
 <||spec_done None||> ** V293_rdy_raw_cells(PubCells initialized present)(PubFrame cs).
Proof.
 intros initialized present cs.
 eapply PubStar with(m1:=emp)(m2:=PubWhole initialized present).
 - apply map_join_comm;apply map_join_emp.
 - split;[reflexivity| ]. split;reflexivity.
 - apply V293_raw_cells_join. unfold PubWhole.
   eapply PubStar with(m1:=PubMemory(PubCells initialized present))(m2:=merge PubCurrent PubSentinel).
   + apply map_join_merge;apply map_disjoint;intros [b off].
     destruct(Pos.eq_dec b 402%positive);[subst b;left| ].
     * destruct initialized,present;unfold PubCells,PubNew,PubOld;cbn [app PubMemory];PubOutside.
     * destruct(Pos.eq_dec b 601%positive);[subst b;left|right;left].
       -- destruct initialized,present;unfold PubCells,PubNew,PubOld;cbn [app PubMemory];PubOutside.
       -- unfold PubCurrent,PubSentinel,PubBytes. rewrite map_merge_semp by reflexivity.
          rewrite !V293_encoded_memory_outside by(left;congruence). reflexivity.
   + apply PubRawLiteral.
   + unfold PubFrame. eapply PubStar with(m1:=emp)(m2:=merge PubCurrent PubSentinel).
     * apply map_join_comm;apply map_join_emp.
     * repeat(eapply PubStar with(m1:=emp)(m2:=emp);
       [apply map_join_emp|split;[reflexivity|split;reflexivity]| ]).
       split;[reflexivity|split;reflexivity].
     * eapply PubStar with(m1:=emp)(m2:=merge PubCurrent PubSentinel).
       -- apply map_join_comm;apply map_join_emp.
       -- apply PubBindingsSpatial.
       -- apply PubRSpatial.
Qed.
Theorem PubInitialEntry : forall present cs, PubState(PubWhole false present) cs |= PubPre present cs.
Proof. apply PubLiteralEntry. Qed.
Theorem PubReturnEntry : forall present cs, PubState(PubWhole true present) cs |= PubPost present cs(Some(Vint32 Int.zero)).
Proof. intros. unfold PubPost. apply astar_l_apure_intro;[apply PubLiteralEntry|reflexivity]. Qed.
Definition PubChecked : forall Spec sd I present cs,
 InfRules Spec sd V293_witness_li I (PubPost present cs) Afalse
 (PubPre present cs) PubCode Afalse PubTid.
Proof.
 intros. change (InfRules Spec sd V293_witness_li I
 (V293_pub_return_post 108%Z 93%Z 94%Z 95%Z 96%Z
 201%positive 210%positive 211%positive 212%positive 213%positive
 (V293_pub_cells 201%positive 301%positive 128%Z 210%positive 211%positive 212%positive 213%positive
 301%positive 256%Z present 1 3 (V293_pub_old_head present 301%positive 256%Z) Vnull PubNew
 (Nat.setbit 1 1)(Nat.setbit 129 3) 255 PubNew) PubR (spec_done None)(fun _=>false) [] cs) Afalse
 (V293_pub_hstate 108%Z 93%Z 94%Z 95%Z 96%Z
 201%positive 210%positive 211%positive 212%positive 213%positive
 (V293_pub_cells 201%positive 301%positive 128%Z 210%positive 211%positive 212%positive 213%positive
 301%positive 256%Z present 1 3 Vundef Vundef (V293_pub_old_head present 301%positive 256%Z) 1 129 254 Vundef)
 PubR (spec_done None)(fun _=>false) [] cs) PubCode Afalse PubTid).
 apply V293_OS_TCBInit_publish_hoare;first[lia|unfold Int.max_unsigned,Int.modulus,Int.wordsize;cbn;lia|exact PubRGood|exact PubRCurLINV].
Qed.
Theorem PubCounterRead : forall s present cs result, s |= PubPost present cs result ->
 load Tint8(getmem s)(213%positive,0%Z)=Some(V293_byteval 255).
Proof.
 intros s present cs result HS. unfold PubPost,PubFinal in HS.
 eapply V293_star_load_r;[ |exact HS]. intros st H.
 eapply V293_star_load_r;[ |exact H]. intros st1 Owned.
 eapply(V293_rdy_raw_load(PubCells true present) _ _ _ _ st1);
 [do 9 right;left;reflexivity|reflexivity|exact Owned].
Qed.
Theorem PubWrongCounterRead : forall s present cs result, s |= PubPost present cs result ->
 load Tint8(getmem s)(213%positive,0%Z)<>Some(V293_byteval 254).
Proof. intros s present cs result HS. rewrite(PubCounterRead _ _ _ _ HS). discriminate. Qed.
Theorem PubReadyBitsRead : forall s present cs result, s |= PubPost present cs result ->
 load Tint8(getmem s)(211%positive,0%Z)=Some(V293_byteval 3) /\
 load Tint8(getmem s)(212%positive,1%Z)=Some(V293_byteval 137).
Proof.
 intros s present cs result HS. unfold PubPost,PubFinal in HS. split;
 (eapply V293_star_load_r;[ |exact HS];intros st H;
 eapply V293_star_load_r;[ |exact H];intros st1 Owned;
 eapply(V293_rdy_raw_load(PubCells true present) _ _ _ _ st1)).
 - do 7 right;left;reflexivity.
 - reflexivity.
 - exact Owned.
 - do 8 right;left;reflexivity.
 - reflexivity.
 - exact Owned.
Qed.
Theorem PubPreservesOldReadyBits : Nat.testbit 3 0=true /\ Nat.testbit 137 0=true /\ Nat.testbit 137 7=true /\
 Nat.testbit 3 1=true /\ Nat.testbit 137 3=true.
Proof. repeat split;reflexivity. Qed.
Theorem PubCoreSize : length(PubCells false false)=10 /\ length(PubCells false true)=11 /\
 fold_right(fun cell count=>typelen(snd(fst cell))+count) 0(PubCells false false)=22 /\
 fold_right(fun cell count=>typelen(snd(fst cell))+count) 0(PubCells false true)=26.
Proof. repeat split;reflexivity. Qed.

Lemma PubPostLoad : forall s present cs result a tp v,
 In(a,tp,v)(PubCells true present) -> rule_type_val_match tp v=true ->
 s |= PubPost present cs result -> load tp(getmem s) a=Some v.
Proof.
 intros s present cs result a tp v Member Typed HS. unfold PubPost,PubFinal in HS.
 eapply V293_star_load_r;[ |exact HS]. intros st H.
 eapply V293_star_load_r;[ |exact H]. intros st1 Owned.
 eapply(V293_rdy_raw_load(PubCells true present) _ _ _ _ st1);eassumption.
Qed.
Theorem PubLinksRead : forall s present cs result, s |= PubPost present cs result ->
 load(Tcom_ptr 410%Z)(getmem s)(301%positive,148%Z)=Some(PubOld present) /\
 load(Tcom_ptr 410%Z)(getmem s)(301%positive,152%Z)=Some Vnull /\
 load(Tptr V293_tcb_type)(getmem s)(210%positive,0%Z)=Some PubNew.
Proof.
 intros s present cs result HS. repeat split.
 - eapply PubPostLoad;[right;left;reflexivity|destruct present;reflexivity|exact HS].
 - eapply PubPostLoad;[do 2 right;left;reflexivity|reflexivity|exact HS].
 - eapply PubPostLoad;[do 6 right;left;reflexivity|reflexivity|exact HS].
Qed.
Theorem PubOldBacklinkRead : forall s cs result, s |= PubPost true cs result ->
 load(Tcom_ptr 410%Z)(getmem s)(301%positive,280%Z)=Some PubNew.
Proof. intros s cs result HS. eapply(PubPostLoad s true cs result);[do 10 right;left;reflexivity|reflexivity|exact HS]. Qed.
Theorem PubReturnedZero : forall s present cs result, s |= PubPost present cs result -> result=Some(Vint32 Int.zero).
Proof. intros s present cs result HS. apply astar_l_apure_elim in HS. tauto. Qed.
