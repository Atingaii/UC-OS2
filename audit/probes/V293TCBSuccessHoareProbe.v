(* Independent literal entry for the real nonempty-body Hoare theorem.
   No old probe import; no Hook or global startup invariant is instantiated. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.certiucos.v293.proofs.V293TCBFieldsHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TCBSuccessHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitPrefix.
Require Import CertiOS.certiucos.v293.code.V293OSTCBInitFunction.
Require Import CertiOS.certiucos.v293.code.V293OSTCBInitPrefix.
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
Definition SuccessGE : env := set (sig OSTCBCur (402%positive,Tptr Tvoid)) 91%Z (210%positive,Tptr V293_tcb_type).
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
Definition SuccessNext := Vptr(301%positive,Int.repr 256).
Definition SuccessCells pc cpu :=
 ((209%positive,0%Z),Tint32,cpu)::(SuccessOld++SuccessInputs pc++
 [((210%positive,0%Z),Tptr V293_tcb_type,SuccessHead);
  ((301%positive,148%Z),Tcom_ptr 410%Z,SuccessNext)]).
Definition SuccessFinalCells :=
 ((209%positive,0%Z),Tint32,Vint32 Int.zero)::(SuccessFinal++SuccessInputs SuccessHead++
 [((210%positive,0%Z),Tptr V293_tcb_type,SuccessNext);
  ((301%positive,148%Z),Tcom_ptr 410%Z,SuccessNext)]).
Definition SuccessWhole pc cpu := merge (SuccessMemory (SuccessCells pc cpu)) (merge SuccessCurrent SuccessSentinel).
Definition SuccessState M cs : RstateOP :=
 (SuccessGE,SuccessLE,M,(fun _=>false),(false,[],cs),(emp:osabst),spec_done None).
Definition SuccessR := CurTid SuccessTid ** LINV V293_witness_li SuccessTid [] **
 Amapsto (601%positive,0%Z) Tint8 true (Vint32(Int.repr 77)).
Definition SuccessFieldBindings := V293_tcb_fields_bindings 108%Z 101%Z 102%Z 103%Z 104%Z 105%Z 106%Z 107%Z
 201%positive 202%positive 203%positive 204%positive 205%positive 206%positive 207%positive 208%positive.
Definition SuccessBindings := SuccessFieldBindings ** V293_tcb_success_extra 210%positive 209%positive.
Definition SuccessFrame cs := OS[(fun _=>false),false,[],cs] ** (SuccessBindings ** SuccessR).
Definition SuccessPre pc cpu cs := <||spec_done None||> ** V293_rdy_raw_cells (SuccessCells pc cpu) (SuccessFrame cs).
Definition SuccessPost cs := <||spec_done None||> ** V293_rdy_raw_cells SuccessFinalCells (SuccessFrame cs).
Definition SuccessCode := sseq (V293_TCBInit_pop 91%Z 108%Z)
 (sseq (sprim excrit) (V293_TCBInit_fields 108%Z 101%Z 102%Z 103%Z 104%Z 105%Z 106%Z 107%Z)).
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
Theorem SuccessRawLiteral : forall pc cpu cs, SuccessState (SuccessMemory (SuccessCells pc cpu)) cs |= V293_rdy_raw_cells (SuccessCells pc cpu) Aemp.
Proof.
 intros pc cpu cs. unfold SuccessCells,SuccessOld,SuccessInputs,SuccessHead,SuccessNext.
 cbn [app SuccessMemory V293_rdy_raw_cells].
 eapply SuccessStar with (m1:=V293_encoded_memory 209%positive 0%Z true (encode_val Tint32 cpu));
 [SuccessApart 209%positive 0%Z 4%Z|split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
 eapply SuccessStar with (m1:=V293_encoded_memory 301%positive 128%Z true (encode_val (Tptr Tint32) (Vundef)));
 [SuccessApart 301%positive 128%Z 4%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply SuccessStar with (m1:=V293_encoded_memory 301%positive 178%Z true (encode_val (Tint8) (Vundef)));
 [SuccessApart 301%positive 178%Z 1%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply SuccessStar with (m1:=V293_encoded_memory 301%positive 176%Z true (encode_val (Tint8) (Vundef)));
 [SuccessApart 301%positive 176%Z 1%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply SuccessStar with (m1:=V293_encoded_memory 301%positive 177%Z true (encode_val (Tint8) (Vundef)));
 [SuccessApart 301%positive 177%Z 1%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply SuccessStar with (m1:=V293_encoded_memory 301%positive 172%Z true (encode_val (Tint32) (Vundef)));
 [SuccessApart 301%positive 172%Z 4%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply SuccessStar with (m1:=V293_encoded_memory 301%positive 132%Z true (encode_val (Tptr Tvoid) (Vundef)));
 [SuccessApart 301%positive 132%Z 4%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply SuccessStar with (m1:=V293_encoded_memory 301%positive 140%Z true (encode_val (Tint32) (Vundef)));
 [SuccessApart 301%positive 140%Z 4%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply SuccessStar with (m1:=V293_encoded_memory 301%positive 136%Z true (encode_val (Tptr Tint32) (Vundef)));
 [SuccessApart 301%positive 136%Z 4%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply SuccessStar with (m1:=V293_encoded_memory 301%positive 144%Z true (encode_val (Tint16) (Vundef)));
 [SuccessApart 301%positive 144%Z 2%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply SuccessStar with (m1:=V293_encoded_memory 301%positive 146%Z true (encode_val (Tint16) (Vundef)));
 [SuccessApart 301%positive 146%Z 2%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply SuccessStar with (m1:=V293_encoded_memory 301%positive 183%Z true (encode_val (Tint8) (Vundef)));
 [SuccessApart 301%positive 183%Z 1%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply SuccessStar with (m1:=V293_encoded_memory 301%positive 180%Z true (encode_val (Tint8) (Vundef)));
 [SuccessApart 301%positive 180%Z 1%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply SuccessStar with (m1:=V293_encoded_memory 301%positive 179%Z true (encode_val (Tint8) (Vundef)));
 [SuccessApart 301%positive 179%Z 1%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply SuccessStar with (m1:=V293_encoded_memory 301%positive 182%Z true (encode_val (Tint8) (Vundef)));
 [SuccessApart 301%positive 182%Z 1%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply SuccessStar with (m1:=V293_encoded_memory 301%positive 181%Z true (encode_val (Tint8) (Vundef)));
 [SuccessApart 301%positive 181%Z 1%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply SuccessStar with (m1:=V293_encoded_memory 301%positive 156%Z true (encode_val (Tcom_ptr 411%Z) (Vundef)));
 [SuccessApart 301%positive 156%Z 4%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply SuccessStar with (m1:=V293_encoded_memory 301%positive 164%Z true (encode_val (Tcom_ptr 412%Z) (Vundef)));
 [SuccessApart 301%positive 164%Z 4%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply SuccessStar with (m1:=V293_encoded_memory 301%positive 160%Z true (encode_val (Tptr Tvoid) (Vundef)));
 [SuccessApart 301%positive 160%Z 4%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply SuccessStar with (m1:=V293_encoded_memory 201%positive 0%Z true (encode_val (Tptr V293_tcb_type) (pc)));
 [SuccessApart 201%positive 0%Z 4%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply SuccessStar with (m1:=V293_encoded_memory 202%positive 0%Z true (encode_val (Tint8) (V293_byteval 11)));
 [SuccessApart 202%positive 0%Z 1%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply SuccessStar with (m1:=V293_encoded_memory 203%positive 0%Z true (encode_val (Tptr Tint32) (Vnull)));
 [SuccessApart 203%positive 0%Z 4%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply SuccessStar with (m1:=V293_encoded_memory 204%positive 0%Z true (encode_val (Tptr Tint32) (Vnull)));
 [SuccessApart 204%positive 0%Z 4%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply SuccessStar with (m1:=V293_encoded_memory 205%positive 0%Z true (encode_val (Tint16) (Vint32 Int.zero)));
 [SuccessApart 205%positive 0%Z 2%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply SuccessStar with (m1:=V293_encoded_memory 206%positive 0%Z true (encode_val (Tint32) (Vint32(Int.repr 128))));
 [SuccessApart 206%positive 0%Z 4%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply SuccessStar with (m1:=V293_encoded_memory 207%positive 0%Z true (encode_val (Tptr Tvoid) (Vnull)));
 [SuccessApart 207%positive 0%Z 4%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply SuccessStar with (m1:=V293_encoded_memory 208%positive 0%Z true (encode_val (Tint16) (Vint32 Int.zero)));
 [SuccessApart 208%positive 0%Z 2%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply SuccessStar with (m1:=V293_encoded_memory 210%positive 0%Z true (encode_val (Tptr V293_tcb_type) (Vptr(301%positive,Int.repr 128))));
 [SuccessApart 210%positive 0%Z 4%Z|split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
 eapply SuccessStar with (m1:=V293_encoded_memory 301%positive 148%Z true (encode_val (Tcom_ptr 410%Z) (Vptr(301%positive,Int.repr 256))));
 [SuccessApart 301%positive 148%Z 4%Z|split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
 split;reflexivity.
Qed.
Theorem SuccessLiteralEntry : forall pc cpu cs,
 SuccessState (SuccessWhole pc cpu) cs |= SuccessPre pc cpu cs.
Proof.
 intros pc cpu cs. unfold SuccessPre.
 eapply SuccessStar with (m1:=emp) (m2:=SuccessWhole pc cpu).
 - apply map_join_comm;apply map_join_emp.
 - split;[reflexivity| ]. split;reflexivity.
 - apply V293_raw_cells_join. unfold SuccessWhole.
   eapply SuccessStar with (m1:=SuccessMemory (SuccessCells pc cpu)) (m2:=merge SuccessCurrent SuccessSentinel).
   + apply map_join_merge;apply map_disjoint;intros [b off].
     destruct (Pos.eq_dec b 402%positive);[subst b;left| ].
     * unfold SuccessCells,SuccessOld,SuccessInputs. cbn [app SuccessMemory]. SuccessOutside.
     * destruct (Pos.eq_dec b 601%positive);[subst b;left|right;left].
       -- unfold SuccessCells,SuccessOld,SuccessInputs. cbn [app SuccessMemory]. SuccessOutside.
       -- unfold SuccessCurrent,SuccessSentinel,SuccessBytes.
          rewrite map_merge_semp by reflexivity.
          rewrite !V293_encoded_memory_outside by (left;congruence). reflexivity.
   + apply SuccessRawLiteral.
   + unfold SuccessFrame. eapply SuccessStar with (m1:=emp) (m2:=merge SuccessCurrent SuccessSentinel).
     * apply map_join_comm;apply map_join_emp.
     * repeat (eapply SuccessStar with (m1:=emp) (m2:=emp);
        [apply map_join_emp|split;[reflexivity|split;reflexivity]| ]).
       split;[reflexivity|split;reflexivity].
     * eapply SuccessStar with (m1:=emp) (m2:=merge SuccessCurrent SuccessSentinel).
       -- apply map_join_comm;apply map_join_emp.
       -- apply SuccessBindingsSpatial.
       -- apply SuccessRSpatial.
Qed.
Definition SuccessChecked : forall Spec sd I r ri cs,
 InfRules Spec sd V293_witness_li I r ri
 (SuccessPre SuccessHead (Vint32 Int.zero) (false::cs)) SuccessCode (SuccessPost cs) SuccessTid.
Proof.
 intros. exact (V293_OS_TCBInit_pop_fields_hoare Spec sd V293_witness_li I r ri SuccessTid (spec_done None) SuccessR
 210%positive 209%positive 201%positive 202%positive 203%positive 204%positive 205%positive 206%positive 207%positive 208%positive 301%positive 128%Z 11 Vnull Vnull (Vint32 Int.zero) (Vint32(Int.repr 128)) Vnull (Vint32 Int.zero) (fun _=>Vundef) (Vint32 Int.zero) SuccessNext (fun _=>false) [] cs
 ltac:(lia) ltac:(lia) ltac:(unfold Int.max_unsigned,Int.modulus,Int.wordsize;cbn;lia)
 ltac:(repeat split;reflexivity) ltac:(reflexivity) SuccessRGood SuccessRCurLINV).
Qed.
Definition SuccessBodyChecked : forall Spec sd I r ri hi hc cs,
 InfRules Spec sd V293_witness_li I r ri (SuccessPost cs)
 (V293_TCBInit_success_suffix hi hc) Afalse SuccessTid ->
 InfRules Spec sd V293_witness_li I r ri (SuccessPre Vundef Vundef cs)
 (V293_TCBInit_function_body hi hc) Afalse SuccessTid.
Proof.
 intros Spec sd I r ri hi hc cs Suffix.
 exact (V293_OS_TCBInit_nonempty_body_with_suffix_hoare Spec sd V293_witness_li I r ri SuccessTid hi hc (spec_done None) SuccessR
 210%positive 209%positive 201%positive 202%positive 203%positive 204%positive 205%positive 206%positive 207%positive 208%positive 301%positive 128%Z 11 Vnull Vnull (Vint32 Int.zero) (Vint32(Int.repr 128)) Vnull (Vint32 Int.zero) (fun _=>Vundef) Vundef Vundef SuccessNext (fun _=>false) [] cs
 ltac:(lia) ltac:(lia) ltac:(unfold Int.max_unsigned,Int.modulus,Int.wordsize;cbn;lia)
 ltac:(repeat split;reflexivity) ltac:(reflexivity) SuccessRGood SuccessRCurLINV Suffix).
Qed.
Theorem SuccessHeadRead : forall s cs,
 s |= SuccessPost cs -> load (Tptr V293_tcb_type) (getmem s) (210%positive,0%Z)=Some SuccessNext.
Proof.
 intros s cs HS. unfold SuccessPost in HS. eapply V293_star_load_r;[ |exact HS]. intros st Owned.
 eapply (V293_rdy_raw_load SuccessFinalCells _ _ _ _ st);
 [do 27 right;left;reflexivity|reflexivity|exact Owned].
Qed.
Theorem SuccessWrongHeadRead : forall s cs,
 s |= SuccessPost cs -> load (Tptr V293_tcb_type) (getmem s) (210%positive,0%Z)<>Some SuccessHead.
Proof. intros s cs HS. rewrite (SuccessHeadRead _ _ HS). discriminate. Qed.
Theorem SuccessNextPreserved : forall s cs,
 s |= SuccessPost cs -> load (Tcom_ptr 410%Z) (getmem s) (301%positive,148%Z)=Some SuccessNext.
Proof.
 intros s cs HS. unfold SuccessPost in HS. eapply V293_star_load_r;[ |exact HS]. intros st Owned.
 eapply (V293_rdy_raw_load SuccessFinalCells _ _ _ _ st);
 [do 28 right;left;reflexivity|reflexivity|exact Owned].
Qed.
Theorem SuccessInitialEntry : forall cs,
 SuccessState (SuccessWhole Vundef Vundef) cs |= SuccessPre Vundef Vundef cs.
Proof. apply SuccessLiteralEntry. Qed.
Theorem SuccessPopEntry : forall cs,
 SuccessState (SuccessWhole SuccessHead (Vint32 Int.zero)) (false::cs) |= SuccessPre SuccessHead (Vint32 Int.zero) (false::cs).
Proof. intro cs. apply SuccessLiteralEntry. Qed.
Theorem SuccessCoreSize : length (SuccessCells Vundef Vundef)=29 /\
 fold_right (fun cell count=>typelen(snd(fst cell))+count) 0 (SuccessCells Vundef Vundef)=81.
Proof. split;reflexivity. Qed.
