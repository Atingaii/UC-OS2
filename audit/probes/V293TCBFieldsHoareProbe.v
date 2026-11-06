(* Independent literal entry for the real eighteen-store Hoare theorem.
   No old probe import; no Hook or global startup invariant is instantiated. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.certiucos.v293.proofs.V293TCBFieldsHoare.
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
Definition FieldsOld : list V293_record_cell :=
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
Definition FieldsInputs : list V293_record_cell :=
 [((201%positive,0%Z),(Tptr V293_tcb_type),(Vptr(301%positive,Int.repr 128)));
  ((202%positive,0%Z),(Tint8),(V293_byteval 11));
  ((203%positive,0%Z),(Tptr Tint32),(Vnull));
  ((204%positive,0%Z),(Tptr Tint32),(Vnull));
  ((205%positive,0%Z),(Tint16),(Vint32 Int.zero));
  ((206%positive,0%Z),(Tint32),(Vint32(Int.repr 128)));
  ((207%positive,0%Z),(Tptr Tvoid),(Vnull));
  ((208%positive,0%Z),(Tint16),(Vint32 Int.zero))].
Definition FieldsFinal : list V293_record_cell :=
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
Definition FieldsGE : env := sig OSTCBCur (402%positive,Tptr Tvoid).
Definition FieldsLE : env :=
 set (set (set (set (set (set (set (set (emp:env)
 108%Z (201%positive,Tptr V293_tcb_type)) 101%Z (202%positive,Tint8))
 102%Z (203%positive,Tptr Tint32)) 103%Z (204%positive,Tptr Tint32))
 104%Z (205%positive,Tint16)) 105%Z (206%positive,Tint32))
 106%Z (207%positive,Tptr Tvoid)) 107%Z (208%positive,Tint16).
Definition FieldsTid : tid := (301%positive,Int.repr 8).
Definition FieldsBytes b permission tp v := V293_encoded_memory b 0 permission (encode_val tp v).
Definition FieldsCurrent := FieldsBytes 402%positive false (Tptr Tvoid) (Vptr FieldsTid).
Definition FieldsSentinel := FieldsBytes 601%positive true Tint8 (Vint32(Int.repr 77)).
Fixpoint FieldsMemory (cells : list V293_record_cell) : mem :=
 match cells with []=>emp | ((b,i),tp,v)::tail=>
 merge (V293_encoded_memory b i true (encode_val tp v)) (FieldsMemory tail) end.
Definition FieldsCells := FieldsOld++FieldsInputs.
Definition FieldsWhole := merge (FieldsMemory FieldsCells) (merge FieldsCurrent FieldsSentinel).
Definition FieldsState M cs : RstateOP :=
 (FieldsGE,FieldsLE,M,(fun _=>false),(false,[],cs),(emp:osabst),spec_done None).
Definition FieldsR := CurTid FieldsTid ** LINV V293_witness_li FieldsTid [] **
 Amapsto (601%positive,0%Z) Tint8 true (Vint32(Int.repr 77)).
Definition FieldsFrame cs := OS[(fun _=>false),false,[],cs] ** FieldsR.
Definition FieldsBindings := V293_tcb_fields_bindings 108%Z 101%Z 102%Z 103%Z 104%Z 105%Z 106%Z 107%Z
 201%positive 202%positive 203%positive 204%positive 205%positive 206%positive 207%positive 208%positive.
Definition FieldsPre cs := <||spec_done None||> **
 V293_rdy_raw_cells FieldsCells (FieldsBindings ** FieldsFrame cs).
Definition FieldsPost cs := <||spec_done None||> **
 V293_rdy_raw_cells (FieldsFinal++FieldsInputs) (FieldsBindings ** FieldsFrame cs).
Definition FieldsCode := V293_TCBInit_fields 108%Z 101%Z 102%Z 103%Z 104%Z 105%Z 106%Z 107%Z.
Lemma FieldsStar : forall m1 m2 m cs p q,
 join m1 m2 m -> FieldsState m1 cs |= p -> FieldsState m2 cs |= q ->
 FieldsState m cs |= p ** q.
Proof.
 intros. apply sat_split'. exists m1. exists m2.
 exists(emp:osabst). exists(emp:osabst).
 split;[exact H | ]. split;[apply map_join_emp | ]. split;assumption.
Qed.
Lemma FieldsCurrentSpatial : forall cs, FieldsState FieldsCurrent cs |= CurTid FieldsTid.
Proof.
 intro cs. exists Tvoid. exists 402%positive.
 eapply FieldsStar with (m1:=emp) (m2:=FieldsCurrent).
 - apply map_join_comm;apply map_join_emp.
 - exists 402%positive. split;[vm_compute;reflexivity | ]. repeat split;reflexivity.
 - split;[apply V293_encoded_memory_mapsto|reflexivity].
Qed.
Lemma FieldsLInvSpatial : forall cs, FieldsState emp cs |= LINV V293_witness_li FieldsTid [].
Proof.
 intro cs. unfold LINV. apply astar_comm. apply astar_l_apure_intro.
 - split;reflexivity.
 - apply V293_witness_li_good.
Qed.
Ltac FieldsFrameApart b :=
 apply map_join_merge;apply map_disjoint;intros [other offset];
 destruct(Pos.eq_dec other b);[subst other;right;left|left];
 unfold FieldsCurrent,FieldsSentinel,FieldsBytes;
 repeat first [rewrite map_merge_semp by reflexivity |
 rewrite V293_encoded_memory_outside by (left;congruence)];reflexivity.
Lemma FieldsRSpatial : forall cs,
 FieldsState (merge FieldsCurrent FieldsSentinel) cs |= FieldsR.
Proof.
 intro cs. unfold FieldsR.
 eapply FieldsStar with (m1:=FieldsCurrent) (m2:=FieldsSentinel).
 - FieldsFrameApart 402%positive.
 - apply FieldsCurrentSpatial.
 - eapply FieldsStar with (m1:=emp) (m2:=FieldsSentinel).
   + apply map_join_comm;apply map_join_emp.
   + apply FieldsLInvSpatial.
   + split;[apply V293_encoded_memory_mapsto|reflexivity].
Qed.
Lemma FieldsRGood : GoodFrm FieldsR.
Proof. cbn [FieldsR CurTid LINV V293_witness_li GoodFrm]. repeat split;exact I. Qed.
Lemma FieldsRCurLINV : FieldsR ==> CurLINV V293_witness_li FieldsTid.
Proof.
 intros s HS. unfold CurLINV. exists([]:list logicvar).
 unfold FieldsR in HS. clear -HS. sep auto.
Qed.
Lemma FieldsBindingsSpatial : forall cs, FieldsState emp cs |= FieldsBindings.
Proof.
 intro cs. unfold FieldsBindings,V293_tcb_fields_bindings. repeat split.
 - exists 201%positive. split;[vm_compute;reflexivity | ]. repeat split;reflexivity.
 - exists 202%positive. split;[vm_compute;reflexivity | ]. repeat split;reflexivity.
 - exists 203%positive. split;[vm_compute;reflexivity | ]. repeat split;reflexivity.
 - exists 204%positive. split;[vm_compute;reflexivity | ]. repeat split;reflexivity.
 - exists 205%positive. split;[vm_compute;reflexivity | ]. repeat split;reflexivity.
 - exists 206%positive. split;[vm_compute;reflexivity | ]. repeat split;reflexivity.
 - exists 207%positive. split;[vm_compute;reflexivity | ]. repeat split;reflexivity.
 - exists 208%positive. split;[vm_compute;reflexivity | ]. repeat split;reflexivity.
Qed.
Lemma FieldsFrameCurLINV : forall cs, FieldsFrame cs ==> CurLINV V293_witness_li FieldsTid.
Proof. intro cs. unfold FieldsFrame. apply V293_star_CurLINV_r;apply FieldsRCurLINV. Qed.
Ltac FieldsOutside :=
 repeat first [rewrite V293_encoded_memory_outside by
 (first [left;congruence | right;cbn [V293_byteval length encode_val typelen list_repeat inj_pointer inj_bytes encode_int List.map];lia])
 |rewrite map_merge_semp by reflexivity];reflexivity.
Ltac FieldsApart b start count :=
 apply map_join_merge;apply map_disjoint;intros [other off];
 destruct (Pos.eq_dec other b) as [B|B];
 [subst other;destruct (Z_lt_dec off start) as [Low|Low];
 [left;apply V293_encoded_memory_outside;right;left;exact Low |
 destruct (Z_lt_dec off (start+count)) as [Inside|Outside];
 [right;left;FieldsOutside |left;apply V293_encoded_memory_outside;right;right;
 cbn [V293_byteval length encode_val typelen list_repeat inj_pointer inj_bytes encode_int List.map];lia]] |
 left;apply V293_encoded_memory_outside;left;exact B].
Theorem FieldsRawLiteral : forall cs, FieldsState (FieldsMemory FieldsCells) cs |= V293_rdy_raw_cells FieldsCells Aemp.
Proof.
 intro cs. unfold FieldsCells,FieldsOld,FieldsInputs.
 cbn [app FieldsMemory V293_rdy_raw_cells].
 eapply FieldsStar with (m1:=V293_encoded_memory 301%positive 128%Z true (encode_val (Tptr Tint32) (Vundef)));
 [FieldsApart 301%positive 128%Z 4%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply FieldsStar with (m1:=V293_encoded_memory 301%positive 178%Z true (encode_val (Tint8) (Vundef)));
 [FieldsApart 301%positive 178%Z 1%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply FieldsStar with (m1:=V293_encoded_memory 301%positive 176%Z true (encode_val (Tint8) (Vundef)));
 [FieldsApart 301%positive 176%Z 1%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply FieldsStar with (m1:=V293_encoded_memory 301%positive 177%Z true (encode_val (Tint8) (Vundef)));
 [FieldsApart 301%positive 177%Z 1%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply FieldsStar with (m1:=V293_encoded_memory 301%positive 172%Z true (encode_val (Tint32) (Vundef)));
 [FieldsApart 301%positive 172%Z 4%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply FieldsStar with (m1:=V293_encoded_memory 301%positive 132%Z true (encode_val (Tptr Tvoid) (Vundef)));
 [FieldsApart 301%positive 132%Z 4%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply FieldsStar with (m1:=V293_encoded_memory 301%positive 140%Z true (encode_val (Tint32) (Vundef)));
 [FieldsApart 301%positive 140%Z 4%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply FieldsStar with (m1:=V293_encoded_memory 301%positive 136%Z true (encode_val (Tptr Tint32) (Vundef)));
 [FieldsApart 301%positive 136%Z 4%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply FieldsStar with (m1:=V293_encoded_memory 301%positive 144%Z true (encode_val (Tint16) (Vundef)));
 [FieldsApart 301%positive 144%Z 2%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply FieldsStar with (m1:=V293_encoded_memory 301%positive 146%Z true (encode_val (Tint16) (Vundef)));
 [FieldsApart 301%positive 146%Z 2%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply FieldsStar with (m1:=V293_encoded_memory 301%positive 183%Z true (encode_val (Tint8) (Vundef)));
 [FieldsApart 301%positive 183%Z 1%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply FieldsStar with (m1:=V293_encoded_memory 301%positive 180%Z true (encode_val (Tint8) (Vundef)));
 [FieldsApart 301%positive 180%Z 1%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply FieldsStar with (m1:=V293_encoded_memory 301%positive 179%Z true (encode_val (Tint8) (Vundef)));
 [FieldsApart 301%positive 179%Z 1%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply FieldsStar with (m1:=V293_encoded_memory 301%positive 182%Z true (encode_val (Tint8) (Vundef)));
 [FieldsApart 301%positive 182%Z 1%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply FieldsStar with (m1:=V293_encoded_memory 301%positive 181%Z true (encode_val (Tint8) (Vundef)));
 [FieldsApart 301%positive 181%Z 1%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply FieldsStar with (m1:=V293_encoded_memory 301%positive 156%Z true (encode_val (Tcom_ptr 411%Z) (Vundef)));
 [FieldsApart 301%positive 156%Z 4%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply FieldsStar with (m1:=V293_encoded_memory 301%positive 164%Z true (encode_val (Tcom_ptr 412%Z) (Vundef)));
 [FieldsApart 301%positive 164%Z 4%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply FieldsStar with (m1:=V293_encoded_memory 301%positive 160%Z true (encode_val (Tptr Tvoid) (Vundef)));
 [FieldsApart 301%positive 160%Z 4%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply FieldsStar with (m1:=V293_encoded_memory 201%positive 0%Z true (encode_val (Tptr V293_tcb_type) (Vptr(301%positive,Int.repr 128))));
 [FieldsApart 201%positive 0%Z 4%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply FieldsStar with (m1:=V293_encoded_memory 202%positive 0%Z true (encode_val (Tint8) (V293_byteval 11)));
 [FieldsApart 202%positive 0%Z 1%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply FieldsStar with (m1:=V293_encoded_memory 203%positive 0%Z true (encode_val (Tptr Tint32) (Vnull)));
 [FieldsApart 203%positive 0%Z 4%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply FieldsStar with (m1:=V293_encoded_memory 204%positive 0%Z true (encode_val (Tptr Tint32) (Vnull)));
 [FieldsApart 204%positive 0%Z 4%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply FieldsStar with (m1:=V293_encoded_memory 205%positive 0%Z true (encode_val (Tint16) (Vint32 Int.zero)));
 [FieldsApart 205%positive 0%Z 2%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply FieldsStar with (m1:=V293_encoded_memory 206%positive 0%Z true (encode_val (Tint32) (Vint32(Int.repr 128))));
 [FieldsApart 206%positive 0%Z 4%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply FieldsStar with (m1:=V293_encoded_memory 207%positive 0%Z true (encode_val (Tptr Tvoid) (Vnull)));
 [FieldsApart 207%positive 0%Z 4%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply FieldsStar with (m1:=V293_encoded_memory 208%positive 0%Z true (encode_val (Tint16) (Vint32 Int.zero)));
 [FieldsApart 208%positive 0%Z 2%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 split;reflexivity.
Qed.
Theorem FieldsLiteralEntry : forall cs, FieldsState FieldsWhole cs |= FieldsPre cs.
Proof.
 intro cs. unfold FieldsPre.
 eapply FieldsStar with (m1:=emp) (m2:=FieldsWhole).
 - apply map_join_comm;apply map_join_emp.
 - split;[reflexivity | ]. split;reflexivity.
 - apply V293_raw_cells_join. unfold FieldsWhole.
   eapply FieldsStar with (m1:=FieldsMemory FieldsCells) (m2:=merge FieldsCurrent FieldsSentinel).
   + apply map_join_merge;apply map_disjoint;intros [b off].
     destruct (Pos.eq_dec b 402%positive);[subst b;left | ].
     * unfold FieldsCells,FieldsOld,FieldsInputs. cbn [app FieldsMemory]. FieldsOutside.
     * destruct (Pos.eq_dec b 601%positive);[subst b;left |right;left].
       -- unfold FieldsCells,FieldsOld,FieldsInputs. cbn [app FieldsMemory]. FieldsOutside.
       -- unfold FieldsCurrent,FieldsSentinel,FieldsBytes.
          rewrite map_merge_semp by reflexivity.
          rewrite !V293_encoded_memory_outside by (left;congruence). reflexivity.
   + apply FieldsRawLiteral.
   + eapply FieldsStar with (m1:=emp) (m2:=merge FieldsCurrent FieldsSentinel).
     * apply map_join_comm;apply map_join_emp.
     * apply FieldsBindingsSpatial.
     * unfold FieldsFrame. eapply FieldsStar with (m1:=emp) (m2:=merge FieldsCurrent FieldsSentinel).
       -- apply map_join_comm;apply map_join_emp.
       -- repeat (eapply FieldsStar with (m1:=emp) (m2:=emp);
          [apply map_join_emp|split;[reflexivity|split;reflexivity] | ]).
          split;[reflexivity|split;reflexivity].
       -- apply FieldsRSpatial.
Qed.
Definition FieldsChecked : forall Spec sd I r ri cs,
 InfRules Spec sd V293_witness_li I r ri (FieldsPre cs) FieldsCode (FieldsPost cs) FieldsTid.
Proof.
 intros. unfold FieldsPre,FieldsPost,FieldsCells,FieldsBindings,FieldsCode.
 change (InfRules Spec sd V293_witness_li I r ri
 (<||spec_done None||> ** V293_rdy_raw_cells
  (V293_tcb_init_old_fields 301%positive 128%Z (fun _=>Vundef) ++
   V293_tcb_init_input_cells 201%positive 202%positive 203%positive 204%positive 205%positive 206%positive 207%positive 208%positive
    301%positive 128%Z 11 Vnull Vnull (Vint32 Int.zero) (Vint32(Int.repr 128)) Vnull (Vint32 Int.zero))
  (V293_tcb_fields_bindings 108%Z 101%Z 102%Z 103%Z 104%Z 105%Z 106%Z 107%Z
    201%positive 202%positive 203%positive 204%positive 205%positive 206%positive 207%positive 208%positive ** FieldsFrame cs))
 (V293_TCBInit_fields 108%Z 101%Z 102%Z 103%Z 104%Z 105%Z 106%Z 107%Z)
 (<||spec_done None||> ** V293_rdy_raw_cells
  (V293_tcb_init_final_fields 301%positive 128%Z 11 Vnull Vnull (Vint32 Int.zero) (Vint32(Int.repr 128)) Vnull (Vint32 Int.zero) ++
   V293_tcb_init_input_cells 201%positive 202%positive 203%positive 204%positive 205%positive 206%positive 207%positive 208%positive
    301%positive 128%Z 11 Vnull Vnull (Vint32 Int.zero) (Vint32(Int.repr 128)) Vnull (Vint32 Int.zero))
  (V293_tcb_fields_bindings 108%Z 101%Z 102%Z 103%Z 104%Z 105%Z 106%Z 107%Z
    201%positive 202%positive 203%positive 204%positive 205%positive 206%positive 207%positive 208%positive ** FieldsFrame cs)) FieldsTid).
 apply V293_OS_TCBInit_fields_hoare;try (unfold Int.max_unsigned,Int.modulus,Int.wordsize;cbn;lia).
 - repeat split;reflexivity.
 - apply FieldsFrameCurLINV.
Qed.
Theorem FieldsPriorityRead : forall s cs,
 s |= FieldsPost cs -> load Tint8 (getmem s) (301%positive,178%Z)=Some(V293_byteval 11).
Proof.
 intros s cs HS. unfold FieldsPost in HS.
 eapply V293_star_load_r;[ |exact HS]. intros st Owned.
 eapply (V293_rdy_raw_load (FieldsFinal++FieldsInputs) _ _ _ _ st);[right;left;reflexivity|reflexivity|exact Owned].
Qed.
Theorem FieldsWrongPriorityRead : forall s cs,
 s |= FieldsPost cs -> load Tint8 (getmem s) (301%positive,178%Z)<>Some(V293_byteval 10).
Proof. intros s cs HS. rewrite (FieldsPriorityRead _ _ HS). discriminate. Qed.

Definition RecordsExisting : list V293_record_cell :=
 [((301%positive,58%Z),(Tint8),(V293_byteval 12));
  ((301%positive,60%Z),(Tint8),(V293_byteval 1));
  ((301%positive,59%Z),(Tint8),(V293_byteval 4));
  ((301%positive,62%Z),(Tint8),(V293_byteval 2));
  ((301%positive,61%Z),(Tint8),(V293_byteval 16));
  ((301%positive,40%Z),(Tptr Tvoid),(Vnull));
  ((301%positive,56%Z),(Tint8),(V293_byteval 0))].

Definition RecordsTasks : TcbMod.map := sig FieldsTid (Int.repr 12,rdy,Vnull).
Definition RecordsNewTid : tid := (301%positive,Int.repr 128).
Definition RecordsWhole := merge (FieldsMemory (FieldsCells++RecordsExisting)) (merge FieldsCurrent FieldsSentinel).
Definition RecordsRawPre cs := <||spec_done None||> **
 V293_rdy_raw_cells (FieldsCells++RecordsExisting) (FieldsBindings ** FieldsFrame cs).
Definition RecordsPre cs := <||spec_done None||> **
 V293_rdy_raw_cells FieldsCells (FieldsBindings ** (V293_owned_task_records RecordsTasks ** FieldsFrame cs)).
Definition RecordsPost cs := <||spec_done None||> **
 (V293_owned_task_records (set RecordsTasks RecordsNewTid (Int.repr 11,rdy,Vnull)) **
 V293_rdy_raw_cells
  (V293_tcb_init_record_remainder 301%positive 128%Z Vnull Vnull (Vint32 Int.zero)
   (Vint32(Int.repr 128)) Vnull (Vint32 Int.zero))
  (V293_rdy_raw_cells FieldsInputs (FieldsBindings ** FieldsFrame cs))).
Theorem RecordsRawLiteral : forall cs, FieldsState (FieldsMemory (FieldsCells++RecordsExisting)) cs |= V293_rdy_raw_cells (FieldsCells++RecordsExisting) Aemp.
Proof.
 intro cs. unfold FieldsCells,FieldsOld,FieldsInputs,RecordsExisting.
 cbn [app FieldsMemory V293_rdy_raw_cells].
 eapply FieldsStar with (m1:=V293_encoded_memory 301%positive 128%Z true (encode_val (Tptr Tint32) (Vundef)));
 [FieldsApart 301%positive 128%Z 4%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply FieldsStar with (m1:=V293_encoded_memory 301%positive 178%Z true (encode_val (Tint8) (Vundef)));
 [FieldsApart 301%positive 178%Z 1%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply FieldsStar with (m1:=V293_encoded_memory 301%positive 176%Z true (encode_val (Tint8) (Vundef)));
 [FieldsApart 301%positive 176%Z 1%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply FieldsStar with (m1:=V293_encoded_memory 301%positive 177%Z true (encode_val (Tint8) (Vundef)));
 [FieldsApart 301%positive 177%Z 1%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply FieldsStar with (m1:=V293_encoded_memory 301%positive 172%Z true (encode_val (Tint32) (Vundef)));
 [FieldsApart 301%positive 172%Z 4%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply FieldsStar with (m1:=V293_encoded_memory 301%positive 132%Z true (encode_val (Tptr Tvoid) (Vundef)));
 [FieldsApart 301%positive 132%Z 4%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply FieldsStar with (m1:=V293_encoded_memory 301%positive 140%Z true (encode_val (Tint32) (Vundef)));
 [FieldsApart 301%positive 140%Z 4%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply FieldsStar with (m1:=V293_encoded_memory 301%positive 136%Z true (encode_val (Tptr Tint32) (Vundef)));
 [FieldsApart 301%positive 136%Z 4%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply FieldsStar with (m1:=V293_encoded_memory 301%positive 144%Z true (encode_val (Tint16) (Vundef)));
 [FieldsApart 301%positive 144%Z 2%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply FieldsStar with (m1:=V293_encoded_memory 301%positive 146%Z true (encode_val (Tint16) (Vundef)));
 [FieldsApart 301%positive 146%Z 2%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply FieldsStar with (m1:=V293_encoded_memory 301%positive 183%Z true (encode_val (Tint8) (Vundef)));
 [FieldsApart 301%positive 183%Z 1%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply FieldsStar with (m1:=V293_encoded_memory 301%positive 180%Z true (encode_val (Tint8) (Vundef)));
 [FieldsApart 301%positive 180%Z 1%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply FieldsStar with (m1:=V293_encoded_memory 301%positive 179%Z true (encode_val (Tint8) (Vundef)));
 [FieldsApart 301%positive 179%Z 1%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply FieldsStar with (m1:=V293_encoded_memory 301%positive 182%Z true (encode_val (Tint8) (Vundef)));
 [FieldsApart 301%positive 182%Z 1%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply FieldsStar with (m1:=V293_encoded_memory 301%positive 181%Z true (encode_val (Tint8) (Vundef)));
 [FieldsApart 301%positive 181%Z 1%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply FieldsStar with (m1:=V293_encoded_memory 301%positive 156%Z true (encode_val (Tcom_ptr 411%Z) (Vundef)));
 [FieldsApart 301%positive 156%Z 4%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply FieldsStar with (m1:=V293_encoded_memory 301%positive 164%Z true (encode_val (Tcom_ptr 412%Z) (Vundef)));
 [FieldsApart 301%positive 164%Z 4%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply FieldsStar with (m1:=V293_encoded_memory 301%positive 160%Z true (encode_val (Tptr Tvoid) (Vundef)));
 [FieldsApart 301%positive 160%Z 4%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply FieldsStar with (m1:=V293_encoded_memory 201%positive 0%Z true (encode_val (Tptr V293_tcb_type) (Vptr(301%positive,Int.repr 128))));
 [FieldsApart 201%positive 0%Z 4%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply FieldsStar with (m1:=V293_encoded_memory 202%positive 0%Z true (encode_val (Tint8) (V293_byteval 11)));
 [FieldsApart 202%positive 0%Z 1%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply FieldsStar with (m1:=V293_encoded_memory 203%positive 0%Z true (encode_val (Tptr Tint32) (Vnull)));
 [FieldsApart 203%positive 0%Z 4%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply FieldsStar with (m1:=V293_encoded_memory 204%positive 0%Z true (encode_val (Tptr Tint32) (Vnull)));
 [FieldsApart 204%positive 0%Z 4%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply FieldsStar with (m1:=V293_encoded_memory 205%positive 0%Z true (encode_val (Tint16) (Vint32 Int.zero)));
 [FieldsApart 205%positive 0%Z 2%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply FieldsStar with (m1:=V293_encoded_memory 206%positive 0%Z true (encode_val (Tint32) (Vint32(Int.repr 128))));
 [FieldsApart 206%positive 0%Z 4%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply FieldsStar with (m1:=V293_encoded_memory 207%positive 0%Z true (encode_val (Tptr Tvoid) (Vnull)));
 [FieldsApart 207%positive 0%Z 4%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply FieldsStar with (m1:=V293_encoded_memory 208%positive 0%Z true (encode_val (Tint16) (Vint32 Int.zero)));
 [FieldsApart 208%positive 0%Z 2%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply FieldsStar with (m1:=V293_encoded_memory 301%positive 58%Z true (encode_val (Tint8) (V293_byteval 12)));
 [FieldsApart 301%positive 58%Z 1%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply FieldsStar with (m1:=V293_encoded_memory 301%positive 60%Z true (encode_val (Tint8) (V293_byteval 1)));
 [FieldsApart 301%positive 60%Z 1%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply FieldsStar with (m1:=V293_encoded_memory 301%positive 59%Z true (encode_val (Tint8) (V293_byteval 4)));
 [FieldsApart 301%positive 59%Z 1%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply FieldsStar with (m1:=V293_encoded_memory 301%positive 62%Z true (encode_val (Tint8) (V293_byteval 2)));
 [FieldsApart 301%positive 62%Z 1%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply FieldsStar with (m1:=V293_encoded_memory 301%positive 61%Z true (encode_val (Tint8) (V293_byteval 16)));
 [FieldsApart 301%positive 61%Z 1%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply FieldsStar with (m1:=V293_encoded_memory 301%positive 40%Z true (encode_val (Tptr Tvoid) (Vnull)));
 [FieldsApart 301%positive 40%Z 4%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 eapply FieldsStar with (m1:=V293_encoded_memory 301%positive 56%Z true (encode_val (Tint8) (V293_byteval 0)));
 [FieldsApart 301%positive 56%Z 1%Z |split;[apply V293_encoded_memory_mapsto |reflexivity] | ].
 split;reflexivity.
Qed.
Theorem RecordsRawEntry : forall cs, FieldsState RecordsWhole cs |= RecordsRawPre cs.
Proof.
 intro cs. unfold RecordsRawPre.
 eapply FieldsStar with (m1:=emp) (m2:=RecordsWhole).
 - apply map_join_comm;apply map_join_emp.
 - split;[reflexivity | ]. split;reflexivity.
 - apply V293_raw_cells_join. unfold RecordsWhole.
   eapply FieldsStar with (m1:=FieldsMemory (FieldsCells++RecordsExisting)) (m2:=merge FieldsCurrent FieldsSentinel).
   + apply map_join_merge;apply map_disjoint;intros [b off].
     destruct (Pos.eq_dec b 402%positive);[subst b;left | ].
     * unfold FieldsCells,FieldsOld,FieldsInputs,RecordsExisting. cbn [app FieldsMemory]. FieldsOutside.
     * destruct (Pos.eq_dec b 601%positive);[subst b;left |right;left].
       -- unfold FieldsCells,FieldsOld,FieldsInputs,RecordsExisting. cbn [app FieldsMemory]. FieldsOutside.
       -- unfold FieldsCurrent,FieldsSentinel,FieldsBytes.
          rewrite map_merge_semp by reflexivity.
          rewrite !V293_encoded_memory_outside by (left;congruence). reflexivity.
   + apply RecordsRawLiteral.
   + eapply FieldsStar with (m1:=emp) (m2:=merge FieldsCurrent FieldsSentinel).
     * apply map_join_comm;apply map_join_emp.
     * apply FieldsBindingsSpatial.
     * unfold FieldsFrame. eapply FieldsStar with (m1:=emp) (m2:=merge FieldsCurrent FieldsSentinel).
       -- apply map_join_comm;apply map_join_emp.
       -- repeat (eapply FieldsStar with (m1:=emp) (m2:=emp);
          [apply map_join_emp|split;[reflexivity|split;reflexivity] | ]).
          split;[reflexivity|split;reflexivity].
       -- apply FieldsRSpatial.
Qed.
Theorem RecordsExistingOwned : forall R,
 V293_rdy_raw_cells RecordsExisting R ==> V293_owned_task_records RecordsTasks ** R.
Proof.
 intros R s Owned.
 assert (Types : Forall (fun cell => let '(_,tp,v):=cell in rule_type_val_match tp v=true) RecordsExisting)
 by (repeat constructor).
 apply (V293_raw_record_ownership _ _ Types) in Owned.
 assert (Held : s |= V293_owned_task_record FieldsTid (Int.repr 12) rdy Vnull ** R).
 { eapply astar_mono;[ |intros st HS;exact HS |exact Owned].
 intros st HS. exists 12. exists 0. apply astar_l_apure_intro;[exact HS |repeat split;try reflexivity;lia]. }
 change (s |= (V293_owned_task_record FieldsTid (Int.repr 12) rdy Vnull ** Aemp) ** R).
 clear -Held. sep auto.
Qed.
Theorem RecordsLiteralEntry : forall cs, FieldsState RecordsWhole cs |= RecordsPre cs.
Proof.
 intro cs. pose proof (RecordsRawEntry cs) as H.
 unfold RecordsRawPre in H. unfold RecordsPre. rewrite V293_raw_cells_append in H.
 eapply astar_mono;[intros st HS;exact HS| |exact H].
 eapply V293_raw_cells_mono. intros st HS.
 pose proof (RecordsExistingOwned _ st HS) as Held. clear -Held. sep auto.
Qed.
Theorem RecordsFresh : get RecordsTasks RecordsNewTid=None.
Proof. reflexivity. Qed.
Definition RecordsChecked : forall Spec sd I r ri cs,
 InfRules Spec sd V293_witness_li I r ri (RecordsPre cs) FieldsCode (RecordsPost cs) FieldsTid.
Proof.
 intros. unfold RecordsPre,RecordsPost,FieldsCode,FieldsCells,FieldsBindings,RecordsNewTid.
 change (InfRules Spec sd V293_witness_li I r ri
 (<||spec_done None||> ** V293_rdy_raw_cells
  (V293_tcb_init_old_fields 301%positive 128%Z (fun _=>Vundef) ++
   V293_tcb_init_input_cells 201%positive 202%positive 203%positive 204%positive 205%positive 206%positive 207%positive 208%positive
    301%positive 128%Z 11 Vnull Vnull (Vint32 Int.zero) (Vint32(Int.repr 128)) Vnull (Vint32 Int.zero))
  (V293_tcb_fields_bindings 108%Z 101%Z 102%Z 103%Z 104%Z 105%Z 106%Z 107%Z
    201%positive 202%positive 203%positive 204%positive 205%positive 206%positive 207%positive 208%positive **
   (V293_owned_task_records RecordsTasks ** FieldsFrame cs)))
 (V293_TCBInit_fields 108%Z 101%Z 102%Z 103%Z 104%Z 105%Z 106%Z 107%Z)
 (<||spec_done None||> ** (V293_owned_task_records (set RecordsTasks (301%positive,Int.repr 128) (Int.repr 11,rdy,Vnull)) **
 V293_rdy_raw_cells
  (V293_tcb_init_record_remainder 301%positive 128%Z Vnull Vnull (Vint32 Int.zero)
   (Vint32(Int.repr 128)) Vnull (Vint32 Int.zero))
  (V293_rdy_raw_cells
   (V293_tcb_init_input_cells 201%positive 202%positive 203%positive 204%positive 205%positive 206%positive 207%positive 208%positive
    301%positive 128%Z 11 Vnull Vnull (Vint32 Int.zero) (Vint32(Int.repr 128)) Vnull (Vint32 Int.zero))
   (V293_tcb_fields_bindings 108%Z 101%Z 102%Z 103%Z 104%Z 105%Z 106%Z 107%Z
    201%positive 202%positive 203%positive 204%positive 205%positive 206%positive 207%positive 208%positive ** FieldsFrame cs)))) FieldsTid).
 apply V293_OS_TCBInit_fields_records_hoare;try (unfold Int.max_unsigned,Int.modulus,Int.wordsize;cbn;lia).
 - repeat split;reflexivity.
 - apply RecordsFresh.
 - apply FieldsFrameCurLINV.
Qed.
