(* Independent finite entry; no old audit probe imports, no assumed callee result.
   Idle and Stat parameters are separate executions, not two published tasks. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.code.V293OSTCBInit.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitFields.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewWitness.
Require Import CertiOS.certiucos.v293.proofs.V293NullBytes.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope Z_scope.
Require Import CertiOS.certiucos.v293.code.V293OSTCBInitPrefix.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitPrefix.
Definition PrefixNext (tail : bool) := if tail then Vptr (501%positive,Int.repr 56) else Vnull.
Definition PrefixOld : list V293_record_cell :=
 [((301%positive,8%Z),(Tptr Tint32),(Vundef));
  ((301%positive,58%Z),(Tint8),(Vundef));
  ((301%positive,56%Z),(Tint8),(Vundef));
  ((301%positive,57%Z),(Tint8),(Vundef));
  ((301%positive,52%Z),(Tint32),(Vundef));
  ((301%positive,12%Z),(Tptr Tvoid),(Vundef));
  ((301%positive,20%Z),(Tint32),(Vundef));
  ((301%positive,16%Z),(Tptr Tint32),(Vundef));
  ((301%positive,24%Z),(Tint16),(Vundef));
  ((301%positive,26%Z),(Tint16),(Vundef));
  ((301%positive,63%Z),(Tint8),(Vundef));
  ((301%positive,60%Z),(Tint8),(Vundef));
  ((301%positive,59%Z),(Tint8),(Vundef));
  ((301%positive,62%Z),(Tint8),(Vundef));
  ((301%positive,61%Z),(Tint8),(Vundef));
  ((301%positive,36%Z),(Tcom_ptr 411%Z),(Vundef));
  ((301%positive,44%Z),(Tcom_ptr 412%Z),(Vundef));
  ((301%positive,40%Z),(Tptr Tvoid),(Vundef))].
Definition PrefixInputs (p : nat): list V293_record_cell :=
 [((201%positive,0%Z),(Tptr V293_tcb_type),(Vundef));
  ((202%positive,0%Z),(Tint8),(Vint32 (Int.repr (Z.of_nat p))));
  ((203%positive,0%Z),(Tptr Tint32),(Vptr (401%positive,Int.repr 508)));
  ((204%positive,0%Z),(Tptr Tint32),(Vptr (401%positive,Int.zero)));
  ((205%positive,0%Z),(Tint16),(Vint32 (Int.repr (if Nat.eqb p 12 then 65535 else 65534))));
  ((206%positive,0%Z),(Tint32),(Vint32 (Int.repr 128)));
  ((207%positive,0%Z),(Tptr Tvoid),(Vnull));
  ((208%positive,0%Z),(Tint16),(Vint32 (Int.repr 3)))].
Definition PrefixLinks (tail : bool): list V293_record_cell :=
 [((209%positive,0%Z),(Tptr V293_tcb_type),(Vptr (301%positive,Int.repr 8)));
  ((301%positive,28%Z),(Tcom_ptr 410%Z),(PrefixNext tail))].
Definition PrefixFrame : list V293_record_cell :=
 [((301%positive,32%Z),(Tcom_ptr 410%Z),(Vptr (502%positive,Int.zero)));
  ((301%positive,48%Z),(Tint16),(Vint32 (Int.repr 4660)));
  ((301%positive,50%Z),(Tint16),(Vint32 (Int.repr 22136)));
  ((601%positive,0%Z),(Tint32),(Vint32 (Int.repr 77)))].
Definition PrefixLE : env := set (set (set (set (set (set (set (set ((emp:env)) 101%Z (201%positive,(Tptr V293_tcb_type))) 102%Z (202%positive,(Tint8))) 103%Z (203%positive,(Tptr Tint32))) 104%Z (204%positive,(Tptr Tint32))) 105%Z (205%positive,(Tint16))) 106%Z (206%positive,(Tint32))) 107%Z (207%positive,(Tptr Tvoid))) 108%Z (208%positive,(Tint16)).
Definition PrefixGE : env := set (emp:env) 99%Z (209%positive,Tptr V293_tcb_type).
Fixpoint PrefixMemory (cells : list V293_record_cell) : mem :=
  match cells with []=>emp | ((b,off),tp,v)::tail=>
    merge (V293_encoded_memory b off true (encode_val tp v)) (PrefixMemory tail) end.
Definition PrefixEntry p tail := PrefixMemory (PrefixOld++PrefixInputs p++PrefixLinks tail++PrefixFrame).
Definition PrefixState M := V293_wstate PrefixGE PrefixLE M.
Ltac InitOutside :=
  repeat first [rewrite V293_encoded_memory_outside by
    (first [left;congruence | right;cbn [length encode_val typelen list_repeat inj_pointer inj_bytes encode_int List.map];lia])
    | rewrite map_merge_semp by reflexivity];reflexivity.
Ltac InitApart b start count :=
  apply map_join_merge;apply map_disjoint;intros [other off];
  destruct (Pos.eq_dec other b) as [B|B];
  [subst other;destruct (Z_lt_dec off start) as [Low|Low];
    [left;apply V293_encoded_memory_outside;right;left;exact Low |
     destruct (Z_lt_dec off (start+count)) as [Inside|Outside];
     [right;left;InitOutside | left;apply V293_encoded_memory_outside;right;right;
       cbn [length encode_val typelen list_repeat inj_pointer inj_bytes encode_int List.map];lia]] |
   left;apply V293_encoded_memory_outside;left;exact B].
Lemma PrefixLiteralEntry : forall p tail,
  PrefixState (PrefixEntry p tail) |=
    V293_rdy_raw_cells (PrefixOld++PrefixInputs p++PrefixLinks tail++PrefixFrame) Aemp.
Proof.
  intros p tail. destruct tail;
    unfold PrefixState,PrefixEntry;
    cbn [PrefixOld PrefixInputs PrefixLinks PrefixNext PrefixFrame app PrefixMemory V293_rdy_raw_cells].
  all: eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 8%Z true (encode_val (Tptr Tint32) (Vundef)));
    [InitApart 301%positive 8%Z 4%Z | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
  all: eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 58%Z true (encode_val (Tint8) (Vundef)));
    [InitApart 301%positive 58%Z 1%Z | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
  all: eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 56%Z true (encode_val (Tint8) (Vundef)));
    [InitApart 301%positive 56%Z 1%Z | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
  all: eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 57%Z true (encode_val (Tint8) (Vundef)));
    [InitApart 301%positive 57%Z 1%Z | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
  all: eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 52%Z true (encode_val (Tint32) (Vundef)));
    [InitApart 301%positive 52%Z 4%Z | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
  all: eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 12%Z true (encode_val (Tptr Tvoid) (Vundef)));
    [InitApart 301%positive 12%Z 4%Z | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
  all: eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 20%Z true (encode_val (Tint32) (Vundef)));
    [InitApart 301%positive 20%Z 4%Z | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
  all: eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 16%Z true (encode_val (Tptr Tint32) (Vundef)));
    [InitApart 301%positive 16%Z 4%Z | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
  all: eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 24%Z true (encode_val (Tint16) (Vundef)));
    [InitApart 301%positive 24%Z 2%Z | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
  all: eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 26%Z true (encode_val (Tint16) (Vundef)));
    [InitApart 301%positive 26%Z 2%Z | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
  all: eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 63%Z true (encode_val (Tint8) (Vundef)));
    [InitApart 301%positive 63%Z 1%Z | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
  all: eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 60%Z true (encode_val (Tint8) (Vundef)));
    [InitApart 301%positive 60%Z 1%Z | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
  all: eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 59%Z true (encode_val (Tint8) (Vundef)));
    [InitApart 301%positive 59%Z 1%Z | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
  all: eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 62%Z true (encode_val (Tint8) (Vundef)));
    [InitApart 301%positive 62%Z 1%Z | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
  all: eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 61%Z true (encode_val (Tint8) (Vundef)));
    [InitApart 301%positive 61%Z 1%Z | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
  all: eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 36%Z true (encode_val (Tcom_ptr 411%Z) (Vundef)));
    [InitApart 301%positive 36%Z 4%Z | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
  all: eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 44%Z true (encode_val (Tcom_ptr 412%Z) (Vundef)));
    [InitApart 301%positive 44%Z 4%Z | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
  all: eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 40%Z true (encode_val (Tptr Tvoid) (Vundef)));
    [InitApart 301%positive 40%Z 4%Z | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
  all: eapply V293_wstate_star with (m1:=V293_encoded_memory 201%positive 0%Z true (encode_val (Tptr V293_tcb_type) (Vundef)));
    [InitApart 201%positive 0%Z 4%Z | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
  all: eapply V293_wstate_star with (m1:=V293_encoded_memory 202%positive 0%Z true (encode_val (Tint8) (Vint32 (Int.repr (Z.of_nat p)))));
    [InitApart 202%positive 0%Z 1%Z | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
  all: eapply V293_wstate_star with (m1:=V293_encoded_memory 203%positive 0%Z true (encode_val (Tptr Tint32) (Vptr (401%positive,Int.repr 508))));
    [InitApart 203%positive 0%Z 4%Z | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
  all: eapply V293_wstate_star with (m1:=V293_encoded_memory 204%positive 0%Z true (encode_val (Tptr Tint32) (Vptr (401%positive,Int.zero))));
    [InitApart 204%positive 0%Z 4%Z | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
  all: eapply V293_wstate_star with (m1:=V293_encoded_memory 205%positive 0%Z true (encode_val (Tint16) (Vint32 (Int.repr (if Nat.eqb p 12 then 65535 else 65534)))));
    [InitApart 205%positive 0%Z 2%Z | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
  all: eapply V293_wstate_star with (m1:=V293_encoded_memory 206%positive 0%Z true (encode_val (Tint32) (Vint32 (Int.repr 128))));
    [InitApart 206%positive 0%Z 4%Z | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
  all: eapply V293_wstate_star with (m1:=V293_encoded_memory 207%positive 0%Z true (encode_val (Tptr Tvoid) (Vnull)));
    [InitApart 207%positive 0%Z 4%Z | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
  all: eapply V293_wstate_star with (m1:=V293_encoded_memory 208%positive 0%Z true (encode_val (Tint16) (Vint32 (Int.repr 3))));
    [InitApart 208%positive 0%Z 2%Z | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
  all: eapply V293_wstate_star with (m1:=V293_encoded_memory 209%positive 0%Z true (encode_val (Tptr V293_tcb_type) (Vptr (301%positive,Int.repr 8))));
    [InitApart 209%positive 0%Z 4%Z | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
  all: eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 28%Z true (encode_val (Tcom_ptr 410%Z) _));
    [InitApart 301%positive 28%Z 4%Z | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
  all: eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 32%Z true (encode_val (Tcom_ptr 410%Z) (Vptr (502%positive,Int.zero))));
    [InitApart 301%positive 32%Z 4%Z | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
  all: eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 48%Z true (encode_val (Tint16) (Vint32 (Int.repr 4660))));
    [InitApart 301%positive 48%Z 2%Z | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
  all: eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 50%Z true (encode_val (Tint16) (Vint32 (Int.repr 22136))));
    [InitApart 301%positive 50%Z 2%Z | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
  all: eapply V293_wstate_star with (m1:=V293_encoded_memory 601%positive 0%Z true (encode_val (Tint32) (Vint32 (Int.repr 77))));
    [InitApart 601%positive 0%Z 4%Z | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
  all: split;reflexivity.
Qed.
Lemma InitEnvironment : V293_tcb_init_env PrefixLE 101%Z 102%Z 103%Z 104%Z 105%Z 106%Z 107%Z 108%Z
  201%positive 202%positive 203%positive 204%positive 205%positive 206%positive 207%positive 208%positive.
Proof.
  unfold V293_tcb_init_env,PrefixLE.
  repeat split;repeat first [rewrite map_get_set | rewrite map_get_set' by discriminate];reflexivity.
Qed.
Lemma InitValues : forall p, V293_tcb_init_values_valid
  (Vptr (401%positive,Int.repr 508)) (Vptr (401%positive,Int.zero))
  (Vint32 (Int.repr (if Nat.eqb p 12 then 65535 else 65534))) (Vint32 (Int.repr 128)) Vnull (Vint32 (Int.repr 3)).
Proof. intro p. unfold V293_tcb_init_values_valid. destruct (Nat.eqb p 12);repeat split;reflexivity. Qed.
Lemma PrefixFreeBindings : get PrefixLE 99%Z=None /\ get PrefixGE 99%Z=Some (209%positive,Tptr V293_tcb_type).
Proof. split;reflexivity. Qed.
Definition PrefixChecks (p : nat) (tail : bool) : list V293_record_cell :=
 [((301%positive,8%Z),(Tptr Tint32),(Vptr (401%positive,Int.repr 508)));
  ((301%positive,58%Z),(Tint8),(Vint32 (Int.repr (Z.of_nat p))));
  ((301%positive,56%Z),(Tint8),(Vint32 Int.zero));
  ((301%positive,57%Z),(Tint8),(Vint32 Int.zero));
  ((301%positive,52%Z),(Tint32),(Vint32 Int.zero));
  ((301%positive,12%Z),(Tptr Tvoid),(Vnull));
  ((301%positive,20%Z),(Tint32),(Vint32 (Int.repr 128)));
  ((301%positive,16%Z),(Tptr Tint32),(Vptr (401%positive,Int.zero)));
  ((301%positive,24%Z),(Tint16),(Vint32 (Int.repr 3)));
  ((301%positive,26%Z),(Tint16),(Vint32 (Int.repr (if Nat.eqb p 12 then 65535 else 65534))));
  ((301%positive,63%Z),(Tint8),(Vint32 Int.zero));
  ((301%positive,60%Z),(Tint8),(Vint32 Int.one));
  ((301%positive,59%Z),(Tint8),(Vint32 (Int.repr (if Nat.eqb p 12 then 4 else 3))));
  ((301%positive,62%Z),(Tint8),(Vint32 (Int.repr 2)));
  ((301%positive,61%Z),(Tint8),(Vint32 (Int.repr (if Nat.eqb p 12 then 16 else 8))));
  ((301%positive,36%Z),(Tcom_ptr 411%Z),(Vnull));
  ((301%positive,44%Z),(Tcom_ptr 412%Z),(Vnull));
  ((301%positive,40%Z),(Tptr Tvoid),(Vnull));
  ((201%positive,0%Z),(Tptr V293_tcb_type),(Vptr (301%positive,Int.repr 8)));
  ((202%positive,0%Z),(Tint8),(Vint32 (Int.repr (Z.of_nat p))));
  ((203%positive,0%Z),(Tptr Tint32),(Vptr (401%positive,Int.repr 508)));
  ((204%positive,0%Z),(Tptr Tint32),(Vptr (401%positive,Int.zero)));
  ((205%positive,0%Z),(Tint16),(Vint32 (Int.repr (if Nat.eqb p 12 then 65535 else 65534))));
  ((206%positive,0%Z),(Tint32),(Vint32 (Int.repr 128)));
  ((207%positive,0%Z),(Tptr Tvoid),(Vnull));
  ((208%positive,0%Z),(Tint16),(Vint32 (Int.repr 3)));
  ((209%positive,0%Z),(Tptr V293_tcb_type),(PrefixNext tail));
  ((301%positive,28%Z),(Tcom_ptr 410%Z),(PrefixNext tail));
  ((301%positive,32%Z),(Tcom_ptr 410%Z),(Vptr (502%positive,Int.zero)));
  ((301%positive,48%Z),(Tint16),(Vint32 (Int.repr 4660)));
  ((301%positive,50%Z),(Tint16),(Vint32 (Int.repr 22136)));
  ((601%positive,0%Z),(Tint32),(Vint32 (Int.repr 77)))].
Lemma PrefixChecksCount : length (PrefixChecks 12 true)=32%nat. Proof. reflexivity. Qed.
Definition PrefixProgram suffix := V293_TCBInit_prefix 99%Z 101%Z 102%Z 103%Z 104%Z 105%Z 106%Z 107%Z 108%Z suffix.
Theorem PrefixConcreteExecution : forall p tail P ks enabled si ci suffix,
  p=12%nat \/ p=11%nat ->
  exists Mf,
    V293_local_steps P (curs (PrefixProgram suffix),(kenil,ks))
      ((PrefixGE,PrefixLE,PrefixEntry p tail),(fun _=>false),(enabled,si,ci))
      (curs suffix,(kenil,kseq V293_TCBInit_empty ks))
      ((PrefixGE,PrefixLE,Mf),(fun _=>false),(enabled,si,ci)) /\
    PrefixState Mf |= V293_rdy_raw_cells (PrefixChecks p tail) Aemp /\
    (forall a tp v, In (a,tp,v) (PrefixChecks p tail) -> load tp Mf a=Some v).
Proof.
  intros p tail P ks enabled si ci suffix Case.
  assert (Range : (p<13)%nat) by (destruct Case;subst;lia).
  destruct (V293_OS_TCBInit_prefix_execution P ks PrefixGE PrefixLE (PrefixEntry p tail)
    (fun _=>false) (false,nil,nil) (emp:osabst) (spec_done None) (V293_rdy_raw_cells PrefixFrame Aemp)
    enabled si ci 99%Z 101%Z 102%Z 103%Z 104%Z 105%Z 106%Z 107%Z 108%Z
    201%positive 202%positive 203%positive 204%positive 205%positive 206%positive 207%positive 208%positive
    209%positive 301%positive 8 p (Vptr (401%positive,Int.repr 508)) (Vptr (401%positive,Int.zero))
    (Vint32 (Int.repr (if Nat.eqb p 12 then 65535 else 65534))) (Vint32 (Int.repr 128)) Vnull (Vint32 (Int.repr 3))
    Vundef (PrefixNext tail) (fun _=>Vundef) suffix Range ltac:(lia) ltac:(change (8+55<=4294967295);lia)
    (proj1 PrefixFreeBindings) (proj2 PrefixFreeBindings) InitEnvironment (InitValues p)
    ltac:(destruct tail;reflexivity)) as (Mf & Exec & Owned).
  { change (PrefixState (PrefixEntry p tail) |= V293_rdy_raw_cells
      (PrefixOld++PrefixInputs p++PrefixLinks tail) (V293_rdy_raw_cells PrefixFrame Aemp)).
    rewrite <- V293_raw_cells_append. rewrite <- !app_assoc. apply PrefixLiteralEntry. }
  assert (Final : PrefixState Mf |= V293_rdy_raw_cells (PrefixChecks p tail) Aemp).
  { rewrite <- V293_raw_cells_append in Owned. rewrite <- !app_assoc in Owned.
    destruct Case as [Case|Case];subst p;exact Owned. }
  exists Mf. split;[exact Exec | ]. split;[exact Final | ].
  intros a tp v Member. change (load tp (getmem (PrefixState Mf)) a=Some v).
  eapply (V293_rdy_raw_load (PrefixChecks p tail) Aemp a tp v (PrefixState Mf));[exact Member | | exact Final].
  destruct Case as [Case|Case];subst p;destruct tail;cbn [PrefixChecks PrefixNext In] in Member;
    repeat destruct Member as [Same|Member];try contradiction;inversion Same;subst;reflexivity.
Qed.

Definition PrefixEmptyEntry := PrefixMemory
  (V293_tcb_empty_cells 201%positive 209%positive Vundef ++
    [((601%positive,0%Z),Tint32,Vint32 (Int.repr 77))]).
Definition PrefixEmptyFrame := Amapsto (601%positive,0%Z) Tint32 true (Vint32 (Int.repr 77)) ** Aemp.
Lemma PrefixEmptyLiteral : PrefixState PrefixEmptyEntry |=
  V293_rdy_raw_cells (V293_tcb_empty_cells 201%positive 209%positive Vundef) PrefixEmptyFrame.
Proof.
  unfold PrefixEmptyEntry,PrefixEmptyFrame,PrefixState.
  cbn [V293_tcb_empty_cells app PrefixMemory V293_rdy_raw_cells].
  eapply V293_wstate_star with (m1:=V293_encoded_memory 201%positive 0%Z true (encode_val (Tptr V293_tcb_type) Vundef));
    [InitApart 201%positive 0%Z 4%Z | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
  eapply V293_wstate_star with (m1:=V293_encoded_memory 209%positive 0%Z true (encode_val (Tptr V293_tcb_type) Vnull));
    [InitApart 209%positive 0%Z 4%Z | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
  eapply V293_wstate_star with (m1:=V293_encoded_memory 601%positive 0%Z true (encode_val Tint32 (Vint32 (Int.repr 77))));
    [InitApart 601%positive 0%Z 4%Z | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
  split;reflexivity.
Qed.
Theorem PrefixEmptyConcrete : forall P ks enabled si ci suffix,
  exists Mf,
    V293_local_steps P (curs (PrefixProgram suffix),(kenil,ks))
      ((PrefixGE,PrefixLE,PrefixEmptyEntry),(fun _=>false),(enabled,si,ci))
      (curs (srete (econst32 (Int.repr 66))),(kenil,ks))
      ((PrefixGE,PrefixLE,Mf),(fun _=>false),(enabled,si,ci)) /\
    load (Tptr V293_tcb_type) Mf (201%positive,0%Z)=Some Vnull /\
    load (Tptr V293_tcb_type) Mf (209%positive,0%Z)=Some Vnull /\
    load Tint32 Mf (601%positive,0%Z)=Some (Vint32 (Int.repr 77)).
Proof.
  intros P ks enabled si ci suffix.
  destruct (V293_OS_TCBInit_empty_prefix_execution P ks PrefixGE PrefixLE PrefixEmptyEntry
    (fun _=>false) (false,nil,nil) (emp:osabst) (spec_done None) PrefixEmptyFrame
    enabled si ci 99%Z 101%Z 102%Z 103%Z 104%Z 105%Z 106%Z 107%Z 108%Z
    201%positive 209%positive Vundef suffix
    (proj1 PrefixFreeBindings) (proj2 PrefixFreeBindings) ltac:(reflexivity) PrefixEmptyLiteral)
    as (Mf & Exec & Owned).
  change (PrefixState Mf |= V293_rdy_raw_cells
    (V293_tcb_empty_cells 201%positive 209%positive Vnull)
    (V293_rdy_raw_cells (cons ((601%positive,0%Z),Tint32,Vint32 (Int.repr 77)) nil) Aemp)) in Owned.
  rewrite <- V293_raw_cells_append in Owned.
  unfold V293_tcb_empty_cells in Owned. cbn [app] in Owned.
  unfold PrefixState,V293_wstate in Owned.
  V293_tcb_init_read Owned 0%nat PcRead.
  V293_tcb_init_read Owned 1%nat HeadRead.
  V293_tcb_init_read Owned 2%nat FrameRead.
  exists Mf. repeat split;assumption.
Qed.
