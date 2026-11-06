(* Independent finite typed entry; four separate executions, not two coexisting tasks.
   Entry is after OSTaskCreateHook, not reached from the initialization prefix here. *)
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
Require Import CertiOS.certiucos.v293.code.V293OSTCBPublish.
Require Import CertiOS.certiucos.v293.proofs.V293TCBPublish.
Definition PubX (p : nat) := if Nat.eqb p 12 then 4%nat else 3%nat.
Definition PubHead (present : bool) := if present then Vptr(501%positive,Int.repr 16) else Vnull.
Definition PubCore p present next prev head g r n back :=
 V293_pub_cells 201%positive 301%positive 8%Z 209%positive 210%positive
  211%positive 212%positive 501%positive 16%Z present 1%nat (PubX p) next prev head g r n back.
Definition PubFrame : list V293_record_cell :=
 [((211%positive,0%Z),Tint8,V293_byteval 85); ((601%positive,0%Z),Tint32,V293_byteval 77)].
Definition PubOld p present := PubCore p present Vundef Vundef (PubHead present) 1%nat 2%nat 4%nat Vundef.
Definition PubChecks p present := PubCore p present (PubHead present) Vnull
 (Vptr(301%positive,Int.repr 8)) 3%nat (if Nat.eqb p 12 then 18%nat else 10%nat) 5%nat
 (Vptr(301%positive,Int.repr 8)) ++ PubFrame.
Definition PubLE : env := set (emp:env) 101%Z (201%positive,Tptr V293_tcb_type).
Definition PubGE : env := set (set (set (set (emp:env) 99%Z (209%positive,Tptr V293_tcb_type))
 98%Z (210%positive,Tint8)) 97%Z (211%positive,Tarray Tint8 2)) 96%Z (212%positive,Tint8).
Fixpoint PubMemory (cells : list V293_record_cell) : mem :=
 match cells with []=>emp | ((b,off),tp,v)::tail=>
  merge (V293_encoded_memory b off true (encode_val tp v)) (PubMemory tail) end.
Definition PubEntry p present := PubMemory (PubOld p present ++ PubFrame).
Definition PubState M := V293_wstate PubGE PubLE M.
Ltac InitOutside :=
  repeat first [rewrite V293_encoded_memory_outside by
    (first [left;congruence | right;cbn [length V293_byteval encode_val typelen list_repeat inj_pointer inj_bytes encode_int List.map];lia])
    | rewrite map_merge_semp by reflexivity];reflexivity.
Ltac InitApart b start count :=
  apply map_join_merge;apply map_disjoint;intros [other off];
  destruct (Pos.eq_dec other b) as [B|B];
  [subst other;destruct (Z_lt_dec off start) as [Low|Low];
    [left;apply V293_encoded_memory_outside;right;left;exact Low |
     destruct (Z_lt_dec off (start+count)) as [Inside|Outside];
     [right;left;InitOutside | left;apply V293_encoded_memory_outside;right;right;
       cbn [length V293_byteval encode_val typelen list_repeat inj_pointer inj_bytes encode_int List.map];lia]] |
   left;apply V293_encoded_memory_outside;left;exact B].
Lemma PubLiteralEntry : forall p present,
 PubState (PubEntry p present) |= V293_rdy_raw_cells (PubOld p present ++ PubFrame) Aemp.
Proof.
 intros p present. destruct present;
 unfold PubState,PubEntry;
 cbn [PubOld PubCore V293_pub_cells PubHead PubFrame app PubMemory V293_rdy_raw_cells].
 all: eapply V293_wstate_star with (m1:=V293_encoded_memory 201%positive 0%Z true (encode_val (Tptr V293_tcb_type) (Vptr(301%positive,Int.repr 8))));
 [InitApart 201%positive 0%Z 4%Z | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
 all: eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 28%Z true (encode_val (Tcom_ptr 410%Z) (Vundef)));
 [InitApart 301%positive 28%Z 4%Z | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
 all: eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 32%Z true (encode_val (Tcom_ptr 410%Z) (Vundef)));
 [InitApart 301%positive 32%Z 4%Z | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
 all: eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 60%Z true (encode_val (Tint8) (V293_byteval 1)));
 [InitApart 301%positive 60%Z 1%Z | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
 all: eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 62%Z true (encode_val (Tint8) (V293_byteval 2)));
 [InitApart 301%positive 62%Z 1%Z | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
 all: eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 61%Z true (encode_val (Tint8) (V293_byteval (2^(PubX p)))));
 [InitApart 301%positive 61%Z 1%Z | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
 all: eapply V293_wstate_star with (m1:=V293_encoded_memory 209%positive 0%Z true (encode_val (Tptr V293_tcb_type) (_)));
 [InitApart 209%positive 0%Z 4%Z | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
 all: eapply V293_wstate_star with (m1:=V293_encoded_memory 210%positive 0%Z true (encode_val (Tint8) (V293_byteval 1)));
 [InitApart 210%positive 0%Z 1%Z | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
 all: eapply V293_wstate_star with (m1:=V293_encoded_memory 211%positive 1%Z true (encode_val (Tint8) (V293_byteval 2)));
 [InitApart 211%positive 1%Z 1%Z | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
 all: eapply V293_wstate_star with (m1:=V293_encoded_memory 212%positive 0%Z true (encode_val (Tint8) (V293_byteval 4)));
 [InitApart 212%positive 0%Z 1%Z | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
 - eapply V293_wstate_star with (m1:=V293_encoded_memory 501%positive 40%Z true (encode_val (Tcom_ptr 410%Z) Vundef));
   [InitApart 501%positive 40%Z 4%Z | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
   eapply V293_wstate_star with (m1:=V293_encoded_memory 211%positive 0%Z true (encode_val Tint8 (V293_byteval 85)));
   [InitApart 211%positive 0%Z 1%Z | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
   eapply V293_wstate_star with (m1:=V293_encoded_memory 601%positive 0%Z true (encode_val Tint32 (V293_byteval 77)));
   [InitApart 601%positive 0%Z 4%Z | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
   split;reflexivity.
 - eapply V293_wstate_star with (m1:=V293_encoded_memory 211%positive 0%Z true (encode_val Tint8 (V293_byteval 85)));
   [InitApart 211%positive 0%Z 1%Z | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
   eapply V293_wstate_star with (m1:=V293_encoded_memory 601%positive 0%Z true (encode_val Tint32 (V293_byteval 77)));
   [InitApart 601%positive 0%Z 4%Z | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
   split;reflexivity.
Qed.
Lemma PubBindings : V293_pub_env PubGE PubLE 101%Z 99%Z 98%Z 97%Z 96%Z
 201%positive 209%positive 210%positive 211%positive 212%positive.
Proof. unfold V293_pub_env,PubGE,PubLE. repeat split;
 repeat first [rewrite map_get_set | rewrite map_get_set' by discriminate];reflexivity. Qed.
Definition PubProgram := V293_TCB_publish 101%Z 99%Z 98%Z 97%Z 96%Z.
Lemma PubChecksCount : length(PubChecks 12 true)=13%nat /\ length(PubChecks 11 false)=12%nat.
Proof. split;reflexivity. Qed.
Theorem PubConcreteExecution : forall p present P ks enabled si ci,
 p=12%nat \/ p=11%nat ->
 exists Mf,
  V293_local_steps P (curs PubProgram,(kenil,ks))
   ((PubGE,PubLE,PubEntry p present),(fun _=>false),(enabled,si,ci))
   (curs(srete(econst32 Int.zero)),(kenil,ks)) ((PubGE,PubLE,Mf),(fun _=>false),(enabled,si,ci)) /\
  PubState Mf |= V293_rdy_raw_cells (PubChecks p present) Aemp /\
  (forall a tp v, In (a,tp,v) (PubChecks p present) -> load tp Mf a=Some v).
Proof.
 intros p present P ks enabled si ci Case.
 assert (X : (PubX p<8)%nat) by (unfold PubX;destruct(Nat.eqb p 12);lia).
 destruct (V293_OS_TCBInit_publication_execution P ks PubGE PubLE (PubEntry p present)
  (fun _=>false) (false,nil,nil) (emp:osabst) (spec_done None) (V293_rdy_raw_cells PubFrame Aemp)
  enabled si ci 101%Z 99%Z 98%Z 97%Z 96%Z 201%positive 301%positive 8%Z
  209%positive 210%positive 211%positive 212%positive 501%positive 16%Z present
  1%nat (PubX p) 1%nat 2%nat 4%nat Vundef Vundef Vundef PubBindings
  ltac:(lia) ltac:(change (8+54<=4294967295);lia)
  ltac:(lia) ltac:(change (16+24<=4294967295);lia)
  ltac:(lia) X ltac:(lia) ltac:(lia) ltac:(lia)) as (Mf & Exec & Owned).
 { change (PubState (PubEntry p present) |= V293_rdy_raw_cells (PubOld p present) (V293_rdy_raw_cells PubFrame Aemp)).
   rewrite <- V293_raw_cells_append. apply PubLiteralEntry. }
 assert (Final : PubState Mf |= V293_rdy_raw_cells (PubChecks p present) Aemp).
 { rewrite <- V293_raw_cells_append in Owned.
   destruct Case as [Case|Case];subst p;destruct present;exact Owned. }
 exists Mf. split;[exact Exec | ]. split;[exact Final | ].
 intros a tp v Member. change (load tp (getmem (PubState Mf)) a=Some v).
 eapply (V293_rdy_raw_load (PubChecks p present) Aemp a tp v (PubState Mf));[exact Member | | exact Final].
 destruct Case as [Case|Case];subst p;destruct present;
 cbn [PubChecks PubCore V293_pub_cells PubX PubHead PubFrame In app] in Member;
 repeat destruct Member as [Same|Member];try contradiction;inversion Same;subst;reflexivity.
Qed.
