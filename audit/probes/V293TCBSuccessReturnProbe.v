(* Actual post-second-Hook suffix, including publication and physical return/free.
   No claim that this return anchor is reachable with missing port definitions. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.proofs.V293TCBPriorityHook.
Require Import CertiOS.certiucos.v293.proofs.V293TCBPublish.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitFunction.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitPrefix.
Require Import CertiOS.certiucos.v293.proofs.V293InitTCBCall.
Require Import CertiOS.certiucos.v293.proofs.V293InitTCBList.
Require Import CertiOS.certiucos.v293.proofs.V293NullBytes.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickStorage.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickLifecycle.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.code.V293OSTCBInitFunction.
Require Import CertiOS.certiucos.v293.code.V293OSTCBInitPrefix.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.code.V293OSTCBPublish.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope Z_scope.
Require Import CertiOS.certiucos.v293.proofs.V293TCBSuccessReturn.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitFields.

(* Independent literal finite memories; no other audit probe imported. *)
Definition SuccessLE := V293_tcb_function_env 201%positive 202%positive 203%positive 204%positive 205%positive 206%positive 207%positive 208%positive 209%positive.
Definition SuccessGE : env := set (set (set (set emp 93%Z (401%positive,Tptr V293_tcb_type)) 94%Z (402%positive,Tint8)) 95%Z (403%positive,Tarray Tint8 2)) 96%Z (404%positive,Tint8).
Definition SuccessCaller : env := set emp 108%Z (602%positive,Tint8).
Definition SuccessProgram f := if Z.eq_dec f 500%Z then Some(V293_TCBInit_function 501%Z 502%Z) else None.
Definition SuccessBit p := (p mod 8)%nat.
Definition SuccessFrame p : list V293_record_cell :=
 [((310%positive,4*Z.of_nat p),Tptr V293_tcb_type,Vptr(301%positive,Int.repr 8));
  ((310%positive,0),Tptr V293_tcb_type,Vnull);
  ((601%positive,0),Tint32,Vint32(Int.repr 77));
  ((602%positive,0),Tint8,Vint32(Int.repr 88))].
Definition SuccessLocals p : list V293_record_cell :=
 [((209%positive,0),Tint32,Vint32 Int.zero);
  ((201%positive,0),Tint8,V293_byteval p);
  ((202%positive,0),Tptr Tint32,Vnull);
  ((203%positive,0),Tptr Tint32,Vnull);
  ((204%positive,0),Tint16,Vint32 Int.zero);
  ((205%positive,0),Tint32,Vint32 Int.zero);
  ((206%positive,0),Tptr Tvoid,Vnull);
  ((207%positive,0),Tint16,Vint32 Int.zero)].
Definition SuccessHead (present : bool) := if present then Vptr(302%positive,Int.repr 16) else Vnull.
Definition SuccessPub p (present : bool) : list V293_record_cell :=
 [((208%positive,0),Tptr V293_tcb_type,Vptr(301%positive,Int.repr 8));
  ((301%positive,28),Tcom_ptr 410%Z,Vnull);
  ((301%positive,32),Tcom_ptr 410%Z,Vundef);
  ((301%positive,60),Tint8,V293_byteval 1);
  ((301%positive,62),Tint8,V293_byteval 2);
  ((301%positive,61),Tint8,V293_byteval (2^SuccessBit p));
  ((401%positive,0),Tptr V293_tcb_type,SuccessHead present);
  ((402%positive,0),Tint8,V293_byteval 2);
  ((403%positive,1),Tint8,V293_byteval 2);
  ((404%positive,0),Tint8,V293_byteval 7)]++
  if present then [((302%positive,40),Tcom_ptr 410%Z,Vnull)] else [].
Fixpoint SuccessMemory cells : mem :=
 match cells with []=>emp | ((b,off),tp,v)::tail=>
 merge (V293_encoded_memory b off true (encode_val tp v)) (SuccessMemory tail) end.
Definition SuccessEntry p present := SuccessMemory (SuccessPub p present++SuccessLocals p++SuccessFrame p).
Definition SuccessStart := (curs(sskip None),(kenil,V293_tcb_second_hook_cont 500%Z 501%Z 502%Z SuccessCaller kstop)).
Definition SuccessStop := (curs(sskip(Some(Vint32 Int.zero))),(kenil,kstop)).
Ltac SuccessOutside :=
 repeat first [rewrite V293_encoded_memory_outside by
 (first [left;congruence|right;cbn [length V293_byteval encode_val typelen list_repeat inj_pointer inj_bytes encode_int List.map];lia])
 |rewrite map_merge_semp by reflexivity];reflexivity.
Ltac SuccessApart b start count :=
 apply map_join_merge;apply map_disjoint;intros [other off];
 destruct (Pos.eq_dec other b) as [B|B];
 [subst other;destruct (Z_lt_dec off start) as [Low|Low];
 [left;apply V293_encoded_memory_outside;right;left;exact Low|
 destruct (Z_lt_dec off (start+count)) as [Inside|Outside];
 [right;left;SuccessOutside|left;apply V293_encoded_memory_outside;right;right;
 cbn [length V293_byteval encode_val typelen list_repeat inj_pointer inj_bytes encode_int List.map];lia]]|
 left;apply V293_encoded_memory_outside;left;exact B].

Lemma SuccessLiteralEntry : forall p present,
 p=12%nat \/ p=11%nat ->
 V293_wstate SuccessGE SuccessLE (SuccessEntry p present) |=
 V293_rdy_raw_cells (SuccessPub p present++SuccessLocals p++SuccessFrame p) Atrue.
Proof.
 intros p present Case. destruct Case;subst p;destruct present;
 unfold SuccessEntry;cbn [SuccessPub SuccessHead SuccessBit SuccessLocals SuccessFrame app SuccessMemory V293_rdy_raw_cells].
 all: repeat match goal with
 |- V293_wstate _ _ (merge (V293_encoded_memory ?b ?off true ?bytes) _) |= _ =>
 let count:=eval cbn [length V293_byteval encode_val typelen list_repeat inj_pointer inj_bytes encode_int List.map] in (Z.of_nat(length bytes)) in
 eapply V293_wstate_star with (m1:=V293_encoded_memory b off true bytes);
 [SuccessApart b off count|split;[apply V293_encoded_memory_mapsto|reflexivity]| ]
 end.
 all: exact I.
Qed.
Definition SuccessExpected p (present : bool) : list V293_record_cell :=
 [((301%positive,28),Tcom_ptr 410%Z,SuccessHead present);
  ((301%positive,32),Tcom_ptr 410%Z,Vnull);
  ((301%positive,60),Tint8,V293_byteval 1);
  ((301%positive,62),Tint8,V293_byteval 2);
  ((301%positive,61),Tint8,V293_byteval (2^SuccessBit p));
  ((401%positive,0),Tptr V293_tcb_type,Vptr(301%positive,Int.repr 8));
  ((402%positive,0),Tint8,V293_byteval 2);
  ((403%positive,1),Tint8,V293_byteval (Nat.setbit 2 (SuccessBit p)));
  ((404%positive,0),Tint8,V293_byteval 8)]++
  (if present then [((302%positive,40),Tcom_ptr 410%Z,Vptr(301%positive,Int.repr 8))] else [])++SuccessFrame p.
Theorem SuccessConcreteExecution : forall p present enabled si ci,
 p=12%nat \/ p=11%nat ->
 exists Mf,
 V293_local_steps SuccessProgram SuccessStart
  ((SuccessGE,SuccessLE,SuccessEntry p present),(fun _=>false),(enabled,si,ci))
  SuccessStop ((SuccessGE,SuccessCaller,Mf),(fun _=>false),(enabled,si,ci)) /\
 (forall a tp v, In (a,tp,v) (SuccessExpected p present) -> load tp Mf a=Some v) /\
 (forall b tp k, In (b,tp) (V293_tcb_function_addresses 201%positive 202%positive 203%positive 204%positive 205%positive 206%positive 207%positive 208%positive 209%positive) ->
 (k<typelen tp)%nat -> get Mf(b,Z.of_nat k)=None).
Proof.
 intros p present enabled si ci Case.
 pose proof (SuccessLiteralEntry p present Case) as Entry.
 rewrite V293_raw_cells_append in Entry.
 destruct (V293_OS_TCBInit_success_suffix_return SuccessProgram 500%Z 501%Z 502%Z SuccessCaller kstop
 SuccessGE (SuccessEntry p present) (fun _=>false) (false,nil,nil) (emp:osabst) (spec_done None) enabled si ci
 201%positive 202%positive 203%positive 204%positive 205%positive 206%positive 207%positive 208%positive 209%positive
 301%positive 8%Z 401%positive 402%positive 403%positive 404%positive 302%positive 16%Z present
 1%nat (SuccessBit p) 2%nat 2%nat 7%nat Vnull Vundef Vnull
 (V293_byteval p) Vnull Vnull (Vint32 Int.zero) (Vint32 Int.zero) Vnull (Vint32 Int.zero) (Vint32 Int.zero) (SuccessFrame p))
 as (Ms&Mf&Exec&BeforeReturn&Owned&Freed).
 - repeat split;reflexivity.
 - repeat constructor;cbn;intuition congruence.
 - lia.
 - change (8+54<=4294967295)%Z;lia.
 - lia.
 - change (16+24<=4294967295)%Z;lia.
 - lia.
 - destruct Case;subst p;vm_compute;lia.
 - lia.
 - lia.
 - lia.
 - intros a tp v Member. destruct present;
   cbn [V293_pub_cells SuccessFrame tl app In V293_tcb_function_blocks] in Member |- *;
   repeat destruct Member as [E|Member];try contradiction;inversion E;subst;cbn;intuition congruence.
 - change ((SuccessGE,SuccessLE,SuccessEntry p present,(fun _=>false),(false,nil,nil),(emp:osabst),(spec_done None)) |=
    V293_rdy_raw_cells (SuccessPub p present) (V293_rdy_raw_cells (SuccessLocals p++SuccessFrame p) Atrue)).
   exact Entry.
 - exists Mf. split;[exact Exec| ]. split;[ |exact Freed].
   assert (Expected : (SuccessGE,SuccessCaller,Mf,(fun _=>false),(false,nil,nil),(emp:osabst),(spec_done None)) |=
    V293_rdy_raw_cells (SuccessExpected p present) Atrue).
   { destruct Case;subst p;destruct present;exact Owned. }
   intros a tp v Member.
   eapply (V293_rdy_raw_load (SuccessExpected p present) Atrue a tp v
    (SuccessGE,SuccessCaller,Mf,(fun _=>false),(false,nil,nil),(emp:osabst),(spec_done None))).
   + exact Member.
   + destruct Case;subst p;destruct present;
     cbn [SuccessExpected SuccessHead SuccessBit SuccessFrame app In] in Member;
     repeat destruct Member as [E|Member];try contradiction;inversion E;subst;reflexivity.
   + exact Expected.
Qed.
Print Assumptions SuccessLiteralEntry.
Print Assumptions SuccessConcreteExecution.
