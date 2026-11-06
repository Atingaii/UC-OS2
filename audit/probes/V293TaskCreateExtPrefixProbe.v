(* Independent literal body-entry fixtures. No old audit probe imports.
   The unexecuted four task-creation arguments deliberately have no bindings:
   this probe reaches call setup, NOT argument evaluation or a Hook sfexec. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.code.V293OSTaskCreateExtPrefix.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateExtPrefix.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitFields.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope Z_scope.
Definition CreateGE : env :=
 set(set(set emp 92%Z (510%positive,Tarray(Tptr V293_tcb_type)13))
  97%Z (502%positive,Tint8)) 98%Z (700%positive,Tint8).
Definition CreateLE : env :=
 set(set(set emp 101%Z (501%positive,Tint8)) 109%Z (503%positive,Tint32))
 108%Z (504%positive,Tptr Tint32).
Definition CreateFrame : list V293_record_cell :=
 [((504%positive,0),Tptr Tint32,Vnull);
  ((510%positive,4),Tptr V293_tcb_type,Vnull);
  ((601%positive,0),Tint32,Vint32(Int.repr 77));
  ((602%positive,0),Tint8,Vint32(Int.repr 88))].
Definition CreateInputs p : list V293_record_cell :=
 [((501%positive,0),Tint8,V293_byteval p);
  ((502%positive,0),Tint8,Vint32 Int.zero);
  ((503%positive,0),Tint32,Vint32(Int.repr 23));
  ((510%positive,4*Z.of_nat p),Tptr V293_tcb_type,Vnull)]++CreateFrame.
Definition CreateExpected p : list V293_record_cell :=
 [((501%positive,0),Tint8,V293_byteval p);
  ((502%positive,0),Tint8,Vint32 Int.zero);
  ((503%positive,0),Tint32,Vint32 Int.zero);
  ((510%positive,4*Z.of_nat p),Tptr V293_tcb_type,Vptr(700%positive,Int.zero))]++CreateFrame.
Fixpoint CreateMemory (cells : list V293_record_cell) : mem :=
 match cells with []=>emp | ((b,off),tp,v)::tail=>
 merge (V293_encoded_memory b off true (encode_val tp v)) (CreateMemory tail) end.
Definition CreateEntry p := CreateMemory(CreateInputs p).
Definition CreateCall := V293_TaskCreateExt_stack_call 108%Z 900%Z 201%Z 202%Z 203%Z 204%Z.
Definition CreateStart :=
 (curs(V293_TaskCreateExt_prefix 92%Z 101%Z 97%Z 109%Z 98%Z
   (sseq CreateCall (sskip None))),(kenil,kstop)).
Definition CreateStop :=
 (curs(scall 900%Z (evar 201%Z::evar 202%Z::evar 203%Z::evar 204%Z::nil)),
  (kenil,kassignr (evar 108%Z) (Tptr Tint32)
   (kseq (sskip None) (kseq V293_TaskCreateExt_occupied kstop)))).
Ltac CreateOutside :=
 repeat first [rewrite V293_encoded_memory_outside by
 (first [left;congruence | right;cbn [length V293_byteval encode_val typelen list_repeat inj_pointer inj_bytes encode_int List.map];lia])
 | rewrite map_merge_semp by reflexivity];reflexivity.
Ltac CreateApart b start count :=
 apply map_join_merge;apply map_disjoint;intros [other off];
 destruct (Pos.eq_dec other b) as [B | B];
 [subst other;destruct (Z_lt_dec off start) as [Low | Low];
 [left;apply V293_encoded_memory_outside;right;left;exact Low |
 destruct (Z_lt_dec off (start+count)) as [Inside | Outside];
 [right;left;CreateOutside | left;apply V293_encoded_memory_outside;right;right;
 cbn [length V293_byteval encode_val typelen list_repeat inj_pointer inj_bytes encode_int List.map];lia]] |
 left;apply V293_encoded_memory_outside;left;exact B].
Lemma CreateLiteralEntry : forall p,
 p=0%nat \/ p=12%nat ->
 V293_wstate CreateGE CreateLE (CreateEntry p) |=
 V293_rdy_raw_cells (CreateInputs p) Atrue.
Proof.
 intros p Case. destruct Case;subst p;
 unfold CreateEntry;cbn [CreateInputs CreateFrame app CreateMemory V293_rdy_raw_cells].
 all: repeat match goal with
 |- V293_wstate _ _ (merge (V293_encoded_memory ?b ?off true ?bytes) _) |= _ =>
 let count:=eval cbn [length V293_byteval encode_val typelen list_repeat inj_pointer inj_bytes encode_int List.map] in (Z.of_nat(length bytes)) in
 eapply V293_wstate_star with (m1:=V293_encoded_memory b off true bytes);
 [CreateApart b off count | split;[apply V293_encoded_memory_mapsto | reflexivity] | ]
 end.
 all: exact I.
Qed.
Theorem CreateActualSetup : forall P p enabled si ci,
 p=0%nat \/ p=12%nat ->
 exists Mf,
 V293_local_steps P CreateStart ((CreateGE,CreateLE,CreateEntry p),(fun _=>false),(enabled,si,ci))
 CreateStop ((CreateGE,CreateLE,Mf),(fun _=>false),(enabled,si,ci)) /\
 (forall a tp v, In (a,tp,v) (CreateExpected p) -> load tp Mf a=Some v).
Proof.
 intros P p enabled si ci Case.
 pose proof(CreateLiteralEntry p Case) as Entry.
 destruct (V293_OSTaskCreateExt_to_stack_call_setup P kstop CreateGE CreateLE (CreateEntry p)
  (fun _=>false) (false,nil,nil) (emp:osabst) (spec_done None)
  (V293_rdy_raw_cells CreateFrame Atrue) enabled si ci
  92%Z 101%Z 97%Z 109%Z 98%Z 501%positive 502%positive 503%positive 510%positive 700%positive p
  (Vint32(Int.repr 23)) 108%Z 900%Z 201%Z 202%Z 203%Z 204%Z 504%positive (sskip None))
  as (Mf&Exec&Owned).
 all: try reflexivity.
 - destruct Case;subst p;lia.
 - exact Entry.
 - exists Mf. split;[exact Exec | ].
   assert (Expected : (CreateGE,CreateLE,Mf,(fun _=>false),(false,nil,nil),(emp:osabst),(spec_done None)) |=
    V293_rdy_raw_cells (CreateExpected p) Atrue).
   { destruct Case;subst p;exact Owned. }
   intros a tp v Member.
   eapply (V293_rdy_raw_load (CreateExpected p) Atrue a tp v
    (CreateGE,CreateLE,Mf,(fun _=>false),(false,nil,nil),(emp:osabst),(spec_done None))).
   + exact Member.
   + destruct Case;subst p;cbn [CreateExpected CreateFrame app In] in Member;
     repeat destruct Member as [E | Member];try contradiction;inversion E;subst;reflexivity.
   + exact Expected.
Qed.
(* Deliberate bound: four argument variables are unbound, so first argument
   evaluation cannot start in this literal fixture. This is NOT a Hook-missing
   no-step claim and does not negate the proved unconditional call setup. *)
Lemma CreateTaskArgumentUnbound :
 evaltype(evar 201%Z)(CreateGE,CreateLE,CreateEntry 0)=None.
Proof. reflexivity. Qed.
Print Assumptions CreateLiteralEntry.
Print Assumptions CreateActualSetup.
