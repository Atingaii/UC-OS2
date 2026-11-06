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

Require Import CertiOS.certiucos.v293.proofs.V293TCBCallSuccess.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitEntry.
Definition SuccessOld : list V293_record_cell :=
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

Definition SuccessCaller : env := set emp 108%Z (602%positive,Tint8).
Definition SuccessProgram f := if Z.eq_dec f 500%Z then Some(V293_TCBInit_function 501%Z 502%Z) else None.
Definition SuccessGE : env :=
 set (set (set (set (set (set emp 91%Z (209%positive,Tptr V293_tcb_type))
 92%Z (310%positive,Tarray (Tptr V293_tcb_type) 13))
 93%Z (401%positive,Tptr V293_tcb_type)) 94%Z (402%positive,Tint8))
 95%Z (403%positive,Tarray Tint8 2)) 96%Z (404%positive,Tint8).
Definition SuccessHead (present : bool) := if present then Vptr(302%positive,Int.repr 16) else Vnull.
Definition SuccessNext := Vptr(501%positive,Int.repr 56).
Definition SuccessTop := Vptr(405%positive,Int.repr 508).
Definition SuccessBottom := Vptr(405%positive,Int.zero).
Definition SuccessFrame : list V293_record_cell :=
 [((310%positive,0),Tptr V293_tcb_type,Vnull);
  ((301%positive,48),Tint16,Vint32(Int.repr 4660));
  ((301%positive,50),Tint16,Vint32(Int.repr 22136));
  ((601%positive,0),Tint32,Vint32(Int.repr 77));
  ((602%positive,0),Tint8,Vint32(Int.repr 88))].
Definition SuccessTail (p : nat) (present : bool) : list V293_record_cell :=
 [((301%positive,32),Tcom_ptr 410%Z,Vundef);
  ((401%positive,0),Tptr V293_tcb_type,SuccessHead present);
  ((402%positive,0),Tint8,V293_byteval 2);
  ((403%positive,1),Tint8,V293_byteval 2);
  ((404%positive,0),Tint8,V293_byteval 7)]++
 (if present then [((302%positive,40),Tcom_ptr 410%Z,Vnull)] else [])++SuccessFrame.
Definition SuccessInputs p present : list V293_record_cell :=
 SuccessOld++
 [((209%positive,0),Tptr V293_tcb_type,Vptr(301%positive,Int.repr 8));
  ((301%positive,28),Tcom_ptr 410%Z,SuccessNext);
  ((310%positive,4*Z.of_nat p),Tptr V293_tcb_type,Vundef)]++SuccessTail p present.
Fixpoint SuccessMemory (cells : list V293_record_cell) : mem :=
 match cells with []=>emp | ((b,off),tp,v)::tail=>
 merge (V293_encoded_memory b off true (encode_val tp v)) (SuccessMemory tail) end.
Definition SuccessEntry p present := SuccessMemory (SuccessInputs p present).
Definition SuccessArgs p :=
 [Vint32(Int.repr 3);Vnull;Vint32(Int.repr 128);Vint32(Int.repr 65535);
  SuccessBottom;SuccessTop;V293_byteval p].
Definition SuccessStart p := (curs(sfexec 500%Z (SuccessArgs p) V293_TCBInit_argument_types),(kenil,kstop)).
Definition SuccessStop := (curs(sskip(Some(Vint32 Int.zero))),(kenil,kstop)).
Ltac SuccessOutside :=
 repeat first [rewrite V293_encoded_memory_outside by
 (first [left;congruence|right;cbn [length SuccessNext SuccessTop SuccessBottom V293_byteval encode_val typelen list_repeat inj_pointer inj_bytes encode_int List.map];lia])
 |rewrite map_merge_semp by reflexivity];reflexivity.
Ltac SuccessApart b start count :=
 apply map_join_merge;apply map_disjoint;intros [other off];
 destruct (Pos.eq_dec other b) as [B|B];
 [subst other;destruct (Z_lt_dec off start) as [Low|Low];
 [left;apply V293_encoded_memory_outside;right;left;exact Low|
 destruct (Z_lt_dec off (start+count)) as [Inside|Outside];
 [right;left;SuccessOutside|left;apply V293_encoded_memory_outside;right;right;
 cbn [length SuccessNext SuccessTop SuccessBottom V293_byteval encode_val typelen list_repeat inj_pointer inj_bytes encode_int List.map];lia]]|
 left;apply V293_encoded_memory_outside;left;exact B].


Lemma SuccessLiteralEntry : forall p present,
 p=12%nat \/ p=11%nat ->
 V293_wstate SuccessGE SuccessCaller (SuccessEntry p present) |=
 V293_rdy_raw_cells (SuccessInputs p present) Atrue.
Proof.
 intros p present Case. destruct Case;subst p;destruct present;
 unfold SuccessEntry;cbn [SuccessInputs SuccessOld SuccessTail SuccessHead SuccessNext SuccessFrame app SuccessMemory V293_rdy_raw_cells].
 all: eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 8%Z true (encode_val (Tptr Tint32) Vundef));
 [SuccessApart 301%positive 8%Z 4%Z|split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
 all: eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 58%Z true (encode_val Tint8 Vundef));
 [SuccessApart 301%positive 58%Z 1%Z|split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
 all: repeat match goal with
 |- V293_wstate _ _ (merge (V293_encoded_memory ?b ?off true ?bytes) _) |= _ =>
 let count:=eval cbn [length SuccessNext SuccessTop SuccessBottom V293_byteval encode_val typelen list_repeat inj_pointer inj_bytes encode_int List.map] in (Z.of_nat(length bytes)) in
 eapply V293_wstate_star with (m1:=V293_encoded_memory b off true bytes);
 [SuccessApart b off count|split;[apply V293_encoded_memory_mapsto|reflexivity]| ]
 end.
 all: exact I.
Qed.
(* These are hypotheses, never constructed for the declaration-only program. *)
Definition SuccessHook P p present enabled si ci (second : bool) :=
 forall b1 b2 b3 b4 b5 b6 b7 b8 b9,
 NoDup (V293_tcb_function_blocks b1 b2 b3 b4 b5 b6 b7 b8 b9) ->
 V293_tcb_creation_hook_return P (if second then 502%Z else 501%Z) 301%positive 8%Z
  (if second then V293_tcb_second_hook_cont 500%Z 501%Z 502%Z SuccessCaller kstop
   else V293_tcb_first_hook_cont 500%Z 501%Z 502%Z SuccessCaller kstop)
  SuccessGE (V293_tcb_function_env b1 b2 b3 b4 b5 b6 b7 b8 b9)
  (fun _=>false) (false,nil,nil) (emp:osabst) (spec_done None) enabled si ci
  (V293_tcb_hook_cells b1 b2 b3 b4 b5 b6 b7 b8 b9 209%positive 310%positive 301%positive 8%Z p
    SuccessTop SuccessBottom (Vint32(Int.repr 65535)) (Vint32(Int.repr 128)) Vnull (Vint32(Int.repr 3))
    SuccessNext (if second then Vptr(301%positive,Int.repr 8) else Vundef) (SuccessTail p present)).
Definition SuccessFields p : list V293_record_cell :=
 [((301%positive,8),Tptr Tint32,SuccessTop);
  ((301%positive,58),Tint8,V293_byteval p);
  ((301%positive,56),Tint8,Vint32 Int.zero);
  ((301%positive,57),Tint8,Vint32 Int.zero);
  ((301%positive,52),Tint32,Vint32 Int.zero);
  ((301%positive,12),Tptr Tvoid,Vnull);
  ((301%positive,20),Tint32,Vint32(Int.repr 128));
  ((301%positive,16),Tptr Tint32,SuccessBottom);
  ((301%positive,24),Tint16,Vint32(Int.repr 3));
  ((301%positive,26),Tint16,Vint32(Int.repr 65535));
  ((301%positive,63),Tint8,Vint32 Int.zero);
  ((301%positive,59),Tint8,V293_byteval (p mod 8));
  ((301%positive,36),Tcom_ptr 411%Z,Vnull);
  ((301%positive,44),Tcom_ptr 412%Z,Vnull);
  ((301%positive,40),Tptr Tvoid,Vnull)].
Definition SuccessExpected p (present : bool) : list V293_record_cell :=
 [((301%positive,28),Tcom_ptr 410%Z,SuccessHead present);
  ((301%positive,32),Tcom_ptr 410%Z,Vnull);
  ((301%positive,60),Tint8,V293_byteval 1);
  ((301%positive,62),Tint8,V293_byteval 2);
  ((301%positive,61),Tint8,V293_byteval (2^(p mod 8)));
  ((401%positive,0),Tptr V293_tcb_type,Vptr(301%positive,Int.repr 8));
  ((402%positive,0),Tint8,V293_byteval 2);
  ((403%positive,1),Tint8,V293_byteval (Nat.setbit 2 (p mod 8)));
  ((404%positive,0),Tint8,V293_byteval 8)]++
 (if present then [((302%positive,40),Tcom_ptr 410%Z,Vptr(301%positive,Int.repr 8))] else [])++
 SuccessFields p++
 [((209%positive,0),Tptr V293_tcb_type,SuccessNext);
  ((310%positive,4*Z.of_nat p),Tptr V293_tcb_type,Vptr(301%positive,Int.repr 8))]++SuccessFrame.
Theorem SuccessConditionalExecution : forall P p present enabled si ci,
 p=12%nat \/ p=11%nat ->
 P 500%Z=Some(V293_TCBInit_function 501%Z 502%Z) ->
 SuccessHook P p present enabled si ci false ->
 SuccessHook P p present enabled si ci true ->
 exists b1 b2 b3 b4 b5 b6 b7 b8 b9 Mf,
 NoDup (V293_tcb_function_blocks b1 b2 b3 b4 b5 b6 b7 b8 b9) /\ (forall b, In b (V293_tcb_function_blocks b1 b2 b3 b4 b5 b6 b7 b8 b9) -> fresh (SuccessEntry p present) b) /\ V293_local_steps P (SuccessStart p)
 ((SuccessGE,SuccessCaller,SuccessEntry p present),(fun _=>false),(enabled,si,ci))
 SuccessStop ((SuccessGE,SuccessCaller,Mf),(fun _=>false),(enabled,si,ci)) /\ (forall a tp v, In (a,tp,v) (SuccessExpected p present) -> load tp Mf a=Some v) /\ (forall b tp k, In (b,tp) (V293_tcb_function_addresses b1 b2 b3 b4 b5 b6 b7 b8 b9) ->
 (k<typelen tp)%nat -> get Mf(b,Z.of_nat k)=None).
Proof.
 intros P p present enabled si ci Case Program Hook1 Hook2.
 pose proof (SuccessLiteralEntry p present Case) as Entry.
 destruct (V293_OS_TCBInit_success_call_under_hooks P kstop SuccessGE SuccessCaller (SuccessEntry p present)
 (fun _=>false) (false,nil,nil) (emp:osabst) (spec_done None) enabled si ci
 500%Z 501%Z 502%Z 209%positive 310%positive 301%positive 8%Z
 401%positive 402%positive 403%positive 404%positive 302%positive 16%Z present p
 SuccessTop SuccessBottom (Vint32(Int.repr 65535)) (Vint32(Int.repr 128)) Vnull (Vint32(Int.repr 3))
 SuccessNext (fun _=>Vundef) Vundef Vundef 2%nat 2%nat 7%nat Vnull SuccessFrame)
 as (b1&b2&b3&b4&b5&b6&b7&b8&b9&Mf&ND&Fresh&Exec&Owned&Freed).
 - exact Program.
 - reflexivity.
 - reflexivity.
 - reflexivity.
 - reflexivity.
 - reflexivity.
 - reflexivity.
 - destruct Case;subst;lia.
 - lia.
 - change (8+55<=4294967295)%Z;lia.
 - lia.
 - change (16+24<=4294967295)%Z;lia.
 - lia.
 - lia.
 - lia.
 - repeat split;reflexivity.
 - reflexivity.
 - destruct Case;subst p;exact Hook1.
 - destruct Case;subst p;exact Hook2.
 - destruct Case;subst p;exact Entry.
 - exists b1. exists b2. exists b3. exists b4. exists b5. exists b6. exists b7. exists b8. exists b9. exists Mf.
   split;[exact ND| ]. split;[exact Fresh| ]. split;[exact Exec| ]. split;[ |exact Freed].
   assert (Expected : (SuccessGE,SuccessCaller,Mf,(fun _=>false),(false,nil,nil),(emp:osabst),(spec_done None)) |=
    V293_rdy_raw_cells (SuccessExpected p present) Atrue).
   { destruct Case;subst p;destruct present;exact Owned. }
   intros a tp v Member.
   eapply (V293_rdy_raw_load (SuccessExpected p present) Atrue a tp v
    (SuccessGE,SuccessCaller,Mf,(fun _=>false),(false,nil,nil),(emp:osabst),(spec_done None))).
   + exact Member.
   + destruct Case;subst p;destruct present;
     cbn [SuccessExpected SuccessHead SuccessFields SuccessTop SuccessBottom SuccessNext SuccessFrame app In] in Member;
     repeat destruct Member as [E|Member];try contradiction;inversion E;subst;reflexivity.
   + exact Expected.
Qed.
Lemma SuccessFixedMissing : SuccessProgram 501%Z=None /\ SuccessProgram 502%Z=None.
Proof. split;reflexivity. Qed.
Print Assumptions SuccessLiteralEntry.
Print Assumptions SuccessConditionalExecution.
Print Assumptions SuccessFixedMissing.

(* Unconditional witness for the fixed declaration-only program: the very same
   satisfiable literal entries reach the first Hook and have no next local step. *)
Definition SuccessFirstAnchor :=
 (curs(sfexec 501%Z [Vptr(301%positive,Int.repr 8)] [Tptr V293_tcb_type]),
 (kenil,V293_tcb_first_hook_cont 500%Z 501%Z 502%Z SuccessCaller kstop)).
Theorem SuccessActualFirstHookStuck : forall p present enabled si ci,
 p=12%nat \/ p=11%nat ->
 exists le Mh,
 V293_local_steps SuccessProgram (SuccessStart p)
 ((SuccessGE,SuccessCaller,SuccessEntry p present),(fun _=>false),(enabled,si,ci))
 SuccessFirstAnchor ((SuccessGE,le,Mh),(fun _=>false),(enabled,si,ci)) /\
 ~exists C' state', loststep SuccessProgram SuccessFirstAnchor
 ((SuccessGE,le,Mh),(fun _=>false),(enabled,si,ci)) C' state'.
Proof.
 intros p present enabled si ci Case.
 pose proof (SuccessLiteralEntry p present Case) as Entry.
 destruct (V293_OS_TCBInit_call_to_first_hook SuccessProgram kstop SuccessGE SuccessCaller (SuccessEntry p present)
 (fun _=>false) (false,nil,nil) (emp:osabst) (spec_done None) enabled si ci
 500%Z 501%Z 502%Z 209%positive 301%positive 8%Z p
 SuccessTop SuccessBottom (Vint32(Int.repr 65535)) (Vint32(Int.repr 128)) Vnull (Vint32(Int.repr 3))
 SuccessNext (fun _=>Vundef)
 (((310%positive,4*Z.of_nat p),Tptr V293_tcb_type,Vundef)::SuccessTail p present))
 as (b1&b2&b3&b4&b5&b6&b7&b8&b9&Mh&ND&Exec&Owned&Stuck).
 - reflexivity.
 - reflexivity.
 - destruct Case;subst;lia.
 - lia.
 - change (8+55<=4294967295)%Z;lia.
 - repeat split;reflexivity.
 - reflexivity.
 - exact Entry.
 - exists (V293_tcb_function_env b1 b2 b3 b4 b5 b6 b7 b8 b9). exists Mh.
   split;[exact Exec|apply Stuck;reflexivity].
Qed.
Print Assumptions SuccessActualFirstHookStuck.
