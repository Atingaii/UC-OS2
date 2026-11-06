(* Independent literal inputs with all four argument bindings. No imports
   from previous probes. Source mapping is manual per ADR0004/5/7. *)
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
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateStackEntry.
Require Import CertiOS.certiucos.v293.proofs.V293NullBytes.

Definition StackGE : env :=
 set(set(set emp 92%Z (510%positive,Tarray(Tptr V293_tcb_type)13))
  97%Z (502%positive,Tint8)) 98%Z (700%positive,Tint8).
Definition StackLE : env :=
 set(set(set(set(set(set(set emp 101%Z (501%positive,Tint8))
  109%Z (503%positive,Tint32)) 108%Z (504%positive,Tptr Tint32))
  201%Z (505%positive,Tint32)) 202%Z (506%positive,Tptr Tvoid))
  203%Z (507%positive,Tptr Tint32)) 204%Z (508%positive,Tint16).
Definition StackArg := Vptr(801%positive,Int.zero).
Definition StackTop := Vptr(802%positive,Int.repr 16).
Definition StackOpt := Vint32(Int.repr 5).
Definition StackArguments target : list V293_record_cell :=
 [((505%positive,0),Tint32,V293_task_selector target);
  ((506%positive,0),Tptr Tvoid,StackArg);
  ((507%positive,0),Tptr Tint32,StackTop);
  ((508%positive,0),Tint16,StackOpt)].
Definition StackFrame : list V293_record_cell :=
 [((504%positive,0),Tptr Tint32,Vnull);
  ((510%positive,4),Tptr V293_tcb_type,Vnull);
  ((601%positive,0),Tint32,Vint32(Int.repr 77));
  ((602%positive,0),Tint8,Vint32(Int.repr 88))].
Definition StackInputs p target : list V293_record_cell :=
 [((501%positive,0),Tint8,V293_byteval p);
  ((502%positive,0),Tint8,Vint32 Int.zero);
  ((503%positive,0),Tint32,Vint32(Int.repr 23));
  ((510%positive,4*Z.of_nat p),Tptr V293_tcb_type,Vnull)]++StackArguments target++StackFrame.
Definition StackExpected p target : list V293_record_cell :=
 [((501%positive,0),Tint8,V293_byteval p);
  ((502%positive,0),Tint8,Vint32 Int.zero);
  ((503%positive,0),Tint32,Vint32 Int.zero);
  ((510%positive,4*Z.of_nat p),Tptr V293_tcb_type,Vptr(700%positive,Int.zero))]++StackArguments target++StackFrame.
Fixpoint StackMemory (cells : list V293_record_cell) : mem :=
 match cells with []=>emp | ((b,off),tp,v)::tail=>
 merge (V293_encoded_memory b off true (encode_val tp v)) (StackMemory tail) end.
Definition StackEntry p target := StackMemory(StackInputs p target).
Definition StackCall := V293_TaskCreateExt_stack_call 108%Z 900%Z 201%Z 202%Z 203%Z 204%Z.
Definition StackStart :=
 (curs(V293_TaskCreateExt_prefix 92%Z 101%Z 97%Z 109%Z 98%Z
   (sseq StackCall (sskip None))),(kenil,kstop)).
Definition StackContinuation :=
 kassignr (evar 108%Z) (Tptr Tint32)
  (kseq (sskip None) (kseq V293_TaskCreateExt_occupied kstop)).
Definition StackStop target :=
 (curs(sfexec 900%Z [StackOpt;StackTop;StackArg;V293_task_selector target]
   V293_stack_argument_types),(kenil,StackContinuation)).
Ltac StackOutside :=
 repeat first [rewrite V293_encoded_memory_outside by
 (first [left;congruence | right;cbn [length V293_byteval V293_task_selector StackArg StackTop StackOpt encode_val typelen list_repeat inj_pointer inj_bytes encode_int List.map];lia])
 | rewrite map_merge_semp by reflexivity];reflexivity.
Ltac StackApart b start count :=
 apply map_join_merge;apply map_disjoint;intros [other off];
 destruct (Pos.eq_dec other b) as [B | B];
 [subst other;destruct (Z_lt_dec off start) as [Low | Low];
 [left;apply V293_encoded_memory_outside;right;left;exact Low |
 destruct (Z_lt_dec off (start+count)) as [Inside | Outside];
 [right;left;StackOutside | left;apply V293_encoded_memory_outside;right;right;
 cbn [length V293_byteval V293_task_selector StackArg StackTop StackOpt encode_val typelen list_repeat inj_pointer inj_bytes encode_int List.map];lia]] |
 left;apply V293_encoded_memory_outside;left;exact B].

Lemma StackLiteralEntry : forall p target,
 (p=0%nat \/ p=12%nat) -> (target=700 \/ target=701) ->
 V293_wstate StackGE StackLE (StackEntry p target) |=
 V293_rdy_raw_cells (StackInputs p target) Atrue.
Proof.
 intros p target PC TC. destruct PC;destruct TC;subst p;subst target;
 unfold StackEntry;cbn [StackInputs StackArguments StackFrame app StackMemory V293_rdy_raw_cells].
 all: repeat match goal with
 |- V293_wstate _ _ (merge (V293_encoded_memory ?b ?off true ?bytes) _) |= _ =>
 let count:=eval cbn [length V293_byteval V293_task_selector StackArg StackTop StackOpt encode_val typelen list_repeat inj_pointer inj_bytes encode_int List.map] in (Z.of_nat(length bytes)) in
 eapply V293_wstate_star with (m1:=V293_encoded_memory b off true bytes);
 [StackApart b off count | split;[apply V293_encoded_memory_mapsto | reflexivity] | ]
 end.
 all: exact I.
Qed.
Theorem StackActualHookEntry : forall P p target enabled si ci,
 (p=0%nat \/ p=12%nat) -> (target=700 \/ target=701) ->
 exists Mf,
 V293_local_steps P StackStart ((StackGE,StackLE,StackEntry p target),(fun _=>false),(enabled,si,ci))
 (StackStop target) ((StackGE,StackLE,Mf),(fun _=>false),(enabled,si,ci)) /\
 (forall a tp v, In (a,tp,v) (StackExpected p target) -> load tp Mf a=Some v) /\
 vtoZ(V293_task_selector target)=Some target /\
 (P 900%Z=None -> ~exists C' state', loststep P (StackStop target)
  ((StackGE,StackLE,Mf),(fun _=>false),(enabled,si,ci)) C' state').
Proof.
 intros P p target enabled si ci PC TC.
 pose proof(StackLiteralEntry p target PC TC) as Entry.
 assert (Range : (p<13)%nat) by (destruct PC;subst p;lia).
 assert (Target : 0<=target<=Int.max_unsigned).
 { destruct TC;subst target;unfold Int.max_unsigned,Int.modulus,Int.wordsize;cbn;lia. }
 destruct(V293_OSTaskCreateExt_to_stack_hook P kstop StackGE StackLE (StackEntry p target)
  (fun _=>false) (false,nil,nil) (emp:osabst) (spec_done None)
  (V293_rdy_raw_cells StackFrame Atrue) enabled si ci
  92%Z 101%Z 97%Z 109%Z 98%Z 501%positive 502%positive 503%positive 510%positive 700%positive p
  (Vint32(Int.repr 23)) 108%Z 900%Z 201%Z 202%Z 203%Z 204%Z 504%positive
  505%positive 506%positive 507%positive 508%positive target StackArg StackTop StackOpt (sskip None))
 as (Mf&Exec&Owned&Decode&Missing).
 all: try reflexivity.
 - exact Range.
 - exact Target.
 - repeat split;reflexivity.
 - repeat split;reflexivity.
 - rewrite <-V293_raw_cells_append. exact Entry.
 - exists Mf. split;[exact Exec | ]. split;[ | split;[exact Decode | exact Missing]].
   assert (Expected : (StackGE,StackLE,Mf,(fun _=>false),(false,nil,nil),(emp:osabst),(spec_done None)) |=
    V293_rdy_raw_cells (StackExpected p target) Atrue).
   { rewrite <-V293_raw_cells_append in Owned. exact Owned. }
   intros a tp v Member.
   eapply (V293_rdy_raw_load (StackExpected p target) Atrue a tp v
    (StackGE,StackLE,Mf,(fun _=>false),(false,nil,nil),(emp:osabst),(spec_done None))).
   + exact Member.
   + destruct PC;destruct TC;subst p;subst target;
     cbn [StackExpected StackArguments StackFrame StackArg StackTop StackOpt V293_task_selector app In] in Member;
     repeat destruct Member as [E | Member];try contradiction;inversion E;subst;reflexivity.
   + exact Expected.
Qed.
(* This is an actual reachable missing-port endpoint, not the unbound-task
   fixture of stage66. Other P entries are arbitrary and remain untouched. *)
Theorem StackActualMissingPort : forall P p target enabled si ci,
 P 900%Z=None -> (p=0%nat \/ p=12%nat) -> (target=700 \/ target=701) ->
 exists Mf,
 V293_local_steps P StackStart ((StackGE,StackLE,StackEntry p target),(fun _=>false),(enabled,si,ci))
 (StackStop target) ((StackGE,StackLE,Mf),(fun _=>false),(enabled,si,ci)) /\
 ~exists C' state', loststep P (StackStop target)
  ((StackGE,StackLE,Mf),(fun _=>false),(enabled,si,ci)) C' state'.
Proof.
 intros P p target enabled si ci Missing PC TC.
 destruct(StackActualHookEntry P p target enabled si ci PC TC) as (Mf&Exec&Reads&Decode&Stuck).
 exists Mf. split;[exact Exec | apply Stuck;exact Missing].
Qed.
Print Assumptions StackLiteralEntry.
Print Assumptions StackActualHookEntry.
Print Assumptions StackActualMissingPort.
