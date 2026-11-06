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

Require Import CertiOS.certiucos.v293.code.V293OSTaskCreateExtCalls.
Require Import CertiOS.certiucos.v293.code.V293OSTCBInitFunction.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateTCBEntry.
Local Open Scope Z_scope.

Definition BridgeGE : env :=
 set(set(set emp 92%Z (510%positive,Tarray(Tptr V293_tcb_type)13))
  97%Z (502%positive,Tint8)) 98%Z (700%positive,Tint8).
Definition BridgeLE : env :=
 set(set(set(set(set(set(set(set(set(set(set(set emp
  101%Z (501%positive,Tint8)) 109%Z (503%positive,Tint32))
  108%Z (504%positive,Tptr Tint32)) 201%Z (505%positive,Tint32))
  202%Z (506%positive,Tptr Tvoid)) 203%Z (507%positive,Tptr Tint32))
  204%Z (508%positive,Tint16)) 205%Z (509%positive,Tptr Tint32))
  206%Z (511%positive,Tint16)) 207%Z (512%positive,Tint32))
  208%Z (513%positive,Tptr Tvoid)) 209%Z (514%positive,Tint8).
Definition BridgeArg := Vptr(801%positive,Int.zero).
Definition BridgeTop := Vptr(802%positive,Int.repr 16).
Definition BridgeOpt := Vint32(Int.repr 5).
Definition BridgeBottom := Vptr(804%positive,Int.repr 64).
Definition BridgeId := Vint32(Int.repr 17).
Definition BridgeSize := Vint32(Int.repr 1024).
Definition BridgeExt := Vptr(805%positive,Int.zero).
Definition BridgeValue (nonnull:bool) := if nonnull then Vptr(803%positive,Int.repr 32) else Vnull.
Definition BridgeFrame : list V293_record_cell :=
 [((510%positive,4),Tptr V293_tcb_type,Vnull);
  ((601%positive,0),Tint32,Vint32(Int.repr 77));
  ((602%positive,0),Tint8,Vint32(Int.repr 88))].
Definition BridgeCells p cpu slot pspv : list V293_record_cell :=
 [((501%positive,0),Tint8,V293_byteval p);
  ((502%positive,0),Tint8,Vint32 Int.zero);
  ((503%positive,0),Tint32,cpu);
  ((510%positive,4*Z.of_nat p),Tptr V293_tcb_type,slot);
  ((505%positive,0),Tint32,V293_task_selector 700);
  ((506%positive,0),Tptr Tvoid,BridgeArg);
  ((507%positive,0),Tptr Tint32,BridgeTop);
  ((508%positive,0),Tint16,BridgeOpt);
  ((504%positive,0),Tptr Tint32,pspv);
  ((509%positive,0),Tptr Tint32,BridgeBottom);
  ((511%positive,0),Tint16,BridgeId);
  ((512%positive,0),Tint32,BridgeSize);
  ((513%positive,0),Tptr Tvoid,BridgeExt);
  ((514%positive,0),Tint8,Vint32(Int.repr 9))]++BridgeFrame.
Definition BridgeReturnCells p := BridgeCells p (Vint32 Int.zero) (Vptr(700%positive,Int.zero)) Vnull.
Definition BridgeBodyCells p := BridgeCells p (Vint32(Int.repr 23)) Vnull Vnull.
Definition BridgeExpected p nonnull := BridgeCells p (Vint32 Int.zero) (Vptr(700%positive,Int.zero)) (BridgeValue nonnull).
Fixpoint BridgeMemory (cells : list V293_record_cell) : mem :=
 match cells with []=>emp | ((b,off),tp,v)::tail=>
 merge (V293_encoded_memory b off true (encode_val tp v)) (BridgeMemory tail) end.
Definition BridgeEntry p := BridgeMemory(BridgeReturnCells p).
Definition BridgeBodyEntry p := BridgeMemory(BridgeBodyCells p).
Definition BridgeContinuation := V293_create_stack_cont 108%Z 209%Z 901%Z 101%Z 205%Z 206%Z 207%Z 208%Z 204%Z (sskip None) kstop.
Definition BridgeReturnStart nonnull := (curs(sskip(Some(BridgeValue nonnull))),(kenil,BridgeContinuation)).
Definition BridgeTCBContinuation := V293_create_TCB_cont 209%Z (sskip None) kstop.
Definition BridgeStop p nonnull :=
 (curs(sfexec 901%Z [BridgeOpt;BridgeExt;BridgeSize;BridgeId;BridgeBottom;BridgeValue nonnull;V293_byteval p]
 V293_TCBInit_argument_types),(kenil,BridgeTCBContinuation)).
Definition BridgeStart :=
 (curs(V293_TaskCreateExt_prefix 92%Z 101%Z 97%Z 109%Z 98%Z
 (V293_TaskCreateExt_calls 108%Z 900%Z 201%Z 202%Z 203%Z 204%Z 209%Z 901%Z 101%Z 205%Z 206%Z 207%Z 208%Z (sskip None))),
 (kenil,kstop)).
Definition BridgeHookStop :=
 (curs(sfexec 900%Z [BridgeOpt;BridgeTop;BridgeArg;V293_task_selector 700] V293_stack_argument_types),
 (kenil,BridgeContinuation)).
Ltac BridgeOutside :=
 repeat first [rewrite V293_encoded_memory_outside by
 (first [left;congruence | right;cbn [length V293_byteval V293_task_selector BridgeArg BridgeTop BridgeOpt BridgeBottom BridgeId BridgeSize BridgeExt BridgeValue encode_val typelen list_repeat inj_pointer inj_bytes encode_int List.map];lia])
 | rewrite map_merge_semp by reflexivity];reflexivity.
Ltac BridgeApart b start count :=
 apply map_join_merge;apply map_disjoint;intros [other off];
 destruct (Pos.eq_dec other b) as [B | B];
 [subst other;destruct (Z_lt_dec off start) as [Low | Low];
 [left;apply V293_encoded_memory_outside;right;left;exact Low |
 destruct (Z_lt_dec off (start+count)) as [Inside | Outside];
 [right;left;BridgeOutside | left;apply V293_encoded_memory_outside;right;right;
 cbn [length V293_byteval V293_task_selector BridgeArg BridgeTop BridgeOpt BridgeBottom BridgeId BridgeSize BridgeExt BridgeValue encode_val typelen list_repeat inj_pointer inj_bytes encode_int List.map];lia]] |
 left;apply V293_encoded_memory_outside;left;exact B].


Lemma BridgeLiteralReturnEntry : forall p,
 (p=0%nat \/ p=12%nat) ->
 V293_wstate BridgeGE BridgeLE (BridgeEntry p) |= V293_rdy_raw_cells (BridgeReturnCells p) Atrue.
Proof.
 intros p PC. destruct PC;subst p;unfold BridgeEntry;
 cbn [BridgeReturnCells BridgeCells BridgeFrame app BridgeMemory V293_rdy_raw_cells].
 all: repeat match goal with
 |- V293_wstate _ _ (merge (V293_encoded_memory ?b ?off true ?bytes) _) |= _ =>
 let count:=eval cbn [length V293_byteval V293_task_selector BridgeArg BridgeTop BridgeOpt BridgeBottom BridgeId BridgeSize BridgeExt encode_val typelen list_repeat inj_pointer inj_bytes encode_int List.map] in (Z.of_nat(length bytes)) in
 eapply V293_wstate_star with (m1:=V293_encoded_memory b off true bytes);
 [BridgeApart b off count | split;[apply V293_encoded_memory_mapsto | reflexivity] | ]
 end.
 all: exact I.
Qed.
Lemma BridgeLiteralBodyEntry : forall p,
 (p=0%nat \/ p=12%nat) ->
 V293_wstate BridgeGE BridgeLE (BridgeBodyEntry p) |= V293_rdy_raw_cells (BridgeBodyCells p) Atrue.
Proof.
 intros p PC. destruct PC;subst p;unfold BridgeBodyEntry;
 cbn [BridgeBodyCells BridgeCells BridgeFrame app BridgeMemory V293_rdy_raw_cells].
 all: repeat match goal with
 |- V293_wstate _ _ (merge (V293_encoded_memory ?b ?off true ?bytes) _) |= _ =>
 let count:=eval cbn [length V293_byteval V293_task_selector BridgeArg BridgeTop BridgeOpt BridgeBottom BridgeId BridgeSize BridgeExt encode_val typelen list_repeat inj_pointer inj_bytes encode_int List.map] in (Z.of_nat(length bytes)) in
 eapply V293_wstate_star with (m1:=V293_encoded_memory b off true bytes);
 [BridgeApart b off count | split;[apply V293_encoded_memory_mapsto | reflexivity] | ]
 end.
 all: exact I.
Qed.

Theorem BridgeActualAfterReturn : forall P p nonnull enabled si ci,
 (p=0%nat \/ p=12%nat) ->
 exists Mf,
 V293_local_steps P (BridgeReturnStart nonnull)
 ((BridgeGE,BridgeLE,BridgeEntry p),(fun _=>false),(enabled,si,ci))
 (BridgeStop p nonnull) ((BridgeGE,BridgeLE,Mf),(fun _=>false),(enabled,si,ci)) /\
 (forall a tp v, In (a,tp,v) (BridgeExpected p nonnull) -> load tp Mf a=Some v).
Proof.
 intros P p nonnull enabled si ci PC.
 pose proof(BridgeLiteralReturnEntry p PC) as Entry.
 assert(Range:(p<13)%nat) by (destruct PC;subst p;lia).
 destruct(V293_OSTaskCreateExt_after_stack_to_TCB P kstop BridgeGE BridgeLE (BridgeEntry p)
 (fun _=>false) (false,nil,nil) (emp:osabst) (spec_done None)
 (V293_rdy_raw_cells BridgeFrame Atrue) enabled si ci
 108%Z 209%Z 901%Z 101%Z 205%Z 206%Z 207%Z 208%Z 204%Z (sskip None)
 501%positive 502%positive 503%positive 510%positive 700%positive p
 505%positive 506%positive 507%positive 508%positive 700 BridgeArg BridgeTop BridgeOpt
 504%positive 509%positive 511%positive 512%positive 513%positive 514%positive
 Vnull BridgeBottom BridgeId BridgeSize BridgeExt (Vint32(Int.repr 9)) (BridgeValue nonnull))
 as (Mf&Exec&Owned).
 all: try reflexivity.
 - exact Range.
 - repeat split;reflexivity.
 - destruct nonnull;repeat split;reflexivity.
 - unfold V293_create_bridge_cells. rewrite <-V293_raw_cells_append. exact Entry.
 - exists Mf. split;[exact Exec | ].
   assert(Expected:(BridgeGE,BridgeLE,Mf,(fun _=>false),(false,nil,nil),(emp:osabst),(spec_done None)) |=
    V293_rdy_raw_cells (BridgeExpected p nonnull) Atrue).
   { unfold V293_create_bridge_cells in Owned. rewrite <-V293_raw_cells_append in Owned. exact Owned. }
   intros a tp v Member.
   eapply(V293_rdy_raw_load (BridgeExpected p nonnull) Atrue a tp v
    (BridgeGE,BridgeLE,Mf,(fun _=>false),(false,nil,nil),(emp:osabst),(spec_done None))).
   + exact Member.
   + destruct PC;destruct nonnull;subst p;
     cbn [BridgeExpected BridgeCells BridgeFrame BridgeValue BridgeArg BridgeTop BridgeOpt BridgeBottom BridgeId BridgeSize BridgeExt V293_task_selector app In] in Member;
     repeat destruct Member as [E | Member];try contradiction;inversion E;subst;reflexivity.
   + exact Expected.
Qed.

Theorem BridgeActualMissingStack : forall P p enabled si ci,
 P 900%Z=None -> (p=0%nat \/ p=12%nat) ->
 exists Mf,
 V293_local_steps P BridgeStart ((BridgeGE,BridgeLE,BridgeBodyEntry p),(fun _=>false),(enabled,si,ci))
 BridgeHookStop ((BridgeGE,BridgeLE,Mf),(fun _=>false),(enabled,si,ci)) /\
 ~exists C' state',loststep P BridgeHookStop ((BridgeGE,BridgeLE,Mf),(fun _=>false),(enabled,si,ci)) C' state'.
Proof.
 intros P p enabled si ci Missing PC.
 pose proof(BridgeLiteralBodyEntry p PC) as Entry.
 assert(Range:(p<13)%nat) by (destruct PC;subst p;lia).
 destruct(V293_OSTaskCreateExt_to_stack_hook P kstop BridgeGE BridgeLE (BridgeBodyEntry p)
 (fun _=>false) (false,nil,nil) (emp:osabst) (spec_done None)
 (V293_rdy_raw_cells (V293_create_bridge_extra 504%positive 509%positive 511%positive 512%positive 513%positive 514%positive
 Vnull BridgeBottom BridgeId BridgeSize BridgeExt (Vint32(Int.repr 9))) (V293_rdy_raw_cells BridgeFrame Atrue))
 enabled si ci 92%Z 101%Z 97%Z 109%Z 98%Z 501%positive 502%positive 503%positive 510%positive 700%positive p
 (Vint32(Int.repr 23)) 108%Z 900%Z 201%Z 202%Z 203%Z 204%Z 504%positive
 505%positive 506%positive 507%positive 508%positive 700 BridgeArg BridgeTop BridgeOpt
 (sseq (V293_TaskCreateExt_TCB_call 209%Z 901%Z 101%Z 108%Z 205%Z 206%Z 207%Z 208%Z 204%Z) (sskip None)))
 as (Mf&Exec&Owned&Decode&Stuck).
 all: try reflexivity.
 - exact Range.
 - unfold Int.max_unsigned,Int.modulus,Int.wordsize;cbn;lia.
 - repeat split;reflexivity.
 - repeat split;reflexivity.
 - rewrite <-V293_raw_cells_append. rewrite <-V293_raw_cells_append. exact Entry.
 - exists Mf. split;[exact Exec |apply Stuck;exact Missing].
Qed.
Print Assumptions BridgeLiteralReturnEntry.
Print Assumptions BridgeLiteralBodyEntry.
Print Assumptions BridgeActualAfterReturn.
Print Assumptions BridgeActualMissingStack.
