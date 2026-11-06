(* Independent finite nonzero entry, same-name caller, full actual call. *)
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewWitness.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.code.V293OSInitEventList.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.code.V293OSMemClr.
Require Import CertiOS.certiucos.v293.proofs.V293InitEventList.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293InitTCBClear.
Require Import CertiOS.certiucos.v293.proofs.V293NullBytes.
Require Import CertiOS.certiucos.v293.proofs.V293MemClr.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewExec.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.basetac.join_lib.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope Z_scope.
Definition EventGE : env := set (set emp 31%Z (82%positive,V293_event_table_type))
  34%Z (94%positive,Tptr V293_event_type).
Definition EventCaller : env := set emp 41%Z (110%positive,Tint32).
Definition EventLE := V293_event_call_locals 41%Z 42%Z 43%Z 44%Z
  90%positive 91%positive 92%positive 93%positive.
Definition EventHead := V293_event_call_head 94%positive (Vptr (121%positive,Int.zero)).
Definition EventFrame : list V293_record_cell :=
  [((82%positive,32),Tint8,Vint32 (Int.repr 17));
   ((99%positive,0),Tint32,Vint32 (Int.repr 123));
   ((110%positive,0),Tint32,Vint32 (Int.repr 7))].
Fixpoint EventMem (cells : list V293_record_cell) : mem :=
  match cells with []=>emp | ((b,off),tp,v)::tail=>
    merge (V293_encoded_memory b off true (encode_val tp v)) (EventMem tail) end.
Definition EventTable := V293_encoded_memory 82%positive 0 true (repeat (Byte (Byte.repr 255)) 32).
Definition EventMemory := merge EventTable (EventMem (EventHead++EventFrame)).
Definition EventState M := V293_wstate EventGE EventCaller M.
Lemma EventConstantRange : forall n v byte ge le b off,
  encode_val Tint8 v=[byte] ->
  V293_wstate ge le (V293_encoded_memory b off true (repeat byte n)) |=
    V293_rdy_raw_cells (V293_clr_bytes b off (repeat v n)) Aemp.
Proof.
  induction n as [ | n IH];intros v byte ge le b off Encoding.
  - split;reflexivity.
  - cbn [repeat V293_clr_bytes V293_rdy_raw_cells].
    eapply V293_wstate_star;[apply V293_encoded_memory_join | | apply IH;exact Encoding].
    split;[ | reflexivity]. exists [byte]. split;[exact Encoding | ].
    exists (sig (b,off) (true,byte)). exists (emp:mem). split;[apply map_join_emp | ]. split;reflexivity.
Qed.

Ltac EventOutside :=
  unfold EventTable;cbn [EventHead EventFrame V293_event_call_head EventMem app];
  repeat first [rewrite V293_encoded_memory_outside by
    (first [left;congruence | right;rewrite ?repeat_length;cbn [length encode_val inj_bytes encode_int];lia])
    | rewrite map_merge_semp by reflexivity];reflexivity.
Ltac EventApart b :=
  apply map_join_merge;apply map_disjoint;intros [other off];
  destruct (Pos.eq_dec other b);[subst other;right;left | left];
  repeat first [rewrite V293_encoded_memory_outside by (left;congruence)
    | rewrite map_merge_semp by reflexivity];reflexivity.
Lemma EventLiteralEntry : EventState EventMemory |= V293_rdy_raw_cells
  (V293_clr_bytes 82%positive 0 (repeat (Vint32 (Int.repr 255)) 32)++EventHead++EventFrame) Atrue.
Proof.
  unfold EventState,EventMemory. repeat rewrite V293_raw_cells_append.
  apply (V293_raw_cells_join (V293_clr_bytes 82%positive 0 (repeat (Vint32 (Int.repr 255)) 32))
    (V293_rdy_raw_cells EventHead (V293_rdy_raw_cells EventFrame Atrue))).
  eapply V293_wstate_star with (m1:=EventTable).
  - apply map_join_merge;apply map_disjoint;intros [b i].
    destruct (Pos.eq_dec b 82%positive) as [B|B].
    + subst b. destruct (Z_lt_dec i 32) as [I|I].
      * right;left;EventOutside.
      * left. unfold EventTable. apply V293_encoded_memory_outside. right;right. rewrite repeat_length;lia.
    + left. unfold EventTable. apply V293_encoded_memory_outside;left;exact B.
  - unfold EventTable;apply EventConstantRange;reflexivity.
  - cbn [EventHead EventFrame V293_event_call_head EventMem app V293_rdy_raw_cells].
    eapply V293_wstate_star with (m1:=V293_encoded_memory 94%positive 0 true
      (encode_val (Tptr V293_event_type) (Vptr (121%positive,Int.zero))));
      [EventApart 94%positive | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
    eapply V293_wstate_star with (m1:=V293_encoded_memory 82%positive 32 true
      (encode_val Tint8 (Vint32 (Int.repr 17))));
      [EventApart 82%positive | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
    eapply V293_wstate_star with (m1:=V293_encoded_memory 99%positive 0 true
      (encode_val Tint32 (Vint32 (Int.repr 123))));
      [EventApart 99%positive | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
    eapply V293_wstate_star with (m1:=V293_encoded_memory 110%positive 0 true
      (encode_val Tint32 (Vint32 (Int.repr 7)))).
    + apply map_join_merge;apply map_disjoint;intros;right;left;apply map_emp_get.
    + split;[apply V293_encoded_memory_mapsto | reflexivity].
    + exact I.
Qed.
Definition EventProgram (f : fid) : option function :=
  if Z.eq_dec f 100%Z then Some (V293_InitEventList_function 101%Z 31%Z 34%Z 41%Z 42%Z 43%Z 44%Z)
  else if Z.eq_dec f 101%Z then Some (V293_MemClr_function 11%Z 12%Z) else None.
Lemma EventEnvironment : V293_event_link_env EventGE EventLE 31%Z 34%Z 41%Z 42%Z 43%Z 44%Z
  82%positive 94%positive 90%positive 91%positive 92%positive 93%positive.
Proof. vm_compute;repeat split;reflexivity. Qed.
Lemma EventAbsentLocals : forall b, In b [90%positive;91%positive;92%positive;93%positive] -> fresh EventMemory b.
Proof.
  intros b Member a i E [v Read];subst a.
  assert (Absent : get EventMemory (b,i)=None).
  { destruct Member as [E|[E|[E|[E|E]]]];try contradiction;subst b;
      unfold EventMemory;EventOutside. }
  change (get EventMemory (b,i)=Some v) in Read.
  assert (Conflict : None=Some v) by (etransitivity;[symmetry;exact Absent|exact Read]).
  discriminate Conflict.
Qed.
Definition EventFinalCells := V293_event_call_result 94%positive 82%positive EventFrame.
Lemma EventFinalCount : length EventFinalCells=30%nat.
Proof. reflexivity. Qed.
Lemma EventFinalValid : forall a tp v, In (a,tp,v) EventFinalCells -> rule_type_val_match tp v=true.
Proof.
  intros a tp v Member. vm_compute in Member.
  repeat (destruct Member as [E|Member];[inversion E;subst;reflexivity| ]);contradiction.
Qed.
Lemma EventAway : forall a tp v, In (a,tp,v) EventFinalCells ->
  ~In (fst a) (V293_event_call_blocks 90%positive 91%positive 92%positive 93%positive).
Proof.
  intros a tp v Member. cbn [EventFinalCells V293_event_call_result V293_event_call_head
    V293_event_linked V293_event_untouched_cells V293_clr_bytes EventFrame repeat app] in Member.
  repeat (destruct Member as [E|Member];[inversion E;subst;cbn;intuition congruence| ]);contradiction.
Qed.
Theorem EventConcreteExecution : forall ks, exists Ms Mf,
  cstepstar EventProgram (curs (scall 100%Z nil),(kenil,ks))
    (EventGE,EventCaller,EventMemory) (curs (sskip None),(kenil,ks)) (EventGE,EventCaller,Mf) /\
  EventState Mf |= V293_rdy_raw_cells EventFinalCells Atrue /\
  (forall a tp v, In (a,tp,v) EventFinalCells -> load tp Mf a=Some v) /\
  (forall b tp k, In (b,tp) [(90%positive,Tint16);(91%positive,Tint16);
    (92%positive,Tptr V293_event_type);(93%positive,Tptr V293_event_type)] ->
    (k<typelen tp)%nat -> get Mf (b,Z.of_nat k)=None) /\
  load Tint16 Ms (90%positive,0)=Some (Vint32 Int.one) /\
  evalval (evar 41%Z) (EventGE,EventCaller,Mf)=Some (Vint32 (Int.repr 7)).
Proof.
  intro ks.
  destruct (V293_OS_InitEventList_call_return (repeat (Vint32 (Int.repr 255)) 32)
    EventFrame EventProgram ks EventGE EventCaller EventMemory
    (fun _=>false) (false,nil,nil) emp (spec_done None)
    100%Z 101%Z 11%Z 12%Z 31%Z 34%Z 41%Z 42%Z 43%Z 44%Z
    82%positive 94%positive 90%positive 91%positive 92%positive 93%positive
    (Vptr (121%positive,Int.zero))
    ltac:(reflexivity) ltac:(reflexivity) ltac:(discriminate)
    ltac:(lia) ltac:(lia) ltac:(lia)
    ltac:(repeat constructor;cbn;intuition congruence)
    ltac:(apply EventAbsentLocals;cbn;auto) ltac:(apply EventAbsentLocals;cbn;auto)
    ltac:(apply EventAbsentLocals;cbn;auto) ltac:(apply EventAbsentLocals;cbn;auto)
    EventEnvironment ltac:(apply repeat_length) EventAway EventLiteralEntry)
    as (Ms&Mf&Exec&PreFree&Final&Preserve&Removed).
  assert (Reads : forall a tp v, In (a,tp,v) EventFinalCells -> load tp Mf a=Some v).
  { intros a tp v Member. change (load tp (getmem (EventState Mf)) a=Some v).
    eapply (V293_rdy_raw_load EventFinalCells Atrue);[exact Member | eapply EventFinalValid;exact Member | exact Final]. }
  exists Ms. exists Mf. split;[exact Exec | ]. split;[exact Final | ].
  split;[exact Reads | ]. split;[exact Removed | ]. split.
  - change (load Tint16 (getmem (V293_wstate EventGE EventLE Ms)) (90%positive,0)=Some (Vint32 Int.one)).
    eapply V293_rdy_raw_load;[ | reflexivity | exact PreFree].
    unfold V293_event_link_final,V293_event_link_locals. apply in_or_app;left;left;reflexivity.
  - cbn [evalval evaladdr get_smem get_genv get_lenv EventCaller].
    change (load Tint32 Mf (110%positive,0)=Some (Vint32 (Int.repr 7))).
    apply Reads;vm_compute;tauto.
Qed.
(* Four prospective negative controls target only final readback connections. *)
Theorem EventReturnConnections : forall ks, exists Mf,
  cstepstar EventProgram (curs (scall 100%Z nil),(kenil,ks))
    (EventGE,EventCaller,EventMemory) (curs (sskip None),(kenil,ks)) (EventGE,EventCaller,Mf) /\
  load (Tptr Tvoid) Mf (82%positive,4)=Some (Vptr (82%positive,Int.repr 16)) /\
  load (Tptr Tvoid) Mf (82%positive,20)=Some Vnull /\
  load (Tptr V293_event_type) Mf (94%positive,0)=Some (Vptr (82%positive,Int.zero)) /\
  load Tint32 Mf (99%positive,0)=Some (Vint32 (Int.repr 123)).
Proof.
  intro ks. destruct (EventConcreteExecution ks) as (Ms&Mf&Exec&Owned&Reads&Removed&Counter&Restored).
  exists Mf. split;[exact Exec | ]. split.
  - apply Reads;vm_compute;tauto.
  - split.
    + apply Reads;vm_compute;tauto.
    + split.
      * apply Reads;vm_compute;tauto.
      * apply Reads;vm_compute;tauto.
Qed.
Print Assumptions EventLiteralEntry.
Print Assumptions EventConcreteExecution.
Print Assumptions EventReturnConnections.

(* Literal manual frontend check, independent of production statement helpers. *)
Theorem EventLiteralAST : V293_InitEventList_function 101%Z 31%Z 34%Z 41%Z 42%Z 43%Z 44%Z =
 (Tvoid,dnil,dcons 41%Z Tint16 (dcons 42%Z Tint16 (dcons 43%Z (Tptr V293_event_type) (dcons 44%Z (Tptr V293_event_type) dnil))),
 (sseq (sseq (scall 101%Z [(ecast (eaddrof (earrayelem (evar 31%Z) (econst32 Int.zero))) (Tptr Tint8));(ecast (econst32 (Int.repr 32)) Tint16)])
 (sseq (sassign (evar 41%Z) (ecast (econst32 Int.zero) Tint16))
 (sseq (swhile (ebinop olt (ecast (evar 41%Z) Tint32) (econst32 Int.one))
 (sseq (sassign (evar 42%Z) (ecast (ebinop oplus (ecast (evar 41%Z) Tint32) (econst32 Int.one)) Tint16))
 (sseq (sassign (evar 43%Z) (eaddrof (earrayelem (evar 31%Z) (evar 41%Z))))
 (sseq (sassign (evar 44%Z) (eaddrof (earrayelem (evar 31%Z) (evar 42%Z))))
 (sseq (sassign (efield (ederef (evar 43%Z)) 1%Z) (ecast (econst32 Int.zero) Tint8))
 (sseq (sassign (efield (ederef (evar 43%Z)) 2%Z) (ecast (evar 44%Z) (Tptr Tvoid)))
 (sassign (evar 41%Z) (ecast (ebinop oplus (ecast (evar 41%Z) Tint32) (econst32 Int.one)) Tint16))))))))
 (sseq (sassign (evar 43%Z) (eaddrof (earrayelem (evar 31%Z) (evar 41%Z))))
 (sseq (sassign (efield (ederef (evar 43%Z)) 1%Z) (ecast (econst32 Int.zero) Tint8))
 (sseq (sassign (efield (ederef (evar 43%Z)) 2%Z) (ecast enull (Tptr Tvoid)))
 (sassign (evar 34%Z) (eaddrof (earrayelem (evar 31%Z) (econst32 Int.zero)))))))))) sret)).
Proof. reflexivity. Qed.
