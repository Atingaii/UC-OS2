(* Independent finite nonzero entry, same-name caller, full actual call. *)
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewWitness.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.code.V293OSMemInit.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.code.V293OSMemClr.
Require Import CertiOS.certiucos.v293.proofs.V293MemInit.
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
Definition MemGE : env := set (set emp 31%Z (82%positive,V293_mem_table_type))
  34%Z (94%positive,Tptr V293_mem_type).
Definition MemCaller : env := set emp 41%Z (110%positive,Tint32).
Definition MemLE := V293_mem_call_locals 41%Z 42%Z
  90%positive 91%positive.
Definition MemHead := V293_mem_call_head 94%positive (Vptr (121%positive,Int.zero)).
Definition MemFrame : list V293_record_cell :=
  [((82%positive,100),Tint8,Vint32 (Int.repr 17));
   ((99%positive,0),Tint32,Vint32 (Int.repr 123));
   ((110%positive,0),Tint32,Vint32 (Int.repr 7))].
Fixpoint MemMem (cells : list V293_record_cell) : mem :=
  match cells with []=>emp | ((b,off),tp,v)::tail=>
    merge (V293_encoded_memory b off true (encode_val tp v)) (MemMem tail) end.
Definition MemTable := V293_encoded_memory 82%positive 0 true (repeat (Byte (Byte.repr 255)) 100).
Definition MemMemory := merge MemTable (MemMem (MemHead++MemFrame)).
Definition MemState M := V293_wstate MemGE MemCaller M.
Lemma MemConstantRange : forall n v byte ge le b off,
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

Ltac MemOutside :=
  unfold MemTable;cbn [MemHead MemFrame V293_mem_call_head MemMem app];
  repeat first [rewrite V293_encoded_memory_outside by
    (first [left;congruence | right;rewrite ?repeat_length;cbn [length encode_val inj_bytes encode_int];lia])
    | rewrite map_merge_semp by reflexivity];reflexivity.
Ltac MemApart b :=
  apply map_join_merge;apply map_disjoint;intros [other off];
  destruct (Pos.eq_dec other b);[subst other;right;left | left];
  repeat first [rewrite V293_encoded_memory_outside by (left;congruence)
    | rewrite map_merge_semp by reflexivity];reflexivity.
Lemma MemLiteralEntry : MemState MemMemory |= V293_rdy_raw_cells
  (V293_clr_bytes 82%positive 0 (repeat (Vint32 (Int.repr 255)) 100)++MemHead++MemFrame) Atrue.
Proof.
  unfold MemState,MemMemory. repeat rewrite V293_raw_cells_append.
  apply (V293_raw_cells_join (V293_clr_bytes 82%positive 0 (repeat (Vint32 (Int.repr 255)) 100))
    (V293_rdy_raw_cells MemHead (V293_rdy_raw_cells MemFrame Atrue))).
  eapply V293_wstate_star with (m1:=MemTable).
  - apply map_join_merge;apply map_disjoint;intros [b i].
    destruct (Pos.eq_dec b 82%positive) as [B|B].
    + subst b. destruct (Z_lt_dec i 100) as [I|I].
      * right;left;MemOutside.
      * left. unfold MemTable. apply V293_encoded_memory_outside. right;right. rewrite repeat_length;lia.
    + left. unfold MemTable. apply V293_encoded_memory_outside;left;exact B.
  - unfold MemTable;apply MemConstantRange;reflexivity.
  - cbn [MemHead MemFrame V293_mem_call_head MemMem app V293_rdy_raw_cells].
    eapply V293_wstate_star with (m1:=V293_encoded_memory 94%positive 0 true
      (encode_val (Tptr V293_mem_type) (Vptr (121%positive,Int.zero))));
      [MemApart 94%positive | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
    eapply V293_wstate_star with (m1:=V293_encoded_memory 82%positive 100 true
      (encode_val Tint8 (Vint32 (Int.repr 17))));
      [MemApart 82%positive | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
    eapply V293_wstate_star with (m1:=V293_encoded_memory 99%positive 0 true
      (encode_val Tint32 (Vint32 (Int.repr 123))));
      [MemApart 99%positive | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
    eapply V293_wstate_star with (m1:=V293_encoded_memory 110%positive 0 true
      (encode_val Tint32 (Vint32 (Int.repr 7)))).
    + apply map_join_merge;apply map_disjoint;intros;right;left;apply map_emp_get.
    + split;[apply V293_encoded_memory_mapsto | reflexivity].
    + exact I.
Qed.
Definition MemProgram (f : fid) : option function :=
  if Z.eq_dec f 100%Z then Some (V293_MemInit_function 101%Z 31%Z 34%Z 41%Z 42%Z)
  else if Z.eq_dec f 101%Z then Some (V293_MemClr_function 11%Z 12%Z) else None.
Lemma MemEnvironment : V293_mem_link_env MemGE MemLE 31%Z 34%Z 41%Z 42%Z
  82%positive 94%positive 90%positive 91%positive.
Proof. vm_compute;repeat split;reflexivity. Qed.
Lemma MemAbsentLocals : forall b, In b [90%positive;91%positive] -> fresh MemMemory b.
Proof.
  intros b Member a i E [v Read];subst a.
  assert (Absent : get MemMemory (b,i)=None).
  { destruct Member as [E|[E|E]];try contradiction;subst b;
      unfold MemMemory;MemOutside. }
  change (get MemMemory (b,i)=Some v) in Read.
  assert (Conflict : None=Some v) by (etransitivity;[symmetry;exact Absent|exact Read]).
  discriminate Conflict.
Qed.
Definition MemFinalCells := V293_mem_call_result 94%positive 82%positive MemFrame.
Lemma MemFinalCount : length MemFinalCells=89%nat.
Proof. reflexivity. Qed.
Lemma MemFinalValid : forall a tp v, In (a,tp,v) MemFinalCells -> rule_type_val_match tp v=true.
Proof.
  intros a tp v Member. vm_compute in Member.
  repeat (destruct Member as [E|Member];[inversion E;subst;reflexivity| ]);contradiction.
Qed.
Lemma MemAway : forall a tp v, In (a,tp,v) MemFinalCells ->
  ~In (fst a) (V293_mem_call_blocks 90%positive 91%positive).
Proof.
  intros a tp v Member. cbn [MemFinalCells V293_mem_call_result V293_mem_call_head
    V293_mem_linked V293_mem_untouched_cells V293_clr_bytes MemFrame repeat app] in Member.
  repeat (destruct Member as [E|Member];[inversion E;subst;cbn;intuition congruence| ]);contradiction.
Qed.
Theorem MemConcreteExecution : forall ks, exists Ms Mf,
  cstepstar MemProgram (curs (scall 100%Z nil),(kenil,ks))
    (MemGE,MemCaller,MemMemory) (curs (sskip None),(kenil,ks)) (MemGE,MemCaller,Mf) /\
  MemState Mf |= V293_rdy_raw_cells MemFinalCells Atrue /\
  (forall a tp v, In (a,tp,v) MemFinalCells -> load tp Mf a=Some v) /\
  (forall b tp k, In (b,tp) [(90%positive,Tptr V293_mem_type);(91%positive,Tint16)] ->
    (k<typelen tp)%nat -> get Mf (b,Z.of_nat k)=None) /\
  load Tint16 Ms (91%positive,0)=Some (Vint32 (Int.repr 4)) /\
  evalval (evar 41%Z) (MemGE,MemCaller,Mf)=Some (Vint32 (Int.repr 7)).
Proof.
  intro ks.
  destruct (V293_OS_MemInit_call_return (repeat (Vint32 (Int.repr 255)) 100)
    MemFrame MemProgram ks MemGE MemCaller MemMemory
    (fun _=>false) (false,nil,nil) emp (spec_done None)
    100%Z 101%Z 11%Z 12%Z 31%Z 34%Z 41%Z 42%Z
    82%positive 94%positive 90%positive 91%positive
    (Vptr (121%positive,Int.zero))
    ltac:(reflexivity) ltac:(reflexivity) ltac:(discriminate) ltac:(lia)
    ltac:(repeat constructor;cbn;intuition congruence)
    ltac:(apply MemAbsentLocals;cbn;auto) ltac:(apply MemAbsentLocals;cbn;auto)
    MemEnvironment ltac:(apply repeat_length) MemAway MemLiteralEntry)
    as (Ms&Mf&Exec&PreFree&Final&Preserve&Removed).
  assert (Reads : forall a tp v, In (a,tp,v) MemFinalCells -> load tp Mf a=Some v).
  { intros a tp v Member. change (load tp (getmem (MemState Mf)) a=Some v).
    eapply (V293_rdy_raw_load MemFinalCells Atrue);[exact Member | eapply MemFinalValid;exact Member | exact Final]. }
  exists Ms. exists Mf. split;[exact Exec | ]. split;[exact Final | ].
  split;[exact Reads | ]. split;[exact Removed | ]. split.
  - change (load Tint16 (getmem (V293_wstate MemGE MemLE Ms)) (91%positive,0)=Some (Vint32 (Int.repr 4))).
    eapply V293_rdy_raw_load;[ | reflexivity | exact PreFree].
    unfold V293_mem_link_final,V293_mem_link_locals.
    apply in_or_app;left;right;left;reflexivity.
  - cbn [evalval evaladdr get_smem get_genv get_lenv MemCaller].
    change (load Tint32 Mf (110%positive,0)=Some (Vint32 (Int.repr 7))).
    apply Reads;vm_compute;tauto.
Qed.
(* Final-interface controls, not independent internal-mechanism ablations. *)
Theorem MemReturnConnections : forall ks, exists Mf,
  cstepstar MemProgram (curs (scall 100%Z nil),(kenil,ks))
    (MemGE,MemCaller,MemMemory) (curs (sskip None),(kenil,ks)) (MemGE,MemCaller,Mf) /\
  load (Tptr Tvoid) Mf (82%positive,4)=Some (Vptr (82%positive,Int.repr 20)) /\
  load (Tptr Tvoid) Mf (82%positive,84)=Some Vnull /\
  load (Tptr V293_mem_type) Mf (94%positive,0)=Some (Vptr (82%positive,Int.zero)) /\
  load Tint32 Mf (99%positive,0)=Some (Vint32 (Int.repr 123)).
Proof.
  intro ks. destruct (MemConcreteExecution ks) as (Ms&Mf&Exec&Owned&Reads&Removed&Counter&Restored).
  exists Mf. split;[exact Exec | ]. split.
  - apply Reads;vm_compute;tauto.
  - split.
    + apply Reads;vm_compute;tauto.
    + split.
      * apply Reads;vm_compute;tauto.
      * apply Reads;vm_compute;tauto.
Qed.
Print Assumptions MemLiteralEntry.
Print Assumptions MemConcreteExecution.
Print Assumptions MemReturnConnections.
(* This explicit AST has no production statement helpers on the right-hand side. *)
Theorem MemLiteralAST : V293_MemInit_function 101%Z 31%Z 34%Z 41%Z 42%Z =
 (Tvoid,dnil,dcons 41%Z (Tptr V293_mem_type) (dcons 42%Z Tint16 dnil),
 sseq (sseq (scall 101%Z [
   (ecast (eaddrof (earrayelem (evar 31%Z) (econst32 Int.zero))) (Tptr Tint8));
   (ecast (econst32 (Int.repr 100)) Tint16)])
 (sseq (sassign (evar 42%Z) (ecast (econst32 Int.zero) Tint16))
 (sseq (swhile (ebinop olt (ecast (evar 42%Z) Tint32) (econst32 (Int.repr 4)))
 (sseq (sassign (evar 41%Z) (eaddrof (earrayelem (evar 31%Z) (evar 42%Z))))
 (sseq (sassign (efield (ederef (evar 41%Z)) 2%Z)
   (ecast (eaddrof (earrayelem (evar 31%Z)
     (ebinop oplus (ecast (evar 42%Z) Tint32) (econst32 Int.one)))) (Tptr Tvoid)))
 (sassign (evar 42%Z) (ecast (ebinop oplus (ecast (evar 42%Z) Tint32) (econst32 Int.one)) Tint16)))))
 (sseq (sassign (evar 41%Z) (eaddrof (earrayelem (evar 31%Z) (evar 42%Z))))
 (sseq (sassign (efield (ederef (evar 41%Z)) 2%Z) (ecast enull (Tptr Tvoid)))
 (sassign (evar 34%Z) (eaddrof (earrayelem (evar 31%Z) (econst32 Int.zero))))))))) sret).
Proof. reflexivity. Qed.

(* Only the external call site is neutralized; P, input and frame are fixed. *)
Theorem MemWithoutCall : forall ks, exists Mf,
  cstepstar MemProgram (curs (sskip None),(kenil,ks))
    (MemGE,MemCaller,MemMemory) (curs (sskip None),(kenil,ks)) (MemGE,MemCaller,Mf) /\
  load Tint8 Mf (82%positive,0)=Some (Vint32 (Int.repr 255)) /\
  load Tint8 Mf (82%positive,8)=Some (Vint32 (Int.repr 255)) /\
  load (Tptr V293_mem_type) Mf (94%positive,0)=Some (Vptr (121%positive,Int.zero)) /\
  load Tint32 Mf (99%positive,0)=Some (Vint32 (Int.repr 123)).
Proof.
  intro ks. exists MemMemory. split;[apply c_stepstar0 | ].
  set (entry:=V293_clr_bytes 82%positive 0 (repeat (Vint32 (Int.repr 255)) 100)++MemHead++MemFrame).
  assert (Load : forall a tp v, In (a,tp,v) entry -> rule_type_val_match tp v=true -> load tp MemMemory a=Some v).
  { intros a tp v Member Valid. change (load tp (getmem (MemState MemMemory)) a=Some v).
    eapply (V293_rdy_raw_load entry Atrue);[exact Member | exact Valid | exact MemLiteralEntry]. }
  split.
  - apply Load;[unfold entry;vm_compute;tauto | reflexivity].
  - split.
    + apply Load;[unfold entry;vm_compute;tauto | reflexivity].
    + split.
      * apply Load;[unfold entry;vm_compute;tauto | reflexivity].
      * apply Load;[unfold entry;vm_compute;tauto | reflexivity].
Qed.
Print Assumptions MemWithoutCall.
