(* Whole call: independently encoded finite entry, absent callee locals, nonempty shadowed caller. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.code.V293OSInitTCBList.
Require Import CertiOS.certiucos.v293.code.V293OSInitTCBCall.
Require Import CertiOS.certiucos.v293.proofs.V293InitTCBCall.
Require Import CertiOS.certiucos.v293.code.V293OSInitTCBClear.
Require Import CertiOS.certiucos.v293.code.V293OSMemClr.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.proofs.V293InitTCBList.
Require Import CertiOS.certiucos.v293.proofs.V293InitTCBClear.
Require Import CertiOS.certiucos.v293.proofs.V293MemClr.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293NullBytes.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewWitness.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope Z_scope.
Definition LinkGE : env := set (set (set (set emp
  31%Z (82%positive,Tarray V293_tcb_type 13))
  32%Z (84%positive,Tarray (Tptr V293_tcb_type) 13))
  33%Z (94%positive,Tptr V293_tcb_type)) 34%Z (95%positive,Tptr V293_tcb_type).
Definition LinkLE : env := set (set (set (set emp
  41%Z (90%positive,Tint8)) 42%Z (91%positive,Tint8))
  43%Z (92%positive,Tptr V293_tcb_type)) 44%Z (93%positive,Tptr V293_tcb_type).
Definition LinkTCB := V293_encoded_memory 82%positive 0 true (repeat Undef 728).
Definition LinkPrio := V293_encoded_memory 84%positive 0 true (repeat (Byte (Byte.repr 255)) 52).
Definition LinkLocals : list V293_record_cell :=
  [((94%positive,0),Tptr V293_tcb_type,Vptr (121%positive,Int.zero));
   ((95%positive,0),Tptr V293_tcb_type,Vptr (122%positive,Int.zero))].
Definition LinkFrame : list V293_record_cell :=
  [((82%positive,728),Tint8,Vint32 (Int.repr 17));
   ((84%positive,52),Tint8,Vint32 (Int.repr 29));
   ((99%positive,0),Tint32,Vint32 (Int.repr 123));
   ((110%positive,0),Tint32,Vint32 (Int.repr 7))].
Fixpoint LinkMem (cells : list V293_record_cell) : mem :=
  match cells with []=>emp | ((b,off),tp,v)::tail=>
    merge (V293_encoded_memory b off true (encode_val tp v)) (LinkMem tail) end.
Definition LinkMemory := merge LinkTCB (merge LinkPrio (LinkMem (LinkLocals++LinkFrame))).
Definition LinkCaller : env := set emp 41%Z (110%positive,Tint32).
Definition LinkState M := V293_wstate LinkGE LinkCaller M.

Lemma LinkConstantRange : forall n v byte ge le b off,
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
Ltac LinkOutside :=
  unfold LinkTCB,LinkPrio;
  cbn [LinkLocals LinkFrame LinkMem app];
  repeat rewrite map_merge_semp by reflexivity;
  repeat rewrite V293_encoded_memory_outside by
    (first [left;congruence | right;rewrite ?repeat_length;cbn [length encode_val inj_bytes encode_int];lia]);
  reflexivity.
Ltac LinkApart b :=
  apply map_join_merge;apply map_disjoint;intros [other off];
  destruct (Pos.eq_dec other b);[subst other;right;left | left];
  repeat rewrite map_merge_semp by reflexivity;
  repeat rewrite V293_encoded_memory_outside by (left;congruence);reflexivity.
Lemma LinkLiteralEntry : LinkState LinkMemory |= V293_rdy_raw_cells
  (V293_clr_bytes 82%positive 0 (repeat Vundef 728)++
   V293_clr_bytes 84%positive 0 (repeat (Vint32 (Int.repr 255)) 52)++LinkLocals++LinkFrame) Atrue.
Proof.
  unfold LinkState,LinkMemory. repeat rewrite V293_raw_cells_append.
  apply (V293_raw_cells_join (V293_clr_bytes 82%positive 0 (repeat Vundef 728))
    (V293_rdy_raw_cells (V293_clr_bytes 84%positive 0 (repeat (Vint32 (Int.repr 255)) 52))
      (V293_rdy_raw_cells LinkLocals (V293_rdy_raw_cells LinkFrame Atrue)))).
  eapply V293_wstate_star with (m1:=LinkTCB).
  - apply map_join_merge;apply map_disjoint;intros [b i].
    destruct (Pos.eq_dec b 82%positive) as [B|B].
    + subst b. destruct (Z_lt_dec i 728) as [I|I].
      * right;left;LinkOutside.
      * left. unfold LinkTCB. apply V293_encoded_memory_outside. right;right. rewrite repeat_length;lia.
    + left. unfold LinkTCB. apply V293_encoded_memory_outside;left;exact B.
  - unfold LinkTCB;apply LinkConstantRange;reflexivity.
  - apply (V293_raw_cells_join (V293_clr_bytes 84%positive 0 (repeat (Vint32 (Int.repr 255)) 52))
      (V293_rdy_raw_cells LinkLocals (V293_rdy_raw_cells LinkFrame Atrue))).
    eapply V293_wstate_star with (m1:=LinkPrio).
    + apply map_join_merge;apply map_disjoint;intros [b i].
      destruct (Pos.eq_dec b 84%positive) as [B|B].
      * subst b. destruct (Z_lt_dec i 52) as [I|I].
        -- right;left;LinkOutside.
        -- left. unfold LinkPrio. apply V293_encoded_memory_outside. right;right. rewrite repeat_length;lia.
      * left. unfold LinkPrio. apply V293_encoded_memory_outside;left;exact B.
    + unfold LinkPrio;apply LinkConstantRange;reflexivity.
    + cbn [LinkLocals LinkFrame LinkMem app V293_rdy_raw_cells].
      eapply V293_wstate_star with (m1:=V293_encoded_memory 94%positive 0 true (encode_val (Tptr V293_tcb_type) (Vptr (121%positive,Int.zero))));
        [LinkApart 94%positive | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
      eapply V293_wstate_star with (m1:=V293_encoded_memory 95%positive 0 true (encode_val (Tptr V293_tcb_type) (Vptr (122%positive,Int.zero))));
        [LinkApart 95%positive | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
      eapply V293_wstate_star with (m1:=V293_encoded_memory 82%positive 728 true (encode_val (Tint8) (Vint32 (Int.repr 17))));
        [LinkApart 82%positive | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
      eapply V293_wstate_star with (m1:=V293_encoded_memory 84%positive 52 true (encode_val (Tint8) (Vint32 (Int.repr 29))));
        [LinkApart 84%positive | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
      eapply V293_wstate_star with (m1:=V293_encoded_memory 99%positive 0 true (encode_val (Tint32) (Vint32 (Int.repr 123))));
        [LinkApart 99%positive | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
      eapply V293_wstate_star with (m1:=V293_encoded_memory 110%positive 0 true (encode_val Tint32 (Vint32 (Int.repr 7))));
        [LinkApart 110%positive | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
      exact I.
Qed.
Definition LinkProgram f :=
  if Z.eq_dec f 100%Z then Some (V293_InitTCBList_function 101%Z 31%Z 32%Z 33%Z 34%Z 41%Z 42%Z 43%Z 44%Z)
  else if Z.eq_dec f 101%Z then Some (V293_MemClr_function 11%Z 12%Z) else None.
Lemma LinkEnvironment : V293_tcb_link_env LinkGE LinkLE 31%Z 33%Z 34%Z 41%Z 42%Z 43%Z 44%Z
  82%positive 94%positive 95%positive 90%positive 91%positive 92%positive 93%positive.
Proof. vm_compute;repeat split;reflexivity. Qed.
Lemma LinkAbsentLocals : forall b, In b [90%positive;91%positive;92%positive;93%positive] -> fresh LinkMemory b.
Proof.
  intros b Member a i E [v Read];subst a.
  assert (Absent : get LinkMemory (b,i)=None).
  { destruct Member as [E|[E|[E|[E|E]]]];try contradiction;subst b;
      unfold LinkMemory;LinkOutside. }
  change (get LinkMemory (b,i)=Some v) in Read.
  assert (Conflict : None=Some v) by (etransitivity;[symmetry;exact Absent|exact Read]).
  discriminate Conflict.
Qed.
Lemma LinkLiteralAST : V293_InitTCBList_function 101%Z 31%Z 32%Z 33%Z 34%Z 41%Z 42%Z 43%Z 44%Z =
(Tvoid,dnil,dcons 41%Z Tint8 (dcons 42%Z Tint8 (dcons 43%Z (Tptr V293_tcb_type) (dcons 44%Z (Tptr V293_tcb_type) dnil))), sseq
(sseq (sseq (scall 101%Z [(ecast (eaddrof (earrayelem (evar 31%Z) (econst32 Int.zero))) (Tptr Tint8));(ecast (econst32 (Int.repr 728)) Tint16)]) (scall 101%Z [(ecast (eaddrof (earrayelem (evar 32%Z) (econst32 Int.zero))) (Tptr Tint8));(ecast (econst32 (Int.repr 52)) Tint16)])) (sseq (sassign (evar 41%Z) (ecast (econst32 Int.zero) Tint8)) (sseq (swhile (ebinop olt (ecast (evar 41%Z) Tint32) (econst32 (Int.repr 12))) (sseq (sassign (evar 42%Z) (ecast (ebinop oplus (ecast (evar 41%Z) Tint32) (econst32 Int.one)) Tint8)) (sseq (sassign (evar 43%Z) (eaddrof (earrayelem (evar 31%Z) (evar 41%Z)))) (sseq (sassign (evar 44%Z) (eaddrof (earrayelem (evar 31%Z) (evar 42%Z)))) (sseq (sassign (efield (ederef (evar 43%Z)) 7%Z) (evar 44%Z)) (sassign (evar 41%Z) (ecast (ebinop oplus (ecast (evar 41%Z) Tint32) (econst32 Int.one)) Tint8))))))) (sseq (sassign (evar 43%Z) (eaddrof (earrayelem (evar 31%Z) (evar 41%Z)))) (sseq (sassign (efield (ederef (evar 43%Z)) 7%Z) (ecast enull (Tptr V293_tcb_type))) (sseq (sassign (evar 33%Z) (ecast enull (Tptr V293_tcb_type))) (sassign (evar 34%Z) (eaddrof (earrayelem (evar 31%Z) (econst32 Int.zero)))))))))) sret).
Proof. reflexivity. Qed.
Definition LinkFinalCells := V293_tcb_call_result 94%positive 95%positive 82%positive 84%positive LinkFrame.
Lemma LinkAway : forall a tp v, In (a,tp,v) LinkFinalCells ->
  ~In (fst a) (V293_tcb_call_blocks 90%positive 91%positive 92%positive 93%positive).
Proof.
  intros a tp v Member. unfold LinkFinalCells,V293_tcb_call_result in Member.
  repeat rewrite in_app_iff in Member. destruct Member as [H|[H|[H|[H|H]]]].
  - cbn [V293_tcb_call_heads] in H. destruct H as [E|[E|E]];try contradiction;inversion E;subst;cbn;intuition congruence.
  - unfold V293_tcb_linked_next in H. apply in_app_iff in H. destruct H as [H|[E|E]];try contradiction.
    + apply in_map_iff in H. destruct H as [i [E Hi]]. inversion E;subst;cbn;intuition congruence.
    + inversion E;subst;cbn;intuition congruence.
  - assert (fst a=82%positive).
    { clear -H. remember 13%nat as n in H. remember 0%Z as off in H. clear Heqn Heqoff. revert off H.
      induction n;intros off H;cbn [V293_tcb_untouched_cells] in H;[contradiction| ].
      repeat rewrite in_app_iff in H. destruct H as [H|[H|H]];
        [eapply V293_clr_bytes_blocks;exact H|eapply V293_clr_bytes_blocks;exact H|eapply IHn;exact H]. }
    rewrite H0;cbn;intuition congruence.
  - unfold V293_null_pointer_cells in H.
    repeat (destruct H as [E|H];[inversion E;subst;cbn;intuition congruence| ]);contradiction.
  - cbn [LinkFrame] in H. destruct H as [E|[E|[E|[E|E]]]];try contradiction;inversion E;subst;cbn;intuition congruence.
Qed.
Ltac LinkRead H :=
  lazymatch goal with |- load ?tp ?M ?a=Some ?v =>
    change (load tp (getmem (LinkState M)) a=Some v);
    eapply (V293_rdy_raw_load LinkFinalCells Atrue);[ | reflexivity | exact H]
  end.
Theorem LinkConcreteExecution : forall ks, exists Ms Mf,
  cstepstar LinkProgram (curs (scall 100%Z nil),(kenil,ks))
    (LinkGE,LinkCaller,LinkMemory) (curs (sskip None),(kenil,ks)) (LinkGE,LinkCaller,Mf) /\
  LinkState Mf |= V293_rdy_raw_cells LinkFinalCells Atrue /\
  (forall i, (i<12)%nat -> load (Tcom_ptr 410) Mf (82%positive,56*Z.of_nat i+20)=
    Some (Vptr (82%positive,Int.repr (56*Z.of_nat (S i))))) /\
  load (Tcom_ptr 410) Mf (82%positive,692)=Some Vnull /\
  load (Tptr V293_tcb_type) Mf (94%positive,0)=Some Vnull /\
  load (Tptr V293_tcb_type) Mf (95%positive,0)=Some (Vptr (82%positive,Int.zero)) /\
  (forall p, (p<13)%nat -> load (Tptr V293_tcb_type) Mf (84%positive,4*Z.of_nat p)=Some Vnull) /\
  load Tint8 Mf (82%positive,0)=Some (Vint32 Int.zero) /\
  load Tint8 Mf (82%positive,728)=Some (Vint32 (Int.repr 17)) /\
  load Tint8 Mf (84%positive,52)=Some (Vint32 (Int.repr 29)) /\
  load Tint32 Mf (99%positive,0)=Some (Vint32 (Int.repr 123)) /\
  load Tint32 Mf (110%positive,0)=Some (Vint32 (Int.repr 7)) /\
  (forall b tp k, In (b,tp) [(90%positive,Tint8);(91%positive,Tint8);(92%positive,Tptr V293_tcb_type);(93%positive,Tptr V293_tcb_type)] ->
    (k<typelen tp)%nat -> get Mf (b,Z.of_nat k)=None) /\
  load Tint8 Ms (90%positive,0)=Some (Vint32 (Int.repr 12)) /\
  evalval (evar 41%Z) (LinkGE,LinkCaller,Mf)=Some (Vint32 (Int.repr 7)).
Proof.
  intro ks.
  destruct (V293_OS_InitTCBList_call_return (repeat Vundef 728)
    (repeat (Vint32 (Int.repr 255)) 52) LinkFrame LinkProgram ks LinkGE LinkCaller LinkMemory
    (fun _=>false) (false,nil,nil) emp (spec_done None)
    100%Z 101%Z 11%Z 12%Z 31%Z 32%Z 33%Z 34%Z 41%Z 42%Z 43%Z 44%Z
    82%positive 84%positive 94%positive 95%positive 90%positive 91%positive 92%positive 93%positive
    (Vptr (121%positive,Int.zero)) (Vptr (122%positive,Int.zero))
    ltac:(reflexivity) ltac:(reflexivity) ltac:(discriminate)
    ltac:(lia) ltac:(lia) ltac:(lia)
    ltac:(repeat constructor;cbn;intuition congruence)
    ltac:(apply LinkAbsentLocals;cbn;auto) ltac:(apply LinkAbsentLocals;cbn;auto)
    ltac:(apply LinkAbsentLocals;cbn;auto) ltac:(apply LinkAbsentLocals;cbn;auto)
    LinkEnvironment ltac:(reflexivity) ltac:(reflexivity)
    ltac:(apply repeat_length) ltac:(apply repeat_length) LinkAway LinkLiteralEntry)
    as (Ms&Mf&Exec&PreFree&Final&Preserve&Removed).
  exists Ms. exists Mf. split;[exact Exec| ]. split;[exact Final| ].
  split.
  - intros i Small. LinkRead Final. unfold LinkFinalCells,V293_tcb_call_result.
    apply in_or_app;right. apply in_or_app;left.
    unfold V293_tcb_linked_next. apply in_or_app;left.
    apply in_map_iff. exists i. split;[reflexivity|apply in_seq;lia].
  - split.
    + LinkRead Final. unfold LinkFinalCells,V293_tcb_call_result.
      apply in_or_app;right. apply in_or_app;left.
      unfold V293_tcb_linked_next. apply in_or_app;right;left;reflexivity.
    + split.
      * LinkRead Final. unfold LinkFinalCells,V293_tcb_call_result. apply in_or_app;left;left;reflexivity.
      * split.
        -- LinkRead Final. unfold LinkFinalCells,V293_tcb_call_result. apply in_or_app;left;right;left;reflexivity.
        -- split.
           ++ intros p Small. LinkRead Final. unfold LinkFinalCells,V293_tcb_call_result.
              apply in_or_app;right. apply in_or_app;right. apply in_or_app;right. apply in_or_app;left.
              replace (4*Z.of_nat p) with (0+4*Z.of_nat p) by lia.
              apply V293_null_pointer_member;exact Small.
           ++ split.
              ** LinkRead Final. unfold LinkFinalCells,V293_tcb_call_result.
                 apply in_or_app;right. apply in_or_app;right. apply in_or_app;left.
                 cbn [V293_tcb_untouched_cells]. apply in_or_app;left;left;reflexivity.
              ** assert (FrameRead : forall a tp v, In (a,tp,v) LinkFrame -> rule_type_val_match tp v=true -> load tp Mf a=Some v).
                 { intros a tp v Member Valid. change (load tp (getmem (LinkState Mf)) a=Some v).
                   eapply (V293_rdy_raw_load LinkFinalCells Atrue);[ | exact Valid|exact Final].
                   unfold LinkFinalCells,V293_tcb_call_result. do 4 (apply in_or_app;right). exact Member. }
                 repeat split.
                 --- apply FrameRead;[left;reflexivity|reflexivity].
                 --- apply FrameRead;[right;left;reflexivity|reflexivity].
                 --- apply FrameRead;[right;right;left;reflexivity|reflexivity].
                 --- apply FrameRead;[right;right;right;left;reflexivity|reflexivity].
                 --- exact Removed.
                 --- change (load Tint8 (getmem (V293_wstate LinkGE LinkLE Ms)) (90%positive,0)=Some (Vint32 (Int.repr 12))).
                     eapply V293_rdy_raw_load;[ | reflexivity|exact PreFree].
                     unfold V293_tcb_link_final,V293_tcb_link_locals. apply in_or_app;left;left;reflexivity.
                 --- cbn [evalval evaladdr get_smem get_genv get_lenv LinkCaller].
                     change (load Tint32 Mf (110%positive,0)=Some (Vint32 (Int.repr 7))).
                     apply FrameRead;[right;right;right;left;reflexivity|reflexivity].
Qed.
Print Assumptions LinkLiteralEntry.
Print Assumptions LinkLiteralAST.
Print Assumptions LinkConcreteExecution.

(* Controls alter only one named final conclusion; all proof bodies stay fixed. *)
Theorem LinkReturnConnections : forall ks, exists Mf,
  cstepstar LinkProgram (curs (scall 100%Z nil),(kenil,ks))
    (LinkGE,LinkCaller,LinkMemory) (curs (sskip None),(kenil,ks)) (LinkGE,LinkCaller,Mf) /\
  get Mf (90%positive,0)=None /\
  load (Tcom_ptr 410) Mf (82%positive,692)=Some Vnull /\
  load Tint32 Mf (99%positive,0)=Some (Vint32 (Int.repr 123)).
Proof.
  intro ks. destruct (LinkConcreteExecution ks) as (Ms&Mf&Exec&Owned&Links&Last&Head&Free&Prios&B0&Gt&Gp&Frame&Caller&Removed&Counter&Restored).
  exists Mf. split.
  - exact Exec.
  - split.
    + exact (Removed 90%positive Tint8 0%nat ltac:(left;reflexivity) ltac:(cbn;lia)).
    + split;[exact Last|exact Frame].
Qed.
Print Assumptions LinkReturnConnections.
