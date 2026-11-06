(* Finite independently encoded entry and literal source AST; no audit probe imports. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.code.V293OSInitTCBList.
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
  [((90%positive,0),Tint8,Vundef);((91%positive,0),Tint8,Vint32 (Int.repr 99));
   ((92%positive,0),Tptr V293_tcb_type,Vundef);((93%positive,0),Tptr V293_tcb_type,Vnull);
   ((94%positive,0),Tptr V293_tcb_type,Vptr (121%positive,Int.zero));
   ((95%positive,0),Tptr V293_tcb_type,Vptr (122%positive,Int.zero))].
Definition LinkFrame : list V293_record_cell :=
  [((82%positive,728),Tint8,Vint32 (Int.repr 17));
   ((84%positive,52),Tint8,Vint32 (Int.repr 29));
   ((99%positive,0),Tint32,Vint32 (Int.repr 123))].
Fixpoint LinkMem (cells : list V293_record_cell) : mem :=
  match cells with []=>emp | ((b,off),tp,v)::tail=>
    merge (V293_encoded_memory b off true (encode_val tp v)) (LinkMem tail) end.
Definition LinkMemory := merge LinkTCB (merge LinkPrio (LinkMem (LinkLocals++LinkFrame))).
Definition LinkState M := V293_wstate LinkGE LinkLE M.

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
      eapply V293_wstate_star with (m1:=V293_encoded_memory 90%positive 0 true (encode_val (Tint8) (Vundef)));
        [LinkApart 90%positive | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
      eapply V293_wstate_star with (m1:=V293_encoded_memory 91%positive 0 true (encode_val (Tint8) (Vint32 (Int.repr 99))));
        [LinkApart 91%positive | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
      eapply V293_wstate_star with (m1:=V293_encoded_memory 92%positive 0 true (encode_val (Tptr V293_tcb_type) (Vundef)));
        [LinkApart 92%positive | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
      eapply V293_wstate_star with (m1:=V293_encoded_memory 93%positive 0 true (encode_val (Tptr V293_tcb_type) (Vnull)));
        [LinkApart 93%positive | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
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
      exact I.
Qed.
Definition LinkProgram f := if Z.eq_dec f 101%Z then Some (V293_MemClr_function 11%Z 12%Z) else None.
Lemma LinkProgramLookup : LinkProgram 101%Z=Some (V293_MemClr_function 11%Z 12%Z).
Proof. reflexivity. Qed.
Lemma LinkEnvironment : V293_tcb_link_env LinkGE LinkLE 31%Z 33%Z 34%Z 41%Z 42%Z 43%Z 44%Z
  82%positive 94%positive 95%positive 90%positive 91%positive 92%positive 93%positive.
Proof. vm_compute;repeat split;reflexivity. Qed.
Lemma LinkLiteralAST : V293_init_tcb_body 101%Z 31%Z 32%Z 33%Z 34%Z 41%Z 42%Z 43%Z 44%Z =
(sseq (sseq (scall 101%Z [(ecast (eaddrof (earrayelem (evar 31%Z) (econst32 Int.zero))) (Tptr Tint8));(ecast (econst32 (Int.repr 728)) Tint16)]) (scall 101%Z [(ecast (eaddrof (earrayelem (evar 32%Z) (econst32 Int.zero))) (Tptr Tint8));(ecast (econst32 (Int.repr 52)) Tint16)])) (sseq (sassign (evar 41%Z) (ecast (econst32 Int.zero) Tint8)) (sseq (swhile (ebinop olt (ecast (evar 41%Z) Tint32) (econst32 (Int.repr 12))) (sseq (sassign (evar 42%Z) (ecast (ebinop oplus (ecast (evar 41%Z) Tint32) (econst32 Int.one)) Tint8)) (sseq (sassign (evar 43%Z) (eaddrof (earrayelem (evar 31%Z) (evar 41%Z)))) (sseq (sassign (evar 44%Z) (eaddrof (earrayelem (evar 31%Z) (evar 42%Z)))) (sseq (sassign (efield (ederef (evar 43%Z)) 7%Z) (evar 44%Z)) (sassign (evar 41%Z) (ecast (ebinop oplus (ecast (evar 41%Z) Tint32) (econst32 Int.one)) Tint8))))))) (sseq (sassign (evar 43%Z) (eaddrof (earrayelem (evar 31%Z) (evar 41%Z)))) (sseq (sassign (efield (ederef (evar 43%Z)) 7%Z) (ecast enull (Tptr V293_tcb_type))) (sseq (sassign (evar 33%Z) (ecast enull (Tptr V293_tcb_type))) (sassign (evar 34%Z) (eaddrof (earrayelem (evar 31%Z) (econst32 Int.zero)))))))))).
Proof. reflexivity. Qed.
Definition LinkFinalCells :=
  V293_tcb_link_final 90%positive 91%positive 92%positive 93%positive 94%positive 95%positive 82%positive++
  V293_tcb_untouched_cells 82%positive 0 13++V293_null_pointer_cells 84%positive 0 13++LinkFrame.
Ltac LinkRead H :=
  lazymatch goal with |- load ?tp ?M ?a=Some ?v =>
    change (load tp (getmem (LinkState M)) a=Some v);
    eapply (V293_rdy_raw_load LinkFinalCells Atrue);[ | reflexivity | exact H]
  end.
Theorem LinkConcreteExecution : forall ks, exists Mf,
  cstepstar LinkProgram
    (curs (V293_init_tcb_body 101%Z 31%Z 32%Z 33%Z 34%Z 41%Z 42%Z 43%Z 44%Z),(kenil,ks))
    (LinkGE,LinkLE,LinkMemory) (curs (sskip None),(kenil,ks)) (LinkGE,LinkLE,Mf) /\
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
  load Tint32 Mf (99%positive,0)=Some (Vint32 (Int.repr 123)).
Proof.
  intro ks.
  destruct (V293_OS_InitTCBList_body_execution (repeat Vundef 728)
    (repeat (Vint32 (Int.repr 255)) 52) LinkFrame LinkProgram ks LinkGE LinkLE LinkMemory
    (fun _=>false) (false,nil,nil) emp (spec_done None)
    101%Z 11%Z 12%Z 31%Z 32%Z 33%Z 34%Z 41%Z 42%Z 43%Z 44%Z
    82%positive 84%positive 94%positive 95%positive 90%positive 91%positive 92%positive 93%positive
    Vundef (Vint32 (Int.repr 99)) Vundef Vnull (Vptr (121%positive,Int.zero)) (Vptr (122%positive,Int.zero))
    LinkProgramLookup ltac:(discriminate) LinkEnvironment ltac:(reflexivity) ltac:(reflexivity)
    ltac:(apply repeat_length) ltac:(apply repeat_length) LinkLiteralEntry) as (Mf&Exec&Owned).
  assert (Final : LinkState Mf |= V293_rdy_raw_cells LinkFinalCells Atrue).
  { unfold LinkFinalCells. repeat rewrite V293_raw_cells_append. exact Owned. }
  exists Mf. split;[exact Exec | ]. split;[exact Final | ].
  split.
  - intros i Small. LinkRead Final.
    unfold LinkFinalCells. apply in_or_app;left.
    unfold V293_tcb_link_final. apply in_or_app;right.
    unfold V293_tcb_linked_next. apply in_or_app;left.
    apply in_map_iff. exists i. split;[reflexivity | apply in_seq;lia].
  - split.
    + LinkRead Final. unfold LinkFinalCells. apply in_or_app;left.
      unfold V293_tcb_link_final. apply in_or_app;right.
      unfold V293_tcb_linked_next. apply in_or_app;right;left;reflexivity.
    + split.
      * LinkRead Final. unfold LinkFinalCells. apply in_or_app;left.
        unfold V293_tcb_link_final. apply in_or_app;left. cbn [V293_tcb_link_locals]. do 4 right;left;reflexivity.
      * split.
        -- LinkRead Final. unfold LinkFinalCells. apply in_or_app;left.
           unfold V293_tcb_link_final. apply in_or_app;left. cbn [V293_tcb_link_locals]. do 5 right;left;reflexivity.
        -- split.
           ++ intros p Small. LinkRead Final. unfold LinkFinalCells. apply in_or_app;right.
              apply in_or_app;right. apply in_or_app;left.
              replace (4*Z.of_nat p) with (0+4*Z.of_nat p) by lia.
              apply V293_null_pointer_member;exact Small.
           ++ split.
              ** LinkRead Final. unfold LinkFinalCells. apply in_or_app;right.
                 apply in_or_app;left. cbn [V293_tcb_untouched_cells]. apply in_or_app;left;left;reflexivity.
              ** split.
                 --- LinkRead Final. unfold LinkFinalCells. apply in_or_app;right.
                     apply in_or_app;right. apply in_or_app;right. left;reflexivity.
                 --- split.
                     +++ LinkRead Final. unfold LinkFinalCells. apply in_or_app;right.
                         apply in_or_app;right. apply in_or_app;right. right;left;reflexivity.
                     +++ LinkRead Final. unfold LinkFinalCells. apply in_or_app;right.
                         apply in_or_app;right. apply in_or_app;right. right;right;left;reflexivity.
Qed.
Print Assumptions LinkLiteralEntry.
Print Assumptions LinkLiteralAST.
Print Assumptions LinkConcreteExecution.

(* Four separately named final connections, on the SAME actual final Mf. *)
Theorem LinkMiddleAndEnds : forall ks, exists Mf,
  cstepstar LinkProgram
    (curs (V293_init_tcb_body 101%Z 31%Z 32%Z 33%Z 34%Z 41%Z 42%Z 43%Z 44%Z),(kenil,ks))
    (LinkGE,LinkLE,LinkMemory) (curs (sskip None),(kenil,ks)) (LinkGE,LinkLE,Mf) /\
  load (Tcom_ptr 410) Mf (82%positive,356)=Some (Vptr (82%positive,Int.repr 392)) /\
  load (Tcom_ptr 410) Mf (82%positive,692)=Some Vnull /\
  load (Tptr V293_tcb_type) Mf (95%positive,0)=Some (Vptr (82%positive,Int.zero)) /\
  load Tint32 Mf (99%positive,0)=Some (Vint32 (Int.repr 123)).
Proof.
  intro ks. destruct (LinkConcreteExecution ks) as (Mf&Exec&Owned&Links&Last&Head&Free&Prios&B0&Gt&Gp&Frame).
  exists Mf. split;[exact Exec | ]. split.
  - exact (Links 6%nat ltac:(lia)).
  - split;[exact Last | ]. split;[exact Free | exact Frame].
Qed.
Print Assumptions LinkMiddleAndEnds.
