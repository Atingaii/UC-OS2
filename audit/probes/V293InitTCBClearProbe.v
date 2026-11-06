(* Independent finite 780-byte entry, literal two-call source AST. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.code.V293OSMemClr.
Require Import CertiOS.certiucos.v293.code.V293OSInitTCBClear.
Require Import CertiOS.certiucos.v293.proofs.V293InitTCBClear.
Require Import CertiOS.certiucos.v293.proofs.V293MemClr.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewWitness.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope Z_scope.

Definition InitGE : env := set (set emp 31%Z (82%positive,Tarray V293_tcb_type 13))
  32%Z (84%positive,Tarray (Tptr V293_tcb_type) 13).
Definition InitTCB : mem := V293_encoded_memory 82%positive 0 true (repeat Undef 728).
Definition InitPrio : mem := V293_encoded_memory 84%positive 0 true (repeat (Byte (Byte.repr 255)) 52).
Definition InitGuardT : mem := V293_encoded_memory 82%positive 728 true (encode_val Tint8 (Vint32 (Int.repr 17))).
Definition InitGuardP : mem := V293_encoded_memory 84%positive 52 true (encode_val Tint8 (Vint32 (Int.repr 29))).
Definition InitExtra : mem := V293_encoded_memory 99%positive 0 true (encode_val Tint32 (Vint32 (Int.repr 123))).
Definition InitFrame : list V293_record_cell :=
  [((82%positive,728),Tint8,Vint32 (Int.repr 17));
   ((84%positive,52),Tint8,Vint32 (Int.repr 29));
   ((99%positive,0),Tint32,Vint32 (Int.repr 123))].
Definition InitMemory := merge InitTCB (merge InitPrio (merge InitGuardT (merge InitGuardP InitExtra))).

Lemma InitConstantRange : forall n v byte ge le b off,
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
Ltac InitOutside :=
  unfold InitTCB,InitPrio,InitGuardT,InitGuardP,InitExtra;
  repeat rewrite map_merge_semp by reflexivity;
  repeat rewrite V293_encoded_memory_outside by
    (first [left;congruence | right;rewrite ?repeat_length;cbn [length encode_val inj_bytes encode_int];lia]);
  reflexivity.
Lemma InitLiteralEntry : V293_wstate InitGE emp InitMemory |=
  V293_rdy_raw_cells
    (V293_clr_bytes 82%positive 0 (repeat Vundef 728)++
     V293_clr_bytes 84%positive 0 (repeat (Vint32 (Int.repr 255)) 52)++InitFrame) Atrue.
Proof.
  unfold InitMemory. repeat rewrite V293_raw_cells_append.
  apply (V293_raw_cells_join (V293_clr_bytes 82%positive 0 (repeat Vundef 728))
    (V293_rdy_raw_cells (V293_clr_bytes 84%positive 0 (repeat (Vint32 (Int.repr 255)) 52))
      (V293_rdy_raw_cells InitFrame Atrue))).
  eapply V293_wstate_star with (m1:=InitTCB).
  - apply map_join_merge. apply map_disjoint. intros [b i].
    destruct (Pos.eq_dec b 82%positive) as [B|B].
    + subst b. destruct (Z_lt_dec i 728) as [I|I].
      * right;left;InitOutside.
      * left. unfold InitTCB. apply V293_encoded_memory_outside. right;right. rewrite repeat_length;lia.
    + left. unfold InitTCB. apply V293_encoded_memory_outside;left;exact B.
  - unfold InitTCB. apply InitConstantRange;reflexivity.
  - apply (V293_raw_cells_join (V293_clr_bytes 84%positive 0 (repeat (Vint32 (Int.repr 255)) 52))
      (V293_rdy_raw_cells InitFrame Atrue)).
    eapply V293_wstate_star with (m1:=InitPrio).
    + apply map_join_merge. apply map_disjoint. intros [b i].
      destruct (Pos.eq_dec b 84%positive) as [B|B].
      * subst b. destruct (Z_lt_dec i 52) as [I|I].
        -- right;left;InitOutside.
        -- left. unfold InitPrio. apply V293_encoded_memory_outside. right;right. rewrite repeat_length;lia.
      * left. unfold InitPrio. apply V293_encoded_memory_outside;left;exact B.
    + unfold InitPrio. apply InitConstantRange;reflexivity.
    + unfold InitFrame. cbn [V293_rdy_raw_cells].
      eapply V293_wstate_star with (m1:=InitGuardT).
      * apply map_join_merge. apply map_disjoint. intros [b i].
        destruct (Pos.eq_dec b 82%positive) as [B|B];[subst b;right;left;InitOutside | left;InitOutside].
      * unfold InitGuardT. split;[apply V293_encoded_memory_mapsto | reflexivity].
      * eapply V293_wstate_star with (m1:=InitGuardP).
        -- apply map_join_merge. apply map_disjoint. intros [b i].
           destruct (Pos.eq_dec b 84%positive) as [B|B];[subst b;right;left;InitOutside | left;InitOutside].
        -- unfold InitGuardP. split;[apply V293_encoded_memory_mapsto | reflexivity].
        -- eapply V293_wstate_star with (m2:=(emp:mem)).
           ++ apply map_join_emp.
           ++ unfold InitExtra. split;[apply V293_encoded_memory_mapsto | reflexivity].
           ++ exact I.
Qed.

Definition InitProgram f := if Z.eq_dec f 101%Z then Some (V293_MemClr_function 11%Z 12%Z) else None.
Lemma InitProgramLookup : InitProgram 101%Z=Some (V293_MemClr_function 11%Z 12%Z).
Proof. reflexivity. Qed.
Lemma InitLiteralAST : V293_init_tcb_clear 101%Z 31%Z 32%Z =
  sseq
    (scall 101%Z [ecast (eaddrof (earrayelem (evar 31%Z) (econst32 Int.zero))) (Tptr Tint8);
      ecast (econst32 (Int.repr 728)) Tint16])
    (scall 101%Z [ecast (eaddrof (earrayelem (evar 32%Z) (econst32 Int.zero))) (Tptr Tint8);
      ecast (econst32 (Int.repr 52)) Tint16]).
Proof. reflexivity. Qed.

Lemma InitByteMember : forall n p b off v,
  (p<n)%nat -> In ((b,off+Z.of_nat p),Tint8,v) (V293_clr_bytes b off (repeat v n)).
Proof.
  induction n as [ | n IH];intros p b off v Small;[lia | ].
  destruct p as [ | p];cbn [repeat V293_clr_bytes].
  - replace (off+Z.of_nat 0) with off by (cbn;lia). left;reflexivity.
  - right. replace (off+Z.of_nat (S p)) with ((off+1)+Z.of_nat p) by lia.
    apply IH;lia.
Qed.

Theorem InitConcreteExecution : forall ks, exists Mf,
  cstepstar InitProgram (curs (V293_init_tcb_clear 101%Z 31%Z 32%Z),(kenil,ks))
    (InitGE,emp,InitMemory) (curs (sskip None),(kenil,ks)) (InitGE,emp,Mf) /\
  V293_wstate InitGE emp Mf |= V293_rdy_raw_cells
    (V293_clr_bytes 82%positive 0 (repeat (Vint32 Int.zero) 728)++
     V293_null_pointer_cells 84%positive 0 13++InitFrame) Atrue /\
  (forall p, (p<13)%nat -> load (Tptr V293_tcb_type) Mf (84%positive,4*Z.of_nat p)=Some Vnull) /\
  load Tint8 Mf (82%positive,0)=Some (Vint32 Int.zero) /\
  load Tint8 Mf (82%positive,727)=Some (Vint32 Int.zero) /\
  load Tint8 Mf (82%positive,728)=Some (Vint32 (Int.repr 17)) /\
  load Tint8 Mf (84%positive,52)=Some (Vint32 (Int.repr 29)) /\
  load Tint32 Mf (99%positive,0)=Some (Vint32 (Int.repr 123)).
Proof.
  intro ks.
  destruct (V293_OS_InitTCBList_cleared_tables (repeat Vundef 728)
    (repeat (Vint32 (Int.repr 255)) 52) InitFrame InitProgram ks InitGE emp InitMemory
    (fun _=>false) (false,nil,nil) emp (spec_done None) 101%Z 11%Z 12%Z 31%Z 32%Z 82%positive 84%positive
    InitProgramLookup ltac:(discriminate) ltac:(reflexivity) ltac:(reflexivity)
    ltac:(reflexivity) ltac:(reflexivity) ltac:(apply repeat_length) ltac:(apply repeat_length)
    InitLiteralEntry) as (Mf&Exec&Owned&Nulls).
  exists Mf. split;[exact Exec | ]. split;[exact Owned | ]. split;[exact Nulls | ].
  assert (Read : forall a tp v,
    In (a,tp,v) (V293_clr_bytes 82%positive 0 (repeat (Vint32 Int.zero) 728)++
      V293_null_pointer_cells 84%positive 0 13++InitFrame) ->
    rule_type_val_match tp v=true -> load tp Mf a=Some v).
  { intros a tp v Member Valid.
    change (load tp (getmem (V293_wstate InitGE emp Mf)) a=Some v).
    eapply V293_rdy_raw_load;[exact Member | exact Valid | exact Owned]. }
  split.
  - apply Read;[apply in_or_app;left;left;reflexivity | reflexivity].
  - split.
    + apply Read;[apply in_or_app;left;change (In ((82%positive,0+Z.of_nat 727),Tint8,Vint32 Int.zero)
        (V293_clr_bytes 82%positive 0 (repeat (Vint32 Int.zero) 728)));apply InitByteMember;lia | reflexivity].
    + split.
      * apply Read;[apply in_or_app;right;apply in_or_app;right;left;reflexivity | reflexivity].
      * split.
        -- apply Read;[apply in_or_app;right;apply in_or_app;right;right;left;reflexivity | reflexivity].
        -- apply Read;[apply in_or_app;right;apply in_or_app;right;right;right;left;reflexivity | reflexivity].
Qed.
Print Assumptions InitLiteralEntry.
Print Assumptions InitProgramLookup.
Print Assumptions InitLiteralAST.
Print Assumptions InitConcreteExecution.
