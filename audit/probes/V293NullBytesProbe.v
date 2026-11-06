(* Constructive finite old/Vundef byte range, with same-block guards. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.code.V293OSMemClr.
Require Import CertiOS.certiucos.v293.proofs.V293MemClr.
Require Import CertiOS.certiucos.v293.proofs.V293NullBytes.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope Z_scope.
Definition NullLE : env := set (set emp 11%Z (81%positive,Tptr Tint8)) 12%Z (83%positive,Tint16).
Definition NullState M := V293_wstate emp NullLE M.
Definition NullBytes a tp v := V293_encoded_memory (fst a) (snd a) true (encode_val tp v).
Fixpoint NullMem (cells : list V293_record_cell) : mem :=
  match cells with
  | [] => NullBytes (99%positive,0) Tint32 (Vint32 (Int.repr 123))
  | (a,tp,v)::tail => merge (NullBytes a tp v) (NullMem tail)
  end.
Definition NullOld : list val := [Vint32 (Int.repr 255);Vundef;Vint32 (Int.repr 7);Vint32 (Int.repr 1)].
Definition NullGuards : list V293_record_cell :=
  [((82%positive,4),Tint8,Vint32 (Int.repr 17));((82%positive,9),Tint8,Vint32 (Int.repr 29))].
Definition NullFrame := V293_rdy_raw_cells NullGuards
  (Amapsto (99%positive,0) Tint32 true (Vint32 (Int.repr 123))).
Definition NullInitial := V293_clr_cells 81%positive 83%positive 82%positive 5 NullOld.
Ltac NullOutside :=
  unfold NullBytes;cbn [fst snd];repeat rewrite map_merge_semp by reflexivity;
  repeat rewrite V293_encoded_memory_outside by
    (first [left;congruence | right;cbn;lia]);reflexivity.
Ltac NullUnique b :=
  apply map_join_merge;apply map_disjoint;intros [other off];
  destruct (Pos.eq_dec other b);[subst other;right;left;NullOutside | left;apply V293_encoded_memory_outside;left;assumption].
Ltac NullByte b x :=
  apply map_join_merge;apply map_disjoint;intros [other off];
  destruct (Pos.eq_dec other b) as [E | E];
  [subst other;destruct (Z.eq_dec off x) as [F | F];
    [subst off;right;left;NullOutside |
     left;apply V293_encoded_memory_outside;right;cbn;lia] |
   left;apply V293_encoded_memory_outside;left;exact E].
Theorem NullLiteralEntry : NullState (NullMem (NullInitial++NullGuards)) |=
  V293_rdy_raw_cells NullInitial NullFrame.
Proof.
  unfold NullState,NullInitial,NullOld,NullGuards,NullFrame,V293_clr_cells,V293_clr_params.
  cbn [V293_clr_bytes V293_rdy_raw_cells NullMem app length].
  eapply V293_wstate_star with (m1:=NullBytes (81%positive,0) (Tptr Tint8) (Vptr (82%positive,Int.repr 5)));
    [NullUnique 81%positive | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
  eapply V293_wstate_star with (m1:=NullBytes (83%positive,0) Tint16 (Vint32 (Int.repr 4)));
    [NullUnique 83%positive | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
  eapply V293_wstate_star with (m1:=NullBytes (82%positive,5) Tint8 (Vint32 (Int.repr 255)));
    [NullByte 82%positive 5 | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
  eapply V293_wstate_star with (m1:=NullBytes (82%positive,6) Tint8 Vundef);
    [NullByte 82%positive 6 | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
  eapply V293_wstate_star with (m1:=NullBytes (82%positive,7) Tint8 (Vint32 (Int.repr 7)));
    [NullByte 82%positive 7 | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
  eapply V293_wstate_star with (m1:=NullBytes (82%positive,8) Tint8 (Vint32 (Int.repr 1)));
    [NullByte 82%positive 8 | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
  eapply V293_wstate_star with (m1:=NullBytes (82%positive,4) Tint8 (Vint32 (Int.repr 17)));
    [NullByte 82%positive 4 | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
  eapply V293_wstate_star with (m1:=NullBytes (82%positive,9) Tint8 (Vint32 (Int.repr 29)));
    [NullUnique 82%positive | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
  split;[apply V293_encoded_memory_mapsto | reflexivity].
Qed.
Theorem NullLiteralAST : V293_MemClr_function 11%Z 12%Z =
  (Tvoid,dcons 11%Z (Tptr Tint8) (dcons 12%Z Tint16 dnil),dnil,
    sseq (swhile (ebinop olt (econst32 Int.zero) (ecast (evar 12%Z) Tint32))
      (sseq (sassign (ederef (evar 11%Z)) (ecast (econst32 Int.zero) Tint8))
        (sseq (sassign (evar 11%Z) (ebinop oplus (evar 11%Z) (econst32 Int.one)))
          (sassign (evar 12%Z) (ecast
            (ebinop ominus (ecast (evar 12%Z) Tint32) (econst32 Int.one)) Tint16))))) sret).
Proof. reflexivity. Qed.

Definition NullOwned := V293_rdy_raw_cells
  (V293_clr_params 81%positive 83%positive 82%positive 9 0)
  (Amapsto (82%positive,5) (Tptr Tint8) true Vnull ** NullFrame).
Theorem NullConcreteExecution : forall P ks,
  exists Mf,
    cstepstar P (curs (V293_clr_loop 11%Z 12%Z),(kenil,ks))
      (emp,NullLE,NullMem (NullInitial++NullGuards))
      (curs (sskip None),(kenil,ks)) (emp,NullLE,Mf) /\
    NullState Mf |= NullOwned /\
    load (Tptr Tint8) Mf (82%positive,5)=Some Vnull /\
    load (Tptr Tint8) Mf (81%positive,0)=Some (Vptr (82%positive,Int.repr 9)) /\
    load Tint16 Mf (83%positive,0)=Some (Vint32 Int.zero) /\
    load Tint8 Mf (82%positive,4)=Some (Vint32 (Int.repr 17)) /\
    load Tint8 Mf (82%positive,9)=Some (Vint32 (Int.repr 29)) /\
    load Tint32 Mf (99%positive,0)=Some (Vint32 (Int.repr 123)).
Proof.
  intros P ks.
  destruct (V293_OS_MemClr_null_cell NullOld P ks emp NullLE
    (NullMem (NullInitial++NullGuards)) (fun _ => false) (false,nil,nil) emp
    (spec_done None) NullFrame 11%Z 12%Z 81%positive 83%positive 82%positive 5 Tint8
    ltac:(vm_compute;reflexivity) ltac:(vm_compute;reflexivity)
    eq_refl ltac:(lia) ltac:(change (5+4<=4294967295);lia) NullLiteralEntry)
    as (Mf&Exec&Owned&Read).
  exists Mf. split;[exact Exec | ]. split;[exact Owned | ]. split;[exact Read | ].
  assert (Cells : NullState Mf |= V293_rdy_raw_cells
    (V293_clr_params 81%positive 83%positive 82%positive 9 0 ++
      ((82%positive,5),Tptr Tint8,Vnull)::NullGuards)
    (Amapsto (99%positive,0) Tint32 true (Vint32 (Int.repr 123)))).
  { exact Owned. }
  repeat split;try solve [match goal with |- load ?tp Mf ?a=Some ?v =>
    exact (V293_rdy_raw_load
      (V293_clr_params 81%positive 83%positive 82%positive 9 0 ++
        ((82%positive,5),Tptr Tint8,Vnull)::NullGuards)
      (Amapsto (99%positive,0) Tint32 true (Vint32 (Int.repr 123))) a tp v (NullState Mf)
      ltac:(unfold V293_clr_params,NullGuards;cbn;auto 12) eq_refl Cells) end].
  change (load Tint32 (getmem (NullState Mf)) (99%positive,0)=Some (Vint32 (Int.repr 123))).
  cbn [V293_clr_params NullGuards app V293_rdy_raw_cells] in Cells.
  do 5 (eapply V293_star_load_r;[ | exact Cells];clear Cells;intros ? Cells).
  destruct Cells as [Point Empty]. eapply mapstoval_load;[reflexivity | exact Point].
Qed.

Require Import CertiOS.framework.model.memory.
Import ListNotations.
Theorem CanonicalEncoding : forall tp,
  encode_val (Tptr tp) Vnull=concat (repeat (encode_val Tint8 (Vint32 Int.zero)) 4).
Proof. reflexivity. Qed.
Theorem NullRoundTrip : forall tp,
  decode_val (Tptr tp) (encode_val (Tptr tp) Vnull)=Vnull.
Proof. reflexivity. Qed.
Theorem NonzeroRejected : forall tp,
  decode_val (Tptr tp) [Byte (Byte.repr 1);Byte Byte.zero;Byte Byte.zero;Byte Byte.zero]=Vundef.
Proof. reflexivity. Qed.
Theorem WrongLengthsRejected : forall tp,
  decode_val (Tptr tp) [Byte Byte.zero;Byte Byte.zero;Byte Byte.zero]=Vundef /\
  decode_val (Tptr tp) (repeat (Byte Byte.zero) 5)=Vundef.
Proof. split;reflexivity. Qed.
Theorem UndefNotNull : forall tp,
  decode_val (Tptr tp) (repeat Undef 4)=Vundef.
Proof. reflexivity. Qed.
Theorem LegacyNullRejected : forall tp,
  decode_val (Tptr tp) (repeat MNull 4)=Vundef.
Proof. reflexivity. Qed.
Theorem IntegerZeroUnchanged : decode_val Tint32 (repeat (Byte Byte.zero) 4)=Vint32 Int.zero.
Proof. reflexivity. Qed.
Print Assumptions CanonicalEncoding.
Print Assumptions NullRoundTrip.
Print Assumptions NonzeroRejected.
Print Assumptions WrongLengthsRejected.
Print Assumptions UndefNotNull.
Print Assumptions LegacyNullRejected.
Print Assumptions IntegerZeroUnchanged.

Print Assumptions NullLiteralEntry.
Print Assumptions NullLiteralAST.
Print Assumptions NullConcreteExecution.

Theorem AllNullTypes : forall tp id,
  decode_val Tnull (repeat (Byte Byte.zero) 4)=Vnull /\
  decode_val (Tptr tp) (repeat (Byte Byte.zero) 4)=Vnull /\
  decode_val (Tcom_ptr id) (repeat (Byte Byte.zero) 4)=Vnull.
Proof. repeat split;reflexivity. Qed.
Theorem LegacyNotCanonical : forall tp,
  repeat MNull 4 <> encode_val (Tptr tp) Vnull.
Proof. intros tp E;discriminate. Qed.
Print Assumptions AllNullTypes.
Print Assumptions LegacyNotCanonical.
