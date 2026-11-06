(* Constructive finite old/Vundef byte range, with same-block guards. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.code.V293OSMemClr.
Require Import CertiOS.certiucos.v293.proofs.V293MemClr.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewWitness.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope Z_scope.
Definition ClrLE : env := set (set emp 11%Z (81%positive,Tptr Tint8)) 12%Z (83%positive,Tint16).
Definition ClrState M := V293_wstate emp ClrLE M.
Definition ClrBytes a tp v := V293_encoded_memory (fst a) (snd a) true (encode_val tp v).
Fixpoint ClrMem (cells : list V293_record_cell) : mem :=
  match cells with
  | [] => ClrBytes (99%positive,0) Tint32 (Vint32 (Int.repr 123))
  | (a,tp,v)::tail => merge (ClrBytes a tp v) (ClrMem tail)
  end.
Definition ClrOld : list val := [Vint32 (Int.repr 255);Vundef;Vint32 (Int.repr 7)].
Definition ClrGuards : list V293_record_cell :=
  [((82%positive,4),Tint8,Vint32 (Int.repr 17));((82%positive,8),Tint8,Vint32 (Int.repr 29))].
Definition ClrFrame := V293_rdy_raw_cells ClrGuards
  (Amapsto (99%positive,0) Tint32 true (Vint32 (Int.repr 123))).
Definition ClrInitial := V293_clr_cells 81%positive 83%positive 82%positive 5 ClrOld.
Definition ClrFinal := V293_clr_params 81%positive 83%positive 82%positive 8 0 ++
  V293_clr_bytes 82%positive 5 [Vint32 Int.zero;Vint32 Int.zero;Vint32 Int.zero].
Ltac ClrOutside :=
  unfold ClrBytes;cbn [fst snd];repeat rewrite map_merge_semp by reflexivity;
  repeat rewrite V293_encoded_memory_outside by
    (first [left;congruence | right;cbn;lia]);reflexivity.
Ltac ClrUnique b :=
  apply map_join_merge;apply map_disjoint;intros [other off];
  destruct (Pos.eq_dec other b);[subst other;right;left;ClrOutside | left;apply V293_encoded_memory_outside;left;assumption].
Ltac ClrByte b x :=
  apply map_join_merge;apply map_disjoint;intros [other off];
  destruct (Pos.eq_dec other b) as [E | E];
  [subst other;destruct (Z.eq_dec off x) as [F | F];
    [subst off;right;left;ClrOutside |
     left;apply V293_encoded_memory_outside;right;cbn;lia] |
   left;apply V293_encoded_memory_outside;left;exact E].
Theorem ClrLiteralEntry : ClrState (ClrMem (ClrInitial++ClrGuards)) |=
  V293_rdy_raw_cells ClrInitial ClrFrame.
Proof.
  unfold ClrState,ClrInitial,ClrOld,ClrGuards,ClrFrame,V293_clr_cells,V293_clr_params.
  cbn [V293_clr_bytes V293_rdy_raw_cells ClrMem app length].
  eapply V293_wstate_star with (m1:=ClrBytes (81%positive,0) (Tptr Tint8) (Vptr (82%positive,Int.repr 5)));
    [ClrUnique 81%positive | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
  eapply V293_wstate_star with (m1:=ClrBytes (83%positive,0) Tint16 (Vint32 (Int.repr 3)));
    [ClrUnique 83%positive | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
  eapply V293_wstate_star with (m1:=ClrBytes (82%positive,5) Tint8 (Vint32 (Int.repr 255)));
    [ClrByte 82%positive 5 | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
  eapply V293_wstate_star with (m1:=ClrBytes (82%positive,6) Tint8 Vundef);
    [ClrByte 82%positive 6 | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
  eapply V293_wstate_star with (m1:=ClrBytes (82%positive,7) Tint8 (Vint32 (Int.repr 7)));
    [ClrByte 82%positive 7 | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
  eapply V293_wstate_star with (m1:=ClrBytes (82%positive,4) Tint8 (Vint32 (Int.repr 17)));
    [ClrByte 82%positive 4 | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
  eapply V293_wstate_star with (m1:=ClrBytes (82%positive,8) Tint8 (Vint32 (Int.repr 29)));
    [ClrUnique 82%positive | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
  split;[apply V293_encoded_memory_mapsto | reflexivity].
Qed.
Theorem ClrLiteralAST : V293_MemClr_function 11%Z 12%Z =
  (Tvoid,dcons 11%Z (Tptr Tint8) (dcons 12%Z Tint16 dnil),dnil,
    sseq (swhile (ebinop olt (econst32 Int.zero) (ecast (evar 12%Z) Tint32))
      (sseq (sassign (ederef (evar 11%Z)) (ecast (econst32 Int.zero) Tint8))
        (sseq (sassign (evar 11%Z) (ebinop oplus (evar 11%Z) (econst32 Int.one)))
          (sassign (evar 12%Z) (ecast
            (ebinop ominus (ecast (evar 12%Z) Tint32) (econst32 Int.one)) Tint16))))) sret).
Proof. reflexivity. Qed.
Theorem ClrLiteralReadback : forall M,
  ClrState M |= V293_rdy_raw_cells ClrFinal ClrFrame ->
  load (Tptr Tint8) M (81%positive,0)=Some (Vptr (82%positive,Int.repr 8)) /\
  load Tint16 M (83%positive,0)=Some (Vint32 Int.zero) /\
  load Tint8 M (82%positive,5)=Some (Vint32 Int.zero) /\
  load Tint8 M (82%positive,6)=Some (Vint32 Int.zero) /\
  load Tint8 M (82%positive,4)=Some (Vint32 (Int.repr 17)) /\
  load Tint8 M (82%positive,8)=Some (Vint32 (Int.repr 29)) /\
  load Tint8 M (82%positive,7)=Some (Vint32 Int.zero).
Proof.
  intros M Owned. repeat split;
    try solve [match goal with |- load ?tp M ?a=Some ?v =>
      exact (V293_rdy_raw_load ClrFinal ClrFrame a tp v (ClrState M)
        ltac:(unfold ClrFinal,V293_clr_params;cbn;auto 15) eq_refl Owned) end].
  all: match goal with |- load ?tp ?memory ?a=Some ?v =>
    change (load tp (getmem (ClrState memory)) a=Some v) end.
  all: unfold ClrFinal,V293_clr_params in Owned;cbn [V293_clr_bytes app V293_rdy_raw_cells] in Owned.
  all: do 5 (eapply V293_record_star_load_r;[ | exact Owned];clear Owned;intros ? Owned).
  all: eapply (V293_rdy_raw_load ClrGuards _);[unfold ClrGuards;cbn;auto | reflexivity | exact Owned].
Qed.
Theorem ClrConcreteExecution : forall P ks,
  exists Mf,
    cstepstar P (curs (V293_clr_loop 11%Z 12%Z),(kenil,ks))
      (emp,ClrLE,ClrMem (ClrInitial++ClrGuards))
      (curs (sskip None),(kenil,ks)) (emp,ClrLE,Mf) /\
    load (Tptr Tint8) Mf (81%positive,0)=Some (Vptr (82%positive,Int.repr 8)) /\
    load Tint16 Mf (83%positive,0)=Some (Vint32 Int.zero) /\
    load Tint8 Mf (82%positive,5)=Some (Vint32 Int.zero) /\
    load Tint8 Mf (82%positive,6)=Some (Vint32 Int.zero) /\
    load Tint8 Mf (82%positive,4)=Some (Vint32 (Int.repr 17)) /\
    load Tint8 Mf (82%positive,8)=Some (Vint32 (Int.repr 29)) /\
    load Tint8 Mf (82%positive,7)=Some (Vint32 Int.zero).
Proof.
  intros P ks.
  destruct (V293_OS_MemClr_loop_execution ClrOld P ks emp ClrLE
    (ClrMem (ClrInitial++ClrGuards)) (fun _ => false) (false,nil,nil) emp
    (spec_done None) ClrFrame 11%Z 12%Z 81%positive 83%positive 82%positive 5
    ltac:(vm_compute;reflexivity) ltac:(vm_compute;reflexivity)
    ltac:(cbn;lia) ltac:(lia) ltac:(change (5+3<=4294967295);lia) ClrLiteralEntry)
    as (Mf & Exec & Final).
  exists Mf. split;[exact Exec | apply ClrLiteralReadback;exact Final].
Qed.

Theorem ClrEmptyDoesNotReadDest : forall P ks,
  let le : env := set emp 12%Z (83%positive,Tint16) in
  let M := V293_encoded_memory 83%positive 0 true (encode_val Tint16 (Vint32 Int.zero)) in
  cstepstar P (curs (V293_clr_loop 777%Z 12%Z),(kenil,ks)) (emp,le,M)
    (curs (sskip None),(kenil,ks)) (emp,le,M).
Proof.
  intros P ks le M. eapply V293_OS_MemClr_zero_size with
    (ir:=fun _ => false) (aux:=(false,nil,nil)) (O:=emp) (op:=spec_done None) (R:=Aemp) (bs:=83%positive).
  - unfold le. apply map_get_set.
  - change (V293_wstate emp le M |= Amapsto (83%positive,0) Tint16 true (Vint32 Int.zero) ** Aemp).
    eapply V293_wstate_star with (m1:=M) (m2:=emp).
    + apply map_join_emp.
    + split;[apply V293_encoded_memory_mapsto | reflexivity].
    + split;reflexivity.
Qed.

(* A concrete model mismatch, not an axiom granting typed pointer zeros. *)
Theorem ClrZeroBytesNotNull :
  decode_val (Tptr Tint8) (concat (repeat (encode_val Tint8 (Vint32 Int.zero)) 4))=Vundef /\
  decode_val (Tptr Tint8) (encode_val (Tptr Tint8) Vnull)=Vnull /\
  concat (repeat (encode_val Tint8 (Vint32 Int.zero)) 4) <> encode_val (Tptr Tint8) Vnull /\
  load (Tptr Tint8) (V293_encoded_memory 50%positive 0 true
    (concat (repeat (encode_val Tint8 (Vint32 Int.zero)) 4))) (50%positive,0)=Some Vundef.
Proof.
  split;[reflexivity | ]. split;[reflexivity | ].
  split;[discriminate | ].
  pose proof (V293_encoded_memory_mapsto 50%positive 0 true Tint32 (Vint32 Int.zero)) as Own.
  destruct Own as (bytes & Enc & Own). subst bytes.
  apply ptomvallist_loadbytes in Own.
  change (loadbytes (V293_encoded_memory 50%positive 0 true
    (concat (repeat (encode_val Tint8 (Vint32 Int.zero)) 4)))
    (50%positive,0) 4=Some (concat (repeat (encode_val Tint8 (Vint32 Int.zero)) 4))) in Own.
  unfold load,loadm. cbn [typelen].
  rewrite Own. reflexivity.
Qed.
Print Assumptions ClrLiteralEntry.
Print Assumptions ClrLiteralAST.
Print Assumptions ClrConcreteExecution.
Print Assumptions ClrEmptyDoesNotReadDest.
Print Assumptions ClrZeroBytesNotNull.
