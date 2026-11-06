(* Independent literal bytes and environments; local-invariant fixture only,
   not initialization reachability or shared time/IRQ ownership. *)
Require Import CertiOS.certiucos.v293.proofs.V293TimeAccess.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedChange.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewWitness.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.
Definition TimeGE : env := set (sig OSTCBCur (90%positive,Tptr Tvoid)) 1001%Z (80%positive,Tint32).
Definition TimeLE : env := set (sig 1002%Z (81%positive,Tint32)) 1003%Z (82%positive,Tint32).
Definition TimeTid : tid := (91%positive,Int.zero).
Definition TimeState enabled M : RstateOP :=
  (TimeGE,TimeLE,M,(fun _=>false),(enabled,[],[true;false]),(emp:osabst),spec_done None).
Definition TimeBytes b v := V293_encoded_memory b 0 true (encode_val Tint32 v).
Definition TimeCurrent := V293_encoded_memory 90%positive 0 false (encode_val (Tptr Tvoid) (Vptr TimeTid)).
Definition TimeMemory clock tmp save := merge (TimeBytes 80%positive (Vint32 clock))
  (merge (TimeBytes 81%positive tmp) (merge (TimeBytes 82%positive save) TimeCurrent)).
Definition TimeFrame := CurLINV V293_witness_li TimeTid.

Lemma TimeStar : forall enabled m1 m2 m p q,
  join m1 m2 m -> TimeState enabled m1 |= p -> TimeState enabled m2 |= q ->
  TimeState enabled m |= p ** q.
Proof.
  intros. exists m1. exists m2. exists m. exists (emp:osabst). exists (emp:osabst). exists (emp:osabst).
  split; [reflexivity | ]. split; [assumption | ]. split; [reflexivity | ].
  split; [apply map_join_emp | ]. split;assumption.
Qed.
Lemma TimeCell : forall enabled (local:bool) x b v,
  (if local then get TimeLE x = Some (b,Tint32)
   else get TimeLE x = None /\ get TimeGE x = Some (b,Tint32)) ->
  TimeState enabled (TimeBytes b v) |= V293_time_cell local x b v.
Proof.
  intros enabled local x b v E. unfold V293_time_cell.
  eapply TimeStar with (m1:=emp) (m2:=TimeBytes b v).
  - apply map_join_comm. apply map_join_emp.
  - destruct local; cbn [V293_time_binding V293_counter_bindings].
    + exists b. split; [exact E | ]. repeat split;reflexivity.
    + destruct E as [N G]. split.
      * exists b. split; [exact G | ]. repeat split;reflexivity.
      * split; [intros [z Z];change (get TimeLE x = Some z) in Z;rewrite N in Z;discriminate | ]. repeat split;reflexivity.
  - split; [apply V293_encoded_memory_mapsto | reflexivity].
Qed.
Lemma TimeFrameSpatial : forall enabled, TimeState enabled TimeCurrent |= TimeFrame.
Proof.
  intros enabled. unfold TimeFrame,CurLINV. exists (nil:list logicvar).
  eapply TimeStar with (m1:=TimeCurrent) (m2:=emp); [apply map_join_emp | | ].
  - exists Tvoid. exists 90%positive.
    eapply TimeStar with (m1:=emp) (m2:=TimeCurrent).
    + apply map_join_comm. apply map_join_emp.
    + exists 90%positive. split; [vm_compute;reflexivity | ]. repeat split;reflexivity.
    + split; [apply V293_encoded_memory_mapsto | reflexivity].
  - eapply TimeStar with (m1:=emp) (m2:=emp); [apply map_join_emp | | exact I].
    unfold LINV,V293_witness_li.
    eapply TimeStar with (m1:=emp) (m2:=emp); [apply map_join_emp | repeat split;reflexivity | ].
    split; [apply V293_witness_li_good | repeat split;reflexivity].
Qed.
Ltac TimeApart k :=
  apply map_join_merge;apply map_disjoint;intros [b i];
  destruct (Pos.eq_dec b k); [subst b;right;left | left];
  unfold TimeBytes,TimeCurrent;
  repeat rewrite map_merge_semp by reflexivity;
  repeat rewrite V293_encoded_memory_outside by (left;congruence);reflexivity.

Theorem TimeEntrySpatial : forall enabled clock tmp save,
  TimeState enabled (TimeMemory clock tmp save) |=
    <||spec_done None||> ** OS[(fun _=>false),enabled,[],[true;false]] **
      V293_time_payload 1001%Z 1002%Z 1003%Z 80%positive 81%positive 82%positive clock tmp save TimeFrame.
Proof.
  intros. eapply TimeStar with (m1:=emp) (m2:=TimeMemory clock tmp save).
  - apply map_join_comm. apply map_join_emp.
  - repeat split;reflexivity.
  - eapply TimeStar with (m1:=emp) (m2:=TimeMemory clock tmp save).
    + apply map_join_comm. apply map_join_emp.
    + repeat (eapply TimeStar with (m1:=emp) (m2:=emp); [apply map_join_emp | repeat split;reflexivity | ]).
      repeat split;reflexivity.
    + unfold V293_time_payload,TimeMemory.
      eapply TimeStar; [TimeApart 80%positive | apply TimeCell;vm_compute;auto | ].
      eapply TimeStar; [TimeApart 81%positive | apply TimeCell;vm_compute;auto | ].
      eapply TimeStar; [TimeApart 82%positive | apply TimeCell;vm_compute;auto | ].
      apply TimeFrameSpatial.
Qed.
Lemma TimeFrameGood : GoodFrm TimeFrame.
Proof.
  unfold TimeFrame,CurLINV,CurTid,LINV,V293_witness_li,Agvarmapsto.
  cbn [GoodFrm]. firstorder.
Qed.

Theorem TimeGetterInstantiation : forall Spec sd I enabled clock,
  InfRules Spec sd V293_witness_li I
    (fun result => [| result = Some (Vint32 clock) |] **
      (<||spec_done None||> ** OS[(fun _=>false),enabled,[],[true;false]] **
        V293_time_payload 1001%Z 1002%Z 1003%Z 80%positive 81%positive 82%positive
          clock (Vint32 clock) (Vint32 Int.zero) TimeFrame)) Afalse
    (<||spec_done None||> ** OS[(fun _=>false),enabled,[],[true;false]] **
      V293_time_payload 1001%Z 1002%Z 1003%Z 80%positive 81%positive 82%positive
        clock Vundef Vundef TimeFrame)
    (V293_TimeGet_body 1001%Z 1002%Z 1003%Z) Afalse TimeTid.
Proof.
  intros. apply V293_OSTimeGet_body_hoare; [cbn;lia | apply TimeFrameGood | intros s H;exact H].
Qed.
Theorem TimeSetterInstantiation : forall Spec sd I enabled old new,
  InfRules Spec sd V293_witness_li I
    (fun result => [| result = None |] **
      (<||spec_done None||> ** OS[(fun _=>false),enabled,[],[true;false]] **
        V293_time_payload 1001%Z 1002%Z 1003%Z 80%positive 81%positive 82%positive
          new (Vint32 new) (Vint32 Int.zero) TimeFrame)) Afalse
    (<||spec_done None||> ** OS[(fun _=>false),enabled,[],[true;false]] **
      V293_time_payload 1001%Z 1002%Z 1003%Z 80%positive 81%positive 82%positive
        old (Vint32 new) Vundef TimeFrame)
    (V293_TimeSet_body 1001%Z 1002%Z 1003%Z) Afalse TimeTid.
Proof.
  intros. apply V293_OSTimeSet_body_hoare; [cbn;lia | apply TimeFrameGood | intros s H;exact H].
Qed.

(* Read the literal entry back independently of either function's proof. *)
Theorem TimeLiteralReadback : forall enabled clock new,
  evalval (evar 1001%Z) (getsmem (TimeState enabled (TimeMemory clock (Vint32 new) Vundef))) = Some (Vint32 clock) /\
  evalval (evar 1002%Z) (getsmem (TimeState enabled (TimeMemory clock (Vint32 new) Vundef))) = Some (Vint32 new).
Proof.
  intros. pose proof (TimeEntrySpatial enabled clock (Vint32 new) Vundef) as H.
  split.
  - assert (C : TimeState enabled (TimeMemory clock (Vint32 new) Vundef) |=
      V293_time_cell false 1001%Z 80%positive (Vint32 clock) ** Atrue).
    { unfold V293_time_payload in H;sep auto. }
    exact (proj1 (V293_time_cell_read _ _ _ _ _ _ C)).
  - assert (C : TimeState enabled (TimeMemory clock (Vint32 new) Vundef) |=
      V293_time_cell true 1002%Z 81%positive (Vint32 new) ** Atrue).
    { unfold V293_time_payload in H;sep auto. }
    exact (proj1 (V293_time_cell_read _ _ _ _ _ _ C)).
Qed.
Print Assumptions TimeEntrySpatial.
Print Assumptions TimeGetterInstantiation.
Print Assumptions TimeSetterInstantiation.
Print Assumptions TimeLiteralReadback.
