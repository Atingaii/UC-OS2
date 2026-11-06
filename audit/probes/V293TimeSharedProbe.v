(* Independently chosen literal layout and abstract state. No initialization
   reachability or whole-kernel invariant is asserted. *)
Require Import CertiOS.certiucos.v293.proofs.V293TimeShared.
Require Import CertiOS.certiucos.v293.proofs.V293TimeAccess.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedChange.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewWitness.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.sep_combine_lemmas.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.
Definition SharedGE : env := set (sig OSTCBCur (90%positive,Tptr Tvoid)) 1001%Z (80%positive,Tint32).
Definition SharedLE : env := set (sig 1002%Z (81%positive,Tint32)) 1003%Z (82%positive,Tint32).
Definition SharedTid : tid := (91%positive,Int.zero).
Definition SharedState M O : RstateOP :=
  (SharedGE,SharedLE,M,(fun _=>false),(true,[],[true;false]),O,spec_done None).
Definition SharedBytes b perm tp v := V293_encoded_memory b 0 perm (encode_val tp v).
Definition SharedClock n := SharedBytes 80%positive true Tint32 (Vint32 n).
Definition SharedPointer := SharedBytes 90%positive false (Tptr Tvoid) (Vptr SharedTid).
Definition SharedAbstract n := merge (sig curtid (oscurt SharedTid))
  (merge (sig abstcblsid (abstcblist (emp:TcbMod.map)))
    (merge (sig absecblsid (absecblist (emp:EcbMod.map))) (sig ostmid (ostm n)))).
Definition SharedFrame := CurLINV V293_witness_li SharedTid.
Lemma SharedStar : forall m1 m2 m o1 o2 o p q,
  join m1 m2 m -> join o1 o2 o -> SharedState m1 o1 |= p -> SharedState m2 o2 |= q ->
  SharedState m o |= p ** q.
Proof.
  intros. exists m1. exists m2. exists m. exists o1. exists o2. exists o.
  repeat first [assumption | reflexivity | split].
Qed.
Lemma SharedPointerSpatial : SharedState SharedPointer emp |= CurTid SharedTid.
Proof.
  exists Tvoid. exists 90%positive.
  eapply SharedStar with (m1:=emp) (m2:=SharedPointer) (o1:=emp) (o2:=emp).
  - apply map_join_comm;apply map_join_emp.
  - apply map_join_emp.
  - exists 90%positive. split;[vm_compute;reflexivity | ]. repeat split;reflexivity.
  - split;[apply V293_encoded_memory_mapsto | reflexivity].
Qed.
Ltac SharedAbsApart :=
  apply map_join_merge;apply map_disjoint;let k:=fresh "key" in intro k;destruct k;vm_compute;auto.
Lemma SharedAbstractSpatial : forall n,
  SharedState emp (SharedAbstract n) |= V293_shared_fields SharedTid emp emp n.
Proof.
  intro n. unfold V293_shared_fields,SharedAbstract.
  repeat (eapply SharedStar with (m1:=emp) (m2:=emp);
    [apply map_join_emp | SharedAbsApart | split;reflexivity | ]).
  split;reflexivity.
Qed.
Theorem SharedCoreSpatial : forall n,
  SharedState (merge SharedPointer (SharedClock n)) (SharedAbstract n) |= V293_time_shared_core 80%positive.
Proof.
  intro n. exists n. eapply SharedStar with
    (m1:=SharedPointer) (m2:=SharedClock n) (o1:=SharedAbstract n) (o2:=emp).
  - apply map_join_merge. apply map_disjoint. intros [b i].
    destruct (Pos.eq_dec b 90%positive);[subst b;right;left | left].
    all:unfold SharedPointer,SharedClock,SharedBytes;
      rewrite V293_encoded_memory_outside by (left;congruence);reflexivity.
  - apply map_join_emp.
  - exists SharedTid. exists (emp:TcbMod.map). exists (emp:EcbMod.map).
    eapply SharedStar with (m1:=SharedPointer) (m2:=emp) (o1:=emp) (o2:=SharedAbstract n).
    + apply map_join_emp.
    + apply map_join_comm;apply map_join_emp.
    + exact SharedPointerSpatial.
    + apply SharedAbstractSpatial.
  - split;[apply V293_encoded_memory_mapsto | reflexivity].
Qed.
Theorem SharedLiteralClockAgreement : forall n,
  get (SharedAbstract n) ostmid = Some (ostm n) /\
  load Tint32 (merge SharedPointer (SharedClock n)) (80%positive,0%Z) = Some (Vint32 n).
Proof.
  intro n. pose proof (SharedCoreSpatial n) as H.
  destruct (V293_time_shared_clock_agreement _ _ _ _ _ _ _ _ H) as [clock [Abstract Physical]].
  assert (Literal : get (SharedAbstract n) ostmid = Some (ostm n)) by (vm_compute;reflexivity).
  change (get (SharedAbstract n) ostmid = Some (ostm clock)) in Abstract.
  assert (clock=n) by congruence. subst clock. split;assumption.
Qed.
Lemma SharedFrameGood : GoodFrm SharedFrame.
Proof.
  unfold SharedFrame,CurLINV,CurTid,LINV,V293_witness_li,Agvarmapsto.
  cbn [GoodFrm]. firstorder.
Qed.
Definition SharedLocalMemory := merge (SharedBytes 81%positive true Tint32 Vundef)
  (merge (SharedBytes 82%positive true Tint32 Vundef) SharedPointer).
Lemma SharedLocalCell : forall x b,
  get SharedLE x = Some (b,Tint32) ->
  SharedState (SharedBytes b true Tint32 Vundef) emp |= V293_time_cell true x b Vundef.
Proof.
  intros x b E. unfold V293_time_cell.
  eapply SharedStar with (m1:=emp) (m2:=SharedBytes b true Tint32 Vundef) (o1:=emp) (o2:=emp).
  - apply map_join_comm;apply map_join_emp.
  - apply map_join_emp.
  - exists b. split;[exact E | ]. repeat split;reflexivity.
  - split;[apply V293_encoded_memory_mapsto | reflexivity].
Qed.
Lemma SharedFrameSpatial : SharedState SharedPointer emp |= SharedFrame.
Proof.
  unfold SharedFrame,CurLINV. exists (nil:list logicvar).
  eapply SharedStar with (m1:=SharedPointer) (m2:=emp) (o1:=emp) (o2:=emp).
  - apply map_join_emp.
  - apply map_join_emp.
  - exact SharedPointerSpatial.
  - eapply SharedStar with (m1:=emp) (m2:=emp) (o1:=emp) (o2:=emp);
      [apply map_join_emp | apply map_join_emp | | exact I].
    unfold LINV,V293_witness_li.
    eapply SharedStar with (m1:=emp) (m2:=emp) (o1:=emp) (o2:=emp).
    + apply map_join_emp.
    + apply map_join_emp.
    + repeat split;reflexivity.
    + split;[apply V293_witness_li_good | repeat split;reflexivity].
Qed.
Ltac SharedMemApart k :=
  apply map_join_merge;apply map_disjoint;intros [b i];
  destruct (Pos.eq_dec b k);[subst b;right;left | left];
  unfold SharedPointer,SharedBytes;
  repeat rewrite map_merge_semp by reflexivity;
  repeat rewrite V293_encoded_memory_outside by (left;congruence);reflexivity.
Theorem SharedCallerEntry : SharedState SharedLocalMemory emp |=
  <||spec_done None||> ** OS[(fun _=>false),true,[],[true;false]] **
  V293_time_shared_locals 1001%Z 1002%Z 1003%Z 80%positive 81%positive 82%positive Vundef Vundef SharedFrame.
Proof.
  eapply SharedStar with (m1:=emp) (m2:=SharedLocalMemory) (o1:=emp) (o2:=emp).
  - apply map_join_comm;apply map_join_emp.
  - apply map_join_emp.
  - repeat split;reflexivity.
  - eapply SharedStar with (m1:=emp) (m2:=SharedLocalMemory) (o1:=emp) (o2:=emp).
    + apply map_join_comm;apply map_join_emp.
    + apply map_join_emp.
    + repeat (eapply SharedStar with (m1:=emp) (m2:=emp) (o1:=emp) (o2:=emp);
        [apply map_join_emp | apply map_join_emp | repeat split;reflexivity | ]).
      repeat split;reflexivity.
    + unfold V293_time_shared_locals.
      eapply SharedStar with (m1:=emp) (m2:=SharedLocalMemory) (o1:=emp) (o2:=emp).
      * apply map_join_comm;apply map_join_emp.
      * apply map_join_emp.
      * split.
        -- exists 80%positive. split;[vm_compute;reflexivity | ]. repeat split;reflexivity.
        -- split;[intros [z Z];change (get SharedLE 1001%Z=Some z) in Z;vm_compute in Z;discriminate | ].
           repeat split;reflexivity.
      * unfold SharedLocalMemory. eapply SharedStar;
          [SharedMemApart 81%positive | apply map_join_emp | apply SharedLocalCell;vm_compute;reflexivity | ].
        eapply SharedStar;
          [SharedMemApart 82%positive | apply map_join_emp | apply SharedLocalCell;vm_compute;reflexivity | ].
        apply SharedFrameSpatial.
Qed.
(* The caller really has no global-clock byte; the invariant owns them. *)
Theorem SharedCallerLacksClock : forall i, get SharedLocalMemory (80%positive,i)=None.
Proof.
  intro i. unfold SharedLocalMemory,SharedPointer,SharedBytes.
  repeat rewrite map_merge_semp by reflexivity.
  repeat rewrite V293_encoded_memory_outside by (left;discriminate). reflexivity.
Qed.
Theorem SharedGetterInstantiation : forall Spec sd,
  InfRules Spec sd V293_witness_li (V293_time_shared_inv 80%positive)
    (fun result => EX clock : int32, [|result=Some (Vint32 clock)|] **
      (<||spec_done None||> ** OS[(fun _=>false),true,[],[true;false]] **
        V293_time_shared_locals 1001%Z 1002%Z 1003%Z 80%positive 81%positive 82%positive
          (Vint32 clock) (Vint32 Int.zero) SharedFrame)) Afalse
    (<||spec_done None||> ** OS[(fun _=>false),true,[],[true;false]] **
      V293_time_shared_locals 1001%Z 1002%Z 1003%Z 80%positive 81%positive 82%positive Vundef Vundef SharedFrame)
    (V293_TimeGet_body 1001%Z 1002%Z 1003%Z) Afalse SharedTid.
Proof.
  intros. apply V293_OSTimeGet_shared_body;
    [reflexivity | cbn;lia | apply SharedFrameGood | intros s H;exact H].
Qed.
(* Joint nonvacuity: both CurTid halves come from one real writable
   current-pointer cell, rather than assuming two incompatible heaps. *)
Definition SharedJointMemory n := merge (SharedClock n)
  (merge (SharedBytes 81%positive true Tint32 Vundef)
    (merge (SharedBytes 82%positive true Tint32 Vundef)
      (SharedBytes 90%positive true (Tptr Tvoid) (Vptr SharedTid)))).
Lemma SharedCurrentFull : SharedState
    (SharedBytes 90%positive true (Tptr Tvoid) (Vptr SharedTid)) emp |=
    GV OSTCBCur @ (Tptr Tvoid) |-> Vptr SharedTid.
Proof.
  exists 90%positive. eapply SharedStar with (m1:=emp)
    (m2:=SharedBytes 90%positive true (Tptr Tvoid) (Vptr SharedTid)) (o1:=emp) (o2:=emp).
  - apply map_join_comm;apply map_join_emp.
  - apply map_join_emp.
  - exists 90%positive. split;[vm_compute;reflexivity | ]. repeat split;reflexivity.
  - split;[apply V293_encoded_memory_mapsto | reflexivity].
Qed.
Lemma SharedEmptyLocalInv : SharedState emp emp |=
  LINV V293_witness_li SharedTid (nil:list logicvar) ** Atrue.
Proof.
  eapply SharedStar with (m1:=emp) (m2:=emp) (o1:=emp) (o2:=emp);
    [apply map_join_emp | apply map_join_emp | | exact I].
  unfold LINV,V293_witness_li.
  eapply SharedStar with (m1:=emp) (m2:=emp) (o1:=emp) (o2:=emp).
  - apply map_join_emp.
  - apply map_join_emp.
  - repeat split;reflexivity.
  - split;[apply V293_witness_li_good | repeat split;reflexivity].
Qed.
Theorem SharedJointEntry : forall n,
  SharedState (SharedJointMemory n) (SharedAbstract n) |=
    V293_time_shared_core 80%positive **
    V293_time_shared_locals 1001%Z 1002%Z 1003%Z 80%positive 81%positive 82%positive
      Vundef Vundef SharedFrame.
Proof.
  intro n.
  assert (Raw : SharedState (SharedJointMemory n) (SharedAbstract n) |=
    (PV (80%positive,Int.zero) @ Tint32 |-> Vint32 n) **
    (V293_time_cell true 1002%Z 81%positive Vundef **
      (V293_time_cell true 1003%Z 82%positive Vundef **
        ((GV OSTCBCur @ (Tptr Tvoid) |-> Vptr SharedTid) **
          (V293_shared_fields SharedTid emp emp n **
            (V293_time_binding false 1001%Z 80%positive **
              (LINV V293_witness_li SharedTid (nil:list logicvar) ** Atrue))))))).
  { unfold SharedJointMemory.
    eapply SharedStar with (o1:=emp) (o2:=SharedAbstract n).
    - unfold SharedClock. SharedMemApart 80%positive.
    - apply map_join_comm;apply map_join_emp.
    - split;[apply V293_encoded_memory_mapsto | reflexivity].
    - eapply SharedStar with (o1:=emp) (o2:=SharedAbstract n).
      + SharedMemApart 81%positive.
      + apply map_join_comm;apply map_join_emp.
      + apply SharedLocalCell;vm_compute;reflexivity.
      + eapply SharedStar with (o1:=emp) (o2:=SharedAbstract n).
        * SharedMemApart 82%positive.
        * apply map_join_comm;apply map_join_emp.
        * apply SharedLocalCell;vm_compute;reflexivity.
        * eapply SharedStar with (m1:=SharedBytes 90%positive true (Tptr Tvoid) (Vptr SharedTid))
            (m2:=emp) (o1:=emp) (o2:=SharedAbstract n).
          -- apply map_join_emp.
          -- apply map_join_comm;apply map_join_emp.
          -- apply SharedCurrentFull.
          -- eapply SharedStar with (m1:=emp) (m2:=emp) (o1:=SharedAbstract n) (o2:=emp).
             ++ apply map_join_emp.
             ++ apply map_join_emp.
             ++ apply SharedAbstractSpatial.
             ++ eapply SharedStar with (m1:=emp) (m2:=emp) (o1:=emp) (o2:=emp);
                  [apply map_join_emp | apply map_join_emp | | apply SharedEmptyLocalInv].
                split.
                ** exists 80%positive. split;[vm_compute;reflexivity | ]. repeat split;reflexivity.
                ** split;[intros [z Z];change (get SharedLE 1001%Z=Some z) in Z;vm_compute in Z;discriminate | ].
                   repeat split;reflexivity. }
  assert (Pack : SharedState (SharedJointMemory n) (SharedAbstract n) |=
    (GV OSTCBCur @ (Tptr Tvoid) |-> Vptr SharedTid) **
    ((PV (80%positive,Int.zero) @ Tint32 |-> Vint32 n) **
      (V293_time_cell true 1002%Z 81%positive Vundef **
        (V293_time_cell true 1003%Z 82%positive Vundef **
          (V293_shared_fields SharedTid emp emp n **
            (V293_time_binding false 1001%Z 80%positive **
              (LINV V293_witness_li SharedTid (nil:list logicvar) ** Atrue))))))) by (sep auto).
  eapply astar_mono in Pack;[ | apply GV_separate_rw | intros st H;exact H].
  clear Raw. unfold V293_time_shared_core,V293_time_shared_fields,
    V293_time_shared_locals,SharedFrame,CurLINV,CurTid. sep auto.
Qed.
Print Assumptions SharedJointEntry.
Print Assumptions SharedCoreSpatial.
Print Assumptions SharedLiteralClockAgreement.
Print Assumptions SharedCallerEntry.
Print Assumptions SharedCallerLacksClock.
Print Assumptions SharedGetterInstantiation.
