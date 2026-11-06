(* Independently chosen literal layout and abstract state. No initialization
   reachability or whole-kernel invariant is asserted. *)
Require Import CertiOS.certiucos.v293.proofs.V293TimeSharedSet.
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
Definition SetterGE : env := set (sig OSTCBCur (90%positive,Tptr Tvoid)) 1001%Z (80%positive,Tint32).
Definition SetterLE : env := set (sig 1002%Z (81%positive,Tint32)) 1003%Z (82%positive,Tint32).
Definition SetterTid : tid := (91%positive,Int.zero).
Definition SetterState M O : RstateOP :=
  (SetterGE,SetterLE,M,(fun _=>false),(true,[],[true;false]),O,V293_time_set_action (Int.repr 42)).
Definition SetterBytes b perm tp v := V293_encoded_memory b 0 perm (encode_val tp v).
Definition SetterClock n := SetterBytes 80%positive true Tint32 (Vint32 n).
Definition SetterPointer := SetterBytes 90%positive false (Tptr Tvoid) (Vptr SetterTid).
Definition SetterAbstract n := merge (sig curtid (oscurt SetterTid))
  (merge (sig abstcblsid (abstcblist (emp:TcbMod.map)))
    (merge (sig absecblsid (absecblist (emp:EcbMod.map))) (sig ostmid (ostm n)))).
Definition SetterFrame := CurLINV V293_witness_li SetterTid.
Lemma SetterStar : forall m1 m2 m o1 o2 o p q,
  join m1 m2 m -> join o1 o2 o -> SetterState m1 o1 |= p -> SetterState m2 o2 |= q ->
  SetterState m o |= p ** q.
Proof.
  intros. exists m1. exists m2. exists m. exists o1. exists o2. exists o.
  repeat first [assumption | reflexivity | split].
Qed.
Lemma SetterPointerSpatial : SetterState SetterPointer emp |= CurTid SetterTid.
Proof.
  exists Tvoid. exists 90%positive.
  eapply SetterStar with (m1:=emp) (m2:=SetterPointer) (o1:=emp) (o2:=emp).
  - apply map_join_comm;apply map_join_emp.
  - apply map_join_emp.
  - exists 90%positive. split;[vm_compute;reflexivity | ]. repeat split;reflexivity.
  - split;[apply V293_encoded_memory_mapsto | reflexivity].
Qed.
Ltac SetterAbsApart :=
  apply map_join_merge;apply map_disjoint;let k:=fresh "key" in intro k;destruct k;vm_compute;auto.
Lemma SetterAbstractSpatial : forall n,
  SetterState emp (SetterAbstract n) |= V293_shared_fields SetterTid emp emp n.
Proof.
  intro n. unfold V293_shared_fields,SetterAbstract.
  repeat (eapply SetterStar with (m1:=emp) (m2:=emp);
    [apply map_join_emp | SetterAbsApart | split;reflexivity | ]).
  split;reflexivity.
Qed.
Theorem SetterCoreSpatial : forall n,
  SetterState (merge SetterPointer (SetterClock n)) (SetterAbstract n) |= V293_time_shared_core 80%positive.
Proof.
  intro n. exists n. eapply SetterStar with
    (m1:=SetterPointer) (m2:=SetterClock n) (o1:=SetterAbstract n) (o2:=emp).
  - apply map_join_merge. apply map_disjoint. intros [b i].
    destruct (Pos.eq_dec b 90%positive);[subst b;right;left | left].
    all:unfold SetterPointer,SetterClock,SetterBytes;
      rewrite V293_encoded_memory_outside by (left;congruence);reflexivity.
  - apply map_join_emp.
  - exists SetterTid. exists (emp:TcbMod.map). exists (emp:EcbMod.map).
    eapply SetterStar with (m1:=SetterPointer) (m2:=emp) (o1:=emp) (o2:=SetterAbstract n).
    + apply map_join_emp.
    + apply map_join_comm;apply map_join_emp.
    + exact SetterPointerSpatial.
    + apply SetterAbstractSpatial.
  - split;[apply V293_encoded_memory_mapsto | reflexivity].
Qed.
Theorem SetterLiteralClockAgreement : forall n,
  get (SetterAbstract n) ostmid = Some (ostm n) /\
  load Tint32 (merge SetterPointer (SetterClock n)) (80%positive,0%Z) = Some (Vint32 n).
Proof.
  intro n. pose proof (SetterCoreSpatial n) as H.
  destruct (V293_time_shared_clock_agreement _ _ _ _ _ _ _ _ H) as [clock [Abstract Physical]].
  assert (Literal : get (SetterAbstract n) ostmid = Some (ostm n)) by (vm_compute;reflexivity).
  change (get (SetterAbstract n) ostmid = Some (ostm clock)) in Abstract.
  assert (clock=n) by congruence. subst clock. split;assumption.
Qed.
Lemma SetterFrameGood : GoodFrm SetterFrame.
Proof.
  unfold SetterFrame,CurLINV,CurTid,LINV,V293_witness_li,Agvarmapsto.
  cbn [GoodFrm]. firstorder.
Qed.
Definition SetterLocalMemory := merge (SetterBytes 81%positive true Tint32 (Vint32 (Int.repr 42)))
  (merge (SetterBytes 82%positive true Tint32 Vundef) SetterPointer).
Lemma SetterLocalCell : forall x b v,
  get SetterLE x = Some (b,Tint32) ->
  SetterState (SetterBytes b true Tint32 v) emp |= V293_time_cell true x b v.
Proof.
  intros x b v E. unfold V293_time_cell.
  eapply SetterStar with (m1:=emp) (m2:=SetterBytes b true Tint32 v) (o1:=emp) (o2:=emp).
  - apply map_join_comm;apply map_join_emp.
  - apply map_join_emp.
  - exists b. split;[exact E | ]. repeat split;reflexivity.
  - split;[apply V293_encoded_memory_mapsto | reflexivity].
Qed.
Lemma SetterFrameSpatial : SetterState SetterPointer emp |= SetterFrame.
Proof.
  unfold SetterFrame,CurLINV. exists (nil:list logicvar).
  eapply SetterStar with (m1:=SetterPointer) (m2:=emp) (o1:=emp) (o2:=emp).
  - apply map_join_emp.
  - apply map_join_emp.
  - exact SetterPointerSpatial.
  - eapply SetterStar with (m1:=emp) (m2:=emp) (o1:=emp) (o2:=emp);
      [apply map_join_emp | apply map_join_emp | | exact I].
    unfold LINV,V293_witness_li.
    eapply SetterStar with (m1:=emp) (m2:=emp) (o1:=emp) (o2:=emp).
    + apply map_join_emp.
    + apply map_join_emp.
    + repeat split;reflexivity.
    + split;[apply V293_witness_li_good | repeat split;reflexivity].
Qed.
Ltac SetterMemApart k :=
  apply map_join_merge;apply map_disjoint;intros [b i];
  destruct (Pos.eq_dec b k);[subst b;right;left | left];
  unfold SetterPointer,SetterBytes;
  repeat rewrite map_merge_semp by reflexivity;
  repeat rewrite V293_encoded_memory_outside by (left;congruence);reflexivity.
Theorem SetterCallerEntry : SetterState SetterLocalMemory emp |=
  <||V293_time_set_action (Int.repr 42)||> ** OS[(fun _=>false),true,[],[true;false]] **
  V293_time_shared_locals 1001%Z 1002%Z 1003%Z 80%positive 81%positive 82%positive (Vint32 (Int.repr 42)) Vundef SetterFrame.
Proof.
  eapply SetterStar with (m1:=emp) (m2:=SetterLocalMemory) (o1:=emp) (o2:=emp).
  - apply map_join_comm;apply map_join_emp.
  - apply map_join_emp.
  - repeat split;reflexivity.
  - eapply SetterStar with (m1:=emp) (m2:=SetterLocalMemory) (o1:=emp) (o2:=emp).
    + apply map_join_comm;apply map_join_emp.
    + apply map_join_emp.
    + repeat (eapply SetterStar with (m1:=emp) (m2:=emp) (o1:=emp) (o2:=emp);
        [apply map_join_emp | apply map_join_emp | repeat split;reflexivity | ]).
      repeat split;reflexivity.
    + unfold V293_time_shared_locals.
      eapply SetterStar with (m1:=emp) (m2:=SetterLocalMemory) (o1:=emp) (o2:=emp).
      * apply map_join_comm;apply map_join_emp.
      * apply map_join_emp.
      * split.
        -- exists 80%positive. split;[vm_compute;reflexivity | ]. repeat split;reflexivity.
        -- split;[intros [z Z];change (get SetterLE 1001%Z=Some z) in Z;vm_compute in Z;discriminate | ].
           repeat split;reflexivity.
      * unfold SetterLocalMemory. eapply SetterStar;
          [SetterMemApart 81%positive | apply map_join_emp | apply SetterLocalCell;vm_compute;reflexivity | ].
        eapply SetterStar;
          [SetterMemApart 82%positive | apply map_join_emp | apply SetterLocalCell;vm_compute;reflexivity | ].
        apply SetterFrameSpatial.
Qed.
(* The caller really has no global-clock byte; the invariant owns them. *)
Theorem SetterCallerLacksClock : forall i, get SetterLocalMemory (80%positive,i)=None.
Proof.
  intro i. unfold SetterLocalMemory,SetterPointer,SetterBytes.
  repeat rewrite map_merge_semp by reflexivity.
  repeat rewrite V293_encoded_memory_outside by (left;discriminate). reflexivity.
Qed.
Lemma SetterNoAbs : NoAbs V293_witness_li.
Proof.
  intros o O t H O' op. specialize (H op).
  destruct o as [[[[ge le] M] ir] aux].
  destruct H as [lg H].
  apply sat_split in H. destruct H as (m1 & m2 & o1 & o2 & JM & JO & HC & HR).
  assert (EO : o1=emp).
  { destruct HC as [tp [b HC]].
    apply sat_split in HC. destruct HC as (mb & mp & ob & optr & JM1 & JO1 & HB & HP).
    destruct HB as [b' [GE [BE [EM EB]]]]. destruct HP as [Points EP].
    change (ob=emp) in EB. change (optr=emp) in EP. subst ob optr.
    apply map_join_emp' in JO1. symmetry;exact JO1. }
  subst o1. exists lg.
  apply sat_split'. exists m1. exists m2. exists (emp:osabst). exists O'.
  repeat first [assumption | solve [apply map_join_comm;apply map_join_emp] | split].
  unfold LINV,V293_witness_li.
  apply sat_split'. exists (emp:mem). exists m2. exists (emp:osabst). exists O'.
  repeat first [solve [apply map_join_comm;apply map_join_emp] | split].
  - apply astar_l_aemp_intro. split;[apply V293_witness_li_good | repeat split;reflexivity].
Qed.
Theorem SetterBodyInstantiation : forall Spec sd,
  InfRules Spec sd V293_witness_li (V293_time_shared_inv 80%positive)
    (fun result => [|result=None|] **
      (<||END None||> ** OS[(fun _=>false),true,[],[true;false]] **
        V293_time_shared_locals 1001%Z 1002%Z 1003%Z 80%positive 81%positive 82%positive
          (Vint32 (Int.repr 42)) (Vint32 Int.zero) SetterFrame)) Afalse
    (<||V293_time_set_action (Int.repr 42)||> ** OS[(fun _=>false),true,[],[true;false]] **
      V293_time_shared_locals 1001%Z 1002%Z 1003%Z 80%positive 81%positive 82%positive
        (Vint32 (Int.repr 42)) Vundef SetterFrame)
    (V293_TimeSet_body 1001%Z 1002%Z 1003%Z) Afalse SetterTid.
Proof.
  intros. apply V293_OSTimeSet_shared_body;
    [apply SetterNoAbs | reflexivity | cbn;lia | apply SetterFrameGood | intros s H;exact H].
Qed.
(* Joint nonvacuity: both CurTid halves come from one real writable
   current-pointer cell, rather than assuming two incompatible heaps. *)
Definition SetterJointMemory n := merge (SetterClock n)
  (merge (SetterBytes 81%positive true Tint32 (Vint32 (Int.repr 42)))
    (merge (SetterBytes 82%positive true Tint32 Vundef)
      (SetterBytes 90%positive true (Tptr Tvoid) (Vptr SetterTid)))).
Lemma SetterCurrentFull : SetterState
    (SetterBytes 90%positive true (Tptr Tvoid) (Vptr SetterTid)) emp |=
    GV OSTCBCur @ (Tptr Tvoid) |-> Vptr SetterTid.
Proof.
  exists 90%positive. eapply SetterStar with (m1:=emp)
    (m2:=SetterBytes 90%positive true (Tptr Tvoid) (Vptr SetterTid)) (o1:=emp) (o2:=emp).
  - apply map_join_comm;apply map_join_emp.
  - apply map_join_emp.
  - exists 90%positive. split;[vm_compute;reflexivity | ]. repeat split;reflexivity.
  - split;[apply V293_encoded_memory_mapsto | reflexivity].
Qed.
Lemma SetterEmptyLocalInv : SetterState emp emp |=
  LINV V293_witness_li SetterTid (nil:list logicvar) ** Atrue.
Proof.
  eapply SetterStar with (m1:=emp) (m2:=emp) (o1:=emp) (o2:=emp);
    [apply map_join_emp | apply map_join_emp | | exact I].
  unfold LINV,V293_witness_li.
  eapply SetterStar with (m1:=emp) (m2:=emp) (o1:=emp) (o2:=emp).
  - apply map_join_emp.
  - apply map_join_emp.
  - repeat split;reflexivity.
  - split;[apply V293_witness_li_good | repeat split;reflexivity].
Qed.
Theorem SetterJointEntry : forall n,
  SetterState (SetterJointMemory n) (SetterAbstract n) |=
    V293_time_shared_core 80%positive **
    V293_time_shared_locals 1001%Z 1002%Z 1003%Z 80%positive 81%positive 82%positive
      (Vint32 (Int.repr 42)) Vundef SetterFrame.
Proof.
  intro n.
  assert (Raw : SetterState (SetterJointMemory n) (SetterAbstract n) |=
    (PV (80%positive,Int.zero) @ Tint32 |-> Vint32 n) **
    (V293_time_cell true 1002%Z 81%positive (Vint32 (Int.repr 42)) **
      (V293_time_cell true 1003%Z 82%positive Vundef **
        ((GV OSTCBCur @ (Tptr Tvoid) |-> Vptr SetterTid) **
          (V293_shared_fields SetterTid emp emp n **
            (V293_time_binding false 1001%Z 80%positive **
              (LINV V293_witness_li SetterTid (nil:list logicvar) ** Atrue))))))).
  { unfold SetterJointMemory.
    eapply SetterStar with (o1:=emp) (o2:=SetterAbstract n).
    - unfold SetterClock. SetterMemApart 80%positive.
    - apply map_join_comm;apply map_join_emp.
    - split;[apply V293_encoded_memory_mapsto | reflexivity].
    - eapply SetterStar with (o1:=emp) (o2:=SetterAbstract n).
      + SetterMemApart 81%positive.
      + apply map_join_comm;apply map_join_emp.
      + apply SetterLocalCell;vm_compute;reflexivity.
      + eapply SetterStar with (o1:=emp) (o2:=SetterAbstract n).
        * SetterMemApart 82%positive.
        * apply map_join_comm;apply map_join_emp.
        * apply SetterLocalCell;vm_compute;reflexivity.
        * eapply SetterStar with (m1:=SetterBytes 90%positive true (Tptr Tvoid) (Vptr SetterTid))
            (m2:=emp) (o1:=emp) (o2:=SetterAbstract n).
          -- apply map_join_emp.
          -- apply map_join_comm;apply map_join_emp.
          -- apply SetterCurrentFull.
          -- eapply SetterStar with (m1:=emp) (m2:=emp) (o1:=SetterAbstract n) (o2:=emp).
             ++ apply map_join_emp.
             ++ apply map_join_emp.
             ++ apply SetterAbstractSpatial.
             ++ eapply SetterStar with (m1:=emp) (m2:=emp) (o1:=emp) (o2:=emp);
                  [apply map_join_emp | apply map_join_emp | | apply SetterEmptyLocalInv].
                split.
                ** exists 80%positive. split;[vm_compute;reflexivity | ]. repeat split;reflexivity.
                ** split;[intros [z Z];change (get SetterLE 1001%Z=Some z) in Z;vm_compute in Z;discriminate | ].
                   repeat split;reflexivity. }
  assert (Pack : SetterState (SetterJointMemory n) (SetterAbstract n) |=
    (GV OSTCBCur @ (Tptr Tvoid) |-> Vptr SetterTid) **
    ((PV (80%positive,Int.zero) @ Tint32 |-> Vint32 n) **
      (V293_time_cell true 1002%Z 81%positive (Vint32 (Int.repr 42)) **
        (V293_time_cell true 1003%Z 82%positive Vundef **
          (V293_shared_fields SetterTid emp emp n **
            (V293_time_binding false 1001%Z 80%positive **
              (LINV V293_witness_li SetterTid (nil:list logicvar) ** Atrue))))))) by (sep auto).
  eapply astar_mono in Pack;[ | apply GV_separate_rw | intros st H;exact H].
  clear Raw. unfold V293_time_shared_core,V293_time_shared_fields,
    V293_time_shared_locals,SetterFrame,CurLINV,CurTid. sep auto.
Qed.
(* Literal old=7 and new=42; not the expected update fed back as a premise. *)
Theorem SetterLiteralAbstractTransition : forall sd,
  spec_step sd (V293_time_set_action (Int.repr 42))
    (SetterAbstract (Int.repr 7)) (END None)
    (set (SetterAbstract (Int.repr 7)) ostmid (ostm (Int.repr 42))) /\
  get (set (SetterAbstract (Int.repr 7)) ostmid (ostm (Int.repr 42))) ostmid=Some(ostm (Int.repr 42)) /\
  get (set (SetterAbstract (Int.repr 7)) ostmid (ostm (Int.repr 42))) curtid=Some(oscurt SetterTid) /\
  get (set (SetterAbstract (Int.repr 7)) ostmid (ostm (Int.repr 42))) abstcblsid=Some(abstcblist (emp:TcbMod.map)) /\
  get (set (SetterAbstract (Int.repr 7)) ostmid (ostm (Int.repr 42))) absecblsid=Some(absecblist (emp:EcbMod.map)) /\
  Int.repr 7 <> Int.repr 42.
Proof.
  intro sd. split.
  - apply V293_time_set_transition with (old:=Int.repr 7). vm_compute;reflexivity.
  - repeat split;vm_compute;congruence.
Qed.
Print Assumptions SetterJointEntry.
Print Assumptions SetterCallerEntry.
Print Assumptions SetterCallerLacksClock.
Print Assumptions SetterNoAbs.
Print Assumptions SetterBodyInstantiation.
Print Assumptions SetterLiteralAbstractTransition.
