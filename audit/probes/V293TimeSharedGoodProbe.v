(* Literal pointer/clock bytes with all abstract keys. No initialization claim. *)
Require Import CertiOS.certiucos.v293.proofs.V293TimeSharedGood.
Require Import CertiOS.certiucos.v293.proofs.V293TimeShared.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewWitness.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.
Definition SwitchOld : tid := (91%positive,Int.zero).
Definition SwitchNew : tid := (92%positive,Int.zero).
Definition SwitchGE : env := sig OSTCBCur (90%positive,Tptr Tvoid).
Definition SwitchState M O : RstateOP :=
  (SwitchGE,(emp:env),M,(fun _=>false),(false,[],[true;false]),O,spec_done None).
Definition SwitchBytes b tp v := V293_encoded_memory b 0 true (encode_val tp v).
Definition SwitchPointer := SwitchBytes 90%positive (Tptr Tvoid) (Vptr SwitchOld).
Definition SwitchClock n := SwitchBytes 80%positive Tint32 (Vint32 n).
Definition SwitchMemory n := merge SwitchPointer (SwitchClock n).
Definition SwitchAbstract ts es n := merge (sig curtid (oscurt SwitchOld))
  (merge (sig abstcblsid (abstcblist ts))
    (merge (sig absecblsid (absecblist es)) (sig ostmid (ostm n)))).
Lemma SwitchStar : forall m1 m2 m o1 o2 o p q,
  join m1 m2 m -> join o1 o2 o -> SwitchState m1 o1 |= p -> SwitchState m2 o2 |= q ->
  SwitchState m o |= p ** q.
Proof.
  intros. exists m1. exists m2. exists m. exists o1. exists o2. exists o.
  repeat first [assumption | reflexivity | split].
Qed.
Ltac SwitchAbsApart :=
  apply map_join_merge;apply map_disjoint;let k:=fresh "key" in intro k;destruct k;vm_compute;auto.
Lemma SwitchAbstractSpatial : forall ts es n,
  SwitchState emp (SwitchAbstract ts es n) |= V293_shared_fields SwitchOld ts es n.
Proof.
  intros ts es n. unfold V293_shared_fields,SwitchAbstract.
  repeat (eapply SwitchStar with (m1:=emp) (m2:=emp);
    [apply map_join_emp | SwitchAbsApart | split;reflexivity | ]).
  split;reflexivity.
Qed.
Lemma SwitchPointerSpatial : SwitchState SwitchPointer emp |=
  GV OSTCBCur @ (Tptr Tvoid) |-> Vptr SwitchOld.
Proof.
  exists 90%positive. eapply SwitchStar with (m1:=emp) (m2:=SwitchPointer) (o1:=emp) (o2:=emp).
  - apply map_join_comm;apply map_join_emp.
  - apply map_join_emp.
  - exists 90%positive. split;[vm_compute;reflexivity | ]. repeat split;reflexivity.
  - split;[apply V293_encoded_memory_mapsto | reflexivity].
Qed.
Lemma SwitchFlagsSpatial : SwitchState emp emp |= V293_shared_flags.
Proof.
  unfold V293_shared_flags.
  eapply SwitchStar with (m1:=emp) (m2:=emp) (o1:=emp) (o2:=emp);
    [apply map_join_emp | apply map_join_emp | | exists INUM;repeat split;reflexivity].
  eapply SwitchStar with (m1:=emp) (m2:=emp) (o1:=emp) (o2:=emp);
    [apply map_join_emp | apply map_join_emp | | repeat split;reflexivity].
  exists (fun _:hid=>false). repeat split;reflexivity.
Qed.
Theorem SwitchLiteralOwnedEntry : forall ts es n,
  SwitchState (SwitchMemory n) (SwitchAbstract ts es n) |= V293_shared_flags **
    ((GV OSTCBCur @ (Tptr Tvoid) |-> Vptr SwitchOld) **
      V293_time_switch_fields 80%positive SwitchOld ts es n).
Proof.
  intros ts es n.
  eapply SwitchStar with (m1:=emp) (m2:=SwitchMemory n) (o1:=emp) (o2:=SwitchAbstract ts es n).
  - apply map_join_comm;apply map_join_emp.
  - apply map_join_comm;apply map_join_emp.
  - apply SwitchFlagsSpatial.
  - eapply SwitchStar with (m1:=SwitchPointer) (m2:=SwitchClock n) (o1:=emp) (o2:=SwitchAbstract ts es n).
    + apply map_join_merge. apply map_disjoint. intros [b i].
      destruct (Pos.eq_dec b 90%positive);[subst b;right;left | left].
      all:unfold SwitchPointer,SwitchClock,SwitchBytes;
        rewrite V293_encoded_memory_outside by (left;congruence);reflexivity.
    + apply map_join_comm;apply map_join_emp.
    + exact SwitchPointerSpatial.
    + unfold V293_time_switch_fields.
      eapply SwitchStar with (m1:=emp) (m2:=SwitchClock n) (o1:=SwitchAbstract ts es n) (o2:=emp).
      * apply map_join_comm;apply map_join_emp.
      * apply map_join_emp.
      * apply SwitchAbstractSpatial.
      * split;[apply V293_encoded_memory_mapsto | reflexivity].
Qed.
Theorem SwitchLiteralSWINVEntry : forall ts es n,
  SwitchState (SwitchMemory n) (SwitchAbstract ts es n) |= SWINVt (V293_time_shared_inv 80%positive) SwitchOld.
Proof.
  intros ts es n. apply V293_time_switch_full_close.
  pose proof (SwitchLiteralOwnedEntry ts es n) as H.
  unfold V293_time_switch_full. sep auto.
Qed.
Theorem SwitchLiteralExecution : forall ts es n,
  exists Mf,
    store (Tptr Tvoid) (SwitchMemory n) (90%positive,0%Z) (Vptr SwitchNew)=Some Mf /\
    SwitchState Mf (set (SwitchAbstract ts es n) curtid (oscurt SwitchNew)) |=
      SWINVt (V293_time_shared_inv 80%positive) SwitchNew /\
    get (set (SwitchAbstract ts es n) curtid (oscurt SwitchNew)) curtid=Some(oscurt SwitchNew) /\
    get (set (SwitchAbstract ts es n) curtid (oscurt SwitchNew)) abstcblsid=Some(abstcblist ts) /\
    get (set (SwitchAbstract ts es n) curtid (oscurt SwitchNew)) absecblsid=Some(absecblist es) /\
    get (set (SwitchAbstract ts es n) curtid (oscurt SwitchNew)) ostmid=Some(ostm n) /\
    load (Tptr Tvoid) Mf (90%positive,0%Z)=Some(Vptr SwitchNew) /\
    load Tint32 Mf (80%positive,0%Z)=Some(Vint32 n).
Proof.
  intros ts es n. apply (V293_time_owned_switch 80%positive SwitchOld SwitchNew ts es n).
  - apply SwitchLiteralOwnedEntry.
  - vm_compute;reflexivity.
Qed.
Definition SwitchLiveTasks : TcbMod.map := sig SwitchOld (Int.one,rdy,Vnull).
Theorem SwitchLiveTaskBranch : indom SwitchLiveTasks SwitchOld /\ SwitchOld<>SwitchNew.
Proof.
  split.
  - exists (Int.one,rdy,Vnull). apply map_get_sig.
  - intro E. inversion E.
Qed.
Theorem SwitchDeadTaskBranch : ~indom (emp:TcbMod.map) SwitchOld /\ SwitchOld<>SwitchNew.
Proof.
  split.
  - intros [v H]. vm_compute in H;discriminate.
  - intro E. inversion E.
Qed.
Theorem SwitchBothTaskMaps : forall n,
  (exists Mf, store (Tptr Tvoid) (SwitchMemory n) (90%positive,0%Z) (Vptr SwitchNew)=Some Mf /\
    SwitchState Mf (set (SwitchAbstract SwitchLiveTasks (emp:EcbMod.map) n) curtid (oscurt SwitchNew)) |=
      SWINVt (V293_time_shared_inv 80%positive) SwitchNew /\
    load Tint32 Mf (80%positive,0%Z)=Some(Vint32 n)) /\
  (exists Mf, store (Tptr Tvoid) (SwitchMemory n) (90%positive,0%Z) (Vptr SwitchNew)=Some Mf /\
    SwitchState Mf (set (SwitchAbstract (emp:TcbMod.map) (emp:EcbMod.map) n) curtid (oscurt SwitchNew)) |=
      SWINVt (V293_time_shared_inv 80%positive) SwitchNew /\
    load Tint32 Mf (80%positive,0%Z)=Some(Vint32 n)).
Proof.
  intro n. split.
  - destruct (SwitchLiteralExecution SwitchLiveTasks (emp:EcbMod.map) n) as [Mf [S [R [C [T [E [N [P Clock]]]]]]]].
    exists Mf. repeat split;assumption.
  - destruct (SwitchLiteralExecution (emp:TcbMod.map) (emp:EcbMod.map) n) as [Mf [S [R [C [T [E [N [P Clock]]]]]]]].
    exists Mf. repeat split;assumption.
Qed.
Print Assumptions SwitchLiteralOwnedEntry.
Print Assumptions SwitchLiteralSWINVEntry.
Print Assumptions SwitchLiteralExecution.
Print Assumptions SwitchLiveTaskBranch.
Print Assumptions SwitchDeadTaskBranch.
Print Assumptions SwitchBothTaskMaps.
