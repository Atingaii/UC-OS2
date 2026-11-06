(* Independent inhabited Hoare fixture; NOT startup reachability. *)
Require Import CertiOS.certiucos.v293.proofs.V293InitMiscHoare.
Require Import CertiOS.framework.proof.soundness.
Require CertiOS.framework.proof.simulation.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.code.V293OSInitMisc.
Require Import CertiOS.certiucos.v293.proofs.V293InitMisc.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.
Definition InitSlots := V293_InitMisc_slots 1001%Z 1002%Z 1003%Z 1004%Z 1005%Z
  1006%Z 1007%Z 1008%Z 1009%Z 1010%Z 81%positive 82%positive 83%positive
  84%positive 85%positive 86%positive 87%positive 88%positive 89%positive 91%positive.
Definition InitGE : env := fold_right
  (fun d e => set e (init_name d) (init_block d,init_type d)) (sig OSTCBCur (90%positive,Tptr Tvoid)) InitSlots.
Definition InitState M O : RstateOP :=
  (InitGE,emp,M,(fun _=>false),(false,[],[]),O,spec_done None).
Definition InitBytes b tp v := V293_encoded_memory b 0%Z true (encode_val tp v).
Definition InitFrame := CurLINV V293_witness_li (92%positive,Int.zero) **
  (Amapsto (99%positive,0%Z) Tint32 true (Vint32 (Int.repr 123)) ** Aabsdata ostmid (ostm (Int.repr 57))).
Definition InitCurrent := V293_encoded_memory 90%positive 0%Z false
 (encode_val (Tptr Tvoid) (Vptr (92%positive,Int.zero))).
Definition InitFrameMem := merge (InitCurrent)
  (InitBytes 99%positive Tint32 (Vint32 (Int.repr 123))).
Definition InitAbs : osabst := sig ostmid (ostm (Int.repr 57)).
Fixpoint InitMem (cells : list (block * type * val)) : mem :=
  match cells with
  | [] => InitFrameMem
  | (b,tp,v)::tail => merge (InitBytes b tp v) (InitMem tail)
  end.
Definition InitCells : list (block * type * val) :=
  [(81%positive,Tint32,Vint32 (Int.repr 7)); (82%positive,Tint8,Vint32 (Int.repr 3));
   (83%positive,Tint8,Vint32 (Int.repr 2)); (84%positive,Tint8,Vint32 (Int.repr 9));
   (85%positive,Tint8,Vint32 Int.one); (86%positive,Tint32,Vint32 (Int.repr 42));
   (87%positive,Tint32,Vundef); (88%positive,Tint32,Vundef);
   (89%positive,Tint32,Vint32 (Int.repr 100)); (91%positive,Tint8,Vint32 Int.one)].
Lemma InitStar : forall m1 m2 m o1 o2 o p q,
  join m1 m2 m -> join o1 o2 o -> InitState m1 o1 |= p -> InitState m2 o2 |= q ->
  InitState m o |= p ** q.
Proof.
  intros. exists m1. exists m2. exists m. exists o1. exists o2. exists o.
  repeat first [assumption | reflexivity | split].
Qed.
Lemma InitCell : forall x tp b v,
  get InitGE x=Some (b,tp) ->
  InitState (InitBytes b tp v) emp |=
    V293_init_binding (Build_V293_init_slot x tp b) ** V293_init_memory (Build_V293_init_slot x tp b) false.
Proof.
  intros x tp b v G. eapply InitStar with (m1:=emp) (m2:=InitBytes b tp v) (o1:=emp) (o2:=emp).
  - apply map_join_comm;apply map_join_emp.
  - apply map_join_emp.
  - split.
    + exists b. split;[exact G | ]. repeat split;reflexivity.
    + split;[intros [w E];vm_compute in E;discriminate | repeat split;reflexivity].
  - exists v. split;[apply V293_encoded_memory_mapsto | reflexivity].
Qed.
Ltac InitApart b :=
  apply map_join_merge;apply map_disjoint;intros [other off];
  destruct (Pos.eq_dec other b);[subst other;right;left | left];
  unfold InitFrameMem,InitBytes,InitCurrent;
  repeat rewrite map_merge_semp by reflexivity;
  repeat rewrite V293_encoded_memory_outside by (left;congruence);reflexivity.
Lemma InitFrameEntry : InitState InitFrameMem InitAbs |= InitFrame.
Proof.
  unfold InitFrame,InitFrameMem.
  eapply InitStar with (m1:=InitCurrent)
    (m2:=InitBytes 99%positive Tint32 (Vint32 (Int.repr 123))) (o1:=emp) (o2:=InitAbs).
  - InitApart 90%positive.
  - apply map_join_comm;apply map_join_emp.
  - unfold CurLINV. exists (nil:list logicvar).
    eapply InitStar with (m1:=InitCurrent)
      (m2:=emp) (o1:=emp) (o2:=emp); [apply map_join_emp|apply map_join_emp | | ].
    + exists Tvoid. exists 90%positive.
      eapply InitStar with (m1:=emp) (m2:=InitCurrent)
        (o1:=emp) (o2:=emp).
      * apply map_join_comm; apply map_join_emp.
      * apply map_join_emp.
      * exists 90%positive. split; [vm_compute; reflexivity | ]. repeat split; reflexivity.
      * split; [apply V293_encoded_memory_mapsto|reflexivity].
    + eapply InitStar with (m1:=emp) (m2:=emp) (o1:=emp) (o2:=emp);
        [apply map_join_emp|apply map_join_emp | | exact I].
      unfold LINV,V293_witness_li.
      eapply InitStar with (m1:=emp) (m2:=emp) (o1:=emp) (o2:=emp);
        [apply map_join_emp|apply map_join_emp|repeat split;reflexivity | ].
      split; [apply V293_witness_li_good|repeat split;reflexivity].
  - eapply InitStar with (m1:=InitBytes 99%positive Tint32 (Vint32 (Int.repr 123)))
      (m2:=emp) (o1:=emp) (o2:=InitAbs).
    + apply map_join_emp.
    + apply map_join_comm;apply map_join_emp.
    + split;[apply V293_encoded_memory_mapsto | reflexivity].
    + split;reflexivity.
Qed.
Theorem InitLiteralEntry : InitState (InitMem InitCells) InitAbs |= V293_init_resources InitSlots false InitFrame.
Proof.
  unfold InitSlots,V293_InitMisc_slots,InitCells.
  cbn [V293_init_resources InitMem].
  eapply InitStar with (m1:=InitBytes 81%positive Tint32 (Vint32 (Int.repr 7))) (o1:=emp) (o2:=InitAbs);
    [InitApart 81%positive | apply map_join_comm;apply map_join_emp | apply InitCell;vm_compute;reflexivity | ].
  eapply InitStar with (m1:=InitBytes 82%positive Tint8 (Vint32 (Int.repr 3))) (o1:=emp) (o2:=InitAbs);
    [InitApart 82%positive | apply map_join_comm;apply map_join_emp | apply InitCell;vm_compute;reflexivity | ].
  eapply InitStar with (m1:=InitBytes 83%positive Tint8 (Vint32 (Int.repr 2))) (o1:=emp) (o2:=InitAbs);
    [InitApart 83%positive | apply map_join_comm;apply map_join_emp | apply InitCell;vm_compute;reflexivity | ].
  eapply InitStar with (m1:=InitBytes 84%positive Tint8 (Vint32 (Int.repr 9))) (o1:=emp) (o2:=InitAbs);
    [InitApart 84%positive | apply map_join_comm;apply map_join_emp | apply InitCell;vm_compute;reflexivity | ].
  eapply InitStar with (m1:=InitBytes 85%positive Tint8 (Vint32 Int.one)) (o1:=emp) (o2:=InitAbs);
    [InitApart 85%positive | apply map_join_comm;apply map_join_emp | apply InitCell;vm_compute;reflexivity | ].
  eapply InitStar with (m1:=InitBytes 86%positive Tint32 (Vint32 (Int.repr 42))) (o1:=emp) (o2:=InitAbs);
    [InitApart 86%positive | apply map_join_comm;apply map_join_emp | apply InitCell;vm_compute;reflexivity | ].
  eapply InitStar with (m1:=InitBytes 87%positive Tint32 (Vundef)) (o1:=emp) (o2:=InitAbs);
    [InitApart 87%positive | apply map_join_comm;apply map_join_emp | apply InitCell;vm_compute;reflexivity | ].
  eapply InitStar with (m1:=InitBytes 88%positive Tint32 (Vundef)) (o1:=emp) (o2:=InitAbs);
    [InitApart 88%positive | apply map_join_comm;apply map_join_emp | apply InitCell;vm_compute;reflexivity | ].
  eapply InitStar with (m1:=InitBytes 89%positive Tint32 (Vint32 (Int.repr 100))) (o1:=emp) (o2:=InitAbs);
    [InitApart 89%positive | apply map_join_comm;apply map_join_emp | apply InitCell;vm_compute;reflexivity | ].
  eapply InitStar with (m1:=InitBytes 91%positive Tint8 (Vint32 Int.one)) (o1:=emp) (o2:=InitAbs);
    [InitApart 91%positive | apply map_join_comm;apply map_join_emp | apply InitCell;vm_compute;reflexivity | ].
  exact InitFrameEntry.
Qed.
Lemma InitTypes : Forall V293_init_scalar InitSlots.
Proof.
  unfold InitSlots,V293_InitMisc_slots.
  repeat (apply Forall_cons;[unfold V293_init_scalar;cbn;auto | ]);apply Forall_nil.
Qed.

Definition InitBody := sseq (V293_InitMisc_updates 1001%Z 1002%Z 1003%Z 1004%Z 1005%Z
  1006%Z 1007%Z 1008%Z 1009%Z 1010%Z) sret.
Theorem InitHoareEntry : InitState (InitMem InitCells) InitAbs |=
  <||spec_done None||> ** V293_init_resources InitSlots false InitFrame.
Proof.
 eapply InitStar with (m1:=emp) (o1:=emp) (o2:=InitAbs);
 [apply map_join_comm;apply map_join_emp|apply map_join_comm;apply map_join_emp|
 repeat split;reflexivity|exact InitLiteralEntry].
Qed.
Theorem InitHoareInstance : forall Spec sd I,
 InfRules Spec sd V293_witness_li I
  (V293_InitMisc_post InitSlots (spec_done None) InitFrame) Afalse
  (<||spec_done None||> ** V293_init_resources InitSlots false InitFrame)
  InitBody Afalse (92%positive,Int.zero).
Proof.
 intros. apply V293_OS_InitMisc_body_hoare.
 unfold InitFrame. apply V293_star_CurLINV_l. intros s Hs;exact Hs.
Qed.
Theorem InitSemanticInstance : forall Spec sd I,
 simulation.RuleSem Spec sd V293_witness_li I
  (V293_InitMisc_post InitSlots (spec_done None) InitFrame) Afalse
  (<||spec_done None||> ** V293_init_resources InitSlots false InitFrame)
  InitBody Afalse (92%positive,Int.zero).
Proof. intros. apply RuleSound. apply InitHoareInstance. Qed.
Theorem InitActualInvariant : InitState (InitMem InitCells) InitAbs |=
 CurLINV V293_witness_li (92%positive,Int.zero).
Proof.
 eapply V293_init_resources_CurLINV; [ | exact InitLiteralEntry].
 unfold InitFrame. apply V293_star_CurLINV_l. intros s Hs;exact Hs.
Qed.
Theorem InitAllPostReads : forall M,
 InitState M InitAbs |= V293_init_resources InitSlots true InitFrame ->
 forall d, In d InitSlots -> load (init_type d) M (init_block d,0%Z)=Some(Vint32 Int.zero).
Proof. intros M H d HD. exact (V293_init_readback InitSlots InitFrame _ InitTypes H d HD). Qed.
Print Assumptions InitHoareEntry.
Print Assumptions InitSemanticInstance.
