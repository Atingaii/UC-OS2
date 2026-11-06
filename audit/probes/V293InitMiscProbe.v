(* Independent finite nonzero/raw-undef startup fixture, not OSInit reachability. *)
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
  (fun d e => set e (init_name d) (init_block d,init_type d)) emp InitSlots.
Definition InitState M O : RstateOP :=
  (InitGE,emp,M,(fun _=>false),(false,[],[]),O,spec_done None).
Definition InitBytes b tp v := V293_encoded_memory b 0%Z true (encode_val tp v).
Definition InitFrame := Amapsto (90%positive,0%Z) (Tptr Tvoid) true Vnull **
  (Amapsto (99%positive,0%Z) Tint32 true (Vint32 (Int.repr 123)) ** Aabsdata ostmid (ostm (Int.repr 57))).
Definition InitFrameMem := merge (InitBytes 90%positive (Tptr Tvoid) Vnull)
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
  unfold InitFrameMem,InitBytes;
  repeat rewrite map_merge_semp by reflexivity;
  repeat rewrite V293_encoded_memory_outside by (left;congruence);reflexivity.
Lemma InitFrameEntry : InitState InitFrameMem InitAbs |= InitFrame.
Proof.
  unfold InitFrame,InitFrameMem.
  eapply InitStar with (m1:=InitBytes 90%positive (Tptr Tvoid) Vnull)
    (m2:=InitBytes 99%positive Tint32 (Vint32 (Int.repr 123))) (o1:=emp) (o2:=InitAbs).
  - InitApart 90%positive.
  - apply map_join_comm;apply map_join_emp.
  - split;[apply V293_encoded_memory_mapsto | reflexivity].
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
(* Literal AST oracle is independent of the recursive production generator. *)
Theorem InitLiteralAST : V293_InitMisc_updates 1001%Z 1002%Z 1003%Z 1004%Z 1005%Z 1006%Z 1007%Z 1008%Z 1009%Z 1010%Z =
  sseq (sassign (evar 1001%Z) (ecast (econst32 Int.zero) Tint32))
  (sseq (sassign (evar 1002%Z) (ecast (econst32 Int.zero) Tint8))
  (sseq (sassign (evar 1003%Z) (ecast (econst32 Int.zero) Tint8))
  (sseq (sassign (evar 1004%Z) (ecast (econst32 Int.zero) Tint8))
  (sseq (sassign (evar 1005%Z) (ecast (econst32 Int.zero) Tint8))
  (sseq (sassign (evar 1006%Z) (ecast (econst32 Int.zero) Tint32))
  (sseq (sassign (evar 1007%Z) (ecast (econst32 Int.zero) Tint32))
  (sseq (sassign (evar 1008%Z) (ecast (econst32 Int.zero) Tint32))
  (sseq (sassign (evar 1009%Z) (ecast (econst32 Int.zero) Tint32))
  (sseq (sassign (evar 1010%Z) (ecast (econst32 Int.zero) Tint8)) (sskip None)))))))))).
Proof. reflexivity. Qed.
Theorem InitConcreteCall : forall P ks caller,
  P 2000%Z = Some (V293_InitMisc_function 1001%Z 1002%Z 1003%Z 1004%Z 1005%Z 1006%Z 1007%Z 1008%Z 1009%Z 1010%Z) ->
  exists Mf,
    cstepstar P (curs (scall 2000%Z nil),(kenil,ks)) (InitGE,caller,InitMem InitCells)
      (curs (sskip None),(kenil,ks)) (InitGE,caller,Mf) /\
    InitState Mf InitAbs |= V293_init_resources InitSlots true InitFrame.
Proof.
  intros P ks caller Program. eapply V293_OS_InitMisc_call_return;[exact Program | exact InitLiteralEntry].
Qed.
(* Check all ten literal final cells, not a conclusion derived by re-running
   the same model. Final abstract time deliberately remains 57: OS_InitMisc
   itself has no abstract primitive and does NOT establish the runtime Inv. *)
Definition InitAllZero M :=
  load Tint32 M (81%positive,0%Z)=Some (Vint32 Int.zero) /\
  load Tint8 M (82%positive,0%Z)=Some (Vint32 Int.zero) /\
  load Tint8 M (83%positive,0%Z)=Some (Vint32 Int.zero) /\
  load Tint8 M (84%positive,0%Z)=Some (Vint32 Int.zero) /\
  load Tint8 M (85%positive,0%Z)=Some (Vint32 Int.zero) /\
  load Tint32 M (86%positive,0%Z)=Some (Vint32 Int.zero) /\
  load Tint32 M (87%positive,0%Z)=Some (Vint32 Int.zero) /\
  load Tint32 M (88%positive,0%Z)=Some (Vint32 Int.zero) /\
  load Tint32 M (89%positive,0%Z)=Some (Vint32 Int.zero) /\
  load Tint8 M (91%positive,0%Z)=Some (Vint32 Int.zero).
Theorem InitLiteralFinal : forall M,
  InitState M InitAbs |= V293_init_resources InitSlots true InitFrame ->
  InitAllZero M /\
  load (Tptr Tvoid) M (90%positive,0%Z)=Some Vnull /\
  load Tint32 M (99%positive,0%Z)=Some (Vint32 (Int.repr 123)) /\
  get InitAbs ostmid=Some (ostm (Int.repr 57)).
Proof.
  intros M Owned.
  pose proof (V293_init_readback InitSlots InitFrame _ InitTypes Owned) as Reads.
  pose proof (V293_init_preserved_frame InitSlots true InitFrame _ Owned) as Frame.
  split.
  - unfold InitAllZero. repeat split;
      match goal with |- load ?tp M (?b,0%Z) = _ =>
        exact (Reads (Build_V293_init_slot _ tp b) ltac:(unfold InitSlots,V293_InitMisc_slots;cbn;auto 12)) end.
  - split.
    + change (load (Tptr Tvoid) (getmem (InitState M InitAbs)) (90%positive,0%Z)=Some Vnull).
      eapply V293_record_star_load_r;[ | exact Frame].
      eapply V293_record_star_load_l. intros st [Points Empty].
      eapply mapstoval_load;[reflexivity | exact Points].
    + split.
      * change (load Tint32 (getmem (InitState M InitAbs)) (99%positive,0%Z)=Some (Vint32 (Int.repr 123))).
        eapply V293_record_star_load_r;[ | exact Frame].
        eapply V293_record_star_load_r. eapply V293_record_star_load_l.
        intros st [Points Empty]. eapply mapstoval_load;[reflexivity | exact Points].
      * vm_compute;reflexivity.
Qed.
Theorem InitFullLiteralExecution : forall P ks caller,
  P 2000%Z = Some (V293_InitMisc_function 1001%Z 1002%Z 1003%Z 1004%Z 1005%Z 1006%Z 1007%Z 1008%Z 1009%Z 1010%Z) ->
  exists Mf,
    cstepstar P (curs (scall 2000%Z nil),(kenil,ks)) (InitGE,caller,InitMem InitCells)
      (curs (sskip None),(kenil,ks)) (InitGE,caller,Mf) /\
    InitAllZero Mf /\ load (Tptr Tvoid) Mf (90%positive,0%Z)=Some Vnull /\
    load Tint32 Mf (99%positive,0%Z)=Some (Vint32 (Int.repr 123)).
Proof.
  intros P ks caller Program. destruct (InitConcreteCall P ks caller Program) as (Mf & Exec & Owned).
  destruct (InitLiteralFinal Mf Owned) as (Zeros & Null & Sentinel & Abstract).
  exists Mf. split;[exact Exec | ]. split;[exact Zeros | ]. split;assumption.
Qed.
Print Assumptions InitLiteralEntry.
Print Assumptions InitLiteralAST.
Print Assumptions InitLiteralFinal.
Print Assumptions InitFullLiteralExecution.
