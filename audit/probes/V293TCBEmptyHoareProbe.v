(* Independent literal, spatially satisfiable body precondition. This fixture
   does not instantiate a kernel global invariant or startup state. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.certiucos.v293.proofs.V293TCBEmptyHoare.
Require Import CertiOS.certiucos.v293.code.V293OSTCBInitFunction.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewWitness.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List.
Import ListNotations.
Definition EmptyGE : env := set (sig 91%Z (401%positive,Tptr V293_tcb_type))
 OSTCBCur (402%positive,Tptr Tvoid).
Definition EmptyLE : env := set (sig 108%Z (201%positive,Tptr V293_tcb_type))
 109%Z (202%positive,Tint32).
Definition EmptyTid : tid := (301%positive,Int.repr 8).
Definition EmptyBytes b permission tp v := V293_encoded_memory b 0 permission (encode_val tp v).
Definition EmptyCPU := EmptyBytes 202%positive true Tint32 Vundef.
Definition EmptyPointer := EmptyBytes 201%positive true (Tptr V293_tcb_type) Vundef.
Definition EmptyFree := EmptyBytes 401%positive false (Tptr V293_tcb_type) Vnull.
Definition EmptyCurrent := EmptyBytes 402%positive false (Tptr Tvoid) (Vptr EmptyTid).
Definition EmptySentinel := EmptyBytes 601%positive true Tint8 (Vint32(Int.repr 77)).
Definition EmptyMemory := merge EmptyCPU (merge EmptyPointer
 (merge EmptyFree (merge EmptyCurrent EmptySentinel))).
Definition EmptyState M cs : RstateOP :=
 (EmptyGE,EmptyLE,M,(fun _=>false),(false,[],cs),(emp:osabst),spec_done None).
Definition EmptyR := CurTid EmptyTid ** LINV V293_witness_li EmptyTid [] **
 Amapsto (601%positive,0%Z) Tint8 true (Vint32(Int.repr 77)).

Lemma EmptyStar : forall m1 m2 m cs p q,
 join m1 m2 m -> EmptyState m1 cs |= p -> EmptyState m2 cs |= q ->
 EmptyState m cs |= p ** q.
Proof.
 intros. apply sat_split'. exists m1. exists m2.
 exists(emp:osabst). exists(emp:osabst).
 split;[exact H | ]. split;[apply map_join_emp | ]. split;assumption.
Qed.
Lemma EmptyBindings : forall cs, EmptyState emp cs |=
 V293_tcb_empty_bindings 401%positive 201%positive 202%positive.
Proof.
 intro cs. unfold V293_tcb_empty_bindings. repeat split.
 - exists 201%positive. split;[vm_compute;reflexivity | ]. repeat split;reflexivity.
 - exists 202%positive. split;[vm_compute;reflexivity | ]. repeat split;reflexivity.
 - exists 401%positive. split;[vm_compute;reflexivity | ]. repeat split;reflexivity.
 - intros [v H]. vm_compute in H. discriminate H.
Qed.
Lemma EmptyCurrentSpatial : forall cs, EmptyState EmptyCurrent cs |= CurTid EmptyTid.
Proof.
 intro cs. exists Tvoid. exists 402%positive.
 eapply EmptyStar with (m1:=emp) (m2:=EmptyCurrent).
 - apply map_join_comm;apply map_join_emp.
 - exists 402%positive. split;[vm_compute;reflexivity | ]. repeat split;reflexivity.
 - split;[apply V293_encoded_memory_mapsto|reflexivity].
Qed.
Lemma EmptyLInvSpatial : forall cs, EmptyState emp cs |= LINV V293_witness_li EmptyTid [].
Proof.
 intro cs. unfold LINV. apply astar_comm. apply astar_l_apure_intro.
 - split;reflexivity.
 - apply V293_witness_li_good.
Qed.
Ltac EmptyApart b :=
 apply map_join_merge;apply map_disjoint;intros [other offset];
 destruct(Pos.eq_dec other b);[subst other;right;left|left];
 unfold EmptyCPU,EmptyPointer,EmptyFree,EmptyCurrent,EmptySentinel,EmptyBytes;
 repeat first [rewrite map_merge_semp by reflexivity |
 rewrite V293_encoded_memory_outside by (left;congruence)];reflexivity.
Lemma EmptyRSpatial : forall cs,
 EmptyState (merge EmptyCurrent EmptySentinel) cs |= EmptyR.
Proof.
 intro cs. unfold EmptyR.
 eapply EmptyStar with (m1:=EmptyCurrent) (m2:=EmptySentinel).
 - EmptyApart 402%positive.
 - apply EmptyCurrentSpatial.
 - eapply EmptyStar with (m1:=emp) (m2:=EmptySentinel).
   + apply map_join_comm;apply map_join_emp.
   + apply EmptyLInvSpatial.
   + split;[apply V293_encoded_memory_mapsto|reflexivity].
Qed.
Lemma EmptyRGood : GoodFrm EmptyR.
Proof. cbn [EmptyR CurTid LINV V293_witness_li GoodFrm]. repeat split;exact I. Qed.
Lemma EmptyRCurLINV : EmptyR ==> CurLINV V293_witness_li EmptyTid.
Proof.
 intros s HS. unfold CurLINV. exists([]:list logicvar).
 unfold EmptyR in HS. clear -HS. sep auto.
Qed.
Theorem EmptyLiteralEntry : forall cs,
 EmptyState EmptyMemory cs |=
 V293_tcb_empty_state 401%positive 201%positive 202%positive Vundef Vundef EmptyR
 (spec_done None) (fun _=>false) [] cs.
Proof.
 intro cs. unfold V293_tcb_empty_state,V293_tcb_empty_resources.
 eapply EmptyStar with (m1:=emp) (m2:=EmptyMemory).
 - apply map_join_comm;apply map_join_emp.
 - split;[reflexivity | ]. split;reflexivity.
 - eapply EmptyStar with (m1:=emp) (m2:=EmptyMemory).
   + apply map_join_comm;apply map_join_emp.
   + repeat (eapply EmptyStar with (m1:=emp) (m2:=emp);
       [apply map_join_emp|split;[reflexivity|split;reflexivity] | ]).
     split;[reflexivity | ]. split;reflexivity.
   + eapply EmptyStar with (m1:=emp) (m2:=EmptyMemory).
     * apply map_join_comm;apply map_join_emp.
     * apply EmptyBindings.
     * assert (Ordered:EmptyState EmptyMemory cs |=
        Amapsto (202%positive,0%Z) Tint32 true Vundef **
        (Amapsto (201%positive,0%Z) (Tptr V293_tcb_type) true Vundef **
        (Amapsto (401%positive,0%Z) (Tptr V293_tcb_type) false Vnull ** EmptyR))).
       { unfold EmptyMemory.
         eapply EmptyStar with (m1:=EmptyCPU)
          (m2:=merge EmptyPointer (merge EmptyFree (merge EmptyCurrent EmptySentinel))).
         - EmptyApart 202%positive.
         - split;[apply V293_encoded_memory_mapsto|reflexivity].
         - eapply EmptyStar with (m1:=EmptyPointer)
            (m2:=merge EmptyFree (merge EmptyCurrent EmptySentinel)).
           + EmptyApart 201%positive.
           + split;[apply V293_encoded_memory_mapsto|reflexivity].
           + eapply EmptyStar with (m1:=EmptyFree) (m2:=merge EmptyCurrent EmptySentinel).
             * EmptyApart 401%positive.
             * split;[apply V293_encoded_memory_mapsto|reflexivity].
             * apply EmptyRSpatial. }
       clear -Ordered. sep auto.
Qed.

Definition EmptyBodyChecked : forall Spec sd I hi hc cs,
 InfRules Spec sd V293_witness_li I
 (fun result => [|result=Some(Vint32(Int.repr 66))|] **
  V293_tcb_empty_state 401%positive 201%positive 202%positive Vnull (Vint32 Int.zero)
   EmptyR (spec_done None) (fun _=>false) [] cs) Afalse
 (V293_tcb_empty_state 401%positive 201%positive 202%positive Vundef Vundef
  EmptyR (spec_done None) (fun _=>false) [] cs)
 (V293_TCBInit_function_body hi hc) Afalse EmptyTid.
Proof. intros. apply V293_OS_TCBInit_empty_body_hoare;[apply EmptyRGood|apply EmptyRCurLINV]. Qed.
Definition EmptyNoHookSpec : funspec := fun _=>None.
Theorem EmptyBodyNoHook : forall sd I hi hc cs,
 InfRules EmptyNoHookSpec sd V293_witness_li I
 (V293_tcb_empty_post 401%positive 201%positive 202%positive EmptyR
  (spec_done None) (fun _=>false) [] cs) Afalse
 (V293_tcb_empty_state 401%positive 201%positive 202%positive Vundef Vundef
  EmptyR (spec_done None) (fun _=>false) [] cs)
 (V293_TCBInit_function_body hi hc) Afalse EmptyTid.
Proof. intros. apply EmptyBodyChecked. Qed.
Theorem EmptyPostRejectZero : forall s cs,
 ~s |= V293_tcb_empty_post 401%positive 201%positive 202%positive EmptyR
 (spec_done None) (fun _=>false) [] cs (Some(Vint32 Int.zero)).
Proof.
 intros s cs H. apply astar_l_apure_elim in H. destruct H as [Bad _]. discriminate Bad.
Qed.
(* Semantic exclusion of the success guard, not a claim about executing it. *)
Theorem EmptyGuardNotTrue : forall bf bp bc cpu R aop isr is cs s,
 s |= V293_tcb_empty_state bf bp bc Vnull cpu R aop isr is cs ->
 ~s |= Aistrue(eunop oppsite(V293_task_prio_null_test(evar 108%Z))).
Proof.
 intros bf bp bc cpu R aop isr is cs s HS [v [V B]].
 destruct (V293_tcb_empty_guard_eval _ _ _ _ _ _ _ _ _ _ HS) as [Z _].
 rewrite Z in V. inversion V;subst v. discriminate B.
Qed.
Print Assumptions EmptyLiteralEntry.
Print Assumptions EmptyBodyChecked.
Print Assumptions EmptyBodyNoHook.
Print Assumptions EmptyPostRejectZero.
Print Assumptions EmptyGuardNotTrue.
