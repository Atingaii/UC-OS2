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
Require Import CertiOS.certiucos.v293.proofs.V293TCBEmptyInternal.
Require Import Coq.Lists.List.
Import ListNotations.
Definition InternalGE : env := set (sig 91%Z (401%positive,Tptr V293_tcb_type))
 OSTCBCur (402%positive,Tptr Tvoid).
Definition InternalLE : env := set (set (set (set (set (set (set (set
 (sig 107%Z (207%positive,Tint16)) 106%Z (206%positive,Tptr Tvoid))
 105%Z (205%positive,Tint32)) 104%Z (204%positive,Tint16))
 103%Z (203%positive,Tptr Tint32)) 102%Z (202%positive,Tptr Tint32))
 101%Z (201%positive,Tint8)) 108%Z (208%positive,Tptr V293_tcb_type))
 109%Z (209%positive,Tint32).
Definition InternalTid : tid := (301%positive,Int.repr 8).
Definition InternalBytes b permission tp v := V293_encoded_memory b 0 permission (encode_val tp v).
Definition InternalCPU := InternalBytes 209%positive true Tint32 Vundef.
Definition InternalPointer := InternalBytes 208%positive true (Tptr V293_tcb_type) Vundef.
Definition InternalFree := InternalBytes 401%positive false (Tptr V293_tcb_type) Vnull.
Definition InternalCurrent := InternalBytes 402%positive false (Tptr Tvoid) (Vptr InternalTid).
Definition InternalSentinel := InternalBytes 601%positive true Tint8 (Vint32(Int.repr 77)).
Definition InternalMemory := merge InternalCPU (merge InternalPointer
 (merge InternalFree (merge InternalCurrent InternalSentinel))).
Definition InternalState M cs : RstateOP :=
 (InternalGE,InternalLE,M,(fun _=>false),(false,[],cs),(emp:osabst),spec_done None).
Definition InternalR := CurTid InternalTid ** LINV V293_witness_li InternalTid [] **
 Amapsto (601%positive,0%Z) Tint8 true (Vint32(Int.repr 77)).

Lemma InternalStar : forall m1 m2 m cs p q,
 join m1 m2 m -> InternalState m1 cs |= p -> InternalState m2 cs |= q ->
 InternalState m cs |= p ** q.
Proof.
 intros. apply sat_split'. exists m1. exists m2.
 exists(emp:osabst). exists(emp:osabst).
 split;[exact H | ]. split;[apply map_join_emp | ]. split;assumption.
Qed.
Lemma InternalBindings : forall cs, InternalState emp cs |=
 V293_tcb_empty_bindings 401%positive 208%positive 209%positive.
Proof.
 intro cs. unfold V293_tcb_empty_bindings. repeat split.
 - exists 208%positive. split;[vm_compute;reflexivity | ]. repeat split;reflexivity.
 - exists 209%positive. split;[vm_compute;reflexivity | ]. repeat split;reflexivity.
 - exists 401%positive. split;[vm_compute;reflexivity | ]. repeat split;reflexivity.
 - intros [v H]. vm_compute in H. discriminate H.
Qed.
Lemma InternalCurrentSpatial : forall cs, InternalState InternalCurrent cs |= CurTid InternalTid.
Proof.
 intro cs. exists Tvoid. exists 402%positive.
 eapply InternalStar with (m1:=emp) (m2:=InternalCurrent).
 - apply map_join_comm;apply map_join_emp.
 - exists 402%positive. split;[vm_compute;reflexivity | ]. repeat split;reflexivity.
 - split;[apply V293_encoded_memory_mapsto|reflexivity].
Qed.
Lemma InternalLInvSpatial : forall cs, InternalState emp cs |= LINV V293_witness_li InternalTid [].
Proof.
 intro cs. unfold LINV. apply astar_comm. apply astar_l_apure_intro.
 - split;reflexivity.
 - apply V293_witness_li_good.
Qed.
Ltac InternalApart b :=
 apply map_join_merge;apply map_disjoint;intros [other offset];
 destruct(Pos.eq_dec other b);[subst other;right;left|left];
 unfold InternalCPU,InternalPointer,InternalFree,InternalCurrent,InternalSentinel,InternalBytes;
 repeat first [rewrite map_merge_semp by reflexivity |
 rewrite V293_encoded_memory_outside by (left;congruence)];reflexivity.
Lemma InternalRSpatial : forall cs,
 InternalState (merge InternalCurrent InternalSentinel) cs |= InternalR.
Proof.
 intro cs. unfold InternalR.
 eapply InternalStar with (m1:=InternalCurrent) (m2:=InternalSentinel).
 - InternalApart 402%positive.
 - apply InternalCurrentSpatial.
 - eapply InternalStar with (m1:=emp) (m2:=InternalSentinel).
   + apply map_join_comm;apply map_join_emp.
   + apply InternalLInvSpatial.
   + split;[apply V293_encoded_memory_mapsto|reflexivity].
Qed.
Lemma InternalRGood : GoodFrm InternalR.
Proof. cbn [InternalR CurTid LINV V293_witness_li GoodFrm]. repeat split;exact I. Qed.
Lemma InternalRCurLINV : InternalR ==> CurLINV V293_witness_li InternalTid.
Proof.
 intros s HS. unfold CurLINV. exists([]:list logicvar).
 unfold InternalR in HS. clear -HS. sep auto.
Qed.

Lemma InternalRFun : GoodFunAsrt InternalR.
Proof.
 cbn [InternalR CurTid LINV V293_witness_li GoodFunAsrt Agvarmapsto Agvarenv' Aptrmapsto].
 repeat split;intros;repeat split;exact I.
Qed.
Lemma InternalDomain : eq_dom_env InternalLE (getlenvdom V293_tcb_internal_declarations).
Proof.
 unfold eq_dom_env. intros x tp.
 destruct (Z.eq_dec x 109%Z) as [E109|E109].
 { subst x. cbn [V293_tcb_internal_declarations V293_TCBInit_parameters V293_TCBInit_locals revlcons getlenvdom].
   unfold InternalLE. repeat rewrite map_get_set' by congruence. rewrite map_get_set.
   split.
   + intro H. repeat destruct H as [H|H];try discriminate;try contradiction;
     inversion H;subst;eexists;reflexivity.
   + intros [b H]. inversion H;subst. cbn. tauto. }
 destruct (Z.eq_dec x 108%Z) as [E108|E108].
 { subst x. cbn [V293_tcb_internal_declarations V293_TCBInit_parameters V293_TCBInit_locals revlcons getlenvdom].
   unfold InternalLE. repeat rewrite map_get_set' by congruence. rewrite map_get_set.
   split.
   + intro H. repeat destruct H as [H|H];try discriminate;try contradiction;
     inversion H;subst;eexists;reflexivity.
   + intros [b H]. inversion H;subst. cbn. tauto. }
 destruct (Z.eq_dec x 101%Z) as [E101|E101].
 { subst x. cbn [V293_tcb_internal_declarations V293_TCBInit_parameters V293_TCBInit_locals revlcons getlenvdom].
   unfold InternalLE. repeat rewrite map_get_set' by congruence. rewrite map_get_set.
   split.
   + intro H. repeat destruct H as [H|H];try discriminate;try contradiction;
     inversion H;subst;eexists;reflexivity.
   + intros [b H]. inversion H;subst. cbn. tauto. }
 destruct (Z.eq_dec x 102%Z) as [E102|E102].
 { subst x. cbn [V293_tcb_internal_declarations V293_TCBInit_parameters V293_TCBInit_locals revlcons getlenvdom].
   unfold InternalLE. repeat rewrite map_get_set' by congruence. rewrite map_get_set.
   split.
   + intro H. repeat destruct H as [H|H];try discriminate;try contradiction;
     inversion H;subst;eexists;reflexivity.
   + intros [b H]. inversion H;subst. cbn. tauto. }
 destruct (Z.eq_dec x 103%Z) as [E103|E103].
 { subst x. cbn [V293_tcb_internal_declarations V293_TCBInit_parameters V293_TCBInit_locals revlcons getlenvdom].
   unfold InternalLE. repeat rewrite map_get_set' by congruence. rewrite map_get_set.
   split.
   + intro H. repeat destruct H as [H|H];try discriminate;try contradiction;
     inversion H;subst;eexists;reflexivity.
   + intros [b H]. inversion H;subst. cbn. tauto. }
 destruct (Z.eq_dec x 104%Z) as [E104|E104].
 { subst x. cbn [V293_tcb_internal_declarations V293_TCBInit_parameters V293_TCBInit_locals revlcons getlenvdom].
   unfold InternalLE. repeat rewrite map_get_set' by congruence. rewrite map_get_set.
   split.
   + intro H. repeat destruct H as [H|H];try discriminate;try contradiction;
     inversion H;subst;eexists;reflexivity.
   + intros [b H]. inversion H;subst. cbn. tauto. }
 destruct (Z.eq_dec x 105%Z) as [E105|E105].
 { subst x. cbn [V293_tcb_internal_declarations V293_TCBInit_parameters V293_TCBInit_locals revlcons getlenvdom].
   unfold InternalLE. repeat rewrite map_get_set' by congruence. rewrite map_get_set.
   split.
   + intro H. repeat destruct H as [H|H];try discriminate;try contradiction;
     inversion H;subst;eexists;reflexivity.
   + intros [b H]. inversion H;subst. cbn. tauto. }
 destruct (Z.eq_dec x 106%Z) as [E106|E106].
 { subst x. cbn [V293_tcb_internal_declarations V293_TCBInit_parameters V293_TCBInit_locals revlcons getlenvdom].
   unfold InternalLE. repeat rewrite map_get_set' by congruence. rewrite map_get_set.
   split.
   + intro H. repeat destruct H as [H|H];try discriminate;try contradiction;
     inversion H;subst;eexists;reflexivity.
   + intros [b H]. inversion H;subst. cbn. tauto. }
 destruct (Z.eq_dec x 107%Z) as [E107|E107].
 { subst x. cbn [V293_tcb_internal_declarations V293_TCBInit_parameters V293_TCBInit_locals revlcons getlenvdom].
   unfold InternalLE. repeat rewrite map_get_set' by congruence. rewrite map_get_sig.
   split.
   + intro H. repeat destruct H as [H|H];try discriminate;try contradiction;
     inversion H;subst;eexists;reflexivity.
   + intros [b H]. inversion H;subst. cbn. tauto. }
 unfold InternalLE. repeat rewrite map_get_set' by congruence. rewrite map_get_sig' by congruence.
 cbn [V293_tcb_internal_declarations V293_TCBInit_parameters V293_TCBInit_locals revlcons getlenvdom].
 split.
 - intro H. repeat destruct H as [H|H];try contradiction;inversion H;congruence.
 - intros [b H]. discriminate.
Qed.
Definition InternalSlot107 := InternalBytes 207%positive true (Tint16) (Vint32(Int.repr 7)).
Definition InternalSlot106 := InternalBytes 206%positive true (Tptr Tvoid) (Vnull).
Definition InternalSlot105 := InternalBytes 205%positive true (Tint32) (Vint32(Int.repr 5)).
Definition InternalSlot104 := InternalBytes 204%positive true (Tint16) (Vint32(Int.repr 4)).
Definition InternalSlot103 := InternalBytes 203%positive true (Tptr Tint32) (Vnull).
Definition InternalSlot102 := InternalBytes 202%positive true (Tptr Tint32) (Vnull).
Definition InternalSlot101 := InternalBytes 201%positive true (Tint8) (Vint32(Int.repr 11)).
Definition InternalSlot108 := InternalBytes 208%positive true (Tptr V293_tcb_type) (Vundef).
Definition InternalSlot109 := InternalBytes 209%positive true (Tint32) (Vundef).
Definition InternalLocalsMemory := merge InternalSlot107 (merge InternalSlot106 (merge InternalSlot105 (merge InternalSlot104 (merge InternalSlot103 (merge InternalSlot102 (merge InternalSlot101 (merge InternalSlot108 (merge InternalSlot109 (emp))))))))).
Ltac InternalLocalsApart b :=
 apply map_join_merge;apply map_disjoint;intros [other offset];
 destruct(Pos.eq_dec other b);[subst other;right;left|left];
 unfold InternalLocalsMemory,InternalSlot107,InternalSlot106,InternalSlot105,InternalSlot104,InternalSlot103,InternalSlot102,InternalSlot101,InternalSlot108,InternalSlot109,InternalBytes;
 repeat first [rewrite map_merge_semp by reflexivity |
 rewrite V293_encoded_memory_outside by (left;congruence)];reflexivity.
Lemma InternalLocalsSpatial : forall cs,
 InternalState InternalLocalsMemory cs |=
 V293_tcb_internal_pre_cells (Vint32(Int.repr 11)) Vnull Vnull
 (Vint32(Int.repr 4)) (Vint32(Int.repr 5)) Vnull (Vint32(Int.repr 7)).
Proof.
 intro cs. unfold InternalLocalsMemory,V293_tcb_internal_pre_cells,V293_tcb_internal_locals.
 eapply InternalStar with (m1:=InternalSlot107).
 { InternalLocalsApart 207%positive. }
 { unfold Alvarmapsto,Alvarenv'. exists 207%positive.
   eapply InternalStar with (m1:=emp) (m2:=InternalSlot107).
   + apply map_join_comm;apply map_join_emp.
   + exists 207%positive. split;[vm_compute;reflexivity| ]. repeat split;reflexivity.
   + split;[apply V293_encoded_memory_mapsto|reflexivity]. }
 eapply InternalStar with (m1:=InternalSlot106).
 { InternalLocalsApart 206%positive. }
 { unfold Alvarmapsto,Alvarenv'. exists 206%positive.
   eapply InternalStar with (m1:=emp) (m2:=InternalSlot106).
   + apply map_join_comm;apply map_join_emp.
   + exists 206%positive. split;[vm_compute;reflexivity| ]. repeat split;reflexivity.
   + split;[apply V293_encoded_memory_mapsto|reflexivity]. }
 eapply InternalStar with (m1:=InternalSlot105).
 { InternalLocalsApart 205%positive. }
 { unfold Alvarmapsto,Alvarenv'. exists 205%positive.
   eapply InternalStar with (m1:=emp) (m2:=InternalSlot105).
   + apply map_join_comm;apply map_join_emp.
   + exists 205%positive. split;[vm_compute;reflexivity| ]. repeat split;reflexivity.
   + split;[apply V293_encoded_memory_mapsto|reflexivity]. }
 eapply InternalStar with (m1:=InternalSlot104).
 { InternalLocalsApart 204%positive. }
 { unfold Alvarmapsto,Alvarenv'. exists 204%positive.
   eapply InternalStar with (m1:=emp) (m2:=InternalSlot104).
   + apply map_join_comm;apply map_join_emp.
   + exists 204%positive. split;[vm_compute;reflexivity| ]. repeat split;reflexivity.
   + split;[apply V293_encoded_memory_mapsto|reflexivity]. }
 eapply InternalStar with (m1:=InternalSlot103).
 { InternalLocalsApart 203%positive. }
 { unfold Alvarmapsto,Alvarenv'. exists 203%positive.
   eapply InternalStar with (m1:=emp) (m2:=InternalSlot103).
   + apply map_join_comm;apply map_join_emp.
   + exists 203%positive. split;[vm_compute;reflexivity| ]. repeat split;reflexivity.
   + split;[apply V293_encoded_memory_mapsto|reflexivity]. }
 eapply InternalStar with (m1:=InternalSlot102).
 { InternalLocalsApart 202%positive. }
 { unfold Alvarmapsto,Alvarenv'. exists 202%positive.
   eapply InternalStar with (m1:=emp) (m2:=InternalSlot102).
   + apply map_join_comm;apply map_join_emp.
   + exists 202%positive. split;[vm_compute;reflexivity| ]. repeat split;reflexivity.
   + split;[apply V293_encoded_memory_mapsto|reflexivity]. }
 eapply InternalStar with (m1:=InternalSlot101).
 { InternalLocalsApart 201%positive. }
 { unfold Alvarmapsto,Alvarenv'. exists 201%positive.
   eapply InternalStar with (m1:=emp) (m2:=InternalSlot101).
   + apply map_join_comm;apply map_join_emp.
   + exists 201%positive. split;[vm_compute;reflexivity| ]. repeat split;reflexivity.
   + split;[apply V293_encoded_memory_mapsto|reflexivity]. }
 eapply InternalStar with (m1:=InternalSlot108).
 { InternalLocalsApart 208%positive. }
 { exists (Vundef). unfold Alvarmapsto,Alvarenv'. exists 208%positive.
   eapply InternalStar with (m1:=emp) (m2:=InternalSlot108).
   + apply map_join_comm;apply map_join_emp.
   + exists 208%positive. split;[vm_compute;reflexivity| ]. repeat split;reflexivity.
   + split;[apply V293_encoded_memory_mapsto|reflexivity]. }
 eapply InternalStar with (m1:=InternalSlot109).
 { InternalLocalsApart 209%positive. }
 { exists (Vundef). unfold Alvarmapsto,Alvarenv'. exists 209%positive.
   eapply InternalStar with (m1:=emp) (m2:=InternalSlot109).
   + apply map_join_comm;apply map_join_emp.
   + exists 209%positive. split;[vm_compute;reflexivity| ]. repeat split;reflexivity.
   + split;[apply V293_encoded_memory_mapsto|reflexivity]. }
 split;reflexivity.
Qed.
Definition InternalOuterMemory := merge InternalFree (merge InternalCurrent InternalSentinel).
Lemma InternalExternalSpatial : forall cs,
 InternalState InternalOuterMemory cs |=
 V293_tcb_empty_external 401%positive InternalR (spec_done None) (fun _=>false) [] cs **
 V293_tcb_internal_domain.
Proof.
 intro cs. unfold V293_tcb_empty_external,V293_tcb_internal_domain.
 apply astar_comm. apply astar_l_adomlenv_intro;[ |apply InternalDomain].
 eapply InternalStar with (m1:=emp) (m2:=InternalOuterMemory).
 - apply map_join_comm;apply map_join_emp.
 - exists 401%positive. split;[vm_compute;reflexivity| ]. repeat split;reflexivity.
 - unfold InternalOuterMemory. eapply InternalStar with (m1:=InternalFree).
   + InternalApart 401%positive.
   + split;[apply V293_encoded_memory_mapsto|reflexivity].
   + apply astar_l_aop'_intro;[ |reflexivity].
     assert (Ordered: InternalState (merge InternalCurrent InternalSentinel) cs |=
       Aisr (fun _=>false) ** Aie false ** (Ais nil) ** Acs cs ** InternalR).
     { apply astar_l_aisr_intro;[ |reflexivity].
       apply astar_l_aie_intro;[ |reflexivity].
       apply astar_l_ais_intro;[ |reflexivity].
       apply astar_l_acs_intro;[ |reflexivity].
       apply InternalRSpatial. }
     clear -Ordered. sep auto.
Qed.
Definition InternalProgram : progunit := fun f =>
 if Z.eq_dec f 500%Z then Some(V293_TCBInit_function 501%Z 502%Z) else None.
Definition InternalArgs : vallist :=
 [Vint32(Int.repr 7);Vnull;Vint32(Int.repr 5);Vint32(Int.repr 4);Vnull;Vnull;Vint32(Int.repr 11)].
Definition InternalPre cs :=
 V293_tcb_internal_pre_cells (Vint32(Int.repr 11)) Vnull Vnull
 (Vint32(Int.repr 4)) (Vint32(Int.repr 5)) Vnull (Vint32(Int.repr 7)) **
 V293_tcb_empty_external 401%positive InternalR (spec_done None) (fun _=>false) [] cs **
 V293_tcb_internal_domain.
Definition InternalPost cs result := V293_tcb_internal_post_cells **
 ([|result=Some(Vint32(Int.repr 66))|] **
 V293_tcb_empty_external 401%positive InternalR (spec_done None) (fun _=>false) [] cs) **
 V293_tcb_internal_domain.
Lemma InternalBuilders : forall cs,
 Some(InternalPre cs)=BuildPreI InternalProgram 500%Z InternalArgs []
 (V293_tcb_empty_fpre 401%positive InternalR (spec_done None) (fun _=>false) [] cs InternalRFun) InternalTid /\
 Some(InternalPost cs)=BuildRetI InternalProgram 500%Z InternalArgs []
 (V293_tcb_empty_fpost 401%positive InternalR (spec_done None) (fun _=>false) [] cs InternalRFun) InternalTid.
Proof. intro cs. split;reflexivity. Qed.
Theorem InternalLiteralBuilderEntry : forall cs,
 InternalState (merge InternalLocalsMemory InternalOuterMemory) cs |= InternalPre cs.
Proof.
 intro cs. unfold InternalPre.
 eapply InternalStar with (m1:=InternalLocalsMemory) (m2:=InternalOuterMemory).
 - apply map_join_merge;apply map_disjoint;intros [b off].
   destruct (Pos.eq_dec b 401%positive);
   destruct (Pos.eq_dec b 402%positive);
   destruct (Pos.eq_dec b 601%positive);try congruence;subst;
   unfold InternalLocalsMemory,InternalOuterMemory,InternalSlot107,InternalSlot106,InternalSlot105,InternalSlot104,InternalSlot103,InternalSlot102,InternalSlot101,InternalSlot108,InternalSlot109,
   InternalFree,InternalCurrent,InternalSentinel,InternalBytes;
   first [left; solve [repeat first [rewrite map_merge_semp by reflexivity |
     rewrite V293_encoded_memory_outside by (left;congruence)];reflexivity] |
     right;left; repeat first [rewrite map_merge_semp by reflexivity |
     rewrite V293_encoded_memory_outside by (left;congruence)];reflexivity].
 - apply InternalLocalsSpatial.
 - apply InternalExternalSpatial.
Qed.

(* Apply the exported constructor-level contract with no Hook specifications. *)
Theorem InternalContractChecked : forall sd I cs,
 InfRules (fun _=>None) sd V293_witness_li I (InternalPost cs) Afalse
 (InternalPre cs) (V293_TCBInit_function_body 501%Z 502%Z) Afalse InternalTid.
Proof.
 intros sd I cs. eapply V293_OS_TCBInit_empty_internal_contract
 with (P:=InternalProgram) (f:=500%Z) (good:=InternalRFun) (vl:=InternalArgs) (lg:=[]).
 - apply InternalRGood.
 - apply InternalRCurLINV.
 - reflexivity.
 - apply (proj1(InternalBuilders cs)).
 - apply (proj2(InternalBuilders cs)).
Qed.
Theorem InternalConstructorsNonvacuous : forall cs,
 exists pre post s,
 Some pre=BuildPreI InternalProgram 500%Z InternalArgs []
 (V293_tcb_empty_fpre 401%positive InternalR (spec_done None) (fun _=>false) [] cs InternalRFun) InternalTid /\
 Some post=BuildRetI InternalProgram 500%Z InternalArgs []
 (V293_tcb_empty_fpost 401%positive InternalR (spec_done None) (fun _=>false) [] cs InternalRFun) InternalTid /\
 s |= pre.
Proof.
 intro cs. exists (InternalPre cs). exists (InternalPost cs). exists
 (InternalState (merge InternalLocalsMemory InternalOuterMemory) cs).
 split;[apply (proj1(InternalBuilders cs))| ].
 split;[apply (proj2(InternalBuilders cs))|apply InternalLiteralBuilderEntry].
Qed.
Lemma InternalPostCode : forall s cs result,
 s |= InternalPost cs result -> result=Some(Vint32(Int.repr 66)).
Proof.
 intros s cs result H. unfold InternalPost in H.
 sep normal in H. sep destruct H. sep auto.
Qed.
Theorem InternalPostRejectZero : forall s cs,
 ~s |= InternalPost cs (Some(Vint32 Int.zero)).
Proof. intros s cs H. pose proof(InternalPostCode _ _ _ H). discriminate. Qed.
Theorem InternalPostRejectNone : forall s cs,
 ~s |= InternalPost cs None.
Proof. intros s cs H. pose proof(InternalPostCode _ _ _ H). discriminate. Qed.
Theorem InternalEmptyArgumentsRejected : forall cs,
 BuildPreI InternalProgram 500%Z [] []
 (V293_tcb_empty_fpre 401%positive InternalR (spec_done None) (fun _=>false) [] cs InternalRFun) InternalTid=None.
Proof. reflexivity. Qed.
(* Removing the precise domain permits global name 91 to be shadowed. *)
Theorem InternalShadowCountermodel :
 get (sig 91%Z (999%positive,Tptr V293_tcb_type)) 91%Z <> None.
Proof. rewrite map_get_sig. discriminate. Qed.
