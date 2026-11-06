(* Independent literal IE=true fixture. NULL head is in the ISR invariant,
   never the caller's enabled resource; empty test LINV is not a kernel model. *)
Require Import CertiOS.certiucos.v293.proofs.V293TCBEmptyEnabled.
Require Import CertiOS.certiucos.v293.proofs.V293TCBEmptyInternal.
Require Import CertiOS.certiucos.v293.proofs.V293TCBEmptyHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TimeShared.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewWitness.
Require Import CertiOS.certiucos.v293.code.V293OSTCBInitFunction.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.framework.proof.rulesoundlib.
Require Import CertiOS.framework.proof.memory_prop.
Require Import CertiOS.tactics.hoareforward.init_spec.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Definition ENGE : env := set (sig 91%Z (401%positive,Tptr V293_tcb_type))
 OSTCBCur (402%positive,Tptr Tvoid).
Definition ENLE : env := set (set (set (set (set (set (set (set
 (sig 107%Z (207%positive,Tint16)) 106%Z (206%positive,Tptr Tvoid))
 105%Z (205%positive,Tint32)) 104%Z (204%positive,Tint16))
 103%Z (203%positive,Tptr Tint32)) 102%Z (202%positive,Tptr Tint32))
 101%Z (201%positive,Tint8)) 108%Z (208%positive,Tptr V293_tcb_type))
 109%Z (209%positive,Tint32).
Definition ENTid : tid := (301%positive,Int.repr 8).
Definition ENBytes b permission tp v := V293_encoded_memory b 0 permission (encode_val tp v).
Definition ENFree := ENBytes 401%positive false (Tptr V293_tcb_type) Vnull.
Definition ENCurrent := ENBytes 402%positive false (Tptr Tvoid) (Vptr ENTid).
Definition ENSentinel := ENBytes 601%positive true Tint8 (Vint32(Int.repr 77)).
Definition ENState M cs : RstateOP :=
 (ENGE,ENLE,M,(fun _=>false),(true,[],cs),(emp:osabst),spec_done None).
Definition ENR := CurTid ENTid ** LINV V293_witness_li ENTid [] **
 Amapsto (601%positive,0%Z) Tint8 true (Vint32(Int.repr 77)).

Lemma ENStar : forall m1 m2 m cs p q,
 join m1 m2 m -> ENState m1 cs |= p -> ENState m2 cs |= q ->
 ENState m cs |= p ** q.
Proof.
 intros. apply sat_split'. exists m1. exists m2.
 exists(emp:osabst). exists(emp:osabst).
 split;[exact H | ]. split;[apply map_join_emp | ]. split;assumption.
Qed.
Lemma ENCurrentSpatial : forall cs, ENState ENCurrent cs |= CurTid ENTid.
Proof.
 intro cs. exists Tvoid. exists 402%positive.
 eapply ENStar with (m1:=emp) (m2:=ENCurrent).
 - apply map_join_comm;apply map_join_emp.
 - exists 402%positive. split;[vm_compute;reflexivity | ]. repeat split;reflexivity.
 - split;[apply V293_encoded_memory_mapsto|reflexivity].
Qed.
Lemma ENLInvSpatial : forall cs, ENState emp cs |= LINV V293_witness_li ENTid [].
Proof.
 intro cs. unfold LINV. apply astar_comm. apply astar_l_apure_intro.
 - split;reflexivity.
 - apply V293_witness_li_good.
Qed.
Ltac ENApart b :=
 apply map_join_merge;apply map_disjoint;intros [other offset];
 destruct(Pos.eq_dec other b);[subst other;right;left|left];
 unfold ENFree,ENCurrent,ENSentinel,ENBytes;
 repeat first [rewrite map_merge_semp by reflexivity |
 rewrite V293_encoded_memory_outside by (left;congruence)];reflexivity.
Lemma ENRSpatial : forall cs,
 ENState (merge ENCurrent ENSentinel) cs |= ENR.
Proof.
 intro cs. unfold ENR.
 eapply ENStar with (m1:=ENCurrent) (m2:=ENSentinel).
 - ENApart 402%positive.
 - apply ENCurrentSpatial.
 - eapply ENStar with (m1:=emp) (m2:=ENSentinel).
   + apply map_join_comm;apply map_join_emp.
   + apply ENLInvSpatial.
   + split;[apply V293_encoded_memory_mapsto|reflexivity].
Qed.
Lemma ENRGood : GoodFrm ENR.
Proof. cbn [ENR CurTid LINV V293_witness_li GoodFrm]. repeat split;exact I. Qed.
Lemma ENRCurLINV : ENR ==> CurLINV V293_witness_li ENTid.
Proof.
 intros s HS. unfold CurLINV. exists([]:list logicvar).
 unfold ENR in HS. clear -HS. sep auto.
Qed.

Lemma ENRFun : GoodFunAsrt ENR.
Proof.
 cbn [ENR CurTid LINV V293_witness_li GoodFunAsrt Agvarmapsto Agvarenv' Aptrmapsto].
 repeat split;intros;repeat split;exact I.
Qed.
Lemma ENDomain : eq_dom_env ENLE (getlenvdom V293_tcb_internal_declarations).
Proof.
 unfold eq_dom_env. intros x tp.
 destruct (Z.eq_dec x 109%Z) as [E109|E109].
 { subst x. cbn [V293_tcb_internal_declarations V293_TCBInit_parameters V293_TCBInit_locals revlcons getlenvdom].
   unfold ENLE. repeat rewrite map_get_set' by congruence. rewrite map_get_set.
   split.
   + intro H. repeat destruct H as [H|H];try discriminate;try contradiction;
     inversion H;subst;eexists;reflexivity.
   + intros [b H]. inversion H;subst. cbn. tauto. }
 destruct (Z.eq_dec x 108%Z) as [E108|E108].
 { subst x. cbn [V293_tcb_internal_declarations V293_TCBInit_parameters V293_TCBInit_locals revlcons getlenvdom].
   unfold ENLE. repeat rewrite map_get_set' by congruence. rewrite map_get_set.
   split.
   + intro H. repeat destruct H as [H|H];try discriminate;try contradiction;
     inversion H;subst;eexists;reflexivity.
   + intros [b H]. inversion H;subst. cbn. tauto. }
 destruct (Z.eq_dec x 101%Z) as [E101|E101].
 { subst x. cbn [V293_tcb_internal_declarations V293_TCBInit_parameters V293_TCBInit_locals revlcons getlenvdom].
   unfold ENLE. repeat rewrite map_get_set' by congruence. rewrite map_get_set.
   split.
   + intro H. repeat destruct H as [H|H];try discriminate;try contradiction;
     inversion H;subst;eexists;reflexivity.
   + intros [b H]. inversion H;subst. cbn. tauto. }
 destruct (Z.eq_dec x 102%Z) as [E102|E102].
 { subst x. cbn [V293_tcb_internal_declarations V293_TCBInit_parameters V293_TCBInit_locals revlcons getlenvdom].
   unfold ENLE. repeat rewrite map_get_set' by congruence. rewrite map_get_set.
   split.
   + intro H. repeat destruct H as [H|H];try discriminate;try contradiction;
     inversion H;subst;eexists;reflexivity.
   + intros [b H]. inversion H;subst. cbn. tauto. }
 destruct (Z.eq_dec x 103%Z) as [E103|E103].
 { subst x. cbn [V293_tcb_internal_declarations V293_TCBInit_parameters V293_TCBInit_locals revlcons getlenvdom].
   unfold ENLE. repeat rewrite map_get_set' by congruence. rewrite map_get_set.
   split.
   + intro H. repeat destruct H as [H|H];try discriminate;try contradiction;
     inversion H;subst;eexists;reflexivity.
   + intros [b H]. inversion H;subst. cbn. tauto. }
 destruct (Z.eq_dec x 104%Z) as [E104|E104].
 { subst x. cbn [V293_tcb_internal_declarations V293_TCBInit_parameters V293_TCBInit_locals revlcons getlenvdom].
   unfold ENLE. repeat rewrite map_get_set' by congruence. rewrite map_get_set.
   split.
   + intro H. repeat destruct H as [H|H];try discriminate;try contradiction;
     inversion H;subst;eexists;reflexivity.
   + intros [b H]. inversion H;subst. cbn. tauto. }
 destruct (Z.eq_dec x 105%Z) as [E105|E105].
 { subst x. cbn [V293_tcb_internal_declarations V293_TCBInit_parameters V293_TCBInit_locals revlcons getlenvdom].
   unfold ENLE. repeat rewrite map_get_set' by congruence. rewrite map_get_set.
   split.
   + intro H. repeat destruct H as [H|H];try discriminate;try contradiction;
     inversion H;subst;eexists;reflexivity.
   + intros [b H]. inversion H;subst. cbn. tauto. }
 destruct (Z.eq_dec x 106%Z) as [E106|E106].
 { subst x. cbn [V293_tcb_internal_declarations V293_TCBInit_parameters V293_TCBInit_locals revlcons getlenvdom].
   unfold ENLE. repeat rewrite map_get_set' by congruence. rewrite map_get_set.
   split.
   + intro H. repeat destruct H as [H|H];try discriminate;try contradiction;
     inversion H;subst;eexists;reflexivity.
   + intros [b H]. inversion H;subst. cbn. tauto. }
 destruct (Z.eq_dec x 107%Z) as [E107|E107].
 { subst x. cbn [V293_tcb_internal_declarations V293_TCBInit_parameters V293_TCBInit_locals revlcons getlenvdom].
   unfold ENLE. repeat rewrite map_get_set' by congruence. rewrite map_get_sig.
   split.
   + intro H. repeat destruct H as [H|H];try discriminate;try contradiction;
     inversion H;subst;eexists;reflexivity.
   + intros [b H]. inversion H;subst. cbn. tauto. }
 unfold ENLE. repeat rewrite map_get_set' by congruence. rewrite map_get_sig' by congruence.
 cbn [V293_tcb_internal_declarations V293_TCBInit_parameters V293_TCBInit_locals revlcons getlenvdom].
 split.
 - intro H. repeat destruct H as [H|H];try contradiction;inversion H;congruence.
 - intros [b H]. discriminate.
Qed.
Definition ENSlot107 := ENBytes 207%positive true (Tint16) (Vint32(Int.repr 7)).
Definition ENSlot106 := ENBytes 206%positive true (Tptr Tvoid) (Vnull).
Definition ENSlot105 := ENBytes 205%positive true (Tint32) (Vint32(Int.repr 5)).
Definition ENSlot104 := ENBytes 204%positive true (Tint16) (Vint32(Int.repr 4)).
Definition ENSlot103 := ENBytes 203%positive true (Tptr Tint32) (Vnull).
Definition ENSlot102 := ENBytes 202%positive true (Tptr Tint32) (Vnull).
Definition ENSlot101 := ENBytes 201%positive true (Tint8) (Vint32(Int.repr 11)).
Definition ENSlot108 := ENBytes 208%positive true (Tptr V293_tcb_type) (Vundef).
Definition ENSlot109 := ENBytes 209%positive true (Tint32) (Vundef).
Definition ENLocalsMemory := merge ENSlot107 (merge ENSlot106 (merge ENSlot105 (merge ENSlot104 (merge ENSlot103 (merge ENSlot102 (merge ENSlot101 (merge ENSlot108 (merge ENSlot109 (emp))))))))).
Ltac ENLocalsApart b :=
 apply map_join_merge;apply map_disjoint;intros [other offset];
 destruct(Pos.eq_dec other b);[subst other;right;left|left];
 unfold ENLocalsMemory,ENSlot107,ENSlot106,ENSlot105,ENSlot104,ENSlot103,ENSlot102,ENSlot101,ENSlot108,ENSlot109,ENBytes;
 repeat first [rewrite map_merge_semp by reflexivity |
 rewrite V293_encoded_memory_outside by (left;congruence)];reflexivity.
Lemma ENLocalsSpatial : forall cs,
 ENState ENLocalsMemory cs |=
 V293_tcb_internal_pre_cells (Vint32(Int.repr 11)) Vnull Vnull
 (Vint32(Int.repr 4)) (Vint32(Int.repr 5)) Vnull (Vint32(Int.repr 7)).
Proof.
 intro cs. unfold ENLocalsMemory,V293_tcb_internal_pre_cells,V293_tcb_internal_locals.
 eapply ENStar with (m1:=ENSlot107).
 { ENLocalsApart 207%positive. }
 { unfold Alvarmapsto,Alvarenv'. exists 207%positive.
   eapply ENStar with (m1:=emp) (m2:=ENSlot107).
   + apply map_join_comm;apply map_join_emp.
   + exists 207%positive. split;[vm_compute;reflexivity| ]. repeat split;reflexivity.
   + split;[apply V293_encoded_memory_mapsto|reflexivity]. }
 eapply ENStar with (m1:=ENSlot106).
 { ENLocalsApart 206%positive. }
 { unfold Alvarmapsto,Alvarenv'. exists 206%positive.
   eapply ENStar with (m1:=emp) (m2:=ENSlot106).
   + apply map_join_comm;apply map_join_emp.
   + exists 206%positive. split;[vm_compute;reflexivity| ]. repeat split;reflexivity.
   + split;[apply V293_encoded_memory_mapsto|reflexivity]. }
 eapply ENStar with (m1:=ENSlot105).
 { ENLocalsApart 205%positive. }
 { unfold Alvarmapsto,Alvarenv'. exists 205%positive.
   eapply ENStar with (m1:=emp) (m2:=ENSlot105).
   + apply map_join_comm;apply map_join_emp.
   + exists 205%positive. split;[vm_compute;reflexivity| ]. repeat split;reflexivity.
   + split;[apply V293_encoded_memory_mapsto|reflexivity]. }
 eapply ENStar with (m1:=ENSlot104).
 { ENLocalsApart 204%positive. }
 { unfold Alvarmapsto,Alvarenv'. exists 204%positive.
   eapply ENStar with (m1:=emp) (m2:=ENSlot104).
   + apply map_join_comm;apply map_join_emp.
   + exists 204%positive. split;[vm_compute;reflexivity| ]. repeat split;reflexivity.
   + split;[apply V293_encoded_memory_mapsto|reflexivity]. }
 eapply ENStar with (m1:=ENSlot103).
 { ENLocalsApart 203%positive. }
 { unfold Alvarmapsto,Alvarenv'. exists 203%positive.
   eapply ENStar with (m1:=emp) (m2:=ENSlot103).
   + apply map_join_comm;apply map_join_emp.
   + exists 203%positive. split;[vm_compute;reflexivity| ]. repeat split;reflexivity.
   + split;[apply V293_encoded_memory_mapsto|reflexivity]. }
 eapply ENStar with (m1:=ENSlot102).
 { ENLocalsApart 202%positive. }
 { unfold Alvarmapsto,Alvarenv'. exists 202%positive.
   eapply ENStar with (m1:=emp) (m2:=ENSlot102).
   + apply map_join_comm;apply map_join_emp.
   + exists 202%positive. split;[vm_compute;reflexivity| ]. repeat split;reflexivity.
   + split;[apply V293_encoded_memory_mapsto|reflexivity]. }
 eapply ENStar with (m1:=ENSlot101).
 { ENLocalsApart 201%positive. }
 { unfold Alvarmapsto,Alvarenv'. exists 201%positive.
   eapply ENStar with (m1:=emp) (m2:=ENSlot101).
   + apply map_join_comm;apply map_join_emp.
   + exists 201%positive. split;[vm_compute;reflexivity| ]. repeat split;reflexivity.
   + split;[apply V293_encoded_memory_mapsto|reflexivity]. }
 eapply ENStar with (m1:=ENSlot108).
 { ENLocalsApart 208%positive. }
 { exists (Vundef). unfold Alvarmapsto,Alvarenv'. exists 208%positive.
   eapply ENStar with (m1:=emp) (m2:=ENSlot108).
   + apply map_join_comm;apply map_join_emp.
   + exists 208%positive. split;[vm_compute;reflexivity| ]. repeat split;reflexivity.
   + split;[apply V293_encoded_memory_mapsto|reflexivity]. }
 eapply ENStar with (m1:=ENSlot109).
 { ENLocalsApart 209%positive. }
 { exists (Vundef). unfold Alvarmapsto,Alvarenv'. exists 209%positive.
   eapply ENStar with (m1:=emp) (m2:=ENSlot109).
   + apply map_join_comm;apply map_join_emp.
   + exists 209%positive. split;[vm_compute;reflexivity| ]. repeat split;reflexivity.
   + split;[apply V293_encoded_memory_mapsto|reflexivity]. }
 split;reflexivity.
Qed.
Definition ENOuterMemory := merge ENCurrent ENSentinel.
Lemma ENExternalSpatial : forall cs,
 ENState ENOuterMemory cs |=
 V293_tcb_enabled_external 401%positive ENR(spec_done None)(fun _=>false)[]cs **
 V293_tcb_internal_domain.
Proof.
 intro cs. unfold V293_tcb_enabled_external,V293_tcb_internal_domain.
 apply astar_comm. apply astar_l_adomlenv_intro;[ |apply ENDomain].
 eapply ENStar with(m1:=emp)(m2:=ENOuterMemory).
 - apply map_join_comm;apply map_join_emp.
 - exists 401%positive. split;[vm_compute;reflexivity| ]. repeat split;reflexivity.
 - apply astar_l_aop'_intro;[ |reflexivity].
   assert(Ordered:ENState ENOuterMemory cs |=
    Aisr(fun _=>false) ** Aie true ** Ais nil ** Acs cs ** ENR).
   { apply astar_l_aisr_intro;[ |reflexivity]. apply astar_l_aie_intro;[ |reflexivity].
     apply astar_l_ais_intro;[ |reflexivity]. apply astar_l_acs_intro;[ |reflexivity].
     apply ENRSpatial. }
   clear -Ordered;sep auto.
Qed.
Definition ENProgram : progunit := fun f =>
 if Z.eq_dec f 500%Z then Some(V293_TCBInit_function 501%Z 502%Z) else None.
Definition ENArgs : vallist :=
 [Vint32(Int.repr 7);Vnull;Vint32(Int.repr 5);Vint32(Int.repr 4);Vnull;Vnull;Vint32(Int.repr 11)].
Definition ENPre cs :=
 V293_tcb_internal_pre_cells (Vint32(Int.repr 11)) Vnull Vnull
 (Vint32(Int.repr 4)) (Vint32(Int.repr 5)) Vnull (Vint32(Int.repr 7)) **
 V293_tcb_enabled_external 401%positive ENR (spec_done None) (fun _=>false) [] cs **
 V293_tcb_internal_domain.
Definition ENPost cs result := V293_tcb_internal_post_cells **
 ([|result=Some(Vint32(Int.repr 66))|] **
 V293_tcb_enabled_external 401%positive ENR (spec_done None) (fun _=>false) [] cs) **
 V293_tcb_internal_domain.
Lemma ENBuilders : forall cs,
 Some(ENPre cs)=BuildPreI ENProgram 500%Z ENArgs []
 (V293_tcb_enabled_fpre 401%positive ENR (spec_done None) (fun _=>false) [] cs ENRFun) ENTid /\
 Some(ENPost cs)=BuildRetI ENProgram 500%Z ENArgs []
 (V293_tcb_enabled_fpost 401%positive ENR (spec_done None) (fun _=>false) [] cs ENRFun) ENTid.
Proof. intro cs. split;reflexivity. Qed.
Theorem ENLiteralBuilderEntry : forall cs,
 ENState (merge ENLocalsMemory ENOuterMemory) cs |= ENPre cs.
Proof.
 intro cs. unfold ENPre.
 eapply ENStar with (m1:=ENLocalsMemory) (m2:=ENOuterMemory).
 - apply map_join_merge;apply map_disjoint;intros [b off].
   destruct (Pos.eq_dec b 401%positive);
   destruct (Pos.eq_dec b 402%positive);
   destruct (Pos.eq_dec b 601%positive);try congruence;subst;
   unfold ENLocalsMemory,ENOuterMemory,ENSlot107,ENSlot106,ENSlot105,ENSlot104,ENSlot103,ENSlot102,ENSlot101,ENSlot108,ENSlot109,
   ENFree,ENCurrent,ENSentinel,ENBytes;
   first [left; solve [repeat first [rewrite map_merge_semp by reflexivity |
     rewrite V293_encoded_memory_outside by (left;congruence)];reflexivity] |
     right;left; repeat first [rewrite map_merge_semp by reflexivity |
     rewrite V293_encoded_memory_outside by (left;congruence)];reflexivity].
 - apply ENLocalsSpatial.
 - apply ENExternalSpatial.
Qed.

Theorem ENConstructorsNonvacuous : forall cs,
 exists pre post s,
 Some pre=BuildPreI ENProgram 500%Z ENArgs []
 (V293_tcb_enabled_fpre 401%positive ENR (spec_done None) (fun _=>false) [] cs ENRFun) ENTid /\
 Some post=BuildRetI ENProgram 500%Z ENArgs []
 (V293_tcb_enabled_fpost 401%positive ENR (spec_done None) (fun _=>false) [] cs ENRFun) ENTid /\
 s |= pre.
Proof.
 intro cs. exists (ENPre cs). exists (ENPost cs). exists
 (ENState (merge ENLocalsMemory ENOuterMemory) cs).
 split;[apply (proj1(ENBuilders cs))| ].
 split;[apply (proj2(ENBuilders cs))|apply ENLiteralBuilderEntry].
Qed.
Lemma ENPostCode : forall s cs result,
 s |= ENPost cs result -> result=Some(Vint32(Int.repr 66)).
Proof.
 intros s cs result H. unfold ENPost in H.
 sep normal in H. sep destruct H. sep auto.
Qed.
Theorem ENPostRejectZero : forall s cs,
 ~s |= ENPost cs (Some(Vint32 Int.zero)).
Proof. intros s cs H. pose proof(ENPostCode _ _ _ H). discriminate. Qed.
Theorem ENPostRejectNone : forall s cs,
 ~s |= ENPost cs None.
Proof. intros s cs H. pose proof(ENPostCode _ _ _ H). discriminate. Qed.
Theorem ENEmptyArgumentsRejected : forall cs,
 BuildPreI ENProgram 500%Z [] []
 (V293_tcb_enabled_fpre 401%positive ENR (spec_done None) (fun _=>false) [] cs ENRFun) ENTid=None.
Proof. reflexivity. Qed.

Definition ENCore := V293_tcb_empty_pool 401%positive Aemp.
Lemma ENBytesUnique : forall vl l permission m1 m2,
 ptomvallist l permission vl m1 -> ptomvallist l permission vl m2 -> m1=m2.
Proof.
 induction vl as [ | head tail IH]; intros [b off] permission m1 m2 H1 H2.
 - cbn[ptomvallist]in *;congruence.
 - cbn[ptomvallist]in H1,H2.
   destruct H1 as[a1[t1[J1[P1 T1]]]]. destruct H2 as[a2[t2[J2[P2 T2]]]].
   unfold ptomval in P1,P2. subst a1 a2.
   assert(E:t1=t2)by(eapply IH;eauto). subst t2.
   eapply map_join_deter; eauto.
Qed.
Lemma ENCorePrecise : precise ENCore.
Proof.
 intros s M1 M2 O1 O2 H1 H2 M O HM1 HM2 HO1 HO2.
 unfold ENCore,V293_tcb_empty_pool in H1,H2.
 apply astar_r_aemp_elim in H1. apply astar_r_aemp_elim in H2.
 destruct s as [[[[[[ge le] mem] ir] aux] oldO] op].
 change(mapstoval(401%positive,0%Z)(Tptr V293_tcb_type)false Vnull M1 /\ O1=emp)in H1.
 change(mapstoval(401%positive,0%Z)(Tptr V293_tcb_type)false Vnull M2 /\ O2=emp)in H2.
 destruct H1 as[[v1[E1 P1]]Oe1]. destruct H2 as[[v2[E2 P2]]Oe2].
 subst v1 v2. split;[eapply ENBytesUnique;eauto|congruence].
Qed.
Lemma ENCoreGood : GoodInvAsrt ENCore.
Proof. cbn[ENCore V293_tcb_empty_pool GoodInvAsrt];tauto. Qed.
Lemma ENCoreISR : assertion.inv_isr_prop ENCore.
Proof.
 unfold assertion.inv_isr_prop,ENCore,V293_tcb_empty_pool.
 repeat split;intros;destruct s as [[[[[[ge le] M] ir] [[ie si] cs]] O] op];exact H.
Qed.
Definition ENInv : Inv := fun i=>match i with
 | O=>mkinvasrt ENCoreGood(conj ENCorePrecise ENCoreISR)
 | S j=>V293_shared_inv(S j) end.
Lemma ENNoisrTail : forall n i,starinv_noisr ENInv(S i)n <==> Aemp.
Proof.
 induction n;intros i s;cbn[starinv_noisr];[reflexivity| ].
 change(s |= Aemp ** starinv_noisr ENInv(S(S i))n <-> s |= Aemp).
 split;intro H.
 - apply astar_l_aemp_elim in H. apply IHn in H;exact H.
 - apply astar_l_aemp_intro. apply IHn;exact H.
Qed.
Lemma ENNoisrCore : forall n,starinv_noisr ENInv 0 n <==> ENCore.
Proof.
 intros[ |n]s;[reflexivity| ].
 change(s |= ENCore ** starinv_noisr ENInv 1 n <-> s |= ENCore).
 split;intro H.
 - apply astar_r_aemp_elim. eapply astar_mono;[intros st HS;exact HS|intros st HS;apply ENNoisrTail in HS;exact HS|exact H].
 - eapply astar_mono;[intros st HS;exact HS|intros st HS;apply ENNoisrTail;exact HS| ]. apply astar_r_aemp_intro;exact H.
Qed.
Theorem ENBorrowEquivalence : forall n,
 Aisr(fun _=>false) ** invlth_isr ENInv 0 n <==> Aisr(fun _=>false) ** ENCore.
Proof.
 intros n s. destruct s as [[[[[[ge le] M] ir] aux] O] op]. split;intro H.
 all: (apply sat_split in H;destruct H as(m1&m2&o1&o2&JM&JO&H1&H2);
 destruct H1 as[E Empty];cbn in E;subst ir;
 apply sat_split';exists m1;exists m2;exists o1;exists o2;
 split;[exact JM| ];split;[exact JO| ];split;[split;[reflexivity|exact Empty]| ]).
 - unfold invlth_isr in H2. rewrite Nat.sub_0_r in H2.
   apply ENNoisrCore with(n:=n). eapply invisr_imply_noisr';[ |exact H2]. reflexivity.
 - unfold invlth_isr. rewrite Nat.sub_0_r.
   apply V293_shared_clear_noisr_close;[reflexivity| ]. apply ENNoisrCore;exact H2.
Qed.

Theorem ENSharedLiteral : forall cs,
 ENState ENFree cs |= invlth_isr ENInv 0 INUM.
Proof.
 intro cs. unfold invlth_isr. rewrite Nat.sub_0_r.
 apply V293_shared_clear_noisr_close;[reflexivity| ]. apply ENNoisrCore.
 unfold ENCore,V293_tcb_empty_pool. apply astar_r_aemp_intro.
 split;[apply V293_encoded_memory_mapsto|reflexivity].
Qed.
Theorem ENCallerHasNoHead : forall off,
 get(merge ENLocalsMemory ENOuterMemory)(401%positive,off)=None.
Proof.
 intro off. unfold ENLocalsMemory,ENOuterMemory,ENSlot107,ENSlot106,ENSlot105,ENSlot104,
 ENSlot103,ENSlot102,ENSlot101,ENSlot108,ENSlot109,ENCurrent,ENSentinel,ENBytes.
 repeat first[rewrite map_merge_semp by reflexivity|
 rewrite V293_encoded_memory_outside by(left;congruence)];reflexivity.
Qed.
Theorem ENWholePartition :
 join(merge ENLocalsMemory ENOuterMemory)ENFree
 (merge(merge ENLocalsMemory ENOuterMemory)ENFree).
Proof.
 apply map_join_merge;apply map_disjoint;intros[b off].
 destruct(Pos.eq_dec b 401%positive)as[E|E].
 - subst b. left;apply ENCallerHasNoHead.
 - right;left. unfold ENFree,ENBytes. apply V293_encoded_memory_outside;left;congruence.
Qed.
Theorem ENWholeSpatial : forall cs,
 ENState(merge(merge ENLocalsMemory ENOuterMemory)ENFree)cs |=
 ENPre cs ** invlth_isr ENInv 0 INUM.
Proof.
 intro cs. eapply ENStar;[apply ENWholePartition|apply ENLiteralBuilderEntry|apply ENSharedLiteral].
Qed.
Theorem ENContractChecked : forall sd cs,
 InfRules(fun _=>None)sd V293_witness_li ENInv(ENPost cs)Afalse
 (ENPre cs)(V293_TCBInit_function_body 501%Z 502%Z)Afalse ENTid.
Proof.
 intros sd cs. eapply V293_OS_TCBInit_empty_enabled_contract
 with(P:=ENProgram)(f:=500%Z)(K:=Aemp)(good:=ENRFun)(vl:=ENArgs)(lg:=[])
 (bf:=401%positive)(R:=ENR)(aop:=spec_done None)(isr:=fun _=>false)(is:=[])(cs:=cs).
 - vm_compute;lia.
 - apply ENRGood.
 - apply ENRCurLINV.
 - intros s H;apply ENBorrowEquivalence in H;exact H.
 - intros s H;apply ENBorrowEquivalence;exact H.
 - reflexivity.
 - apply(proj1(ENBuilders cs)).
 - apply(proj2(ENBuilders cs)).
Qed.
Print Assumptions ENLiteralBuilderEntry.
Print Assumptions ENWholeSpatial.
Print Assumptions ENContractChecked.
