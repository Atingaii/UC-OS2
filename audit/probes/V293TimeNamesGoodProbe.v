Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
(* Independently chosen literal layout and abstract state. No initialization
   reachability or whole-kernel invariant is asserted. *)
Require Import CertiOS.certiucos.v293.proofs.V293TimeNamesGood.
Require Import CertiOS.certiucos.v293.proofs.V293TimeSharedGood.
Require Import CertiOS.certiucos.v293.proofs.V293TimeSetAPI.
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
Definition NamesGE : env := set (sig OSTCBCur (90%positive,Tptr Tvoid)) 1001%Z (80%positive,Tint32).
Definition NamesLE : env := set (sig 1002%Z (81%positive,Tint32)) 1003%Z (82%positive,Tint32).
Definition NamesTid : tid := (91%positive,Int.zero).
Definition NamesState M O : RstateOP :=
  (NamesGE,NamesLE,M,(fun _=>false),(true,[],[]),O,V293_time_set_action (Int.repr 42)).
Definition NamesBytes b perm tp v := V293_encoded_memory b 0 perm (encode_val tp v).
Definition NamesClock n := NamesBytes 80%positive true Tint32 (Vint32 n).
Definition NamesPointer := NamesBytes 90%positive false (Tptr Tvoid) (Vptr NamesTid).
Definition NamesAbstract n := merge (sig curtid (oscurt NamesTid))
  (merge (sig abstcblsid (abstcblist (emp:TcbMod.map)))
    (merge (sig absecblsid (absecblist (emp:EcbMod.map))) (sig ostmid (ostm n)))).

Lemma NamesStar : forall m1 m2 m o1 o2 o p q,
  join m1 m2 m -> join o1 o2 o -> NamesState m1 o1 |= p -> NamesState m2 o2 |= q ->
  NamesState m o |= p ** q.
Proof.
  intros. exists m1. exists m2. exists m. exists o1. exists o2. exists o.
  repeat first [assumption | reflexivity | split].
Qed.
Lemma NamesPointerSpatial : NamesState NamesPointer emp |= CurTid NamesTid.
Proof.
  exists Tvoid. exists 90%positive.
  eapply NamesStar with (m1:=emp) (m2:=NamesPointer) (o1:=emp) (o2:=emp).
  - apply map_join_comm;apply map_join_emp.
  - apply map_join_emp.
  - exists 90%positive. split;[vm_compute;reflexivity | ]. repeat split;reflexivity.
  - split;[apply V293_encoded_memory_mapsto | reflexivity].
Qed.
Ltac NamesAbsApart :=
  apply map_join_merge;apply map_disjoint;let k:=fresh "key" in intro k;destruct k;vm_compute;auto.
Lemma NamesAbstractSpatial : forall n,
  NamesState emp (NamesAbstract n) |= V293_shared_fields NamesTid emp emp n.
Proof.
  intro n. unfold V293_shared_fields,NamesAbstract.
  repeat (eapply NamesStar with (m1:=emp) (m2:=emp);
    [apply map_join_emp | NamesAbsApart | split;reflexivity | ]).
  split;reflexivity.
Qed.
Theorem NamesCoreSpatial : forall n,
  NamesState (merge NamesPointer (NamesClock n)) (NamesAbstract n) |= V293_time_shared_core 80%positive.
Proof.
  intro n. exists n. eapply NamesStar with
    (m1:=NamesPointer) (m2:=NamesClock n) (o1:=NamesAbstract n) (o2:=emp).
  - apply map_join_merge. apply map_disjoint. intros [b i].
    destruct (Pos.eq_dec b 90%positive);[subst b;right;left | left].
    all:unfold NamesPointer,NamesClock,NamesBytes;
      rewrite V293_encoded_memory_outside by (left;congruence);reflexivity.
  - apply map_join_emp.
  - exists NamesTid. exists (emp:TcbMod.map). exists (emp:EcbMod.map).
    eapply NamesStar with (m1:=NamesPointer) (m2:=emp) (o1:=emp) (o2:=NamesAbstract n).
    + apply map_join_emp.
    + apply map_join_comm;apply map_join_emp.
    + exact NamesPointerSpatial.
    + apply NamesAbstractSpatial.
  - split;[apply V293_encoded_memory_mapsto | reflexivity].
Qed.
Theorem NamesLiteralClockAgreement : forall n,
  get (NamesAbstract n) ostmid = Some (ostm n) /\
  load Tint32 (merge NamesPointer (NamesClock n)) (80%positive,0%Z) = Some (Vint32 n).
Proof.
  intro n. pose proof (NamesCoreSpatial n) as H.
  destruct (V293_time_shared_clock_agreement _ _ _ _ _ _ _ _ H) as [clock [Abstract Physical]].
  assert (Literal : get (NamesAbstract n) ostmid = Some (ostm n)) by (vm_compute;reflexivity).
  change (get (NamesAbstract n) ostmid = Some (ostm clock)) in Abstract.
  assert (clock=n) by congruence. subst clock. split;assumption.
Qed.
Lemma NamesLocalCell : forall x b v,
  get NamesLE x = Some (b,Tint32) ->
  NamesState (NamesBytes b true Tint32 v) emp |= V293_time_cell true x b v.
Proof.
  intros x b v E. unfold V293_time_cell.
  eapply NamesStar with (m1:=emp) (m2:=NamesBytes b true Tint32 v) (o1:=emp) (o2:=emp).
  - apply map_join_comm;apply map_join_emp.
  - apply map_join_emp.
  - exists b. split;[exact E | ]. repeat split;reflexivity.
  - split;[apply V293_encoded_memory_mapsto | reflexivity].
Qed.
Ltac NamesMemApart k :=
  apply map_join_merge;apply map_disjoint;intros [b i];
  destruct (Pos.eq_dec b k);[subst b;right;left | left];
  unfold NamesPointer,NamesBytes;
  repeat rewrite map_merge_semp by reflexivity;
  repeat rewrite V293_encoded_memory_outside by (left;congruence);reflexivity.
Definition NamesJointMemory n := merge (NamesClock n)
  (merge (NamesBytes 81%positive true Tint32 (Vint32 (Int.repr 42)))
    (merge (NamesBytes 82%positive true Tint32 Vundef)
      (NamesBytes 90%positive true (Tptr Tvoid) (Vptr NamesTid)))).
Lemma NamesCurrentFull : NamesState
    (NamesBytes 90%positive true (Tptr Tvoid) (Vptr NamesTid)) emp |=
    GV OSTCBCur @ (Tptr Tvoid) |-> Vptr NamesTid.
Proof.
  exists 90%positive. eapply NamesStar with (m1:=emp)
    (m2:=NamesBytes 90%positive true (Tptr Tvoid) (Vptr NamesTid)) (o1:=emp) (o2:=emp).
  - apply map_join_comm;apply map_join_emp.
  - apply map_join_emp.
  - exists 90%positive. split;[vm_compute;reflexivity | ]. repeat split;reflexivity.
  - split;[apply V293_encoded_memory_mapsto | reflexivity].
Qed.
Definition NamesLi : LocalInv := V293_time_names_li 1001%Z 80%positive.
Lemma NamesLiGood : GoodLInvAsrt NamesLi.
Proof. apply V293_time_names_local_good. Qed.
Lemma NamesGlobal : forall t lg,
  p_local NamesLi t lg ==> Agvarenv 1001%Z Tint32 (80%positive,0%Z) ** p_local NamesLi t lg.
Proof. apply V293_time_names_global. Qed.
Lemma NamesNoAbs : NoAbs NamesLi.
Proof. apply V293_time_names_noabs. Qed.
Definition NamesUnit := V293_TimeSet_api_unit 2000%Z 1001%Z 1002%Z 1003%Z.
Definition NamesSpec := V293_TimeSet_api_spec 2000%Z.
Definition NamesPre :=
  ((<||V293_time_set_action (Int.repr 42)||> ** p_local NamesLi NamesTid [] **
    ((LV 1002%Z @ Tint32 |-> Vint32 (Int.repr 42)) **
      ((EX v : val, LV 1003%Z @ Tint32 |-> v) ** Aemp)) **
    Aie true ** Ais nil ** Acs nil ** Aisr empisr) ** V293_time_api_domain 1002%Z 1003%Z).
Definition NamesPost := fun result =>
  ((<||spec_done result||> ** p_local NamesLi NamesTid [] **
    ((EX v : val, LV 1002%Z @ Tint32 |-> v) **
      ((EX v : val, LV 1003%Z @ Tint32 |-> v) ** Aemp)) **
    Aie true ** Ais nil ** Acs nil ** Aisr empisr) ** V293_time_api_domain 1002%Z 1003%Z).
Theorem NamesActualBuilders :
  Some NamesPre=BuildPreA' NamesUnit 2000%Z V293_TimeSet_api
    [Vint32 (Int.repr 42)] NamesLi NamesTid [] /\
  Some NamesPost=BuildRetA' NamesUnit 2000%Z V293_TimeSet_api
    [Vint32 (Int.repr 42)] NamesLi NamesTid [].
Proof. split;reflexivity. Qed.
Theorem NamesRejectsInvalidInputs :
  BuildPreA' NamesUnit 2000%Z V293_TimeSet_api [] NamesLi NamesTid []=None /\
  BuildPreA' NamesUnit 2000%Z V293_TimeSet_api [Vnull] NamesLi NamesTid []=None /\
  BuildPreA' NamesUnit 2000%Z V293_TimeSet_api [Vint32 (Int.repr 42);Vint32 Int.zero] NamesLi NamesTid []=None /\
  BuildPreA' (V293_TimeSet_api_unit 2000%Z 1001%Z 1002%Z 1002%Z)
    2000%Z V293_TimeSet_api [Vint32 (Int.repr 42)] NamesLi NamesTid []=None.
Proof. repeat split;reflexivity. Qed.
Theorem NamesInstantiated : forall Spec sd lg,
  APIRule NamesUnit NamesSpec Spec sd NamesLi (V293_time_shared_inv 80%positive) lg.
Proof.
  intros. apply V293_TimeSet_api_rule;try congruence.
  - apply NamesLiGood.
  - apply NamesNoAbs.
  - apply NamesGlobal.
Qed.
Lemma NamesDomain : eq_dom_env NamesLE [(1002%Z,Tint32);(1003%Z,Tint32)].
Proof.
  intros x tp. split.
  - simpl. intros [E | [E | F]];try contradiction;inversion E;subst;
      eexists;vm_compute;reflexivity.
  - intros [b E]. change (get NamesLE x=Some (b,tp)) in E. destruct (Z.eq_dec x 1002%Z) as [Eq | Neq].
    + subst x. assert (Known : get NamesLE 1002%Z=Some (81%positive,Tint32)) by reflexivity.
      vm_compute in E. inversion E;subst. simpl;auto.
    + destruct (Z.eq_dec x 1003%Z) as [Eq | Neq'].
      * subst x. assert (Known : get NamesLE 1003%Z=Some (82%positive,Tint32)) by reflexivity.
        vm_compute in E. inversion E;subst. simpl;auto.
      * unfold NamesLE in E. rewrite map_get_set' in E by congruence.
        rewrite map_get_sig' in E by congruence. discriminate.
Qed.
Lemma NamesEmpStar : forall p q,
  NamesState emp emp |= p -> NamesState emp emp |= q ->
  NamesState emp emp |= p ** q.
Proof. intros;eapply NamesStar;[apply map_join_emp | apply map_join_emp | eassumption | eassumption]. Qed.
Lemma NamesEmpty : NamesState emp emp |=
  LINV NamesLi NamesTid [] **
    (<||V293_time_set_action (Int.repr 42)||> ** OS[empisr,true,nil,nil] **
      V293_time_api_domain 1002%Z 1003%Z).
Proof.
  apply NamesEmpStar.
  - unfold LINV,NamesLi. apply NamesEmpStar.
    + exists 80%positive. split;[reflexivity | ]. repeat split;reflexivity.
    + split;[apply NamesLiGood | repeat split;reflexivity].
  - apply NamesEmpStar.
    + repeat split;reflexivity.
    + apply NamesEmpStar.
      * repeat apply NamesEmpStar;repeat split;reflexivity.
      * split;[apply NamesDomain | repeat split;reflexivity].
Qed.
Lemma NamesLocalVar : forall x b v,
  get NamesLE x=Some (b,Tint32) ->
  NamesState (NamesBytes b true Tint32 v) emp |= LV x @ Tint32 |-> v.
Proof. intros x b v E. exists b. apply NamesLocalCell;exact E. Qed.
Theorem NamesJointEntry : forall old,
  NamesState (NamesJointMemory old) (NamesAbstract old) |=
    V293_time_shared_core 80%positive ** NamesPre.
Proof.
  intro old.
  assert (Raw : NamesState (NamesJointMemory old) (NamesAbstract old) |=
    (PV (80%positive,Int.zero) @ Tint32 |-> Vint32 old) **
    ((LV 1002%Z @ Tint32 |-> Vint32 (Int.repr 42)) **
      ((LV 1003%Z @ Tint32 |-> Vundef) **
        ((GV OSTCBCur @ (Tptr Tvoid) |-> Vptr NamesTid) **
          (V293_shared_fields NamesTid emp emp old **
            (LINV NamesLi NamesTid [] **
              (<||V293_time_set_action (Int.repr 42)||> ** OS[empisr,true,nil,nil] **
                V293_time_api_domain 1002%Z 1003%Z))))))).
  { unfold NamesJointMemory.
    eapply NamesStar with (o1:=emp) (o2:=NamesAbstract old).
    - unfold NamesClock. NamesMemApart 80%positive.
    - apply map_join_comm;apply map_join_emp.
    - split;[apply V293_encoded_memory_mapsto | reflexivity].
    - eapply NamesStar with (o1:=emp) (o2:=NamesAbstract old).
      + NamesMemApart 81%positive.
      + apply map_join_comm;apply map_join_emp.
      + apply NamesLocalVar;reflexivity.
      + eapply NamesStar with (o1:=emp) (o2:=NamesAbstract old).
        * NamesMemApart 82%positive.
        * apply map_join_comm;apply map_join_emp.
        * apply NamesLocalVar;reflexivity.
        * eapply NamesStar with
            (m1:=NamesBytes 90%positive true (Tptr Tvoid) (Vptr NamesTid))
            (m2:=emp) (o1:=emp) (o2:=NamesAbstract old).
          -- apply map_join_emp.
          -- apply map_join_comm;apply map_join_emp.
          -- apply NamesCurrentFull.
          -- eapply NamesStar with (m1:=emp) (m2:=emp) (o1:=NamesAbstract old) (o2:=emp).
             ++ apply map_join_emp.
             ++ apply map_join_emp.
             ++ apply NamesAbstractSpatial.
             ++ apply NamesEmpty. }
  assert (Pack : NamesState (NamesJointMemory old) (NamesAbstract old) |=
    (GV OSTCBCur @ (Tptr Tvoid) |-> Vptr NamesTid) **
    ((PV (80%positive,Int.zero) @ Tint32 |-> Vint32 old) **
      ((LV 1002%Z @ Tint32 |-> Vint32 (Int.repr 42)) **
        ((LV 1003%Z @ Tint32 |-> Vundef) **
          (V293_shared_fields NamesTid emp emp old **
            (LINV NamesLi NamesTid [] **
              (<||V293_time_set_action (Int.repr 42)||> ** OS[empisr,true,nil,nil] **
                V293_time_api_domain 1002%Z 1003%Z))))))) by (sep auto).
  eapply astar_mono in Pack;[ | apply GV_separate_rw | intros st H;exact H].
  clear Raw. unfold V293_time_shared_core,V293_time_shared_fields,NamesPre,p_local,CurTid.
  sep auto.
Qed.
Definition NamesCallerMemory :=
  merge (NamesBytes 81%positive true Tint32 (Vint32 (Int.repr 42)))
    (merge (NamesBytes 82%positive true Tint32 Vundef) NamesPointer).
Theorem NamesCallerEntry : NamesState NamesCallerMemory emp |= NamesPre.
Proof.
  assert (Raw : NamesState NamesCallerMemory emp |=
    (LV 1002%Z @ Tint32 |-> Vint32 (Int.repr 42)) **
      ((LV 1003%Z @ Tint32 |-> Vundef) **
        (CurTid NamesTid ** (LINV NamesLi NamesTid [] **
          (<||V293_time_set_action (Int.repr 42)||> ** OS[empisr,true,nil,nil] **
            V293_time_api_domain 1002%Z 1003%Z))))).
  { unfold NamesCallerMemory.
    eapply NamesStar;[NamesMemApart 81%positive | apply map_join_emp | apply NamesLocalVar;reflexivity | ].
    eapply NamesStar;[NamesMemApart 82%positive | apply map_join_emp | apply NamesLocalVar;reflexivity | ].
    eapply NamesStar with (m1:=NamesPointer) (m2:=emp) (o1:=emp) (o2:=emp).
    - apply map_join_emp.
    - apply map_join_emp.
    - apply NamesPointerSpatial.
    - apply NamesEmpty. }
  unfold NamesPre,p_local. sep auto.
Qed.
Theorem NamesBodyFromBuilders : forall Spec sd,
  InfRules Spec sd NamesLi (V293_time_shared_inv 80%positive) NamesPost Afalse
    NamesPre (V293_TimeSet_body 1001%Z 1002%Z 1003%Z) Afalse NamesTid.
Proof.
  intros. eapply (V293_TimeSet_api_contract NamesUnit 2000%Z Spec sd NamesLi []
    NamesTid [Vint32 (Int.repr 42)] NamesPre NamesPost 1001%Z 1002%Z 1003%Z 80%positive);
    try congruence.
  - apply NamesLiGood.
  - apply NamesNoAbs.
  - apply NamesGlobal.
  - reflexivity.
  - exact (proj1 NamesActualBuilders).
  - exact (proj2 NamesActualBuilders).
Qed.
Theorem NamesCallerLacksClock : forall i, get NamesCallerMemory (80%positive,i)=None.
Proof.
  intro i. unfold NamesCallerMemory,NamesPointer,NamesBytes.
  repeat rewrite map_merge_semp by reflexivity.
  repeat rewrite V293_encoded_memory_outside by (left;discriminate). reflexivity.
Qed.


Theorem NamesSameGood : GoodI (V293_time_shared_inv 80%positive) V293_scheduler NamesLi.
Proof. exact (V293_time_names_good 1001%Z 80%positive). Qed.
Theorem NamesSameAPI : forall lg Spec,
  APIRule NamesUnit NamesSpec Spec V293_scheduler NamesLi (V293_time_shared_inv 80%positive) lg.
Proof.
  intros lg Spec.
  exact (proj2 (V293_time_names_compatible 2000%Z 1001%Z 1002%Z 1003%Z 80%positive lg Spec
    ltac:(congruence) ltac:(congruence) ltac:(congruence))).
Qed.
Theorem NamesCombinedNonempty : forall old lg Spec,
  GoodI (V293_time_shared_inv 80%positive) V293_scheduler NamesLi /\
  APIRule NamesUnit NamesSpec Spec V293_scheduler NamesLi (V293_time_shared_inv 80%positive) lg /\
  NamesState (NamesJointMemory old) (NamesAbstract old) |=
    V293_time_shared_core 80%positive ** NamesPre.
Proof. intros;split;[apply NamesSameGood | ];split;[apply NamesSameAPI | apply NamesJointEntry]. Qed.
Print Assumptions NamesSameGood.
Print Assumptions NamesSameAPI.
Print Assumptions NamesCombinedNonempty.
Print Assumptions NamesActualBuilders.
Print Assumptions NamesJointEntry.
Print Assumptions NamesCallerEntry.
Print Assumptions NamesCallerLacksClock.
Print Assumptions NamesBodyFromBuilders.
