(* Independently chosen literal layout and abstract state. No initialization
   reachability or whole-kernel invariant is asserted. *)
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
Definition TimeAPIGE : env := set (sig OSTCBCur (90%positive,Tptr Tvoid)) 1001%Z (80%positive,Tint32).
Definition TimeAPILE : env := set (sig 1002%Z (81%positive,Tint32)) 1003%Z (82%positive,Tint32).
Definition TimeAPITid : tid := (91%positive,Int.zero).
Definition TimeAPIState M O : RstateOP :=
  (TimeAPIGE,TimeAPILE,M,(fun _=>false),(true,[],[]),O,V293_time_set_action (Int.repr 42)).
Definition TimeAPIBytes b perm tp v := V293_encoded_memory b 0 perm (encode_val tp v).
Definition TimeAPIClock n := TimeAPIBytes 80%positive true Tint32 (Vint32 n).
Definition TimeAPIPointer := TimeAPIBytes 90%positive false (Tptr Tvoid) (Vptr TimeAPITid).
Definition TimeAPIAbstract n := merge (sig curtid (oscurt TimeAPITid))
  (merge (sig abstcblsid (abstcblist (emp:TcbMod.map)))
    (merge (sig absecblsid (absecblist (emp:EcbMod.map))) (sig ostmid (ostm n)))).

Lemma TimeAPIStar : forall m1 m2 m o1 o2 o p q,
  join m1 m2 m -> join o1 o2 o -> TimeAPIState m1 o1 |= p -> TimeAPIState m2 o2 |= q ->
  TimeAPIState m o |= p ** q.
Proof.
  intros. exists m1. exists m2. exists m. exists o1. exists o2. exists o.
  repeat first [assumption | reflexivity | split].
Qed.
Lemma TimeAPIPointerSpatial : TimeAPIState TimeAPIPointer emp |= CurTid TimeAPITid.
Proof.
  exists Tvoid. exists 90%positive.
  eapply TimeAPIStar with (m1:=emp) (m2:=TimeAPIPointer) (o1:=emp) (o2:=emp).
  - apply map_join_comm;apply map_join_emp.
  - apply map_join_emp.
  - exists 90%positive. split;[vm_compute;reflexivity | ]. repeat split;reflexivity.
  - split;[apply V293_encoded_memory_mapsto | reflexivity].
Qed.
Ltac TimeAPIAbsApart :=
  apply map_join_merge;apply map_disjoint;let k:=fresh "key" in intro k;destruct k;vm_compute;auto.
Lemma TimeAPIAbstractSpatial : forall n,
  TimeAPIState emp (TimeAPIAbstract n) |= V293_shared_fields TimeAPITid emp emp n.
Proof.
  intro n. unfold V293_shared_fields,TimeAPIAbstract.
  repeat (eapply TimeAPIStar with (m1:=emp) (m2:=emp);
    [apply map_join_emp | TimeAPIAbsApart | split;reflexivity | ]).
  split;reflexivity.
Qed.
Theorem TimeAPICoreSpatial : forall n,
  TimeAPIState (merge TimeAPIPointer (TimeAPIClock n)) (TimeAPIAbstract n) |= V293_time_shared_core 80%positive.
Proof.
  intro n. exists n. eapply TimeAPIStar with
    (m1:=TimeAPIPointer) (m2:=TimeAPIClock n) (o1:=TimeAPIAbstract n) (o2:=emp).
  - apply map_join_merge. apply map_disjoint. intros [b i].
    destruct (Pos.eq_dec b 90%positive);[subst b;right;left | left].
    all:unfold TimeAPIPointer,TimeAPIClock,TimeAPIBytes;
      rewrite V293_encoded_memory_outside by (left;congruence);reflexivity.
  - apply map_join_emp.
  - exists TimeAPITid. exists (emp:TcbMod.map). exists (emp:EcbMod.map).
    eapply TimeAPIStar with (m1:=TimeAPIPointer) (m2:=emp) (o1:=emp) (o2:=TimeAPIAbstract n).
    + apply map_join_emp.
    + apply map_join_comm;apply map_join_emp.
    + exact TimeAPIPointerSpatial.
    + apply TimeAPIAbstractSpatial.
  - split;[apply V293_encoded_memory_mapsto | reflexivity].
Qed.
Theorem TimeAPILiteralClockAgreement : forall n,
  get (TimeAPIAbstract n) ostmid = Some (ostm n) /\
  load Tint32 (merge TimeAPIPointer (TimeAPIClock n)) (80%positive,0%Z) = Some (Vint32 n).
Proof.
  intro n. pose proof (TimeAPICoreSpatial n) as H.
  destruct (V293_time_shared_clock_agreement _ _ _ _ _ _ _ _ H) as [clock [Abstract Physical]].
  assert (Literal : get (TimeAPIAbstract n) ostmid = Some (ostm n)) by (vm_compute;reflexivity).
  change (get (TimeAPIAbstract n) ostmid = Some (ostm clock)) in Abstract.
  assert (clock=n) by congruence. subst clock. split;assumption.
Qed.
Lemma TimeAPILocalCell : forall x b v,
  get TimeAPILE x = Some (b,Tint32) ->
  TimeAPIState (TimeAPIBytes b true Tint32 v) emp |= V293_time_cell true x b v.
Proof.
  intros x b v E. unfold V293_time_cell.
  eapply TimeAPIStar with (m1:=emp) (m2:=TimeAPIBytes b true Tint32 v) (o1:=emp) (o2:=emp).
  - apply map_join_comm;apply map_join_emp.
  - apply map_join_emp.
  - exists b. split;[exact E | ]. repeat split;reflexivity.
  - split;[apply V293_encoded_memory_mapsto | reflexivity].
Qed.
Ltac TimeAPIMemApart k :=
  apply map_join_merge;apply map_disjoint;intros [b i];
  destruct (Pos.eq_dec b k);[subst b;right;left | left];
  unfold TimeAPIPointer,TimeAPIBytes;
  repeat rewrite map_merge_semp by reflexivity;
  repeat rewrite V293_encoded_memory_outside by (left;congruence);reflexivity.
Definition TimeAPIJointMemory n := merge (TimeAPIClock n)
  (merge (TimeAPIBytes 81%positive true Tint32 (Vint32 (Int.repr 42)))
    (merge (TimeAPIBytes 82%positive true Tint32 Vundef)
      (TimeAPIBytes 90%positive true (Tptr Tvoid) (Vptr TimeAPITid)))).
Lemma TimeAPICurrentFull : TimeAPIState
    (TimeAPIBytes 90%positive true (Tptr Tvoid) (Vptr TimeAPITid)) emp |=
    GV OSTCBCur @ (Tptr Tvoid) |-> Vptr TimeAPITid.
Proof.
  exists 90%positive. eapply TimeAPIStar with (m1:=emp)
    (m2:=TimeAPIBytes 90%positive true (Tptr Tvoid) (Vptr TimeAPITid)) (o1:=emp) (o2:=emp).
  - apply map_join_comm;apply map_join_emp.
  - apply map_join_emp.
  - exists 90%positive. split;[vm_compute;reflexivity | ]. repeat split;reflexivity.
  - split;[apply V293_encoded_memory_mapsto | reflexivity].
Qed.
Definition TimeAPILi : LocalInv :=
  fun _ _ => Agvarenv 1001%Z Tint32 (80%positive,0%Z).
Lemma TimeAPILiGood : GoodLInvAsrt TimeAPILi.
Proof.
  intros t lg. split;[exact I | ].
  intros ge le M ir aux O le' M' aux' ir' O' H H'.
  specialize (H (END None)). specialize (H' (END None)).
  destruct H as [b [GE [BE [EM EO]]]].
  destruct H' as [b' [GE' [BE' [EM' EO']]]].
  change (M=emp) in EM. change (M'=emp) in EM'.
  change (O=emp) in EO. change (O'=emp) in EO'.
  subst;split;reflexivity.
Qed.
Lemma TimeAPIGlobal : forall t lg,
  p_local TimeAPILi t lg ==>
    Agvarenv 1001%Z Tint32 (80%positive,0%Z) ** p_local TimeAPILi t lg.
Proof.
  intros t lg s H. apply astar_l_agvarenv_intro;[exact H | ].
  destruct s as [[[[[[ge le] M] ir] aux] O] op].
  unfold p_local in H. apply sat_split in H.
  destruct H as (m1 & m2 & o1 & o2 & JM & JO & HC & HR).
  unfold LINV,TimeAPILi in HR. apply sat_split in HR.
  destruct HR as (m3 & m4 & o3 & o4 & JM' & JO' & Name & Good).
  apply agvarenv_elim in Name. exact (proj1 Name).
Qed.
Lemma TimeAPINoAbs : NoAbs TimeAPILi.
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
  assert (GE : get ge 1001%Z = Some (80%positive,Tint32)).
  { apply sat_split in HR. destruct HR as (ml & mf & ol & ofr & JM2 & JO2 & HL & HF).
    unfold LINV,TimeAPILi in HL. apply astar_l_agvarenv_elim in HL.
    exact (proj2 (proj1 HL)). }
  subst o1. exists lg.
  apply sat_split'. exists m1. exists m2. exists (emp:osabst). exists O'.
  repeat first [assumption | solve [apply map_join_comm;apply map_join_emp] | split].
  apply sat_split'. exists (emp:mem). exists m2. exists (emp:osabst). exists O'.
  repeat first [solve [apply map_join_comm;apply map_join_emp] | split].
  unfold LINV,TimeAPILi. apply astar_l_agvarenv_intro.
  - split;[apply TimeAPILiGood | repeat split;reflexivity].
  - split;[reflexivity | exact GE].
Qed.
Definition TimeAPIUnit := V293_TimeSet_api_unit 2000%Z 1001%Z 1002%Z 1003%Z.
Definition TimeAPISpec := V293_TimeSet_api_spec 2000%Z.
Definition TimeAPIPre :=
  ((<||V293_time_set_action (Int.repr 42)||> ** p_local TimeAPILi TimeAPITid [] **
    ((LV 1002%Z @ Tint32 |-> Vint32 (Int.repr 42)) **
      ((EX v : val, LV 1003%Z @ Tint32 |-> v) ** Aemp)) **
    Aie true ** Ais nil ** Acs nil ** Aisr empisr) ** V293_time_api_domain 1002%Z 1003%Z).
Definition TimeAPIPost := fun result =>
  ((<||spec_done result||> ** p_local TimeAPILi TimeAPITid [] **
    ((EX v : val, LV 1002%Z @ Tint32 |-> v) **
      ((EX v : val, LV 1003%Z @ Tint32 |-> v) ** Aemp)) **
    Aie true ** Ais nil ** Acs nil ** Aisr empisr) ** V293_time_api_domain 1002%Z 1003%Z).
Theorem TimeAPIActualBuilders :
  Some TimeAPIPre=BuildPreA' TimeAPIUnit 2000%Z V293_TimeSet_api
    [Vint32 (Int.repr 42)] TimeAPILi TimeAPITid [] /\
  Some TimeAPIPost=BuildRetA' TimeAPIUnit 2000%Z V293_TimeSet_api
    [Vint32 (Int.repr 42)] TimeAPILi TimeAPITid [].
Proof. split;reflexivity. Qed.
Theorem TimeAPIRejectsInvalidInputs :
  BuildPreA' TimeAPIUnit 2000%Z V293_TimeSet_api [] TimeAPILi TimeAPITid []=None /\
  BuildPreA' TimeAPIUnit 2000%Z V293_TimeSet_api [Vnull] TimeAPILi TimeAPITid []=None /\
  BuildPreA' TimeAPIUnit 2000%Z V293_TimeSet_api [Vint32 (Int.repr 42);Vint32 Int.zero] TimeAPILi TimeAPITid []=None /\
  BuildPreA' (V293_TimeSet_api_unit 2000%Z 1001%Z 1002%Z 1002%Z)
    2000%Z V293_TimeSet_api [Vint32 (Int.repr 42)] TimeAPILi TimeAPITid []=None.
Proof. repeat split;reflexivity. Qed.
Theorem TimeAPIInstantiated : forall Spec sd lg,
  APIRule TimeAPIUnit TimeAPISpec Spec sd TimeAPILi (V293_time_shared_inv 80%positive) lg.
Proof.
  intros. apply V293_TimeSet_api_rule;try congruence.
  - apply TimeAPILiGood.
  - apply TimeAPINoAbs.
  - apply TimeAPIGlobal.
Qed.
Lemma TimeAPIDomain : eq_dom_env TimeAPILE [(1002%Z,Tint32);(1003%Z,Tint32)].
Proof.
  intros x tp. split.
  - simpl. intros [E | [E | F]];try contradiction;inversion E;subst;
      eexists;vm_compute;reflexivity.
  - intros [b E]. change (get TimeAPILE x=Some (b,tp)) in E. destruct (Z.eq_dec x 1002%Z) as [Eq | Neq].
    + subst x. assert (Known : get TimeAPILE 1002%Z=Some (81%positive,Tint32)) by reflexivity.
      vm_compute in E. inversion E;subst. simpl;auto.
    + destruct (Z.eq_dec x 1003%Z) as [Eq | Neq'].
      * subst x. assert (Known : get TimeAPILE 1003%Z=Some (82%positive,Tint32)) by reflexivity.
        vm_compute in E. inversion E;subst. simpl;auto.
      * unfold TimeAPILE in E. rewrite map_get_set' in E by congruence.
        rewrite map_get_sig' in E by congruence. discriminate.
Qed.
Lemma TimeAPIEmpStar : forall p q,
  TimeAPIState emp emp |= p -> TimeAPIState emp emp |= q ->
  TimeAPIState emp emp |= p ** q.
Proof. intros;eapply TimeAPIStar;[apply map_join_emp | apply map_join_emp | eassumption | eassumption]. Qed.
Lemma TimeAPIEmpty : TimeAPIState emp emp |=
  LINV TimeAPILi TimeAPITid [] **
    (<||V293_time_set_action (Int.repr 42)||> ** OS[empisr,true,nil,nil] **
      V293_time_api_domain 1002%Z 1003%Z).
Proof.
  apply TimeAPIEmpStar.
  - unfold LINV,TimeAPILi. apply TimeAPIEmpStar.
    + exists 80%positive. split;[reflexivity | ]. repeat split;reflexivity.
    + split;[apply TimeAPILiGood | repeat split;reflexivity].
  - apply TimeAPIEmpStar.
    + repeat split;reflexivity.
    + apply TimeAPIEmpStar.
      * repeat apply TimeAPIEmpStar;repeat split;reflexivity.
      * split;[apply TimeAPIDomain | repeat split;reflexivity].
Qed.
Lemma TimeAPILocalVar : forall x b v,
  get TimeAPILE x=Some (b,Tint32) ->
  TimeAPIState (TimeAPIBytes b true Tint32 v) emp |= LV x @ Tint32 |-> v.
Proof. intros x b v E. exists b. apply TimeAPILocalCell;exact E. Qed.
Theorem TimeAPIJointEntry : forall old,
  TimeAPIState (TimeAPIJointMemory old) (TimeAPIAbstract old) |=
    V293_time_shared_core 80%positive ** TimeAPIPre.
Proof.
  intro old.
  assert (Raw : TimeAPIState (TimeAPIJointMemory old) (TimeAPIAbstract old) |=
    (PV (80%positive,Int.zero) @ Tint32 |-> Vint32 old) **
    ((LV 1002%Z @ Tint32 |-> Vint32 (Int.repr 42)) **
      ((LV 1003%Z @ Tint32 |-> Vundef) **
        ((GV OSTCBCur @ (Tptr Tvoid) |-> Vptr TimeAPITid) **
          (V293_shared_fields TimeAPITid emp emp old **
            (LINV TimeAPILi TimeAPITid [] **
              (<||V293_time_set_action (Int.repr 42)||> ** OS[empisr,true,nil,nil] **
                V293_time_api_domain 1002%Z 1003%Z))))))).
  { unfold TimeAPIJointMemory.
    eapply TimeAPIStar with (o1:=emp) (o2:=TimeAPIAbstract old).
    - unfold TimeAPIClock. TimeAPIMemApart 80%positive.
    - apply map_join_comm;apply map_join_emp.
    - split;[apply V293_encoded_memory_mapsto | reflexivity].
    - eapply TimeAPIStar with (o1:=emp) (o2:=TimeAPIAbstract old).
      + TimeAPIMemApart 81%positive.
      + apply map_join_comm;apply map_join_emp.
      + apply TimeAPILocalVar;reflexivity.
      + eapply TimeAPIStar with (o1:=emp) (o2:=TimeAPIAbstract old).
        * TimeAPIMemApart 82%positive.
        * apply map_join_comm;apply map_join_emp.
        * apply TimeAPILocalVar;reflexivity.
        * eapply TimeAPIStar with
            (m1:=TimeAPIBytes 90%positive true (Tptr Tvoid) (Vptr TimeAPITid))
            (m2:=emp) (o1:=emp) (o2:=TimeAPIAbstract old).
          -- apply map_join_emp.
          -- apply map_join_comm;apply map_join_emp.
          -- apply TimeAPICurrentFull.
          -- eapply TimeAPIStar with (m1:=emp) (m2:=emp) (o1:=TimeAPIAbstract old) (o2:=emp).
             ++ apply map_join_emp.
             ++ apply map_join_emp.
             ++ apply TimeAPIAbstractSpatial.
             ++ apply TimeAPIEmpty. }
  assert (Pack : TimeAPIState (TimeAPIJointMemory old) (TimeAPIAbstract old) |=
    (GV OSTCBCur @ (Tptr Tvoid) |-> Vptr TimeAPITid) **
    ((PV (80%positive,Int.zero) @ Tint32 |-> Vint32 old) **
      ((LV 1002%Z @ Tint32 |-> Vint32 (Int.repr 42)) **
        ((LV 1003%Z @ Tint32 |-> Vundef) **
          (V293_shared_fields TimeAPITid emp emp old **
            (LINV TimeAPILi TimeAPITid [] **
              (<||V293_time_set_action (Int.repr 42)||> ** OS[empisr,true,nil,nil] **
                V293_time_api_domain 1002%Z 1003%Z))))))) by (sep auto).
  eapply astar_mono in Pack;[ | apply GV_separate_rw | intros st H;exact H].
  clear Raw. unfold V293_time_shared_core,V293_time_shared_fields,TimeAPIPre,p_local,CurTid.
  sep auto.
Qed.
Definition TimeAPICallerMemory :=
  merge (TimeAPIBytes 81%positive true Tint32 (Vint32 (Int.repr 42)))
    (merge (TimeAPIBytes 82%positive true Tint32 Vundef) TimeAPIPointer).
Theorem TimeAPICallerEntry : TimeAPIState TimeAPICallerMemory emp |= TimeAPIPre.
Proof.
  assert (Raw : TimeAPIState TimeAPICallerMemory emp |=
    (LV 1002%Z @ Tint32 |-> Vint32 (Int.repr 42)) **
      ((LV 1003%Z @ Tint32 |-> Vundef) **
        (CurTid TimeAPITid ** (LINV TimeAPILi TimeAPITid [] **
          (<||V293_time_set_action (Int.repr 42)||> ** OS[empisr,true,nil,nil] **
            V293_time_api_domain 1002%Z 1003%Z))))).
  { unfold TimeAPICallerMemory.
    eapply TimeAPIStar;[TimeAPIMemApart 81%positive | apply map_join_emp | apply TimeAPILocalVar;reflexivity | ].
    eapply TimeAPIStar;[TimeAPIMemApart 82%positive | apply map_join_emp | apply TimeAPILocalVar;reflexivity | ].
    eapply TimeAPIStar with (m1:=TimeAPIPointer) (m2:=emp) (o1:=emp) (o2:=emp).
    - apply map_join_emp.
    - apply map_join_emp.
    - apply TimeAPIPointerSpatial.
    - apply TimeAPIEmpty. }
  unfold TimeAPIPre,p_local. sep auto.
Qed.
Theorem TimeAPIBodyFromBuilders : forall Spec sd,
  InfRules Spec sd TimeAPILi (V293_time_shared_inv 80%positive) TimeAPIPost Afalse
    TimeAPIPre (V293_TimeSet_body 1001%Z 1002%Z 1003%Z) Afalse TimeAPITid.
Proof.
  intros. eapply (V293_TimeSet_api_contract TimeAPIUnit 2000%Z Spec sd TimeAPILi []
    TimeAPITid [Vint32 (Int.repr 42)] TimeAPIPre TimeAPIPost 1001%Z 1002%Z 1003%Z 80%positive);
    try congruence.
  - apply TimeAPILiGood.
  - apply TimeAPINoAbs.
  - apply TimeAPIGlobal.
  - reflexivity.
  - exact (proj1 TimeAPIActualBuilders).
  - exact (proj2 TimeAPIActualBuilders).
Qed.
Theorem TimeAPICallerLacksClock : forall i, get TimeAPICallerMemory (80%positive,i)=None.
Proof.
  intro i. unfold TimeAPICallerMemory,TimeAPIPointer,TimeAPIBytes.
  repeat rewrite map_merge_semp by reflexivity.
  repeat rewrite V293_encoded_memory_outside by (left;discriminate). reflexivity.
Qed.
Print Assumptions TimeAPILiGood.
Print Assumptions TimeAPINoAbs.
Print Assumptions TimeAPIGlobal.
Print Assumptions TimeAPIActualBuilders.
Print Assumptions TimeAPIRejectsInvalidInputs.
Print Assumptions TimeAPIInstantiated.
Print Assumptions TimeAPIJointEntry.
Print Assumptions TimeAPICallerLacksClock.

Print Assumptions TimeAPICallerEntry.
Print Assumptions TimeAPIBodyFromBuilders.
