(* One literal joint heap: old ready/TCB/table/clock plus two disjoint locals.
   This is allocated-entry satisfiability, not boot or a call-to-return trace. *)
Require Import CertiOS.certiucos.v293.proofs.V293TimeReadyEntry.
Require Import CertiOS.certiucos.v293.proofs.V293TimeReadyAPI.
Require Import CertiOS.certiucos.v293.proofs.V293TimeReadyShared.
Require Import CertiOS.certiucos.v293.proofs.V293TimeGetAPI.
Require Import CertiOS.certiucos.v293.proofs.V293TimeGetLink.
Require Import CertiOS.certiucos.v293.proofs.V293TimeSetAPI.
Require Import CertiOS.certiucos.v293.proofs.V293TimeNamesGood.
Require Import CertiOS.certiucos.v293.proofs.V293TimeShared.
Require Import CertiOS.certiucos.v293.proofs.V293TimeSharedSet.
Require Import CertiOS.certiucos.v293.proofs.V293TimeAccess.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293SharedStateWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTargetWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewWitness.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyTaskInvariant.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.audit.probes.V293TimeReadySharedProbe.
Require Import CertiOS.audit.probes.V293TimeReadyAPIProbe.
Require Import CertiOS.audit.probes.V293TaskRecordOwnershipProbe.
Require Import CertiOS.audit.probes.V293TaskRecordInvariantProbe.
Require Import CertiOS.audit.probes.V293ReadyTaskInvariantProbe.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.auxdef.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.framework.proof.memory_prop.
Require Import CertiOS.framework.proof.lmachLib.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Definition JGE : env := set V293_shared_fixture_ge 1001%Z (150%positive,Tint32).
Definition JLE : env := set (sig 1002%Z (160%positive,Tint32)) 1003%Z (161%positive,Tint32).
Definition Jbytes b v := V293_encoded_memory b 0 true (encode_val Tint32 v).
Definition Jlocals tmp save := merge (Jbytes 160%positive tmp) (Jbytes 161%positive save).
Definition Jmemory ct clock tmp save := merge (TRmemory ct clock) (Jlocals tmp save).
Definition Jstate op M O : RstateOP := (JGE,JLE,M,empisr,(true,[],[]),O,op).
Definition JgetPre ct lg :=
  ((<||V293_time_get_action||> ** p_local RAli ct lg **
    ((EX v : val, LV 1002%Z @ Tint32 |-> v) **
      ((EX v : val, LV 1003%Z @ Tint32 |-> v) ** Aemp)) **
    Aie true ** Ais nil ** Acs nil ** Aisr empisr) ** V293_time_api_domain 1002%Z 1003%Z).
Definition JsetPre ct lg n :=
  ((<||V293_time_set_action n||> ** p_local RAli ct lg **
    ((LV 1002%Z @ Tint32 |-> Vint32 n) **
      ((EX v : val, LV 1003%Z @ Tint32 |-> v) ** Aemp)) **
    Aie true ** Ais nil ** Acs nil ** Aisr empisr) ** V293_time_api_domain 1002%Z 1003%Z).

Lemma Jstar : forall op m1 m2 m o1 o2 o p q,
  join m1 m2 m -> join o1 o2 o -> Jstate op m1 o1 |= p -> Jstate op m2 o2 |= q ->
  Jstate op m o |= p ** q.
Proof. intros. exists m1. exists m2. exists m. exists o1. exists o2. exists o.
  repeat first [assumption | reflexivity | split]. Qed.
Lemma Jcurrent_name : get JGE OSTCBCur=get V293_shared_fixture_ge OSTCBCur.
Proof. reflexivity. Qed.
Theorem Jcore_and_current : forall ct clock op,
  Jstate op (TRmemory ct clock) (TRabstract ct clock) |=
    V293_time_ready_core 80%positive 81%positive 82%positive 150%positive ** CurTid ct.
Proof.
  intros. pose proof (V293_time_ready_entry_halves _ _ _ _ _ _ (TRliteral_spatial ct clock)) as H.
  apply sat_split in H. destruct H as (m1&m2&o1&o2&JM&JO&Core&Current).
  eapply Jstar;[exact JM | exact JO | | ].
  - eapply V293_time_ready_entry_context;[exact Jcurrent_name | exact Core].
  - eapply V293_current_entry_context;[exact Jcurrent_name | exact Current].
Qed.
Lemma Joutside : forall ct clock b off,
  b=160%positive \/ b=161%positive -> get (TRmemory ct clock) (b,off)=None.
Proof.
  intros ct clock b off B. destruct B;subst b;
    unfold TRmemory,RTfull,RImemory,RTmemory,OwnershipMemory,V293_shared_fixture_mem,TRclock;
    repeat rewrite map_merge_semp by reflexivity;
    repeat rewrite V293_encoded_memory_outside by (left;discriminate);
    repeat rewrite OwnershipCellsOutside by (intro H;vm_compute in H;intuition congruence);reflexivity.
Qed.
Lemma Jlocals_join : forall tmp save, join (Jbytes 160%positive tmp) (Jbytes 161%positive save) (Jlocals tmp save).
Proof.
  intros. apply map_join_merge. apply map_disjoint. intros [b off].
  destruct (Pos.eq_dec b 160%positive);[subst b;right;left | left];
    unfold Jbytes;rewrite V293_encoded_memory_outside by (left;congruence);reflexivity.
Qed.
Lemma Jjoint_join : forall ct clock tmp save,
  join (TRmemory ct clock) (Jlocals tmp save) (Jmemory ct clock tmp save).
Proof.
  intros. apply map_join_merge. apply map_disjoint. intros [b off].
  destruct (Pos.eq_dec b 160%positive) as [B | B];[left;apply Joutside;auto | ].
  destruct (Pos.eq_dec b 161%positive) as [C | C];[left;apply Joutside;auto | ].
  right;left. unfold Jlocals,Jbytes. rewrite map_merge_semp by reflexivity.
  repeat rewrite V293_encoded_memory_outside by (left;congruence). reflexivity.
Qed.
Lemma Jlocal : forall op x b v,
  get JLE x=Some(b,Tint32) -> Jstate op (Jbytes b v) emp |= LV x @ Tint32 |-> v.
Proof.
  intros op x b v Name. exists b.
  eapply Jstar with (m1:=emp)(m2:=Jbytes b v)(o1:=emp)(o2:=emp).
  - apply map_join_comm;apply map_join_emp.
  - apply map_join_emp.
  - exists b. split;[exact Name | ]. repeat split;reflexivity.
  - split;[apply V293_encoded_memory_mapsto | reflexivity].
Qed.
Lemma Jdomain : eq_dom_env JLE [(1002%Z,Tint32);(1003%Z,Tint32)].
Proof.
  intros x tp. split.
  - simpl. intros [E | [E | F]];try contradiction;inversion E;subst;
      eexists;vm_compute;reflexivity.
  - intros [b E]. change (get JLE x=Some(b,tp)) in E.
    destruct (Z.eq_dec x 1002%Z) as [B | B].
    + subst x. vm_compute in E. inversion E;subst. simpl;auto.
    + destruct (Z.eq_dec x 1003%Z) as [C | C].
      * subst x. vm_compute in E. inversion E;subst. simpl;auto.
      * unfold JLE in E. rewrite map_get_set' in E by congruence.
        rewrite map_get_sig' in E by congruence. discriminate.
Qed.
Lemma Jempty : forall op ct lg,
  Jstate op emp emp |= LINV RAli ct lg **
    (<||op||> ** OS[empisr,true,nil,nil] ** V293_time_api_domain 1002%Z 1003%Z).
Proof.
  intros op ct lg.
  assert (L : Jstate op emp emp |= LINV RAli ct lg).
  { unfold LINV,RAli,V293_time_names_li.
    eapply Jstar with (m1:=emp)(m2:=emp)(o1:=emp)(o2:=emp).
    - apply map_join_emp.
    - apply map_join_emp.
    - exists 150%positive. split;[reflexivity | ]. repeat split;reflexivity.
    - split;[apply V293_time_names_local_good | repeat split;reflexivity]. }
  assert (D : Jstate op emp emp |= V293_time_api_domain 1002%Z 1003%Z).
  { split;[exact Jdomain | repeat split;reflexivity]. }
  repeat first [exact L | exact D | solve [repeat split;reflexivity] |
    eapply Jstar with (m1:=emp)(m2:=emp)(o1:=emp)(o2:=emp);
      [apply map_join_emp | apply map_join_emp | | ]].
Qed.
Theorem Jraw_joint : forall op ct clock tmp save lg,
  Jstate op (Jmemory ct clock tmp save) (TRabstract ct clock) |=
    (V293_time_ready_core 80%positive 81%positive 82%positive 150%positive ** CurTid ct) **
      ((LV 1002%Z @ Tint32 |-> tmp) ** ((LV 1003%Z @ Tint32 |-> save) **
        (LINV RAli ct lg ** (<||op||> ** OS[empisr,true,nil,nil] ** V293_time_api_domain 1002%Z 1003%Z)))).
Proof.
  intros. eapply Jstar with (m1:=TRmemory ct clock)(m2:=Jlocals tmp save)
    (o1:=TRabstract ct clock)(o2:=emp).
  - apply Jjoint_join.
  - apply map_join_emp.
  - apply Jcore_and_current.
  - eapply Jstar with (m1:=Jbytes 160%positive tmp)(m2:=Jbytes 161%positive save)(o1:=emp)(o2:=emp).
    + apply Jlocals_join.
    + apply map_join_emp.
    + apply Jlocal;reflexivity.
    + eapply Jstar with (m1:=Jbytes 161%positive save)(m2:=emp)(o1:=emp)(o2:=emp).
      * apply map_join_emp.
      * apply map_join_emp.
      * apply Jlocal;reflexivity.
      * apply Jempty.
Qed.
Theorem Jget_joint : forall ct clock tmp save lg,
  Jstate V293_time_get_action (Jmemory ct clock tmp save) (TRabstract ct clock) |=
    V293_time_ready_core 80%positive 81%positive 82%positive 150%positive ** JgetPre ct lg.
Proof. intros. pose proof (Jraw_joint V293_time_get_action ct clock tmp save lg) as H.
  unfold JgetPre,p_local. sep auto. Qed.
Theorem Jset_joint : forall ct clock n save lg,
  Jstate (V293_time_set_action n) (Jmemory ct clock (Vint32 n) save) (TRabstract ct clock) |=
    V293_time_ready_core 80%positive 81%positive 82%positive 150%positive ** JsetPre ct lg n.
Proof. intros. pose proof (Jraw_joint (V293_time_set_action n) ct clock (Vint32 n) save lg) as H.
  unfold JsetPre,p_local. sep auto. Qed.
Theorem Jactual_builders : forall ct lg n,
  Some(JgetPre ct lg)=BuildPreA' RAapi 203%Z V293_TimeGet_api [] RAli ct lg /\
  Some(JsetPre ct lg n)=BuildPreA' RAapi 202%Z V293_TimeSet_api [Vint32 n] RAli ct lg.
Proof. intros;split;reflexivity. Qed.

Theorem Jget_allocated_contract : forall ct clock tmp save lg,
  exists post,
    Some(JgetPre ct lg)=BuildPreA' RAapi 203%Z V293_TimeGet_api [] RAli ct lg /\
    Some post=BuildRetA' RAapi 203%Z V293_TimeGet_api [] RAli ct lg /\
    InfRules RAspec V293_scheduler RAli TRinv post Afalse (JgetPre ct lg)
      (V293_TimeGet_body 1001%Z 1002%Z 1003%Z) Afalse ct /\
    Jstate V293_time_get_action (Jmemory ct clock tmp save) (TRabstract ct clock) |=
      V293_time_ready_core 80%positive 81%positive 82%positive 150%positive ** JgetPre ct lg.
Proof.
  intros. destruct (RAget_builders ct lg) as (pre&post&Pre&Post&Body).
  pose proof (proj1 (Jactual_builders ct lg Int.zero)) as Exact.
  rewrite <-Exact in Pre. inversion Pre;subst pre.
  exists post. split;[exact Exact | ]. split;[exact Post | ]. split;[exact Body | apply Jget_joint].
Qed.
Theorem Jset_allocated_contract : forall ct clock n save lg,
  exists post,
    Some(JsetPre ct lg n)=BuildPreA' RAapi 202%Z V293_TimeSet_api [Vint32 n] RAli ct lg /\
    Some post=BuildRetA' RAapi 202%Z V293_TimeSet_api [Vint32 n] RAli ct lg /\
    InfRules RAspec V293_scheduler RAli TRinv post Afalse (JsetPre ct lg n)
      (V293_TimeSet_body 1001%Z 1002%Z 1003%Z) Afalse ct /\
    Jstate (V293_time_set_action n) (Jmemory ct clock (Vint32 n) save) (TRabstract ct clock) |=
      V293_time_ready_core 80%positive 81%positive 82%positive 150%positive ** JsetPre ct lg n.
Proof.
  intros. destruct (RAset_builders ct lg n) as (pre&post&Pre&Post&Body).
  pose proof (proj2 (Jactual_builders ct lg n)) as Exact.
  rewrite <-Exact in Pre. inversion Pre;subst pre.
  exists post. split;[exact Exact | ]. split;[exact Post | ]. split;[exact Body | apply Jset_joint].
Qed.
Lemma Jclock_load : forall ct clock tmp save,
  load Tint32 (Jmemory ct clock tmp save) (150%positive,0%Z)=Some(Vint32 clock).
Proof.
  intros. eapply load_mem_mono;[apply TRclock_load | exists (Jlocals tmp save);apply Jjoint_join].
Qed.
Lemma Jticks_load : forall ct clock n save,
  load Tint32 (Jmemory ct clock (Vint32 n) save) (160%positive,0%Z)=Some(Vint32 n).
Proof.
  intros. eapply load_mem_mono with (M:=Jlocals (Vint32 n) save).
  - eapply load_mem_mono with (M:=Jbytes 160%positive (Vint32 n)).
    + eapply mapstoval_load;[reflexivity | apply V293_encoded_memory_mapsto].
    + exists (Jbytes 161%positive save). apply Jlocals_join.
  - exists (TRmemory ct clock). apply map_join_comm;apply Jjoint_join.
Qed.
Lemma Jretime_abstract : forall ct old n,
  set (TRabstract ct old) ostmid (ostm n)=TRabstract ct n.
Proof.
  intros. apply OSAbstMod.extensionality. intro id.
  change (get (set (TRabstract ct old) ostmid (ostm n)) id=get (TRabstract ct n) id).
  unfold TRabstract. destruct (OSAbstMod.eq_dec id ostmid);
    [subst id;rewrite !map_get_set | rewrite !map_get_set' by congruence];reflexivity.
Qed.
Lemma Jget_caller_any_clock : forall ct physical abstract tmp save lg,
  Jstate V293_time_get_action (Jmemory ct physical tmp save) (TRabstract ct abstract) |=
    JgetPre ct lg ** Atrue.
Proof.
  intros. pose proof (Jget_joint ct physical tmp save lg) as H.
  assert (Pack : Jstate V293_time_get_action (Jmemory ct physical tmp save) (TRabstract ct physical) |=
    EX v : int32, Aabsdata ostmid (ostm v) ** (JgetPre ct lg ** Atrue)).
  { unfold V293_time_ready_core,V293_time_ready_fields,V293_shared_fields in H. sep auto. }
  destruct Pack as [v Pack]. unfold Jstate in Pack.
  apply V293_shared_replace_slot with (new:=ostm abstract) in Pack.
  rewrite Jretime_abstract in Pack. change (Jstate V293_time_get_action
    (Jmemory ct physical tmp save) (TRabstract ct abstract) |=
    Aabsdata ostmid (ostm abstract) ** (JgetPre ct lg ** Atrue)) in Pack.
  clear H. sep auto.
Qed.
Theorem Jclock_control : forall ct clock bad tmp save lg,
  bad<>clock ->
  Jstate V293_time_get_action (Jmemory ct clock tmp save) (TRabstract ct clock) |=
    V293_time_ready_core 80%positive 81%positive 82%positive 150%positive ** JgetPre ct lg /\
  Jstate V293_time_get_action (Jmemory ct bad tmp save) (TRabstract ct clock) |= JgetPre ct lg ** Atrue /\
  (forall b off, b<>150%positive ->
    get (Jmemory ct bad tmp save) (b,off)=get (Jmemory ct clock tmp save) (b,off)) /\
  ~ Jstate V293_time_get_action (Jmemory ct bad tmp save) (TRabstract ct clock) |=
    V293_time_ready_core 80%positive 81%positive 82%positive 150%positive ** Atrue.
Proof.
  intros ct clock bad tmp save lg Different. split;[apply Jget_joint | ].
  split;[apply Jget_caller_any_clock | ]. split.
  - intros b off Apart. unfold Jmemory,TRmemory,TRclock. repeat rewrite map_merge_semp by reflexivity.
    repeat rewrite V293_encoded_memory_outside by (left;exact Apart). reflexivity.
  - intro Held. destruct (V293_time_ready_clock_agreement _ _ _ _ _ _ Held) as [v [Time Physical]].
    change (get (TRabstract ct clock) ostmid=Some(ostm v)) in Time.
    unfold TRabstract in Time. rewrite map_get_set in Time.
    change (load Tint32 (Jmemory ct bad tmp save) (150%positive,0%Z)=Some(Vint32 v)) in Physical.
    pose proof (Jclock_load ct bad tmp save). assert (v=clock) by congruence. congruence.
Qed.
Lemma Jsetter_required_load : forall op M O ct lg n,
  Jstate op M O |= JsetPre ct lg n ** Atrue ->
  load Tint32 M (160%positive,0%Z)=Some(Vint32 n).
Proof.
  intros op M O ct lg n H. unfold JsetPre in H.
  assert (Cell : Jstate op M O |= (LV 1002%Z @ Tint32 |-> Vint32 n) ** Atrue) by (clear -H;sep auto).
  unfold Alvarmapsto in Cell. sep normal in Cell. sep destruct Cell.
  assert (Name : Jstate op M O |= (L& 1002%Z @ Tint32 == (x,Int.zero)) ** Atrue)
    by (clear -Cell;sep auto).
  change (Jstate op M O |= V293_time_binding true 1002%Z x ** Atrue) in Name.
  destruct (V293_time_binding_env true 1002%Z x Atrue _ Name) as [NameEq | [Impossible _]].
  - change (get JLE 1002%Z=Some(x,Tint32)) in NameEq.
    assert (x=160%positive) by (vm_compute in NameEq;congruence). subst x.
    change (load Tint32 (getmem (Jstate op M O)) (160%positive,0%Z)=Some(Vint32 n)).
    eapply V293_star_load_r;[ | exact Cell]. intros st Both.
    eapply V293_star_load_l;[ | exact Both]. intros st1 Points.
    eapply mapstoval_load;[reflexivity | exact (proj1 Points)].
  - change (get JLE 1002%Z=None) in Impossible. vm_compute in Impossible. discriminate.
Qed.
Theorem Jsetter_slot_control : forall ct clock n bad save lg,
  bad<>n ->
  Jstate (V293_time_set_action n) (Jmemory ct clock (Vint32 n) save) (TRabstract ct clock) |=
    V293_time_ready_core 80%positive 81%positive 82%positive 150%positive ** JsetPre ct lg n /\
  Jstate (V293_time_set_action n) (Jmemory ct clock (Vint32 bad) save) (TRabstract ct clock) |=
    V293_time_ready_core 80%positive 81%positive 82%positive 150%positive ** Atrue /\
  (forall b off, b<>160%positive ->
    get (Jmemory ct clock (Vint32 bad) save) (b,off)=get (Jmemory ct clock (Vint32 n) save) (b,off)) /\
  load Tint32 (Jmemory ct clock (Vint32 bad) save) (150%positive,0%Z)=Some(Vint32 clock) /\
  ~ Jstate (V293_time_set_action n) (Jmemory ct clock (Vint32 bad) save) (TRabstract ct clock) |=
    JsetPre ct lg n ** Atrue.
Proof.
  intros ct clock n bad save lg Different. split;[apply Jset_joint | ]. split.
  - pose proof (Jraw_joint (V293_time_set_action n) ct clock (Vint32 bad) save lg) as H. sep auto.
  - split.
    + intros b off Apart. unfold Jmemory,Jlocals,Jbytes. repeat rewrite map_merge_semp by reflexivity.
      assert (N : get (V293_encoded_memory 160%positive 0 true (encode_val Tint32 (Vint32 n))) (b,off)=None)
        by (apply V293_encoded_memory_outside;left;exact Apart).
      assert (B : get (V293_encoded_memory 160%positive 0 true (encode_val Tint32 (Vint32 bad))) (b,off)=None)
        by (apply V293_encoded_memory_outside;left;exact Apart).
      rewrite N,B. reflexivity.
    + split;[apply Jclock_load | ]. intro Held. apply Jsetter_required_load in Held.
      pose proof (Jticks_load ct clock bad save). congruence.
Qed.
Theorem Jraw_getter_control : forall ct clock lg,
  Jstate V293_time_get_action (Jmemory ct clock Vundef Vundef) (TRabstract ct clock) |=
    V293_time_ready_core 80%positive 81%positive 82%positive 150%positive ** JgetPre ct lg /\
  Jstate V293_time_get_action (Jmemory ct clock (Vint32 Int.one) Vnull) (TRabstract ct clock) |=
    V293_time_ready_core 80%positive 81%positive 82%positive 150%positive ** JgetPre ct lg.
Proof. intros;split;apply Jget_joint. Qed.

(* Current thread is a real ready TCB in the independent task map. *)
Theorem Jconcrete_ready_entry :
  get OwnershipTasks OwnershipReady=Some(Int.repr 4,rdy,Vnull) /\
  get (TRabstract OwnershipReady (Int.repr 37)) abstcblsid=Some(abstcblist OwnershipTasks) /\
  Jstate V293_time_get_action
    (Jmemory OwnershipReady (Int.repr 37) (Vint32(Int.repr 42)) Vundef)
    (TRabstract OwnershipReady (Int.repr 37)) |=
    V293_time_ready_core 80%positive 81%positive 82%positive 150%positive ** JgetPre OwnershipReady [] /\
  Jstate (V293_time_set_action (Int.repr 42))
    (Jmemory OwnershipReady (Int.repr 37) (Vint32(Int.repr 42)) Vundef)
    (TRabstract OwnershipReady (Int.repr 37)) |=
    V293_time_ready_core 80%positive 81%positive 82%positive 150%positive ** JsetPre OwnershipReady [] (Int.repr 42).
Proof.
  split;[vm_compute;reflexivity | ]. split.
  - unfold TRabstract. rewrite map_get_set' by discriminate. apply RIfixed_tasks.
  - split;[apply Jget_joint | apply Jset_joint].
Qed.
