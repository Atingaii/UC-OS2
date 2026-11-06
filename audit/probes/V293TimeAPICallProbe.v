(* The starting heap has NO API locals; the end heap is produced by loststep.
   Both API entries use the same linked program and existing strong invariant. *)
Require Import CertiOS.certiucos.v293.proofs.V293TimeAPICall.
Require Import CertiOS.certiucos.v293.proofs.V293TimeReadyEntry.
Require Import CertiOS.certiucos.v293.proofs.V293TimeGetAPI.
Require Import CertiOS.certiucos.v293.proofs.V293TimeSetAPI.
Require Import CertiOS.certiucos.v293.proofs.V293TimeAccess.
Require Import CertiOS.certiucos.v293.proofs.V293TimeNamesGood.
Require Import CertiOS.certiucos.v293.proofs.V293TimeShared.
Require Import CertiOS.certiucos.v293.proofs.V293TimeSharedSet.
Require Import CertiOS.certiucos.v293.proofs.V293TimeReadyShared.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.audit.probes.V293TimeReadyEntryProbe.
Require Import CertiOS.audit.probes.V293TimeReadySharedProbe.
Require Import CertiOS.audit.probes.V293TimeReadyAPIProbe.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.framework.proof.memory_prop.
Require Import CertiOS.framework.proof.auxdef.
Require Import CertiOS.framework.proof.lmachLib.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List.
Import ListNotations.
Local Open Scope nat_scope.

Definition Cprogram := pumerge RAapi RAinternal.
Definition Ccore := V293_time_ready_core 80%positive 81%positive 82%positive 150%positive.
Definition Cframe op ct lg :=
  (Ccore ** CurTid ct) ** (LINV RAli ct lg **
    (<||op||> ** OS[empisr,true,nil,nil] ** V293_time_api_domain 1002%Z 1003%Z)).
Lemma Ccallee : V293_time_call_locals 1002%Z 1003%Z 160%positive 161%positive=JLE.
Proof.
  apply EnvMod.extensionality. intro x.
  change(get(V293_time_call_locals 1002%Z 1003%Z 160%positive 161%positive)x=get JLE x).
  unfold V293_time_call_locals,JLE.
  destruct(Z.eq_dec x 1003%Z);[subst x;vm_compute;reflexivity | ].
  rewrite !map_get_set' by congruence.
  destruct(Z.eq_dec x 1002%Z);[subst x;vm_compute;reflexivity | ].
  rewrite !map_get_set' by congruence. rewrite !map_emp_get. rewrite map_get_sig' by congruence. reflexivity.
Qed.
Lemma Cbare : forall op ct clock lg,
  Jstate op (TRmemory ct clock) (TRabstract ct clock) |= Cframe op ct lg.
Proof.
  intros. eapply Jstar with (m1:=TRmemory ct clock)(m2:=emp)(o1:=TRabstract ct clock)(o2:=emp).
  - apply map_join_emp.
  - apply map_join_emp.
  - apply Jcore_and_current.
  - apply Jempty.
Qed.
Lemma Cfresh : forall ct clock b,
  b=160%positive \/ b=161%positive -> fresh(TRmemory ct clock)b.
Proof.
  intros ct clock b B l i E [v Bound]. subst l.
  change(get(TRmemory ct clock)(b,i)=Some v)in Bound.
  rewrite Joutside in Bound by exact B. discriminate.
Qed.
Lemma Clocal_wrap : forall op M O b x v,
  get JLE x=Some(b,Tint32) ->
  Jstate op M O |= Amapsto(b,0%Z) Tint32 true v ->
  Jstate op M O |= LV x @ Tint32 |-> v.
Proof.
  intros op M O b x v Name Bytes. exists b.
  eapply Jstar with (m1:=emp)(m2:=M)(o1:=emp)(o2:=O).
  - apply map_join_comm;apply map_join_emp.
  - apply map_join_comm;apply map_join_emp.
  - exists b. split;[exact Name | ]. repeat split;reflexivity.
  - exact Bytes.
Qed.
Lemma Cwrap_pair : forall op ct clock lg tmp save M,
  Jstate op M (TRabstract ct clock) |=
    Amapsto(161%positive,0%Z) Tint32 true save **
      (Amapsto(160%positive,0%Z) Tint32 true tmp ** Cframe op ct lg) ->
  Jstate op M (TRabstract ct clock) |=
    (LV 1003%Z @ Tint32 |-> save) ** ((LV 1002%Z @ Tint32 |-> tmp) ** Cframe op ct lg).
Proof.
  intros op ct clock lg tmp save M H. apply sat_split in H.
  destruct H as(ms&rest&os&orest&JM&JO&Saved&Tail).
  apply sat_split in Tail. destruct Tail as(mt&mf&ot&ofr&JMt&JOt&Ticks&Frame).
  eapply Jstar;[exact JM | exact JO | eapply Clocal_wrap;[reflexivity | exact Saved] | ].
  eapply Jstar;[exact JMt | exact JOt | eapply Clocal_wrap;[reflexivity | exact Ticks] | exact Frame].
Qed.
Lemma Cpack_get : forall ct clock lg M,
  Jstate V293_time_get_action M (TRabstract ct clock) |=
    Amapsto(161%positive,0%Z) Tint32 true Vundef **
      (Amapsto(160%positive,0%Z) Tint32 true Vundef ** Cframe V293_time_get_action ct lg) ->
  Jstate V293_time_get_action M (TRabstract ct clock) |= Ccore ** JgetPre ct lg.
Proof.
  intros ct clock lg M H. apply Cwrap_pair in H.
  unfold Cframe,JgetPre,p_local in *. sep auto.
Qed.
Lemma Cpack_set : forall ct clock lg n M,
  Jstate (V293_time_set_action n) M (TRabstract ct clock) |=
    Amapsto(161%positive,0%Z) Tint32 true Vundef **
      (Amapsto(160%positive,0%Z) Tint32 true (Vint32 n) ** Cframe (V293_time_set_action n) ct lg) ->
  Jstate (V293_time_set_action n) M (TRabstract ct clock) |= Ccore ** JsetPre ct lg n.
Proof.
  intros ct clock lg n M H. apply Cwrap_pair in H.
  unfold Cframe,JsetPre,p_local in *. sep auto.
Qed.
Definition CgetExec caller ks ct clock Mf :=
  V293_local_steps Cprogram (curs(scall 203%Z []),(kenil,ks))
    ((JGE,caller,TRmemory ct clock),empisr,(true,[],[]))
    (curs(V293_TimeGet_body 1001%Z 1002%Z 1003%Z),
      (kenil,kcall 203%Z (V293_TimeGet_body 1001%Z 1002%Z 1003%Z) caller ks))
    ((JGE,JLE,Mf),empisr,(true,[],[])).
Definition CsetExec caller ks ct clock n Mf :=
  V293_local_steps Cprogram (curs(scall 202%Z [econst32 n]),(kenil,ks))
    ((JGE,caller,TRmemory ct clock),empisr,(true,[],[]))
    (curs(V293_TimeSet_body 1001%Z 1002%Z 1003%Z),
      (kenil,kcall 202%Z (V293_TimeSet_body 1001%Z 1002%Z 1003%Z) caller ks))
    ((JGE,JLE,Mf),empisr,(true,[],[])).
Theorem Cget_actual_call : forall caller ks ct clock lg,
  exists Mf post,
    CgetExec caller ks ct clock Mf /\
    Some(JgetPre ct lg)=BuildPreA' RAapi 203%Z V293_TimeGet_api [] RAli ct lg /\
    Some post=BuildRetA' RAapi 203%Z V293_TimeGet_api [] RAli ct lg /\
    InfRules RAspec V293_scheduler RAli TRinv post Afalse (JgetPre ct lg)
      (V293_TimeGet_body 1001%Z 1002%Z 1003%Z) Afalse ct /\
    Jstate V293_time_get_action Mf (TRabstract ct clock) |= Ccore ** JgetPre ct lg /\
    (forall b i,b<>160%positive -> b<>161%positive -> get Mf(b,i)=get(TRmemory ct clock)(b,i)).
Proof.
  intros caller ks ct clock lg.
  pose proof(V293_time_get_call_entry Cprogram ks JGE caller (TRmemory ct clock)
    empisr (true,[],[]) (TRabstract ct clock) V293_time_get_action 203%Z 1001%Z 1002%Z 1003%Z
    160%positive 161%positive (Cframe V293_time_get_action ct lg)) as Entry.
  assert(P:Cprogram 203%Z=Some(V293_TimeGet_function 1001%Z 1002%Z 1003%Z)).
  { exact(proj1(proj2(proj2 RAactual_entries))). }
  specialize(Entry P ltac:(discriminate) (Cfresh ct clock _ (or_introl eq_refl))
    (V293_time_fresh_after_alloc (TRmemory ct clock) 160%positive 161%positive ltac:(discriminate) (Cfresh ct clock _ (or_intror eq_refl)))).
  rewrite Ccallee in Entry. specialize(Entry (Cbare _ ct clock lg)).
  cbn zeta in Entry. destruct Entry as [Exec Owned].
  destruct(RAget_builders ct lg)as(pre&post&Pre&Post&Body).
  pose proof(proj1(Jactual_builders ct lg Int.zero))as Exact.
  rewrite <-Exact in Pre. inversion Pre;subst pre.
  eexists. exists post. split;[exact Exec | ]. split;[exact Exact | ].
  split;[exact Post | ]. split;[exact Body | ]. split;[apply Cpack_get;exact Owned | ].
  intros b i BT BS. repeat rewrite V293_success_allocb_outside by(left;congruence). reflexivity.
Qed.
Theorem Cset_actual_call : forall caller ks ct clock lg n,
  exists Mf post,
    CsetExec caller ks ct clock n Mf /\
    Some(JsetPre ct lg n)=BuildPreA' RAapi 202%Z V293_TimeSet_api [Vint32 n] RAli ct lg /\
    Some post=BuildRetA' RAapi 202%Z V293_TimeSet_api [Vint32 n] RAli ct lg /\
    InfRules RAspec V293_scheduler RAli TRinv post Afalse (JsetPre ct lg n)
      (V293_TimeSet_body 1001%Z 1002%Z 1003%Z) Afalse ct /\
    Jstate (V293_time_set_action n) Mf (TRabstract ct clock) |= Ccore ** JsetPre ct lg n /\
    (forall b i,b<>160%positive -> b<>161%positive -> get Mf(b,i)=get(TRmemory ct clock)(b,i)).
Proof.
  intros caller ks ct clock lg n.
  pose proof(V293_time_set_call_entry Cprogram ks JGE caller (TRmemory ct clock)
    empisr (true,[],[]) (TRabstract ct clock) (V293_time_set_action n) 202%Z 1001%Z 1002%Z 1003%Z
    160%positive 161%positive n (Cframe (V293_time_set_action n) ct lg)) as Entry.
  assert(P:Cprogram 202%Z=Some(V293_TimeSet_function 1001%Z 1002%Z 1003%Z)).
  { exact(proj1(proj2 RAactual_entries)). }
  specialize(Entry P ltac:(discriminate) (Cfresh ct clock _ (or_introl eq_refl))
    (Cfresh ct clock _ (or_intror eq_refl)) ltac:(discriminate)).
  rewrite Ccallee in Entry. specialize(Entry (Cbare _ ct clock lg)).
  destruct Entry as(Mp&Mf&Store&Mem&Exec&Owned). subst Mf.
  destruct(RAset_builders ct lg n)as(pre&post&Pre&Post&Body).
  pose proof(proj2(Jactual_builders ct lg n))as Exact.
  rewrite <-Exact in Pre. inversion Pre;subst pre.
  eexists. exists post. split;[exact Exec | ]. split;[exact Exact | ].
  split;[exact Post | ]. split;[exact Body | ]. split;[apply Cpack_set;exact Owned | ].
  intros b i BT BS. rewrite V293_success_allocb_outside by(left;congruence).
  unfold store in Store. rewrite (V293_storebytes_outside _ _ _ _ _ _ _ Store (or_introl BT)).
  rewrite V293_success_allocb_outside by(left;congruence). reflexivity.
Qed.

(* Wrong local value is tested independently of the abstract action guard. *)
Theorem Cset_parameter_control : forall caller ks ct clock lg n bad,
  bad<>n -> exists Mf,
    CsetExec caller ks ct clock n Mf /\
    Jstate (V293_time_set_action n) Mf (TRabstract ct clock) |= Ccore ** JsetPre ct lg n /\
    load Tint32 Mf (160%positive,0%Z)=Some(Vint32 n) /\
    load Tint32 Mf (150%positive,0%Z)=Some(Vint32 clock) /\
    ~ Jstate (V293_time_set_action n) Mf (TRabstract ct clock) |=
      (LV 1002%Z @ Tint32 |-> Vint32 bad) ** Atrue.
Proof.
  intros caller ks ct clock lg n bad Different.
  destruct(Cset_actual_call caller ks ct clock lg n)as(Mf&post&Exec&Pre&Post&Body&Joint&Frame).
  assert(Caller:Jstate (V293_time_set_action n) Mf (TRabstract ct clock) |= JsetPre ct lg n ** Atrue).
  { clear -Joint;sep auto. }
  pose proof(Jsetter_required_load _ _ _ _ _ _ Caller)as ParameterLoad.
  assert(Clock:load Tint32 Mf (150%positive,0%Z)=Some(Vint32 clock)).
  { etransitivity;[apply V293_load_block_frame;intro i;apply Frame;discriminate | apply TRclock_load]. }
  exists Mf. split;[exact Exec | ]. split;[exact Joint | ].
  split;[exact ParameterLoad | ]. split;[exact Clock | ]. intro Wrong.
  assert(Binding:Jstate (V293_time_set_action n) Mf (TRabstract ct clock) |=
    V293_time_cell true 1002%Z 160%positive (Vint32 bad) ** Atrue).
  { unfold Alvarmapsto in Wrong. sep normal in Wrong. sep destruct Wrong.
    assert(Name:Jstate (V293_time_set_action n) Mf (TRabstract ct clock) |=
      (L& 1002%Z @ Tint32 == (x,Int.zero)) ** Atrue)by(clear -Wrong;sep auto).
    change(Jstate (V293_time_set_action n) Mf (TRabstract ct clock) |=
      V293_time_binding true 1002%Z x ** Atrue)in Name.
    destruct(V293_time_binding_env true 1002%Z x Atrue _ Name)as[E|[E _]].
    - change(get JLE 1002%Z=Some(x,Tint32))in E.
      assert(x=160%positive)by(vm_compute in E;congruence). subst x.
      unfold V293_time_cell,V293_time_binding. sep auto.
    - change(get JLE 1002%Z=None)in E. vm_compute in E. discriminate. }
  destruct(V293_time_cell_read true 1002%Z 160%positive bad Atrue _ Binding)as[Value Typed].
  cbn [getsmem get_smem evalval get_lenv get_genv get_mem] in Value.
  change(load Tint32 Mf (160%positive,0%Z)=Some(Vint32 bad))in Value. congruence.
Qed.

(* Caller and callee use the same variable identifier but different storage.
   The caller's actual clock bytes remain unchanged by the entire call prefix. *)
Definition Ccaller : env := set emp 1002%Z (150%positive,Tint32).
Theorem Ccaller_shadow_control : forall ks ct clock lg,
  get Ccaller 1002%Z=Some(150%positive,Tint32) /\
  get JLE 1002%Z=Some(160%positive,Tint32) /\
  exists Mf,
    CgetExec Ccaller ks ct clock Mf /\
    Jstate V293_time_get_action Mf (TRabstract ct clock) |= Ccore ** JgetPre ct lg /\
    load Tint32 Mf (150%positive,0%Z)=Some(Vint32 clock) /\
    fresh(TRmemory ct clock)160%positive /\ fresh(TRmemory ct clock)161%positive.
Proof.
  intros ks ct clock lg. split;[apply map_get_set | ]. split;[reflexivity | ].
  destruct(Cget_actual_call Ccaller ks ct clock lg)as(Mf&post&Exec&Pre&Post&Body&Joint&Frame).
  exists Mf. split;[exact Exec | ]. split;[exact Joint | ]. split.
  - etransitivity;[apply V293_load_block_frame;intro i;apply Frame;discriminate | apply TRclock_load].
  - split;apply Cfresh;auto.
Qed.

(* Two calls differ only in the source argument; both reach their own real pre.
   The negative check reads the local cell, independently of the action guard. *)
Theorem Cset_two_argument_control : forall caller ks ct clock lg n bad,
  bad<>n -> exists Mn Mb,
    CsetExec caller ks ct clock n Mn /\ CsetExec caller ks ct clock bad Mb /\
    Jstate (V293_time_set_action n) Mn (TRabstract ct clock) |= Ccore ** JsetPre ct lg n /\
    Jstate (V293_time_set_action bad) Mb (TRabstract ct clock) |= Ccore ** JsetPre ct lg bad /\
    load Tint32 Mn (160%positive,0%Z)=Some(Vint32 n) /\
    load Tint32 Mb (160%positive,0%Z)=Some(Vint32 bad) /\
    load Tint32 Mn (150%positive,0%Z)=Some(Vint32 clock) /\
    load Tint32 Mb (150%positive,0%Z)=Some(Vint32 clock) /\
    ~ Jstate (V293_time_set_action bad) Mb (TRabstract ct clock) |=
      (LV 1002%Z @ Tint32 |-> Vint32 n) ** Atrue.
Proof.
  intros caller ks ct clock lg n bad Different.
  destruct(Cset_parameter_control caller ks ct clock lg n bad Different)
    as(Mn&En&Jn&Ln&Cn&Nn).
  destruct(Cset_parameter_control caller ks ct clock lg bad n ltac:(congruence))
    as(Mb&Eb&Jb&Lb&Cb&Nb).
  exists Mn. exists Mb. split;[exact En | ]. split;[exact Eb | ].
  split;[exact Jn | ]. split;[exact Jb | ]. split;[exact Ln | ].
  split;[exact Lb | ]. split;[exact Cn | ]. split;assumption.
Qed.
