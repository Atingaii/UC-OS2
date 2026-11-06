(* Same old heap and program as the real-call checkpoint, now to return.
   Only a finite path without interrupt interleaving is claimed. *)
Require Import CertiOS.certiucos.v293.proofs.V293TimeAPILifecycle.
Require Import CertiOS.certiucos.v293.proofs.V293TimeAPICall.
Require Import CertiOS.certiucos.v293.proofs.V293TimeAccess.
Require Import CertiOS.certiucos.v293.proofs.V293TimeGetAPI.
Require Import CertiOS.certiucos.v293.proofs.V293TimeSetAPI.
Require Import CertiOS.certiucos.v293.proofs.V293TimeReadyShared.
Require Import CertiOS.certiucos.v293.proofs.V293TimeShared.
Require Import CertiOS.certiucos.v293.proofs.V293TimeSharedSet.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTarget.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedChange.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.audit.probes.V293TimeAPICallProbe.
Require Import CertiOS.audit.probes.V293TimeReadyEntryProbe.
Require Import CertiOS.audit.probes.V293TimeReadySharedProbe.
Require Import CertiOS.audit.probes.V293TimeReadyAPIProbe.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.memory_prop.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List.
Import ListNotations.
Local Open Scope nat_scope.

Lemma Linsert : forall op M O A B,
  Jstate op M O |= A -> Jstate op emp emp |= B -> Jstate op M O |= B ** A.
Proof.
  intros. eapply Jstar;[apply map_join_comm;apply map_join_emp |
    apply map_join_comm;apply map_join_emp | eassumption | eassumption].
Qed.
Lemma Lnames : forall op,
  Jstate op emp emp |= V293_time_binding false 1001%Z 150%positive **
    (V293_time_binding true 1002%Z 160%positive ** V293_time_binding true 1003%Z 161%positive).
Proof.
  intro op.
  assert(N:Jstate op emp emp |= V293_time_binding false 1001%Z 150%positive).
  { change(Jstate op emp emp |= V293_counter_bindings 1001%Z 150%positive).
    split.
    - exists 150%positive. split;[reflexivity | ]. repeat split;reflexivity.
    - split;[intros[v E];vm_compute in E;discriminate | ]. split;reflexivity. }
  assert(T:Jstate op emp emp |= V293_time_binding true 1002%Z 160%positive).
  { exists 160%positive. split;[reflexivity | ]. repeat split;reflexivity. }
  assert(S:Jstate op emp emp |= V293_time_binding true 1003%Z 161%positive).
  { exists 161%positive. split;[reflexivity | ]. repeat split;reflexivity. }
  repeat first [exact N | exact T | exact S | eapply Jstar with(m1:=emp)(m2:=emp)(o1:=emp)(o2:=emp);
    [apply map_join_emp | apply map_join_emp | | ]].
Qed.
Lemma Lowned : forall op ct clock lg M tmp,
  Jstate op M(TRabstract ct clock) |= Amapsto(161%positive,0%Z) Tint32 true Vundef **
    (Amapsto(160%positive,0%Z) Tint32 true tmp ** Cframe op ct lg) ->
  Jstate op M(TRabstract ct clock) |= V293_time_cell true 1003%Z 161%positive Vundef **
    (V293_time_cell true 1002%Z 160%positive tmp **
      (V293_time_cell false 1001%Z 150%positive(Vint32 clock) ** Atrue)).
Proof.
  intros op ct clock lg M tmp Held.
  unfold Cframe,Ccore,V293_time_ready_core in Held. sep normal in Held. sep destruct Held.
  assert(Slot:get(TRabstract ct clock)ostmid=Some(ostm x)).
  { change(get(getabst(Jstate op M(TRabstract ct clock)))ostmid=Some(ostm x)).
    eapply V293_star_abst_get_l with(p:=V293_time_ready_fields 80%positive 81%positive 82%positive x)(q:=Atrue).
    - apply V293_time_ready_fields_clock.
    - clear -Held. sep auto. }
  unfold TRabstract in Slot. rewrite map_get_set in Slot. inversion Slot;subst x.
  pose proof(Linsert _ _ _ _ _ Held (Lnames op))as Named.
  unfold V293_time_cell,Aptrmapsto. clear -Named. sep auto.
Qed.

Definition LgetExec caller ks ct clock Mf :=
  V293_local_steps Cprogram (curs(scall 203%Z []),(kenil,ks))
    ((JGE,caller,TRmemory ct clock),empisr,(true,[],[]))
    (curs(sskip(Some(Vint32 clock))),(kenil,ks)) ((JGE,caller,Mf),empisr,(true,[],[])).
Definition LsetExec caller ks ct clock n Mf :=
  V293_local_steps Cprogram (curs(scall 202%Z [econst32 n]),(kenil,ks))
    ((JGE,caller,TRmemory ct clock),empisr,(true,[],[]))
    (curs(sskip None),(kenil,ks)) ((JGE,caller,Mf),empisr,(true,[],[])).

Lemma Lstore_frame : forall M M' b n c i,
  store Tint32 M(b,0%Z)(Vint32 n)=Some M' -> c<>b -> get M'(c,i)=get M(c,i).
Proof.
  intros M M' b n c i Store Different. unfold store in Store.
  eapply V293_storebytes_outside;[exact Store | left;exact Different].
Qed.
Theorem Lget_actual_lifecycle : forall caller ks ct clock lg,
  exists Ma Mf,
    CgetExec caller ks ct clock Ma /\
    Jstate V293_time_get_action Ma(TRabstract ct clock) |= Ccore ** JgetPre ct lg /\
    LgetExec caller ks ct clock Mf /\
    load Tint32 Mf(150%positive,0%Z)=Some(Vint32 clock) /\
    (forall b i,b<>160%positive -> b<>161%positive -> get Mf(b,i)=get(TRmemory ct clock)(b,i)) /\
    (forall k,k<4 -> get Mf(160%positive,Z.of_nat k)=None /\ get Mf(161%positive,Z.of_nat k)=None).
Proof.
  intros caller ks ct clock lg.
  pose proof(V293_time_get_call_entry Cprogram ks JGE caller(TRmemory ct clock)
    empisr (true,[],[]) (TRabstract ct clock) V293_time_get_action 203%Z 1001%Z 1002%Z 1003%Z
    160%positive 161%positive (Cframe V293_time_get_action ct lg))as Entry.
  assert(P:Cprogram 203%Z=Some(V293_TimeGet_function 1001%Z 1002%Z 1003%Z)).
  { exact(proj1(proj2(proj2 RAactual_entries))). }
  specialize(Entry P ltac:(discriminate) (Cfresh ct clock _ (or_introl eq_refl))
    (V293_time_fresh_after_alloc (TRmemory ct clock) 160%positive 161%positive ltac:(discriminate) (Cfresh ct clock _ (or_intror eq_refl)))).
  rewrite Ccallee in Entry. specialize(Entry(Cbare _ ct clock lg)). cbn zeta in Entry.
  destruct Entry as[Call Owned].
  pose proof(Cpack_get ct clock lg _ Owned)as Joint.
  pose proof(Lowned _ ct clock lg _ Vundef Owned)as Named. unfold Jstate in Named. rewrite <-Ccallee in Named.
  destruct(V293_time_get_body_return Cprogram ks JGE caller _ empisr true [] []
    (TRabstract ct clock) V293_time_get_action 1001%Z 1002%Z 1003%Z 150%positive 160%positive 161%positive
    clock Vundef Atrue 203%Z ltac:(discriminate) ltac:(discriminate) Named)
    as(Mz&Mc&Mf&Zero&Copy&Body&Post&Frame&Removed).
  rewrite Ccallee in Body.
  assert(FinalFrame:forall b i,b<>160%positive -> b<>161%positive ->
    get Mf(b,i)=get(TRmemory ct clock)(b,i)).
  { intros b i BT BS. rewrite Frame by assumption.
    rewrite(Lstore_frame _ _ _ _ _ _ Copy BT).
    rewrite(Lstore_frame _ _ _ _ _ _ Zero BS).
    repeat rewrite V293_success_allocb_outside by(left;congruence). reflexivity. }
  eexists. exists Mf. split;[exact Call | ]. split;[exact Joint | ]. split.
  - unfold LgetExec. eapply V293_local_trans;[exact Call | exact Body].
  - split.
    + etransitivity;[apply V293_load_block_frame;intro i;apply FinalFrame;discriminate | apply TRclock_load].
    + split;assumption.
Qed.
Theorem Lset_actual_lifecycle : forall caller ks ct clock lg n,
  exists Ma Mf,
    CsetExec caller ks ct clock n Ma /\
    Jstate(V293_time_set_action n)Ma(TRabstract ct clock) |= Ccore ** JsetPre ct lg n /\
    load Tint32 Ma(160%positive,0%Z)=Some(Vint32 n) /\
    LsetExec caller ks ct clock n Mf /\
    load Tint32 Mf(150%positive,0%Z)=Some(Vint32 n) /\
    (forall b i,b<>150%positive -> b<>160%positive -> b<>161%positive -> get Mf(b,i)=get(TRmemory ct clock)(b,i)) /\
    (forall k,k<4 -> get Mf(160%positive,Z.of_nat k)=None /\ get Mf(161%positive,Z.of_nat k)=None).
Proof.
  intros caller ks ct clock lg n.
  pose proof(V293_time_set_call_entry Cprogram ks JGE caller(TRmemory ct clock)
    empisr (true,[],[]) (TRabstract ct clock) (V293_time_set_action n) 202%Z 1001%Z 1002%Z 1003%Z
    160%positive 161%positive n (Cframe(V293_time_set_action n)ct lg))as Entry.
  assert(P:Cprogram 202%Z=Some(V293_TimeSet_function 1001%Z 1002%Z 1003%Z)).
  { exact(proj1(proj2 RAactual_entries)). }
  specialize(Entry P ltac:(discriminate) (Cfresh ct clock _ (or_introl eq_refl))
    (Cfresh ct clock _ (or_intror eq_refl)) ltac:(discriminate)).
  rewrite Ccallee in Entry. specialize(Entry(Cbare _ ct clock lg)).
  destruct Entry as(Mp&Ma&ParameterStore&Mem&Call&Owned). subst Ma.
  pose proof(Cpack_set ct clock lg n _ Owned)as Joint.
  assert(Pre:Jstate(V293_time_set_action n) (allocb Mp 161%positive 0%Z (typelen Tint32)) (TRabstract ct clock) |= JsetPre ct lg n ** Atrue).
  { clear -Joint. sep auto. }
  pose proof(Jsetter_required_load _ _ _ _ _ _ Pre)as ParameterLoad.
  pose proof(Lowned _ ct clock lg _ (Vint32 n) Owned)as Named.
  assert(Reorder:Jstate(V293_time_set_action n) (allocb Mp 161%positive 0%Z (typelen Tint32)) (TRabstract ct clock) |=
    V293_time_cell true 1003%Z 161%positive Vundef **
      (V293_time_cell false 1001%Z 150%positive(Vint32 clock) **
        (V293_time_cell true 1002%Z 160%positive(Vint32 n) ** Atrue))).
  { clear -Named. sep auto. }
  unfold Jstate in Reorder. rewrite <-Ccallee in Reorder.
  destruct(V293_time_set_body_return Cprogram ks JGE caller _ empisr true [] []
    (TRabstract ct clock)(V293_time_set_action n) 1001%Z 1002%Z 1003%Z 150%positive 160%positive 161%positive
    clock n Atrue 202%Z ltac:(discriminate) ltac:(discriminate) Reorder)
    as(Mz&Mc&Mf&Zero&Copy&Body&Post&Frame&Removed).
  rewrite Ccallee in Body,Post.
  assert(ClockCell:Jstate(V293_time_set_action n) Mc(TRabstract ct clock) |=
    V293_time_cell false 1001%Z 150%positive(Vint32 n) ** Atrue).
  { clear -Post. sep auto. }
  destruct(V293_time_cell_read false 1001%Z 150%positive n Atrue _ ClockCell)as[Read Typed].
  change(load Tint32 Mc(150%positive,0%Z)=Some(Vint32 n))in Read.
  assert(FinalFrame:forall b i,b<>150%positive -> b<>160%positive -> b<>161%positive ->
    get Mf(b,i)=get(TRmemory ct clock)(b,i)).
  { intros b i BN BT BS. rewrite Frame by assumption.
    rewrite(Lstore_frame _ _ _ _ _ _ Copy BN).
    rewrite(Lstore_frame _ _ _ _ _ _ Zero BS).
    rewrite V293_success_allocb_outside by(left;congruence).
    rewrite(Lstore_frame _ _ _ _ _ _ ParameterStore BT).
    rewrite V293_success_allocb_outside by(left;congruence). reflexivity. }
  eexists. exists Mf. split;[exact Call | ]. split;[exact Joint | ]. split;[exact ParameterLoad | ]. split.
  - unfold LsetExec. eapply V293_local_trans;[exact Call | exact Body].
  - split.
    + etransitivity;[apply V293_load_block_frame;intro i;apply Frame;discriminate | exact Read].
    + split;assumption.
Qed.

(* Only the source argument changes; neither result is an assumed endpoint. *)
Theorem Lset_two_argument_control : forall caller ks ct clock (lg:list logicvar) n bad,
  bad<>n -> exists An Ab Mn Mb,
    CsetExec caller ks ct clock n An /\ CsetExec caller ks ct clock bad Ab /\
    load Tint32 An(160%positive,0%Z)=Some(Vint32 n) /\
    load Tint32 Ab(160%positive,0%Z)=Some(Vint32 bad) /\
    LsetExec caller ks ct clock n Mn /\ LsetExec caller ks ct clock bad Mb /\
    load Tint32 Mn(150%positive,0%Z)=Some(Vint32 n) /\
    load Tint32 Mb(150%positive,0%Z)=Some(Vint32 bad) /\
    load Tint32 Mb(150%positive,0%Z)<>Some(Vint32 n).
Proof.
  intros caller ks ct clock lg n bad Different.
  destruct(Lset_actual_lifecycle caller ks ct clock lg n)as(An&Mn&Cn&Jn&Pn&En&Ln&Fn&Rn).
  destruct(Lset_actual_lifecycle caller ks ct clock lg bad)as(Ab&Mb&Cb&Jb&Pb&Eb&Lb&Fb&Rb).
  exists An. exists Ab. exists Mn. exists Mb.
  split;[exact Cn | ]. split;[exact Cb | ]. split;[exact Pn | ]. split;[exact Pb | ].
  split;[exact En | ]. split;[exact Eb | ]. split;[exact Ln | ]. split;[exact Lb | ]. congruence.
Qed.

(* Callee ticks lives at 160; after actual free, caller ticks is again 150. *)
Theorem Lget_caller_shadow_control : forall ks ct clock (lg:list logicvar),
  get Ccaller 1002%Z=Some(150%positive,Tint32) /\
  get JLE 1002%Z=Some(160%positive,Tint32) /\
  exists Mf,
    LgetExec Ccaller ks ct clock Mf /\
    evalval(evar 1002%Z)(JGE,Ccaller,Mf)=Some(Vint32 clock) /\
    (forall k,k<4 -> get Mf(160%positive,Z.of_nat k)=None /\ get Mf(161%positive,Z.of_nat k)=None) /\
    (forall b i,b<>160%positive -> b<>161%positive -> get Mf(b,i)=get(TRmemory ct clock)(b,i)).
Proof.
  intros ks ct clock lg. split;[apply map_get_set | ]. split;[reflexivity | ].
  destruct(Lget_actual_lifecycle Ccaller ks ct clock lg)as(Ma&Mf&Call&Joint&Exec&Clock&Frame&Removed).
  exists Mf. split;[exact Exec | ]. split.
  - change(load Tint32 Mf(150%positive,0%Z)=Some(Vint32 clock)). exact Clock.
  - split;assumption.
Qed.
