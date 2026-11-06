(* Resuming an existing suspended scheduler continuation. Original lpstep only.
   The return is conditional on resources at resumption, NOT interference safety. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.framework.proof.auxdef.
Require Import CertiOS.framework.proof.join_prop.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyFullCall.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyCallGlobal.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyCriticalGlobal.
Require Import CertiOS.certiucos.v293.proofs.V293LocalGlobalTrace.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyGlobalTrace.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import Coq.Lists.List.
Import ListNotations.

Lemma V293_bound_continuation_inos : forall po pi f body caller ks tau d1 d2 c ke inner,
  po f=Some (tau,d1,d2,body) -> callcont inner=Some (kcall f body caller ks) ->
  InOS (c,(ke,inner)) (pumerge po pi).
Proof.
  intros. exists c. exists ke. exists inner. split;[reflexivity| ]. right;left.
  exists f. exists caller. exists ks. exists tau. exists d1. exists d2.
  exists body. exists body. split;[assumption| ]. unfold pumerge. rewrite H. reflexivity.
Qed.

(* Arbitrary memory and frame, arbitrary saved IE and outer critical stack.
   No successful free, final memory or precomputed execution is a premise. *)
Theorem V293_sched_resume_return : forall pc po pi ip T les aus t cst ge M ir
    active enabled si ci O op R f body caller ks tau d1 d2 saved b v,
  po f=Some (tau,d1,d2,body) -> GoodInvAsrt R ->
  get T t=Some (SKIP,(kenil,kseq (sseq (sprim excrit) sret) (kcall f body caller ks))) ->
  get les t=Some (V293_cpu_lenv saved b) ->
  get aus t=Some (active,si,enabled::ci) ->
  (ge,V293_cpu_lenv saved b,M,ir,(active,si,enabled::ci),O,op) |=
    Amapsto (b,0%Z) Tint32 true v ** R ->
  exists Mf,
    V293_global_steps (pc,(po,pi,ip)) cst (T,(ge,les,M,ir,aus),t)
      (set T t (SKIP,(kenil,ks)),
       (ge,set les t caller,Mf,ir,set aus t (enabled,si,ci)),t) /\
    free Tint32 b M=Some Mf /\
    (ge,caller,Mf,ir,(enabled,si,ci),O,op) |= R /\
    (forall i, (0<=i<4)%Z -> get Mf (b,i)=None) /\
    (forall c i, c<>b -> get Mf (c,i)=get M (c,i)) /\
    (forall other, other<>t ->
      get (set T t (SKIP,(kenil,ks))) other=get T other /\
      get (set les t caller) other=get les other /\
      get (set aus t (enabled,si,ci)) other=get aus other).
Proof.
  intros pc po pi ip T les aus t cst ge M ir active enabled si ci O op R
    f body caller ks tau d1 d2 saved b v Bind Good Code Local Aux Held.
  destruct (V293_cpu_release _ _ _ _ _ _ _ _ _ _ Held)
    as (Mf & Free & Rest & Removed & Frame).
  assert (ExitGlobal : V293_global_steps (pc,(po,pi,ip)) cst
    (V293_local_global_at T les aus t
      (SKIP,(kenil,kseq (sseq (sprim excrit) sret) (kcall f body caller ks)))
      ((ge,V293_cpu_lenv saved b,M),ir,(active,si,enabled::ci)))
    (V293_local_global_at T les aus t (curs sret,(kenil,kcall f body caller ks))
      ((ge,V293_cpu_lenv saved b,M),ir,(enabled,si,ci)))).
  { (* No goodks assumption is needed: classify each of the four steps by
       the actual surviving outer OS call, including its saved caller. *)
    eapply V293_global_trans.
    - apply V293_loststep_global_single.
      + eapply V293_bound_continuation_inos;[exact Bind|reflexivity].
      + apply ostc_step. eapply stmt_step;[reflexivity|apply sskip_step].
    - eapply V293_global_trans.
      + apply V293_loststep_global_single.
        * eapply V293_bound_continuation_inos;[exact Bind|reflexivity].
        * apply ostc_step. eapply stmt_step;[reflexivity|apply sseq_step].
      + eapply V293_global_trans.
        * apply V293_loststep_global_single.
          -- eapply V293_bound_continuation_inos;[exact Bind|reflexivity].
          -- apply excrit_step;reflexivity.
        * apply V293_loststep_global_single.
          -- eapply V293_bound_continuation_inos;[exact Bind|reflexivity].
          -- apply ostc_step. eapply stmt_step;[reflexivity|apply sskip_step]. }
  pose proof (V293_sched_global_return pc po pi ip T les aus t cst ge caller M Mf ir
    (enabled,si,ci) ks f body tau d1 d2 saved b Bind Free) as Return.
  exists Mf. split.
  - assert (Trace:=V293_global_trans _ _ _ _ _ ExitGlobal Return).
    cbn [V293_local_global_at V293_global_at] in Trace.
    assert (TC : set T t (SKIP,(kenil,kseq (sseq (sprim excrit) sret)
      (kcall f body caller ks)))=T) by (exact (TasksMod.get_set_same Code)).
    assert (LC : set les t (V293_cpu_lenv saved b)=les)
      by (exact (CltEnvMod.get_set_same Local)).
    assert (AC : set aus t (active,si,enabled::ci)=aus)
      by (exact (TaskLStMod.get_set_same Aux)).
    change (V293_global_steps (pc,(po,pi,ip)) cst
      (set T t (SKIP,(kenil,kseq (sseq (sprim excrit) sret) (kcall f body caller ks))),
       (ge,set les t (V293_cpu_lenv saved b),M,ir,set aus t (active,si,enabled::ci)),t)
      (set T t (SKIP,(kenil,ks)),
       (ge,set les t caller,Mf,ir,set aus t (enabled,si,ci)),t)) in Trace.
    rewrite TC,LC,AC in Trace.
    exact Trace.
  - split;[exact Free| ]. split.
    + eapply good_inv_prop;[exact Good|exact Rest].
    + split;[exact Removed| ]. split;[exact Frame| ].
      intros other Apart. repeat split;apply map_get_set';congruence.
Qed.

Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickStorage.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import Coq.Relations.Relation_Operators.

(* Physical resumption contract, not a claim that the runner's scheduler
   selects this task. The suspended T/les/aus slots are consumed unchanged. *)
Theorem V293_sched_switch_resume_return :
  forall pc po pi ip T les aus runner victim cst ge M ir runle runaux runks
    target bt bc tp active enabled si ci O op R f body caller ks tau d1 d2 saved b v,
  runner<>victim -> po f=Some (tau,d1,d2,body) -> GoodInvAsrt R ->
  get T runner=Some (curs (sprim (switch target)),(kenil,runks)) ->
  get les runner=Some runle -> get aus runner=Some runaux ->
  get T victim=Some (SKIP,(kenil,kseq (sseq (sprim excrit) sret) (kcall f body caller ks))) ->
  get les victim=Some (V293_cpu_lenv saved b) ->
  get aus victim=Some (active,si,enabled::ci) ->
  get ge target=Some (bt,Tptr tp) ->
  load (Tptr tp) M (bt,0%Z)=Some (Vptr victim) ->
  get ge OSTCBCur=Some (bc,Tptr tp) ->
  (ge,V293_cpu_lenv saved b,M,ir,(active,si,enabled::ci),O,op) |=
    V293_owned_record_cell ((bc,0%Z),Tptr tp,Vptr runner) **
      (Amapsto (b,0%Z) Tint32 true v ** R) ->
  exists Ms Mf,
    lpstep (pc,(po,pi,ip)) T cst (ge,les,M,ir,aus) runner
      (set T runner (SKIP,(kenil,runks))) cst (ge,les,Ms,ir,aus) victim /\
    V293_global_steps (pc,(po,pi,ip)) cst (T,(ge,les,M,ir,aus),runner)
      (set (set T runner (SKIP,(kenil,runks))) victim (SKIP,(kenil,ks)),
       (ge,set les victim caller,Mf,ir,set aus victim (enabled,si,ci)),victim) /\
    store (Tptr tp) M (bc,0%Z) (Vptr victim)=Some Ms /\
    free Tint32 b Ms=Some Mf /\
    (ge,caller,Mf,ir,(enabled,si,ci),O,op) |=
      V293_owned_record_cell ((bc,0%Z),Tptr tp,Vptr victim) ** R /\
    (forall i, (0<=i<4)%Z -> get Mf (b,i)=None) /\
    (forall c i, c<>b -> c<>bc -> get Mf (c,i)=get M (c,i)).
Proof.
  intros pc po pi ip T les aus runner victim cst ge M ir runle runaux runks
    target bt bc tp active enabled si ci O op R f body caller ks tau d1 d2 saved b v
    Apart Bind Good RunCode RunLocal RunAux Suspended Local Aux Target Read Current Held.
  destruct (V293_owned_record_cell_update _ (Tptr tp) _ (Vptr victim) _ _ _ _ _ _ _ _ eq_refl Held)
    as (Ms & Store & Stored).
  assert (Step : lpstep (pc,(po,pi,ip)) T cst (ge,les,M,ir,aus) runner
    (set T runner (SKIP,(kenil,runks))) cst (ge,les,Ms,ir,aus) victim).
  { eapply pswitch_step with (tst:=((ge,runle,M),ir,runaux)) (l:=bt) (tp:=tp) (b:=bc)
      (S:=(ge,les,M,ir,aus)) (S':=(ge,les,Ms,ir,aus)).
    - reflexivity.
    - change ((match (match get les runner with
        | Some le=>Some (ge,le,M) | None=>None end),get aus runner with
        | Some sm,Some aux=>Some (sm,ir,aux) | _,_=>None end)=
        Some ((ge,runle,M),ir,runaux)). rewrite RunLocal,RunAux. reflexivity.
    - exact Target.
    - exact Read.
    - exact RunCode.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - exact Current.
    - exact Store. }
  assert (Owned : (ge,V293_cpu_lenv saved b,Ms,ir,(active,si,enabled::ci),O,op) |=
    Amapsto (b,0%Z) Tint32 true v **
      (V293_owned_record_cell ((bc,0%Z),Tptr tp,Vptr victim) ** R)) by (sep auto).
  assert (FrameGood : GoodInvAsrt
    (V293_owned_record_cell ((bc,0%Z),Tptr tp,Vptr victim) ** R)).
  { split;[unfold V293_owned_record_cell;cbn;auto|exact Good]. }
  assert (Keep : get (set T runner (SKIP,(kenil,runks))) victim=
    Some (SKIP,(kenil,kseq (sseq (sprim excrit) sret) (kcall f body caller ks)))).
  { rewrite map_get_set' by exact Apart. exact Suspended. }
  destruct (V293_sched_resume_return pc po pi ip (set T runner (SKIP,(kenil,runks)))
    les aus victim cst ge Ms ir active enabled si ci O op _ f body caller ks tau d1 d2
    saved b v Bind FrameGood Keep Local Aux Owned)
    as (Mf & Resume & Free & Rest & Removed & Frame & Others).
  exists Ms. exists Mf. split;[exact Step| ]. split.
  - unfold V293_global_steps. eapply rt1n_trans with
      (y:=(set T runner (SKIP,(kenil,runks)),(ge,les,Ms,ir,aus),victim));
      [exact Step|exact Resume].
  - split;[exact Store| ]. split;[exact Free| ]. split;[exact Rest| ].
    split;[exact Removed| ]. intros c i NotLocal NotCurrent. rewrite Frame by exact NotLocal.
    eapply V293_storebytes_outside;[exact Store|left;exact NotCurrent].
Qed.

(* Delete exactly the saved top bit, leaving a nonempty outer stack.
   Both executions return through the original semantics, with different IE. *)
Theorem V293_sched_resume_stack_ablation : forall pc po pi ip T les aus t cst ge M ir
    active enabled si ci O op R f body caller ks tau d1 d2 saved b v,
  po f=Some (tau,d1,d2,body) -> GoodInvAsrt R ->
  get T t=Some (SKIP,(kenil,kseq (sseq (sprim excrit) sret) (kcall f body caller ks))) ->
  get les t=Some (V293_cpu_lenv saved b) ->
  get aus t=Some (active,si,enabled::negb enabled::ci) ->
  (ge,V293_cpu_lenv saved b,M,ir,(active,si,enabled::negb enabled::ci),O,op) |=
    Amapsto (b,0%Z) Tint32 true v ** R ->
  exists Mf,
    V293_global_steps (pc,(po,pi,ip)) cst (T,(ge,les,M,ir,aus),t)
      (set T t (SKIP,(kenil,ks)),
       (ge,set les t caller,Mf,ir,set aus t (enabled,si,negb enabled::ci)),t) /\
    V293_global_steps (pc,(po,pi,ip)) cst
      (T,(ge,les,M,ir,set aus t (active,si,negb enabled::ci)),t)
      (set T t (SKIP,(kenil,ks)),
       (ge,set les t caller,Mf,ir,set aus t (negb enabled,si,ci)),t) /\
    free Tint32 b M=Some Mf /\
    set aus t (enabled,si,negb enabled::ci)<>set aus t (negb enabled,si,ci).
Proof.
  intros pc po pi ip T les aus t cst ge M ir active enabled si ci O op R
    f body caller ks tau d1 d2 saved b v Bind Good Code Local Aux Held.
  destruct (V293_sched_resume_return pc po pi ip T les aus t cst ge M ir
    active enabled si (negb enabled::ci) O op R f body caller ks tau d1 d2 saved b v
    Bind Good Code Local Aux Held) as (Mf & Positive & Free & Rest & Removed & Frame & Others).
  assert (NegativeHeld : (ge,V293_cpu_lenv saved b,M,ir,(active,si,negb enabled::ci),O,op) |=
    Amapsto (b,0%Z) Tint32 true v ** R).
  { eapply good_inv_prop;[split;[exact I|exact Good]|exact Held]. }
  destruct (V293_sched_resume_return pc po pi ip T les
    (set aus t (active,si,negb enabled::ci)) t cst ge M ir active (negb enabled) si ci O op R
    f body caller ks tau d1 d2 saved b v Bind Good Code Local (map_get_set _ _ _) NegativeHeld)
    as (Mn & Negative & FreeN & RestN & RemovedN & FrameN & OthersN).
  assert (Mn=Mf) by congruence. subst Mn.
  cbn in Negative. rewrite <- (set_set_eq _ _ _ _ aus t (negb enabled,si,ci) (active,si,negb enabled::ci)) in Negative.
  exists Mf. split;[exact Positive| ]. split;[exact Negative| ]. split;[exact Free| ].
  intro Same. pose proof (f_equal (fun a:ltaskstset=>get a t) Same) as Equal.
  change (get (set aus t (enabled,si,negb enabled::ci)) t=get (set aus t (negb enabled,si,ci)) t) in Equal.
  rewrite !map_get_set in Equal. destruct enabled;discriminate.
Qed.
