(* Resumption of the exact continuation installed by OSIntExit.
   Resources are required at the switch-back snapshot, not assumed invariant
   under arbitrary environment execution. No progress/fairness claim. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitResumedReturn.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyFullCall.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyCallGlobal.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyGlobalTrace.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.framework.proof.join_prop.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import Coq.Relations.Relation_Operators.

Theorem V293_int_exit_switch_resume_return :
  forall pc po pi ip T les aus runner victim cst ge M ir runle runaux runks
    target bt bc tp active enabled si ci O op R f body caller ks tau d1 d2 saved b v,
  runner<>victim -> po f=Some (tau,d1,d2,body) -> GoodInvAsrt R ->
  get T runner=Some (curs (sprim (switch target)),(kenil,runks)) ->
  get les runner=Some runle -> get aus runner=Some runaux ->
  get T victim=Some (SKIP,(kenil,kseq (sprim excrit) (kseq sret (kcall f body caller ks)))) ->
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
    Some (SKIP,(kenil,kseq (sprim excrit) (kseq sret (kcall f body caller ks))))).
  { rewrite map_get_set' by exact Apart. exact Suspended. }
  destruct (V293_int_exit_pending_return pc po pi ip (set T runner (SKIP,(kenil,runks)))
    les aus victim cst ge Ms ir active enabled si ci O op _ f body caller ks tau d1 d2
    saved b v Bind FrameGood Keep Local Aux Owned)
    as (Mf & Resume & Free & Rest & Removed & Frame).
  exists Ms. exists Mf. split;[exact Step| ]. split.
  - unfold V293_global_steps. eapply rt1n_trans with
      (y:=(set T runner (SKIP,(kenil,runks)),(ge,les,Ms,ir,aus),victim));
      [exact Step|exact Resume].
  - split;[exact Store| ]. split;[exact Free| ]. split;[exact Rest| ].
    split;[exact Removed| ]. intros c i NotLocal NotCurrent. rewrite Frame by exact NotLocal.
    eapply V293_storebytes_outside;[exact Store|left;exact NotCurrent].
Qed.

