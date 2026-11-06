(* Actual enabled TCB call and unchanged failure suffix. Shared bytes are
   borrowed afresh after encrit1, not framed across enabled interrupts.
   This physical existential pool does NOT prove reservation ownership. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.proofs.V293TCBEmptyEnabled.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateFailureHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TimeAccess.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateTCBCall.
Require Import CertiOS.certiucos.v293.proofs.V293TCBEmptyInternal.
Require Import CertiOS.certiucos.v293.proofs.V293TCBSuccessInternal.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitFields.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.code.V293OSTaskCreateExtSuffix.
Require Import CertiOS.certiucos.v293.code.V293OSTaskCreateExtCalls.
Require Import CertiOS.certiucos.v293.code.V293OSTCBInitFunction.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293TCBPriorityHoare.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Definition V293_create_rollback_pool table p K :=
 EX slot:val, [|rule_type_val_match(Tptr V293_tcb_type)slot=true|] **
 (Amapsto(table,(4*Z.of_nat p)%Z)(Tptr V293_tcb_type)true slot ** K).
Definition V293_create_enabled_failure_resources table p F :=
 LV 101%Z @ Tint8 |-> V293_byteval p **
 LV 209%Z @ Tint8 |-> Vint32(Int.repr 66) ** (V293_tcb_table_binding table ** F).
Definition V293_create_enabled_failure_state table p F aop ir si ci :=
 <||aop||> ** OS[ir,true,si,ci] ** V293_create_enabled_failure_resources table p F.
Definition V293_create_enabled_failure_return table p F aop ir si ci : retasrt :=
 fun result => [|result=Some(Vint32(Int.repr 66))|] **
 V293_create_enabled_failure_state table p F aop ir si ci.
Definition V293_create_enabled_failure_kept bf top bottom identity size ext options R F :=
 LV 108%Z @ (Tptr Tint32) |-> top **
 LV 205%Z @ (Tptr Tint32) |-> bottom **
 LV 206%Z @ Tint16 |-> identity **
 LV 207%Z @ Tint32 |-> size **
 LV 208%Z @ (Tptr Tvoid) |-> ext **
 LV 204%Z @ Tint16 |-> options **
 (Agvarenv 91%Z (Tptr V293_tcb_type)(bf,0%Z) ** (R ** F)).

Lemma V293_create_enabled_failure_good : forall table p F,
 GoodFrm F -> GoodFrm(V293_create_enabled_failure_resources table p F).
Proof.
 intros. unfold V293_create_enabled_failure_resources,Alvarmapsto,Alvarenv',Aptrmapsto.
 cbn[GoodFrm V293_tcb_table_binding]. tauto.
Qed.

Lemma V293_create_enabled_failure_enter : forall Spec sd li I r ri tid
 bf table p K F aop ir si ci,
 (gettopis si<=INUM)%nat -> GoodFrm F ->
 (Aisr ir ** invlth_isr I 0(gettopis si) ==>
  Aisr ir ** V293_tcb_empty_pool bf(V293_create_rollback_pool table p K)) ->
 InfRules Spec sd li I r ri
 (V293_create_enabled_failure_state table p F aop ir si ci)(sprim encrit)
 (EX slot:val, V293_create_failure_state table p slot
  (Amapsto(bf,0%Z)(Tptr V293_tcb_type)false Vnull ** (K ** F))
  aop ir si(true::ci))tid.
Proof.
 intros Spec sd li I r ri tid bf table p K F aop ir si ci Bound Frame Open.
 unfold V293_create_enabled_failure_state. eapply conseq_rule with
 (p:=<||aop||> ** OS[ir,true,si,ci] ** ATopis(gettopis si) **
  [|(gettopis si<=INUM)%nat|] ** V293_create_enabled_failure_resources table p F)
 (q:=<||aop||> ** OS[ir,false,si,true::ci] ** invlth_isr I 0(gettopis si) **
  V293_create_enabled_failure_resources table p F).
 - intros s H. assert(S:s |= Ais si ** Atrue)by(clear -H;sep auto).
   pose proof(V293_time_topis si Atrue s S)as Top.
   apply astar_l_atopis_elim in Top. destruct Top as[Top _].
   pose proof(@astar_l_atopis_intro s(gettopis si)_ H Top)as HT. clear -HT Bound;sep auto.
 - intros s H.
   assert(B:s |= (Aisr ir ** invlth_isr I 0(gettopis si)) **
    (<||aop||> ** Aie false ** Ais si ** Acs(true::ci) **
     V293_create_enabled_failure_resources table p F))by(clear -H;sep auto).
   eapply astar_mono in B;[ |exact Open|intros st HS;exact HS].
   unfold V293_tcb_empty_pool,V293_create_rollback_pool in B.
   sep normal in B. sep destruct B. sep split in B.
   exists x. unfold V293_create_failure_state,V293_create_failure_resources,
    V293_create_enabled_failure_resources in *;sep auto.
 - apply encrit1_rule. apply V293_create_enabled_failure_good;exact Frame.
Qed.

Lemma V293_create_enabled_failure_exit : forall Spec sd li I r ri tid
 bf table p K F aop ir si ci,
 GoodFrm F -> (F ==> CurLINV li tid) ->
 (Aisr ir ** V293_tcb_empty_pool bf(V293_create_rollback_pool table p K) ==>
  Aisr ir ** invlth_isr I 0(gettopis si)) ->
 InfRules Spec sd li I r ri
 (V293_create_failure_state table p Vnull
  (Amapsto(bf,0%Z)(Tptr V293_tcb_type)false Vnull ** (K ** F))aop ir si(true::ci))
 (sprim excrit)(V293_create_enabled_failure_state table p F aop ir si ci)tid.
Proof.
 intros Spec sd li I r ri tid bf table p K F aop ir si ci Frame HR Close.
 eapply conseq_rule with
 (p:=<||aop||> ** OS[ir,false,si,true::ci] ** ATopis(gettopis si) **
  invlth_isr I 0(gettopis si) ** V293_create_enabled_failure_resources table p F)
 (q:=<||aop||> ** OS[ir,true,si,ci] ** V293_create_enabled_failure_resources table p F).
 - intros s H.
   assert(B:s |= (Aisr ir ** V293_tcb_empty_pool bf(V293_create_rollback_pool table p K)) **
    (<||aop||> ** Aie false ** Ais si ** Acs(true::ci) **
     V293_create_enabled_failure_resources table p F)).
   { unfold V293_create_failure_state,V293_create_failure_resources,
      V293_create_enabled_failure_resources,V293_tcb_empty_pool in *.
     eapply astar_mono;[apply astar_mono;[intros st HS;exact HS| ]|intros st HS;exact HS| ].
     - apply astar_mono;[intros st HS;exact HS| ].
       intros st HS. exists Vnull. apply astar_l_apure_intro;[exact HS|reflexivity].
     - clear -H;sep auto. }
   eapply astar_mono in B;[ |exact Close|intros st HS;exact HS].
   assert(S:s |= Ais si ** Atrue)by(clear -B;sep auto).
   pose proof(V293_time_topis si Atrue s S)as Top.
   apply astar_l_atopis_elim in Top. destruct Top as[Top _].
   pose proof(@astar_l_atopis_intro s(gettopis si)_ B Top)as HT. clear -HT;sep auto.
 - unfold V293_create_enabled_failure_state. intros s H;exact H.
 - apply excrit1_rule.
   + apply V293_create_enabled_failure_good;exact Frame.
   + unfold V293_create_enabled_failure_resources. repeat apply V293_star_CurLINV_r. exact HR.
Qed.

Theorem V293_OSTaskCreateExt_enabled_rollback : forall Spec sd li I r ri tid
 bf table p K F aop ir si ci,
 p<13 -> (gettopis si<=INUM)%nat -> GoodFrm F -> (F ==> CurLINV li tid) ->
 (Aisr ir ** invlth_isr I 0(gettopis si) ==>
  Aisr ir ** V293_tcb_empty_pool bf(V293_create_rollback_pool table p K)) ->
 (Aisr ir ** V293_tcb_empty_pool bf(V293_create_rollback_pool table p K) ==>
  Aisr ir ** invlth_isr I 0(gettopis si)) ->
 InfRules Spec sd li I r ri
 (V293_create_enabled_failure_state table p F aop ir si ci)
 (V293_TaskCreateExt_rollback 92%Z 101%Z)
 (V293_create_enabled_failure_state table p F aop ir si ci)tid.
Proof.
 intros Spec sd li I r ri tid bf table p K F aop ir si ci Range Bound Frame HR Open Close.
 unfold V293_TaskCreateExt_rollback. eapply seq_rule.
 - apply V293_create_enabled_failure_enter with(bf:=bf)(K:=K);assumption.
 - apply ex_intro_rule. intro slot. eapply seq_rule.
   + apply V293_create_failure_store_hoare;[exact Range| ].
     do 2 apply V293_star_CurLINV_r;exact HR.
   + apply V293_create_enabled_failure_exit;assumption.
Qed.

(* Expression observations do not assume an interrupt state. *)
Lemma V293_create_error66_read : forall s,
 s |= LV 209%Z @ Tint8 |-> Vint32(Int.repr 66) ** Atrue ->
 s |= Rv(evar 209%Z) @ Tint8 == Vint32(Int.repr 66).
Proof. intros s H. eapply lvar_rv with(perm:=true)(P:=Atrue);[exact H|reflexivity]. Qed.
Lemma V293_create_error66_guard : forall s,
 s |= LV 209%Z @ Tint8 |-> Vint32(Int.repr 66) ** Atrue ->
 evalval(ebinop oeq(evar 209%Z)(econst32 Int.zero))(getsmem s)=Some(Vint32 Int.zero) /\
 evaltype(ebinop oeq(evar 209%Z)(econst32 Int.zero))(getsmem s)=Some Tint32.
Proof.
 intros s H. pose proof(V293_create_error66_read s H)as Read.
 cbn[sat]in Read. destruct Read as[Value[Kind Defined]].
 destruct(V293_create_local_block _ _ _ _ _ H)as[b Env].
 destruct s as [[[[[[ge le] M] ir] aux] O] op].
 change(get le 209%Z=Some(b,Tint8))in Env.
 cbn[getsmem get_smem evalval evaltype get_lenv get_mem]in Value.
 cbv delta[env var memory.ident Modules.ident]in *. rewrite Env in Value.
 cbn[getsmem get_smem evalval evaltype get_lenv get_mem].
 cbv delta[env var memory.ident Modules.ident].
 rewrite Env. change(load Tint8 M(b,0%Z)=Some(Vint32(Int.repr 66)))in Value.
 cbn -[load]. rewrite Value. split;reflexivity.
Qed.
Lemma V293_create_enabled_failure_error : forall table p F aop ir si ci,
 V293_create_enabled_failure_state table p F aop ir si ci ==>
 LV 209%Z @ Tint8 |-> Vint32(Int.repr 66) ** Atrue.
Proof.
 unfold V293_create_enabled_failure_state,V293_create_enabled_failure_resources.
 intros s H;clear -H;sep auto.
Qed.

Theorem V293_OSTaskCreateExt_enabled_failure_suffix : forall Spec sd li I tid
 bf table p K F aop ir si ci running sched,
 p<13 -> (gettopis si<=INUM)%nat -> GoodFrm F -> (F ==> CurLINV li tid) ->
 (Aisr ir ** invlth_isr I 0(gettopis si) ==>
  Aisr ir ** V293_tcb_empty_pool bf(V293_create_rollback_pool table p K)) ->
 (Aisr ir ** V293_tcb_empty_pool bf(V293_create_rollback_pool table p K) ==>
  Aisr ir ** invlth_isr I 0(gettopis si)) ->
 InfRules Spec sd li I(V293_create_enabled_failure_return table p F aop ir si ci)Afalse
 (V293_create_enabled_failure_state table p F aop ir si ci)
 (V293_TaskCreateExt_suffix 92%Z 101%Z 209%Z running sched)Afalse tid.
Proof.
 intros Spec sd li I tid bf table p K F aop ir si ci running sched Range Bound Frame HR Open Close.
 assert(Guard:forall s,s |= V293_create_enabled_failure_state table p F aop ir si ci ->
  evalval(ebinop oeq(evar 209%Z)(econst32 Int.zero))(getsmem s)=Some(Vint32 Int.zero) /\
  evaltype(ebinop oeq(evar 209%Z)(econst32 Int.zero))(getsmem s)=Some Tint32).
 { intros s H. apply V293_create_error66_guard. eapply V293_create_enabled_failure_error;exact H. }
 unfold V293_TaskCreateExt_suffix. eapply seq_rule.
 - eapply if_rule with(tp:=Tint32).
   + intros s H. exists(Vint32 Int.zero). destruct(Guard s H)as[V T].
     cbn[sat]. repeat split;try assumption;discriminate.
   + eapply conseq_rule with(p:=Afalse)(q:=V293_create_enabled_failure_state table p F aop ir si ci).
     * intros s[H[v[V B]]]. destruct(Guard s H)as[Z _].
       rewrite Z in V. inversion V;subst v. discriminate B.
     * intros s H;exact H.
     * apply pfalse_rule.
   + eapply conseq_rule with(p:=V293_create_enabled_failure_state table p F aop ir si ci).
     * intros s[H _];exact H.
     * intros s H;exact H.
     * apply V293_OSTaskCreateExt_enabled_rollback with(bf:=bf)(K:=K);assumption.
 - apply rete_rule with(v:=Vint32(Int.repr 66))(t:=Tint8).
   intros s H. split.
   + unfold V293_create_enabled_failure_return. apply astar_l_apure_intro;[exact H|reflexivity].
   + apply V293_create_error66_read. eapply V293_create_enabled_failure_error;exact H.
Qed.

Theorem V293_TaskCreateExt_TCB_empty_enabled_call : forall Spec sd li I r ri tid f
 bf p top bottom identity size ext options R aop ir si ci (good:GoodFunAsrt R) F olderr,
 GoodFrm F -> p<256 -> V293_tcb_init_values_valid top bottom identity size ext options ->
 (R ==> CurLINV li tid) ->
 Spec f=Some(V293_tcb_enabled_fpre bf R aop ir si ci good,
  V293_tcb_enabled_fpost bf R aop ir si ci good,(Tint8,rev V293_TCBInit_argument_types)) ->
 InfRules Spec sd li I r ri
 (V293_tcb_enabled_external bf R aop ir si ci ** LV 209%Z @ Tint8 |->olderr **
  V293_create_tcb_arguments p top bottom identity size ext options F)
 (V293_TaskCreateExt_TCB_call 209%Z f 101%Z 108%Z 205%Z 206%Z 207%Z 208%Z 204%Z)
 (V293_tcb_enabled_external bf R aop ir si ci ** LV 209%Z @ Tint8 |->Vint32(Int.repr 66) **
  V293_create_tcb_arguments p top bottom identity size ext options F)tid.
Proof.
 intros Spec sd li I r ri tid f bf p top bottom identity size ext options R aop ir si ci good F olderr
 Frame Range Valid HR Lookup.
 assert(Ret:retpost(V293_tcb_enabled_fpost bf R aop ir si ci good)).
 { intros st args result ghosts task H. cbn[V293_tcb_enabled_fpost getasrt]in H.
   apply astar_l_apure_elim in H. destruct H as[Code _]. rewrite Code;discriminate. }
 unfold V293_TaskCreateExt_TCB_call.
 eapply conseq_rule with
 (q:=EX result:val,
  getasrt(V293_tcb_enabled_fpost bf R aop ir si ci good
   (V293_tcb_success_arguments p top bottom identity size ext options)(Some result)[]tid) **
  LV 209%Z @ Tint8 |->result ** V293_create_tcb_arguments p top bottom identity size ext options F).
 - intros s H;exact H.
 - intros s[result H]. cbn[V293_tcb_enabled_fpost getasrt]in H.
   sep normal in H. sep split in H. inversion H0;subst result. clear -H;sep auto.
 - eapply calle_rule_lvar with
   (pre:=V293_tcb_enabled_fpre bf R aop ir si ci good)
   (post:=V293_tcb_enabled_fpost bf R aop ir si ci good)(tp:=Tint8)
   (tl:=rev V293_TCBInit_argument_types)
   (vl:=V293_tcb_success_arguments p top bottom identity size ext options)
   (logicl:=[])(v':=olderr)(p:=V293_create_tcb_arguments p top bottom identity size ext options F).
   + apply V293_create_tcb_arguments_good;exact Frame.
   + exact Ret.
   + exact Lookup.
   + intros s H;exact H.
   + intros s H. eapply V293_create_tcb_arguments_read with
      (F:=V293_tcb_enabled_external bf R aop ir si ci ** LV 209%Z @ Tint8 |->olderr ** F);
      [exact Range|exact Valid| ].
     cbn[V293_tcb_enabled_fpre getasrt]in H.
     unfold V293_create_tcb_arguments in *;clear -H;sep auto.
   + apply V293_create_tcb_argument_types;assumption.
   + cbn[V293_tcb_enabled_fpre getasrt]. unfold V293_tcb_enabled_external.
     do 3 apply V293_star_CurLINV_r;exact HR.
   + intros s[result H]. cbn[V293_tcb_enabled_fpost getasrt]in H.
     apply astar_l_apure_elim in H. destruct H as[_ H].
     unfold V293_tcb_enabled_external in H.
     eapply V293_star_CurLINV_r;[ |exact H]. do 2 apply V293_star_CurLINV_r;exact HR.
Qed.

(* Stable caller export. No head or slot ownership is required in the
   enabled caller. The body of the looked-up callee is a separate obligation
   discharged by V293_OS_TCBInit_empty_enabled_contract under this SAME Spec. *)
Theorem V293_OSTaskCreateExt_enabled_empty_call_suffix : forall Spec sd li I tid f
 bf table p top bottom identity size ext options K R aop ir si ci
 (good:GoodFunAsrt R) F olderr running sched,
 p<13 -> (gettopis si<=INUM)%nat -> GoodFrm R -> GoodFrm F ->
 V293_tcb_init_values_valid top bottom identity size ext options ->
 (R ==> CurLINV li tid) ->
 (Aisr ir ** invlth_isr I 0(gettopis si) ==>
  Aisr ir ** V293_tcb_empty_pool bf(V293_create_rollback_pool table p K)) ->
 (Aisr ir ** V293_tcb_empty_pool bf(V293_create_rollback_pool table p K) ==>
  Aisr ir ** invlth_isr I 0(gettopis si)) ->
 Spec f=Some(V293_tcb_enabled_fpre bf R aop ir si ci good,
  V293_tcb_enabled_fpost bf R aop ir si ci good,(Tint8,rev V293_TCBInit_argument_types)) ->
 InfRules Spec sd li I
 (V293_create_enabled_failure_return table p
  (V293_create_enabled_failure_kept bf top bottom identity size ext options R F)aop ir si ci)Afalse
 (V293_tcb_enabled_external bf R aop ir si ci ** LV 209%Z @ Tint8 |->olderr **
  V293_create_tcb_arguments p top bottom identity size ext options(V293_tcb_table_binding table ** F))
 (sseq(V293_TaskCreateExt_TCB_call 209%Z f 101%Z 108%Z 205%Z 206%Z 207%Z 208%Z 204%Z)
  (V293_TaskCreateExt_suffix 92%Z 101%Z 209%Z running sched))Afalse tid.
Proof.
 intros Spec sd li I tid f bf table p top bottom identity size ext options K R aop ir si ci
 good F olderr running sched Range Bound ResourceFrame Frame Valid HR Open Close Lookup.
 eapply seq_rule.
 - apply V293_TaskCreateExt_TCB_empty_enabled_call with(good:=good).
   + cbn[GoodFrm V293_tcb_table_binding];tauto.
   + lia.
   + exact Valid.
   + exact HR.
   + exact Lookup.
 - eapply conseq_rule with(p:=V293_create_enabled_failure_state table p
    (V293_create_enabled_failure_kept bf top bottom identity size ext options R F)aop ir si ci).
   + unfold V293_tcb_enabled_external,V293_create_tcb_arguments,
      V293_create_enabled_failure_state,V293_create_enabled_failure_resources,
      V293_create_enabled_failure_kept. intros s H;clear -H;sep auto.
   + intros s H;exact H.
   + apply V293_OSTaskCreateExt_enabled_failure_suffix with(bf:=bf)(K:=K).
     * exact Range.
     * exact Bound.
     * unfold V293_create_enabled_failure_kept,Alvarmapsto,Alvarenv',Aptrmapsto.
       cbn[GoodFrm];tauto.
     * unfold V293_create_enabled_failure_kept. do 6 apply V293_star_CurLINV_r.
       apply V293_star_CurLINV_r. apply V293_star_CurLINV_l;exact HR.
     * exact Open.
     * exact Close.
Qed.

Print Assumptions V293_OSTaskCreateExt_enabled_empty_call_suffix.
