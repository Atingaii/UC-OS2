(* Actual TCB success call and unchanged TaskCreateExt suffix, OSRunning=0.
   No scheduler implementation, full-function or whole-kernel claim. *)
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateBodyFailure.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateFailureHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateTCBCall.
Require Import CertiOS.certiucos.v293.proofs.V293TCBSnapshotInternal.
Require Import CertiOS.certiucos.v293.proofs.V293TCBSuccessInternal.
Require Import CertiOS.certiucos.v293.proofs.V293TCBEmptyInternal.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitFields.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.code.V293OSTaskCreateExtSuffix.
Require Import CertiOS.certiucos.v293.code.V293OSTCBInitFunction.
Require Import CertiOS.certiucos.v293.code.V293OSTaskCreateExtCalls.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Definition V293_create_idle_running running brun :=
 V293_create_global_binding running Tint8 brun **
 Amapsto(brun,0%Z)Tint8 false(Vint32 Int.zero).
Definition V293_create_success_state running brun F :=
 LV 209%Z @ Tint8 |->Vint32 Int.zero **
 (V293_create_idle_running running brun ** F).
Definition V293_create_success_return running brun F : retasrt :=
 fun result=>[|result=Some(Vint32 Int.zero)|] ** V293_create_success_state running brun F.
Lemma V293_create_idle_running_good : forall running brun,
 GoodFrm(V293_create_idle_running running brun).
Proof. intros. cbn [V293_create_idle_running V293_create_global_binding GoodFrm]. tauto. Qed.
Lemma V293_create_success_err_read : forall running brun F,
 V293_create_success_state running brun F ==> Rv(evar 209%Z) @ Tint8 == Vint32 Int.zero.
Proof.
 intros running brun F s H. eapply lvar_rv with(perm:=true)(P:=V293_create_idle_running running brun ** F).
 - exact H.
 - reflexivity.
Qed.
Lemma V293_create_success_guards : forall running brun F s,
 s |= V293_create_success_state running brun F ->
 (evalval(ebinop oeq(evar 209%Z)(econst32 Int.zero))(getsmem s)=Some(Vint32 Int.one) /\
 evaltype(ebinop oeq(evar 209%Z)(econst32 Int.zero))(getsmem s)=Some Tint32) /\
 (evalval(ebinop oeq(evar running)(econst32 Int.one))(getsmem s)=Some(Vint32 Int.zero) /\
 evaltype(ebinop oeq(evar running)(econst32 Int.one))(getsmem s)=Some Tint32).
Proof.
 intros running brun F s H.
 pose proof(V293_create_success_err_read _ _ _ _ H)as Read.
 assert(Local:s |= LV 209%Z @ Tint8 |->Vint32 Int.zero ** Atrue).
 { unfold V293_create_success_state in H. clear -H. sep auto. }
 destruct(V293_create_local_block _ _ _ _ _ Local)as[berr Err].
 assert(Global:s |= V293_create_global_binding running Tint8 brun ** Atrue).
 { unfold V293_create_success_state,V293_create_idle_running in H. clear -H. sep auto. }
 pose proof(V293_star_env_l _ _ (fun ge le=>get le running=None /\ get ge running=Some(brun,Tint8))
 (V293_create_global_binding_env running Tint8 brun)s Global)as[NoShadow Binding].
 assert(Running:s |= Amapsto(brun,0%Z)Tint8 false(Vint32 Int.zero) ** Atrue).
 { unfold V293_create_success_state,V293_create_idle_running in H. clear -H. sep auto. }
 assert(Load:load Tint8(getmem s)(brun,0%Z)=Some(Vint32 Int.zero)).
 { eapply V293_star_load_l;[ |exact Running]. intros st HS.
   eapply V293_mapsto_load with(n:=0);[lia|exact HS]. }
 destruct s as [[[[[[ge le] M] ir] aux] O] op].
 change(get le 209%Z=Some(berr,Tint8))in Err.
 change(get le running=None)in NoShadow. change(get ge running=Some(brun,Tint8))in Binding.
 change(load Tint8 M(brun,0%Z)=Some(Vint32 Int.zero))in Load.
 cbn [sat getsmem get_smem evalval evaltype get_lenv get_mem]in Read.
 cbv delta [env var memory.ident Modules.ident]in *. rewrite Err in Read.
 destruct Read as[Read _].
 cbn [getsmem get_smem evalval evaltype get_lenv get_genv get_mem].
 cbv delta [env var memory.ident Modules.ident]. rewrite Err,NoShadow,Binding.
 cbn -[load]. rewrite Read,Load. repeat split;reflexivity.
Qed.

Theorem V293_OSTaskCreateExt_idle_success_suffix_hoare : forall Spec sd li I tid
 table prio running sched brun F,
 InfRules Spec sd li I (V293_create_success_return running brun F) Afalse
 (V293_create_success_state running brun F)
 (V293_TaskCreateExt_suffix table prio 209%Z running sched) Afalse tid.
Proof.
 intros. unfold V293_TaskCreateExt_suffix. eapply seq_rule.
 - eapply if_rule with(tp:=Tint32).
   + intros s H. exists(Vint32 Int.one).
     destruct(V293_create_success_guards _ _ _ _ H)as[[Value Kind] _].
     cbn [sat]. repeat split;try assumption;discriminate.
   + eapply conseq_rule with(p:=V293_create_success_state running brun F).
     * intros s[H _];exact H.
     * intros s H;exact H.
     * eapply seq_rule;[apply skip_rule| ].
       eapply ift_rule with(tp:=Tint32).
       -- intros s H. exists(Vint32 Int.zero).
          destruct(V293_create_success_guards _ _ _ _ H)as[_ [Value Kind]].
          cbn [sat]. repeat split;try assumption;discriminate.
       -- intros s[H _];exact H.
       -- eapply conseq_rule with(p:=Afalse).
          ++ intros s[H[v[Value Bool]]].
             destruct(V293_create_success_guards _ _ _ _ H)as[_ [Zero _]].
             rewrite Zero in Value. inversion Value;subst v. discriminate Bool.
          ++ intros s H;exact H.
          ++ apply pfalse_rule.
   + eapply conseq_rule with(p:=Afalse).
     * intros s[H[v[Value Bool]]].
       destruct(V293_create_success_guards _ _ _ _ H)as[[One _] _].
       rewrite One in Value. inversion Value;subst v. discriminate Bool.
     * intros s H;exact H.
     * apply pfalse_rule.
 - apply rete_rule with(v:=Vint32 Int.zero)(t:=Tint8).
   intros s H. split.
   + apply astar_l_apure_intro;[exact H|reflexivity].
   + eapply V293_create_success_err_read;exact H.
Qed.

(* Full snapshot callee stays identical to the empty branch's Spec. The
   physical non-NULL entry selects result0; OSRunning=0 selects no dispatch.
   Entire callee post, seven arguments and caller F remain in the return. *)
Theorem V293_OSTaskCreateExt_success_call_suffix_hoare : forall Spec sd li I tid f
 table slot bg bt base old p top bottom identity size ext options next
 bh bgrp br bn oldblock oldbase present oldprev g row n oldback R aop isr is cs
 (good:GoodFunAsrt R) F olderr running sched brun,
 GoodFrm F -> p<256 -> V293_tcb_init_values_valid top bottom identity size ext options ->
 (R ==> CurLINV li tid) ->
 let fp:=V293_tcb_snapshot_fpre (Vptr(bt,Int.repr base))
   (V293_tcb_empty_fpre bg R aop isr is cs good)
   (V293_tcb_success_fpre table slot bg bt base old p top bottom identity size ext options next
      bh bgrp br bn oldblock oldbase present oldprev g row n oldback R aop isr is cs good) in
 let fq:=V293_tcb_snapshot_fpost (Vptr(bt,Int.repr base))
   (V293_tcb_empty_fpost bg R aop isr is cs good)
   (V293_tcb_success_fpost table bg bt base p top bottom identity size ext options next
      bh bgrp br bn oldblock oldbase present g row n R aop isr is cs good) in
 Spec f=Some(fp,fq,(Tint8,rev V293_TCBInit_argument_types)) ->
 InfRules Spec sd li I
 (V293_create_success_return running brun
  (getasrt(fq(V293_tcb_success_arguments p top bottom identity size ext options)
    (Some(Vint32 Int.zero))[logic_val(Vptr(bt,Int.repr base))]tid) **
   V293_create_tcb_arguments p top bottom identity size ext options F)) Afalse
 (getasrt(fp(V293_tcb_success_arguments p top bottom identity size ext options)
  [logic_val(Vptr(bt,Int.repr base))]tid) ** LV 209%Z @ Tint8 |->olderr **
  V293_create_tcb_arguments p top bottom identity size ext options(V293_create_idle_running running brun ** F))
 (sseq (V293_TaskCreateExt_TCB_call 209%Z f 101%Z 108%Z 205%Z 206%Z 207%Z 208%Z 204%Z)
 (V293_TaskCreateExt_suffix 92%Z 101%Z 209%Z running sched)) Afalse tid.
Proof.
 intros Spec sd li I tid f table slot bg bt base old p top bottom identity size ext options next
 bh bgrp br bn oldblock oldbase present oldprev g row n oldback R aop isr is cs good F olderr running sched brun
 Frame Range Valid HR fp fq Lookup.
 eapply seq_rule.
 - eapply V293_TaskCreateExt_TCB_snapshot_call with(good:=good).
   + cbn [GoodFrm V293_create_idle_running V293_create_global_binding]. tauto.
   + exact Range.
   + exact Valid.
   + exact HR.
   + exact Lookup.
 - eapply conseq_rule with
   (p:=V293_create_success_state running brun
   (getasrt(fq(V293_tcb_success_arguments p top bottom identity size ext options)
    (Some(Vint32 Int.zero))[logic_val(Vptr(bt,Int.repr base))]tid) **
    V293_create_tcb_arguments p top bottom identity size ext options F))(q:=Afalse).
   + intros s[result H]. apply astar_l_apure_elim in H. destruct H as[Code H].
     destruct Code as[[Bad _]|[_ Equal]];[discriminate Bad|subst result].
     unfold V293_create_success_state,V293_create_tcb_arguments in *. clear -H. sep auto.
   + intros s H;exact H.
   + apply V293_OSTaskCreateExt_idle_success_suffix_hoare.
Qed.
