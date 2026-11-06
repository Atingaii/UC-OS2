(* Successful TaskCreateExt two-call connection. Stack and two CPU Hooks remain external. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateTCBCall.
Require Import CertiOS.certiucos.v293.proofs.V293TCBPriorityHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TCBEmptyInternal.
Require Import CertiOS.certiucos.v293.proofs.V293TCBSnapshotInternal.
Require Import CertiOS.certiucos.v293.proofs.V293TCBSuccessInternal.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitFields.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.code.V293OSTaskCreateExtSuffix.
Require Import CertiOS.certiucos.v293.code.V293OSTCBInitFunction.
Require Import CertiOS.certiucos.v293.code.V293OSTaskCreateExtCalls.
Require Import CertiOS.certiucos.v293.code.V293OSTaskCreateExtPrefix.
Require Import CertiOS.certiucos.v293.proofs.V293TCBHookCall.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List Lia.
Import Coq.Lists.List.ListNotations.


Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateFailureHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateStackEntry.
Local Open Scope nat_scope.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateSuccessHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateStackCall.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateBodyFailure.

(* Resources are external function assertions, never caller local cells. The
   actual Hook may change this resource; no port implementation is invented. *)
Definition V293_create_stack_resource_fpre (E:funasrt) args : fpre :=
 fun vl lg tid=>@mkfunasrt ([|vl=args|] ** getasrt E) (conj I(getprop E)).
Definition V293_create_stack_resource_fpost (E:funasrt) args stack : fpost :=
 fun vl result lg tid=>@mkfunasrt ([|vl=args /\ result=Some stack|] ** getasrt E) (conj I(getprop E)).
Lemma V293_create_stack_resource_retpost : forall E args stack,
 retpost(V293_create_stack_resource_fpost E args stack).
Proof.
 intros. unfold retpost. intros st vl result lg tid H.
 cbn [V293_create_stack_resource_fpost getasrt]in H.
 apply astar_l_apure_elim in H. destruct H as[[_ Code] _]. rewrite Code. discriminate.
Qed.
Theorem V293_OSTaskCreateExt_stack_resource_call_hoare : forall Spec sd li I r ri tid hook
 (before after:funasrt)
 target argv inputtop options stack oldpsp F,
 GoodFrm F -> V293_stack_argument_valid argv inputtop options ->
 (getasrt before ==> CurLINV li tid) -> (getasrt after ==> CurLINV li tid) ->
 let args:=V293_create_stack_values target argv inputtop options in
 Spec hook=Some(V293_create_stack_resource_fpre before args,
 V293_create_stack_resource_fpost after args stack,
 (Tptr Tint32,rev V293_stack_argument_types)) ->
 InfRules Spec sd li I r ri
 (getasrt before **
 LV 108%Z @ (Tptr Tint32) |-> oldpsp **
 V293_create_stack_arguments target argv inputtop options F)
 (V293_TaskCreateExt_stack_call 108%Z hook 201%Z 202%Z 203%Z 204%Z)
 (getasrt after **
 LV 108%Z @ (Tptr Tint32) |-> stack **
 V293_create_stack_arguments target argv inputtop options F)tid.
Proof.
 intros Spec sd li I r ri tid hook before after
 target argv inputtop options stack oldpsp F Frame Valid Before After args Lookup.
 unfold V293_TaskCreateExt_stack_call.
 eapply conseq_rule with
 (p:=getasrt(V293_create_stack_resource_fpre before args args [] tid) **
 LV 108%Z @ (Tptr Tint32) |-> oldpsp **
 V293_create_stack_arguments target argv inputtop options F)
 (q:=EX result:val,
 getasrt(V293_create_stack_resource_fpost after args stack args (Some result) [] tid) **
 LV 108%Z @ (Tptr Tint32) |-> result **
 V293_create_stack_arguments target argv inputtop options F).
 - intros s H. cbn [V293_create_stack_resource_fpre getasrt].
   apply astar_assoc_intro. apply astar_l_apure_intro;[exact H|reflexivity].
 - intros s[result H]. cbn [V293_create_stack_resource_fpost getasrt]in H.
   apply astar_assoc_elim in H. apply astar_l_apure_elim in H.
   destruct H as[[_ Code] H]. inversion Code;subst result. exact H.
 - eapply calle_rule_lvar with(tp:=Tptr Tint32)(tl:=rev V293_stack_argument_types)
   (vl:=args)(logicl:=[])(v':=oldpsp)
   (p:=V293_create_stack_arguments target argv inputtop options F).
   + apply V293_create_stack_arguments_good. exact Frame.
   + apply V293_create_stack_resource_retpost.
   + exact Lookup.
   + intros s H;exact H.
   + intros s H. eapply V293_create_stack_arguments_read with
     (F:=getasrt(V293_create_stack_resource_fpre before args args [] tid) **
     LV 108%Z @ (Tptr Tint32) |-> oldpsp ** F);[exact Valid| ].
     unfold V293_create_stack_arguments in *. clear -H. sep auto.
   + apply V293_create_stack_argument_types. exact Valid.
   + cbn [V293_create_stack_resource_fpre getasrt]. apply V293_star_CurLINV_r.
     exact Before.
   + intros s[result H]. cbn [V293_create_stack_resource_fpost getasrt]in H.
     eapply V293_star_CurLINV_r;[ |exact H].
     exact After.
Qed.


Theorem V293_OSTaskCreateExt_stack_success_hoare : forall Spec sd li I tid f hook
 table slot bg bt base old p top bottom identity size ext options next
 bh bgrp br bn oldblock oldbase present oldprev g row n oldback R aop isr is cs
 (good:GoodFunAsrt R) (before:funasrt) F olderr oldpsp target argv inputtop running sched brun,
 GoodFrm F -> V293_stack_argument_valid argv inputtop options ->
 (getasrt before ==> CurLINV li tid) -> p<256 -> V293_tcb_init_values_valid top bottom identity size ext options ->
 (R ==> CurLINV li tid) ->
 let fp:=V293_tcb_snapshot_fpre (Vptr(bt,Int.repr base))
   (V293_tcb_empty_fpre bg R aop isr is cs good)
   (V293_tcb_success_fpre table slot bg bt base old p top bottom identity size ext options next
      bh bgrp br bn oldblock oldbase present oldprev g row n oldback R aop isr is cs good) in
 let fq:=V293_tcb_snapshot_fpost (Vptr(bt,Int.repr base))
   (V293_tcb_empty_fpost bg R aop isr is cs good)
   (V293_tcb_success_fpost table bg bt base p top bottom identity size ext options next
      bh bgrp br bn oldblock oldbase present g row n R aop isr is cs good) in
 Spec hook=Some(
 V293_create_stack_resource_fpre before(V293_create_stack_values target argv inputtop options),
 V293_create_stack_resource_fpost
 (fp(V293_tcb_success_arguments p top bottom identity size ext options)[logic_val(Vptr(bt,Int.repr base))]tid)
 (V293_create_stack_values target argv inputtop options)top,
 (Tptr Tint32,rev V293_stack_argument_types)) ->
 Spec f=Some(fp,fq,(Tint8,rev V293_TCBInit_argument_types)) ->
 InfRules Spec sd li I
 (V293_create_success_return running brun
  (getasrt(fq(V293_tcb_success_arguments p top bottom identity size ext options)
    (Some(Vint32 Int.zero))[logic_val(Vptr(bt,Int.repr base))]tid) **
   V293_create_tcb_arguments p top bottom identity size ext options
   (V293_create_stack_kept target argv inputtop F))) Afalse
 (getasrt before ** LV 108%Z @ (Tptr Tint32) |->oldpsp **
 V293_create_stack_arguments target argv inputtop options
 (LV 209%Z @ Tint8 |->olderr ** LV 101%Z @ Tint8 |->V293_byteval p **
 LV 205%Z @ (Tptr Tint32) |->bottom ** LV 206%Z @ Tint16 |->identity **
 LV 207%Z @ Tint32 |->size ** LV 208%Z @ (Tptr Tvoid) |->ext **
 (V293_create_idle_running running brun ** F)))
 (V293_TaskCreateExt_calls 108%Z hook 201%Z 202%Z 203%Z 204%Z 209%Z f
 101%Z 205%Z 206%Z 207%Z 208%Z
 (V293_TaskCreateExt_suffix 92%Z 101%Z 209%Z running sched)) Afalse tid.
Proof.
 intros Spec sd li I tid f hook table slot bg bt base old p top bottom identity size ext options next
 bh bgrp br bn oldblock oldbase present oldprev g row n oldback R aop isr is cs good before
 F olderr oldpsp target argv inputtop running sched brun Frame StackValid HBefore Range Valid HR fp fq Hook TCB.
 unfold V293_TaskCreateExt_calls. eapply seq_rule.
 - eapply V293_OSTaskCreateExt_stack_resource_call_hoare with(before:=before)
   (after:=fp(V293_tcb_success_arguments p top bottom identity size ext options)
    [logic_val(Vptr(bt,Int.repr base))]tid).
   + unfold V293_create_idle_running,V293_create_global_binding,Alvarmapsto,Alvarenv',Aptrmapsto.
     cbn [GoodFrm]. tauto.
   + exact StackValid.
   + exact HBefore.
   + unfold fp. cbn [V293_tcb_snapshot_fpre V293_tcb_guard_fpre V293_tcb_success_fpre getasrt].
     do 2 apply V293_star_CurLINV_r.
     unfold V293_tcb_success_external. apply V293_hook_resource_linv.
     apply V293_star_CurLINV_r. exact HR.
   + exact Hook.
 - eapply conseq_rule with
   (p:=getasrt(fp(V293_tcb_success_arguments p top bottom identity size ext options)
    [logic_val(Vptr(bt,Int.repr base))]tid) ** LV 209%Z @ Tint8 |->olderr **
    V293_create_tcb_arguments p top bottom identity size ext options
    (V293_create_idle_running running brun ** V293_create_stack_kept target argv inputtop F))(q:=Afalse).
   + intros s H. unfold V293_create_stack_arguments,V293_create_tcb_arguments,V293_create_stack_kept in *.
     clear -H. sep auto.
   + intros s H;exact H.
   + eapply V293_OSTaskCreateExt_success_call_suffix_hoare with(good:=good).
     * unfold V293_create_stack_kept,Alvarmapsto,Alvarenv',Aptrmapsto. cbn [GoodFrm]. tauto.
     * exact Range.
     * exact Valid.
     * exact HR.
     * exact TCB.
Qed.
