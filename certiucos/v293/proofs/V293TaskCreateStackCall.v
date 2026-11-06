(* Actual stack Hook call, then the existing empty TCB call and failure suffix.
   The Hook contract is EXTERNAL, not a port implementation or WFIFun proof.
   Rbefore/Rafter may differ, so stack memory need not be silently read-only. *)
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
Definition V293_create_stack_values target argv inputtop options :=
 [V293_task_selector target;argv;inputtop;options].
Definition V293_create_stack_arguments target argv inputtop options F :=
 LV 201%Z @ Tint32 |-> V293_task_selector target **
 LV 202%Z @ (Tptr Tvoid) |-> argv **
 LV 203%Z @ (Tptr Tint32) |-> inputtop **
 LV 204%Z @ Tint16 |-> options ** F.
Definition V293_create_stack_kept target argv inputtop F :=
 LV 201%Z @ Tint32 |-> V293_task_selector target **
 LV 202%Z @ (Tptr Tvoid) |-> argv **
 LV 203%Z @ (Tptr Tint32) |-> inputtop ** F.
Lemma V293_create_stack_arguments_good : forall target argv inputtop options F,
 GoodFrm F -> GoodFrm(V293_create_stack_arguments target argv inputtop options F).
Proof.
 intros. unfold V293_create_stack_arguments,Alvarmapsto,Alvarenv',Aptrmapsto.
 cbn [GoodFrm]. repeat split;auto.
Qed.
Theorem V293_create_stack_arguments_read : forall target argv inputtop options F,
 V293_stack_argument_valid argv inputtop options ->
 V293_create_stack_arguments target argv inputtop options F ==>
 Rvl [evar 201%Z;evar 202%Z;evar 203%Z;evar 204%Z]
 @(rev V293_stack_argument_types)==V293_create_stack_values target argv inputtop options.
Proof.
 intros target argv inputtop options F [Arg [Top Opt]] s Owned.
 assert(ReadTask:s |= Rv(evar 201%Z) @ (Tint32) == (V293_task_selector target)).
 { eapply lvar_rv with(perm:=true)(P:=Atrue).
   - unfold V293_create_stack_arguments in Owned. clear -Owned. sep auto.
   - reflexivity. }
 assert(ReadArg:s |= Rv(evar 202%Z) @ (Tptr Tvoid) == (argv)).
 { eapply lvar_rv with(perm:=true)(P:=Atrue).
   - unfold V293_create_stack_arguments in Owned. clear -Owned. sep auto.
   - exact Arg. }
 assert(ReadTop:s |= Rv(evar 203%Z) @ (Tptr Tint32) == (inputtop)).
 { eapply lvar_rv with(perm:=true)(P:=Atrue).
   - unfold V293_create_stack_arguments in Owned. clear -Owned. sep auto.
   - exact Top. }
 assert(ReadOpt:s |= Rv(evar 204%Z) @ (Tint16) == (options)).
 { eapply lvar_rv with(perm:=true)(P:=Atrue).
   - unfold V293_create_stack_arguments in Owned. clear -Owned. sep auto.
   - exact Opt. }
 cbn [sat getsmem]in ReadTask,ReadArg,ReadTop,ReadOpt.
 cbn [sat getsmem evalexprlist V293_stack_argument_types rev app V293_create_stack_values]. tauto.
Qed.
Lemma V293_create_stack_argument_types : forall target argv inputtop options,
 V293_stack_argument_valid argv inputtop options ->
 tl_vl_match(rev V293_stack_argument_types)(V293_create_stack_values target argv inputtop options)=true.
Proof.
 intros target argv inputtop options [Arg [Top Opt]].
 change(type_val_match(Tptr Tvoid)argv=true)in Arg.
 change(type_val_match(Tptr Tint32)inputtop=true)in Top.
 change(type_val_match Tint16 options=true)in Opt.
 cbn [tl_vl_match V293_stack_argument_types rev app V293_create_stack_values V293_task_selector].
 rewrite Arg,Top,Opt. reflexivity.
Qed.
Definition V293_create_stack_fpre bg R aop isr is cs (good:GoodFunAsrt R) args : fpre :=
 fun vl lg tid=>@mkfunasrt
 ([|vl=args|] ** V293_tcb_empty_external bg R aop isr is cs)
 (conj I(V293_tcb_empty_external_good bg R aop isr is cs good)).
Definition V293_create_stack_fpost bg R aop isr is cs (good:GoodFunAsrt R) args stack : fpost :=
 fun vl result lg tid=>@mkfunasrt
 ([|vl=args /\ result=Some stack|] ** V293_tcb_empty_external bg R aop isr is cs)
 (conj I(V293_tcb_empty_external_good bg R aop isr is cs good)).
Lemma V293_create_stack_retpost : forall bg R aop isr is cs good args stack,
 retpost(V293_create_stack_fpost bg R aop isr is cs good args stack).
Proof.
 intros. unfold retpost. intros st vl result lg tid Owned.
 cbn [V293_create_stack_fpost getasrt]in Owned.
 apply astar_l_apure_elim in Owned. destruct Owned as[[Args Code] _]. rewrite Code. discriminate.
Qed.
Theorem V293_OSTaskCreateExt_stack_call_hoare : forall Spec sd li I r ri tid hook
 bg Rbefore Rafter aop isr is cs (gb:GoodFunAsrt Rbefore)(ga:GoodFunAsrt Rafter)
 target argv inputtop options stack oldpsp F,
 GoodFrm F -> V293_stack_argument_valid argv inputtop options ->
 (Rbefore ==> CurLINV li tid) -> (Rafter ==> CurLINV li tid) ->
 let args:=V293_create_stack_values target argv inputtop options in
 Spec hook=Some(V293_create_stack_fpre bg Rbefore aop isr is cs gb args,
 V293_create_stack_fpost bg Rafter aop isr is cs ga args stack,
 (Tptr Tint32,rev V293_stack_argument_types)) ->
 InfRules Spec sd li I r ri
 (V293_tcb_empty_external bg Rbefore aop isr is cs **
 LV 108%Z @ (Tptr Tint32) |-> oldpsp **
 V293_create_stack_arguments target argv inputtop options F)
 (V293_TaskCreateExt_stack_call 108%Z hook 201%Z 202%Z 203%Z 204%Z)
 (V293_tcb_empty_external bg Rafter aop isr is cs **
 LV 108%Z @ (Tptr Tint32) |-> stack **
 V293_create_stack_arguments target argv inputtop options F)tid.
Proof.
 intros Spec sd li I r ri tid hook bg Rbefore Rafter aop isr is cs gb ga
 target argv inputtop options stack oldpsp F Frame Valid Before After args Lookup.
 unfold V293_TaskCreateExt_stack_call.
 eapply conseq_rule with
 (p:=getasrt(V293_create_stack_fpre bg Rbefore aop isr is cs gb args args [] tid) **
 LV 108%Z @ (Tptr Tint32) |-> oldpsp **
 V293_create_stack_arguments target argv inputtop options F)
 (q:=EX result:val,
 getasrt(V293_create_stack_fpost bg Rafter aop isr is cs ga args stack args (Some result) [] tid) **
 LV 108%Z @ (Tptr Tint32) |-> result **
 V293_create_stack_arguments target argv inputtop options F).
 - intros s H. cbn [V293_create_stack_fpre getasrt].
   apply astar_assoc_intro. apply astar_l_apure_intro;[exact H|reflexivity].
 - intros s[result H]. cbn [V293_create_stack_fpost getasrt]in H.
   apply astar_assoc_elim in H. apply astar_l_apure_elim in H.
   destruct H as[[_ Code] H]. inversion Code;subst result. exact H.
 - eapply calle_rule_lvar with(tp:=Tptr Tint32)(tl:=rev V293_stack_argument_types)
   (vl:=args)(logicl:=[])(v':=oldpsp)
   (p:=V293_create_stack_arguments target argv inputtop options F).
   + apply V293_create_stack_arguments_good. exact Frame.
   + apply V293_create_stack_retpost.
   + exact Lookup.
   + intros s H;exact H.
   + intros s H. eapply V293_create_stack_arguments_read with
     (F:=getasrt(V293_create_stack_fpre bg Rbefore aop isr is cs gb args args [] tid) **
     LV 108%Z @ (Tptr Tint32) |-> oldpsp ** F);[exact Valid| ].
     unfold V293_create_stack_arguments in *. clear -H. sep auto.
   + apply V293_create_stack_argument_types. exact Valid.
   + cbn [V293_create_stack_fpre getasrt]. apply V293_star_CurLINV_r.
     unfold V293_tcb_empty_external. do 4 apply V293_star_CurLINV_r. exact Before.
   + intros s[result H]. cbn [V293_create_stack_fpost getasrt]in H.
     eapply V293_star_CurLINV_r;[ |exact H].
     unfold V293_tcb_empty_external. do 4 apply V293_star_CurLINV_r. exact After.
Qed.

(* Stable interface: two actual calls and original complete failure suffix. *)
Theorem V293_OSTaskCreateExt_stack_empty_failure_hoare : forall Spec sd li I tid f hook
 table reserved slot bg bt base old p top bottom identity size ext options next
 bh bgrp br bn oldblock oldbase present oldprev g row n oldback R aop isr is cs
 (good:GoodFunAsrt R) Rbefore (gb:GoodFunAsrt Rbefore) F olderr oldpsp target argv inputtop running sched,
 GoodFrm R -> GoodFrm F -> p<13 ->
 V293_stack_argument_valid argv inputtop options ->
 (Rbefore ==> CurLINV li tid) ->
 V293_tcb_init_values_valid top bottom identity size ext options ->
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
 V293_create_stack_fpre bg Rbefore aop isr is cs gb(V293_create_stack_values target argv inputtop options),
 V293_create_stack_fpost bg R aop isr is cs good(V293_create_stack_values target argv inputtop options)top,
 (Tptr Tint32,rev V293_stack_argument_types)) ->
 Spec f=Some(fp,fq,(Tint8,rev V293_TCBInit_argument_types)) ->
 InfRules Spec sd li I
 (V293_create_failure_return table p
  (V293_create_failure_kept bg top bottom identity size ext options R
  (V293_create_stack_kept target argv inputtop F)) aop isr is cs) Afalse
 (V293_tcb_empty_external bg Rbefore aop isr is cs **
 LV 108%Z @ (Tptr Tint32) |-> oldpsp **
 V293_create_stack_arguments target argv inputtop options
 (LV 209%Z @ Tint8 |-> olderr **
 LV 101%Z @ Tint8 |-> V293_byteval p **
 LV 205%Z @ (Tptr Tint32) |-> bottom **
 LV 206%Z @ Tint16 |-> identity **
 LV 207%Z @ Tint32 |-> size **
 LV 208%Z @ (Tptr Tvoid) |-> ext **
 (V293_tcb_table_binding table **
 (Amapsto(table,(4*Z.of_nat p)%Z)(Tptr V293_tcb_type)true reserved ** F))))
 (V293_TaskCreateExt_calls 108%Z hook 201%Z 202%Z 203%Z 204%Z 209%Z f
 101%Z 205%Z 206%Z 207%Z 208%Z
 (V293_TaskCreateExt_suffix 92%Z 101%Z 209%Z running sched)) Afalse tid.
Proof.
 intros Spec sd li I tid f hook table reserved slot bg bt base old p top bottom identity size ext options next
 bh bgrp br bn oldblock oldbase present oldprev g row n oldback R aop isr is cs good Rbefore gb
 F olderr oldpsp target argv inputtop running sched RFrame Frame Range StackValid HBefore Valid HR fp fq Hook TCB.
 unfold V293_TaskCreateExt_calls. eapply seq_rule.
 - eapply V293_OSTaskCreateExt_stack_call_hoare with(gb:=gb)(ga:=good).
   + unfold Alvarmapsto,Alvarenv',Aptrmapsto. cbn [GoodFrm V293_tcb_table_binding]. repeat split;auto.
   + exact StackValid.
   + exact HBefore.
   + exact HR.
   + exact Hook.
 - eapply conseq_rule with
   (p:=getasrt(fp(V293_tcb_success_arguments p top bottom identity size ext options)[logic_val Vnull]tid) **
    LV 209%Z @ Tint8 |-> olderr **
    V293_create_tcb_arguments p top bottom identity size ext options
    (V293_tcb_table_binding table **
    (Amapsto(table,(4*Z.of_nat p)%Z)(Tptr V293_tcb_type)true reserved **
    V293_create_stack_kept target argv inputtop F)))
   (q:=Afalse).
   + intros s H. unfold fp. cbn [V293_tcb_snapshot_fpre V293_tcb_empty_fpre getasrt].
     unfold V293_create_stack_arguments,V293_create_tcb_arguments,V293_create_stack_kept in *.
     clear -H. sep auto.
   + intros s H;exact H.
   + eapply V293_OSTaskCreateExt_empty_call_suffix_hoare with(good:=good).
     * exact RFrame.
     * unfold V293_create_stack_kept,Alvarmapsto,Alvarenv',Aptrmapsto. cbn [GoodFrm]. repeat split;auto.
     * exact Range.
     * exact Valid.
     * exact HR.
     * exact TCB.
Qed.
