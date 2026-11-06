(* Standard builders for the actual nine-parameter/three-local TaskCreateExt.
   Restricted empty free-list entry, disabled IE, same original full body and
   three external Hook contracts. Not WFIFun or whole-kernel GOOD_OS. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateStackCall.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateExtPrefix.
Require Import CertiOS.certiucos.v293.proofs.V293TCBFieldsHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TCBSuccessHoare.
Require Import CertiOS.certiucos.v293.proofs.V293InitAllRecords.
Require Import CertiOS.certiucos.v293.proofs.V293TCBEmptyInternal.
Require Import CertiOS.certiucos.v293.proofs.V293TCBSnapshotInternal.
Require Import CertiOS.certiucos.v293.proofs.V293TCBSuccessInternal.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateTCBCall.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateStackEntry.
Require Import CertiOS.certiucos.v293.code.V293OSTCBInitFunction.
Require Import CertiOS.certiucos.v293.proofs.V293TCBPriorityHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateFailureHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitFields.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.code.V293OSTaskCreateExtFunction.
Require Import CertiOS.certiucos.v293.code.V293OSTaskCreateExtSuffix.
Require Import CertiOS.certiucos.v293.code.V293OSTaskCreateExtPrefix.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateBodyFailure.
Require Import CertiOS.tactics.hoareforward.init_spec.

Definition V293_create_internal_declarations :=
 revlcons V293_CreateExt_parameters V293_CreateExt_locals.
Definition V293_create_internal_domain :=
 A_dom_lenv(getlenvdom V293_create_internal_declarations).
Definition V293_create_internal_values target argv inputtop p identity bottom size ext options :=
 [V293_task_selector target;argv;inputtop;V293_byteval p;identity;bottom;size;ext;options].
Definition V293_create_internal_other_parameters target argv inputtop identity bottom size ext options :=
 LV 204%Z @ Tint16 |->options ** LV 208%Z @ (Tptr Tvoid) |->ext **
 LV 207%Z @ Tint32 |->size ** LV 205%Z @ (Tptr Tint32) |->bottom **
 LV 206%Z @ Tint16 |->identity **
 LV 203%Z @ (Tptr Tint32) |->inputtop ** LV 202%Z @ (Tptr Tvoid) |->argv **
 LV 201%Z @ Tint32 |->V293_task_selector target ** Aemp.
Definition V293_create_internal_locals :=
 (EX psp:val, LV 108%Z @ (Tptr Tint32) |->psp) **
 ((EX err:val, LV 209%Z @ Tint8 |->err) **
 ((EX cpu:val, LV 109%Z @ Tint32 |->cpu) ** Aemp)).
Definition V293_create_internal_pre_cells target argv inputtop p identity bottom size ext options :=
 LV 204%Z @ Tint16 |->options ** LV 208%Z @ (Tptr Tvoid) |->ext **
 LV 207%Z @ Tint32 |->size ** LV 205%Z @ (Tptr Tint32) |->bottom **
 LV 206%Z @ Tint16 |->identity ** LV 101%Z @ Tint8 |->V293_byteval p **
 LV 203%Z @ (Tptr Tint32) |->inputtop ** LV 202%Z @ (Tptr Tvoid) |->argv **
 LV 201%Z @ Tint32 |->V293_task_selector target ** V293_create_internal_locals.
Definition V293_create_internal_post_cells :=
 (EX v:val,LV 204%Z @ Tint16 |->v) **
 ((EX v:val,LV 208%Z @ (Tptr Tvoid) |->v) **
 ((EX v:val,LV 207%Z @ Tint32 |->v) **
 ((EX v:val,LV 205%Z @ (Tptr Tint32) |->v) **
 ((EX v:val,LV 206%Z @ Tint16 |->v) **
 ((EX v:val,LV 101%Z @ Tint8 |->v) **
 ((EX v:val,LV 203%Z @ (Tptr Tint32) |->v) **
 ((EX v:val,LV 202%Z @ (Tptr Tvoid) |->v) **
 ((EX v:val,LV 201%Z @ Tint32 |->v) ** V293_create_internal_locals)))))))).
Lemma V293_create_internal_buildp : forall target argv inputtop p identity bottom size ext options,
 buildp V293_create_internal_declarations
 (rev(V293_create_internal_values target argv inputtop p identity bottom size ext options))=
 Some(V293_create_internal_pre_cells target argv inputtop p identity bottom size ext options).
Proof. reflexivity. Qed.
Lemma V293_create_internal_buildq :
 buildq V293_create_internal_declarations=Some V293_create_internal_post_cells.
Proof. reflexivity. Qed.
Lemma V293_create_internal_domain_good : GoodFrm V293_create_internal_domain.
Proof. exact I. Qed.
Lemma V293_create_internal_no_shadow : forall le x,
 eq_dom_env le(getlenvdom V293_create_internal_declarations) ->
 In x [91%Z;92%Z;99%Z;97%Z] -> get le x=None.
Proof.
 intros le x Domain Member. destruct(get le x)as [[b tp] | ] eqn:E;[ |reflexivity].
 exfalso. pose proof(proj2(Domain x tp)(ex_intro _ b E))as Bad.
 cbn [V293_create_internal_declarations V293_CreateExt_parameters V293_CreateExt_locals
 revlcons getlenvdom]in Bad. cbn in Member.
 repeat destruct Member as [Member | Member];try contradiction;subst x;
 repeat destruct Bad as [Bad | Bad];try discriminate;contradiction.
Qed.
Definition V293_create_internal_external table bnest breserved bg p R aop isr is cs :=
 Agvarenv 92%Z(Tarray(Tptr V293_tcb_type)13)(table,0%Z) **
 Agvarenv 99%Z Tint8(bnest,0%Z) ** Agvarenv 97%Z Tint8(breserved,0%Z) **
 Amapsto(bnest,0%Z)Tint8 true(V293_byteval 0) **
 Amapsto(table,(4*Z.of_nat p)%Z)(Tptr V293_tcb_type)true Vnull **
 V293_tcb_empty_external bg R aop isr is cs.
Lemma V293_create_internal_external_good : forall table bnest breserved bg p R aop isr is cs,
 GoodFunAsrt R -> GoodFunAsrt(V293_create_internal_external table bnest breserved bg p R aop isr is cs).
Proof. intros. cbn [V293_create_internal_external V293_tcb_empty_external GoodFunAsrt]. tauto. Qed.
Definition V293_create_empty_fpre table bnest breserved bg p target argv inputtop identity bottom size ext options
 R aop isr is cs(good:GoodFunAsrt R) : fpre :=
 fun vl lg tid=>@mkfunasrt
 ([|vl=V293_create_internal_values target argv inputtop p identity bottom size ext options|] **
 V293_create_internal_external table bnest breserved bg p R aop isr is cs)
 (conj I(V293_create_internal_external_good table bnest breserved bg p R aop isr is cs good)).
Definition V293_create_empty_fpost table bnest breserved bg p R aop isr is cs(good:GoodFunAsrt R) : fpost :=
 fun vl result lg tid=>@mkfunasrt
 ([|result=Some(Vint32(Int.repr 66))|] **
 V293_create_internal_external table bnest breserved bg p R aop isr is cs)
 (conj I(V293_create_internal_external_good table bnest breserved bg p R aop isr is cs good)).

Lemma V293_create_internal_unpack : forall target argv inputtop p identity bottom size ext options Q,
 V293_create_internal_pre_cells target argv inputtop p identity bottom size ext options ** Q ==>
 EX cpu:val,EX err:val,EX psp:val,EX bp:block,EX bc:block,
 (Alvarenv 101%Z Tint8(bp,0%Z) ** Amapsto(bp,0%Z)Tint8 true(V293_byteval p)) **
 ((Alvarenv 109%Z Tint32(bc,0%Z) ** Amapsto(bc,0%Z)Tint32 true cpu) **
 (LV 209%Z @ Tint8 |->err ** LV 108%Z @ (Tptr Tint32) |->psp **
 (V293_create_internal_other_parameters target argv inputtop identity bottom size ext options ** Q))).
Proof.
 intros target argv inputtop p identity bottom size ext options Q.
 unfold V293_create_internal_pre_cells,V293_create_internal_locals,
 V293_create_internal_other_parameters,Alvarmapsto,Alvarenv',Aptrmapsto. sep auto.
Qed.
Lemma V293_create_internal_bindings : forall bp bc table bnest breserved,
 (Alvarenv 101%Z Tint8(bp,0%Z) ** Alvarenv 109%Z Tint32(bc,0%Z) **
 Agvarenv 92%Z(Tarray(Tptr V293_tcb_type)13)(table,0%Z) **
 Agvarenv 99%Z Tint8(bnest,0%Z) ** Agvarenv 97%Z Tint8(breserved,0%Z)) **
 V293_create_internal_domain ==>
 V293_create_prefix_bindings bp bnest bc table 99%Z 97%Z breserved ** V293_create_internal_domain.
Proof.
 intros bp bc table bnest breserved s H. unfold V293_create_internal_domain in *.
 apply astar_comm in H. apply astar_l_adomlenv_elim in H. destruct H as[Domain H].
 apply astar_comm. apply astar_l_adomlenv_intro;[ |exact Domain].
 assert(N92:~indom(getlenv s)92%Z).
 { intros[v E]. rewrite(V293_create_internal_no_shadow _ 92%Z Domain ltac:(simpl;tauto))in E. discriminate. }
 assert(N99:~indom(getlenv s)99%Z).
 { intros[v E]. rewrite(V293_create_internal_no_shadow _ 99%Z Domain ltac:(simpl;tauto))in E. discriminate. }
 assert(N97:~indom(getlenv s)97%Z).
 { intros[v E]. rewrite(V293_create_internal_no_shadow _ 97%Z Domain ltac:(simpl;tauto))in E. discriminate. }
 unfold V293_create_prefix_bindings,V293_create_global_binding,V293_tcb_table_binding.
 sep auto.
 destruct_s s. simpl in *.
 join auto.
Qed.

Lemma V293_create_internal_entry : forall target argv inputtop p identity bottom size ext options
 cpu err psp bp bc table bnest breserved bg R aop isr is cs,
 (Alvarenv 101%Z Tint8(bp,0%Z) ** Amapsto(bp,0%Z)Tint8 true(V293_byteval p)) **
 ((Alvarenv 109%Z Tint32(bc,0%Z) ** Amapsto(bc,0%Z)Tint32 true cpu) **
 (LV 209%Z @ Tint8 |->err ** LV 108%Z @ (Tptr Tint32) |->psp **
 (V293_create_internal_other_parameters target argv inputtop identity bottom size ext options **
 (V293_create_internal_external table bnest breserved bg p R aop isr is cs **
 V293_create_internal_domain)))) ==>
 V293_create_prefix_state bp bnest bc table 99%Z 97%Z breserved p cpu Vnull
 (V293_create_body_frame bg R psp target argv inputtop options err bottom identity size ext
 V293_create_internal_domain) aop isr is cs.
Proof.
 intros target argv inputtop p identity bottom size ext options cpu err psp bp bc table bnest breserved bg R aop isr is cs s H.
 unfold V293_create_internal_external,V293_tcb_empty_external in H.
 assert(K:s |=
 ((Alvarenv 101%Z Tint8(bp,0%Z) ** Alvarenv 109%Z Tint32(bc,0%Z) **
 Agvarenv 92%Z(Tarray(Tptr V293_tcb_type)13)(table,0%Z) **
 Agvarenv 99%Z Tint8(bnest,0%Z) ** Agvarenv 97%Z Tint8(breserved,0%Z)) **
 V293_create_internal_domain) **
 (Amapsto(bp,0%Z)Tint8 true(V293_byteval p) ** Amapsto(bc,0%Z)Tint32 true cpu **
 Amapsto(bnest,0%Z)Tint8 true(V293_byteval 0) **
 Amapsto(table,(4*Z.of_nat p)%Z)(Tptr V293_tcb_type)true Vnull **
 LV 209%Z @ Tint8 |->err ** LV 108%Z @ (Tptr Tint32) |->psp **
 V293_create_internal_other_parameters target argv inputtop identity bottom size ext options **
 Agvarenv 91%Z(Tptr V293_tcb_type)(bg,0%Z) **
 Amapsto(bg,0%Z)(Tptr V293_tcb_type)false Vnull ** <||aop||> ** OS[isr,false,is,cs] ** R)).
 { clear -H. sep auto. }
 eapply astar_mono in K;[ |apply V293_create_internal_bindings|intros st HS;exact HS].
 unfold V293_create_prefix_state,V293_create_prefix_cells,V293_create_body_frame,
 V293_create_stack_arguments,V293_create_internal_other_parameters in *.
 cbn [V293_rdy_raw_cells]in *. clear -K. sep auto.
Qed.
Lemma V293_create_internal_pre_to_post : forall target argv inputtop p identity bottom size ext options,
 V293_create_internal_pre_cells target argv inputtop p identity bottom size ext options ==>
 V293_create_internal_post_cells.
Proof.
 intros target argv inputtop p identity bottom size ext options.
 unfold V293_create_internal_pre_cells,V293_create_internal_post_cells.
 repeat apply astar_mono;intros s H;try(eexists;exact H);exact H.
Qed.
Lemma V293_create_internal_kept_return : forall bnest bc breserved,
 V293_create_prefix_kept bnest bc 99%Z 97%Z breserved V293_create_internal_domain ==>
 LV 109%Z @ Tint32 |->Vint32 Int.zero **
 (Amapsto(bnest,0%Z)Tint8 true(V293_byteval 0) **
 Agvarenv 99%Z Tint8(bnest,0%Z) ** Agvarenv 97%Z Tint8(breserved,0%Z) **
 V293_create_internal_domain).
Proof.
 intros bnest bc breserved s H. unfold V293_create_prefix_kept in H.
 cbn [V293_rdy_raw_cells]in H.
 assert(K:s |=
 (V293_create_global_binding 99%Z Tint8 bnest ** V293_create_global_binding 97%Z Tint8 breserved) **
 ((Alvarenv 109%Z Tint32(bc,0%Z) ** Amapsto(bc,0%Z)Tint32 true(Vint32 Int.zero)) **
 (Amapsto(bnest,0%Z)Tint8 true(V293_byteval 0) ** V293_create_internal_domain))).
 { clear -H. sep auto. }
 eapply astar_mono in K.
 2: { apply astar_mono;intros st [G N];exact G. }
 2: { apply astar_mono;[apply V293_create_raw_local|intros st HS;exact HS]. }
 clear -K. sep auto.
Qed.
Lemma V293_create_internal_exit : forall target argv inputtop p top identity bottom size ext options
 bnest bc table breserved bg R aop isr is cs result,
 V293_create_failure_return table p
 (V293_create_failure_kept bg top bottom identity size ext options R
 (V293_create_stack_kept target argv inputtop
 (V293_create_prefix_kept bnest bc 99%Z 97%Z breserved V293_create_internal_domain)))
 aop isr is cs result ==>
 V293_create_internal_post_cells **
 ([|result=Some(Vint32(Int.repr 66))|] **
 V293_create_internal_external table bnest breserved bg p R aop isr is cs) **
 V293_create_internal_domain.
Proof.
 intros target argv inputtop p top identity bottom size ext options bnest bc table breserved bg R aop isr is cs result s H.
 unfold V293_create_failure_return in H. apply astar_l_apure_elim in H. destruct H as[Code H].
 unfold V293_create_failure_state,V293_create_failure_resources,V293_create_failure_kept,
 V293_create_stack_kept in H.
 assert(K:s |=
 (V293_tcb_table_binding table **
 V293_create_prefix_kept bnest bc 99%Z 97%Z breserved V293_create_internal_domain) **
 (<||aop||> ** OS[isr,false,is,cs] **
 LV 101%Z @ Tint8 |->V293_byteval p ** LV 209%Z @ Tint8 |->Vint32(Int.repr 66) **
 Amapsto(table,(4*Z.of_nat p)%Z)(Tptr V293_tcb_type)true Vnull **
 LV 108%Z @ (Tptr Tint32) |->top ** LV 205%Z @ (Tptr Tint32) |->bottom **
 LV 206%Z @ Tint16 |->identity ** LV 207%Z @ Tint32 |->size **
 LV 208%Z @ (Tptr Tvoid) |->ext ** LV 204%Z @ Tint16 |->options **
 Agvarenv 91%Z(Tptr V293_tcb_type)(bg,0%Z) **
 Amapsto(bg,0%Z)(Tptr V293_tcb_type)false Vnull ** R **
 LV 201%Z @ Tint32 |->V293_task_selector target **
 LV 202%Z @ (Tptr Tvoid) |->argv ** LV 203%Z @ (Tptr Tint32) |->inputtop)).
 { clear -H. sep auto. }
 eapply astar_mono in K.
 2: { apply astar_mono;[intros st [G N];exact G|apply V293_create_internal_kept_return]. }
 2: { intros st HS;exact HS. }
 assert(Ret:s |= V293_create_internal_pre_cells target argv inputtop p identity bottom size ext options **
 (V293_create_internal_external table bnest breserved bg p R aop isr is cs ** V293_create_internal_domain)).
 { unfold V293_create_internal_pre_cells,V293_create_internal_locals,
 V293_create_internal_external,V293_tcb_empty_external. clear -K. sep auto. }
 eapply astar_mono in Ret;[ |apply V293_create_internal_pre_to_post|intros st HS;exact HS].
 clear -Ret Code. sep auto.
Qed.

Theorem V293_OSTaskCreateExt_empty_internal_resources : forall Spec sd li I tid f hook
 bnest table breserved slot bg bt base old p top bottom identity size ext options next
 bh bgrp br bn oldblock oldbase present oldprev g row n oldback R aop isr is cs
 (good:GoodFunAsrt R) Rbefore (gb:GoodFunAsrt Rbefore) target argv inputtop running sched,
 GoodFrm Rbefore -> GoodFrm R -> p<13 ->
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
 (fun result=>V293_create_internal_post_cells **
 ([|result=Some(Vint32(Int.repr 66))|] **
 V293_create_internal_external table bnest breserved bg p R aop isr is cs) **
 V293_create_internal_domain) Afalse
 (V293_create_internal_pre_cells target argv inputtop p identity bottom size ext options **
 V293_create_internal_external table bnest breserved bg p Rbefore aop isr is cs **
 V293_create_internal_domain)
 (V293_CreateExt_body 92%Z 99%Z 97%Z running sched hook f) Afalse tid.
Proof.
 intros Spec sd li I tid f hook bnest table breserved slot bg bt base old p top bottom identity size ext options next
 bh bgrp br bn oldblock oldbase present oldprev g row n oldback R aop isr is cs good Rbefore gb
 target argv inputtop running sched BeforeFrame Frame Range StackValid HBefore Valid HR fp fq Hook TCB.
 eapply conseq_rule.
 - apply V293_create_internal_unpack.
 - intros s H;exact H.
 - apply ex_intro_rule. intro cpu. apply ex_intro_rule. intro err.
   apply ex_intro_rule. intro psp. apply ex_intro_rule. intro bp.
   apply ex_intro_rule. intro bc.
   eapply conseq_rule;[apply V293_create_internal_entry|intros s H;exact H| ].
   eapply r_conseq_rule with(r:=V293_create_failure_return table p
    (V293_create_failure_kept bg top bottom identity size ext options R
    (V293_create_stack_kept target argv inputtop
    (V293_create_prefix_kept bnest bc 99%Z 97%Z breserved V293_create_internal_domain))) aop isr is cs)
    (ri:=Afalse).
   + intro result. apply V293_create_internal_exit.
   + intros s H;exact H.
   + eapply V293_OSTaskCreateExt_empty_body_hoare with
     (good:=good)(gb:=gb)(slot:=slot)(bt:=bt)(base:=base)(old:=old)(next:=next)
     (bh:=bh)(bgrp:=bgrp)(br:=br)(bn:=bn)(oldblock:=oldblock)(oldbase:=oldbase)
     (present:=present)(oldprev:=oldprev)(g:=g)(row:=row)(n:=n)(oldback:=oldback).
     * exact BeforeFrame.
     * exact Frame.
     * apply V293_create_internal_domain_good.
     * exact Range.
     * exact StackValid.
     * exact HBefore.
     * exact Valid.
     * exact HR.
     * exact Hook.
     * exact TCB.
Qed.

(* Public interface: the actual standard function builders, all twelve cells,
   exact declaration domain, and the unchanged full snapshot callee contract.
   Restricted NULL free-list path only; this is not WFIFun or GOOD_OS. *)
Theorem V293_OSTaskCreateExt_empty_internal_contract : forall P creator Spec sd li I tid f hook
 bnest table breserved slot bg bt base old p top bottom identity size ext options next
 bh bgrp br bn oldblock oldbase present oldprev g row n oldback R aop isr is cs
 (good:GoodFunAsrt R) Rbefore (gb:GoodFunAsrt Rbefore) target argv inputtop running sched vl lg pre post,
 GoodFrm Rbefore -> GoodFrm R -> p<13 ->
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
 P creator=Some(V293_CreateExt_function 92%Z 99%Z 97%Z running sched hook f) ->
 Some pre=BuildPreI P creator vl lg
 (V293_create_empty_fpre table bnest breserved bg p target argv inputtop identity bottom size ext options
 Rbefore aop isr is cs gb) tid ->
 Some post=BuildRetI P creator vl lg
 (V293_create_empty_fpost table bnest breserved bg p R aop isr is cs good) tid ->
 InfRules Spec sd li I post Afalse pre
 (V293_CreateExt_body 92%Z 99%Z 97%Z running sched hook f) Afalse tid.
Proof.
 intros P creator Spec sd li I tid f hook bnest table breserved slot bg bt base old p top bottom identity size ext options next
 bh bgrp br bn oldblock oldbase present oldprev g row n oldback R aop isr is cs good Rbefore gb
 target argv inputtop running sched vl lg pre post BeforeFrame Frame Range StackValid HBefore Valid HR fp fq Hook TCB Code Pre Post.
 unfold BuildPreI in Pre. rewrite Code in Pre. cbn [V293_CreateExt_function]in Pre.
 destruct(dl_vl_match V293_CreateExt_parameters(rev vl))eqn:Typed;[ |discriminate].
 fold V293_create_internal_declarations in Pre.
 destruct(buildp V293_create_internal_declarations vl)as[cells | ]eqn:Cells;[ |discriminate].
 change(Some pre=Some(cells **
 ([|rev vl=V293_create_internal_values target argv inputtop p identity bottom size ext options|] **
 V293_create_internal_external table bnest breserved bg p Rbefore aop isr is cs) **
 V293_create_internal_domain))in Pre.
 inversion Pre;subst pre.
 unfold BuildRetI in Post. rewrite Code in Post.
 change(Some post=Some(fun result=>V293_create_internal_post_cells **
 ([|result=Some(Vint32(Int.repr 66))|] **
 V293_create_internal_external table bnest breserved bg p R aop isr is cs) **
 V293_create_internal_domain))in Post.
 inversion Post;subst post.
 eapply conseq_rule with(p:=(cells **
 V293_create_internal_external table bnest breserved bg p Rbefore aop isr is cs **
 V293_create_internal_domain) **
 [|rev vl=V293_create_internal_values target argv inputtop p identity bottom size ext options|]).
 - intros s H. clear -H. sep auto.
 - intros s H;exact H.
 - apply pure_split_rule. intro Args.
   assert(VL:vl=rev(V293_create_internal_values target argv inputtop p identity bottom size ext options)).
   { rewrite <-Args. symmetry. apply rev_involutive. }
   subst vl. rewrite V293_create_internal_buildp in Cells. inversion Cells;subst cells.
   eapply V293_OSTaskCreateExt_empty_internal_resources with
     (good:=good)(gb:=gb)(slot:=slot)(bt:=bt)(base:=base)(old:=old)(next:=next)
     (bh:=bh)(bgrp:=bgrp)(br:=br)(bn:=bn)(oldblock:=oldblock)(oldbase:=oldbase)
     (present:=present)(oldprev:=oldprev)(g:=g)(row:=row)(n:=n)(oldback:=oldback);eassumption.
Qed.
