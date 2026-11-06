(* Original complete TaskCreateExt body, legal task-context/free-priority entry,
   nonempty free-list and OSRunning=0. Three external Hooks remain. Not WFIFun. *)
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

Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateStackSuccess.
Require Import CertiOS.certiucos.v293.proofs.V293TCBFieldsHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TCBSuccessHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateExtPrefix.
Require Import CertiOS.certiucos.v293.code.V293OSTaskCreateExtFunction.


(* cells excludes the priority slot, which is owned solely by the prefix.
   globals carries global environment bindings and the residual R, which may
   own memory. The public theorem adds no callee-local cells to this frame. *)
Definition V293_create_success_body_frame cells globals oldpsp target argv inputtop options olderr
 bottom identity size ext running brun F :=
 V293_rdy_raw_cells cells globals ** LV 108%Z @ (Tptr Tint32) |->oldpsp **
 V293_create_stack_arguments target argv inputtop options
 (LV 209%Z @ Tint8 |->olderr ** LV 205%Z @ (Tptr Tint32) |->bottom **
  LV 206%Z @ Tint16 |->identity ** LV 207%Z @ Tint32 |->size **
  LV 208%Z @ (Tptr Tvoid) |->ext ** (V293_create_idle_running running brun ** F)).
Lemma V293_create_success_body_frame_good : forall cells globals oldpsp target argv inputtop options olderr
 bottom identity size ext running brun F,
 GoodFrm globals -> GoodFrm F ->
 GoodFrm(V293_create_success_body_frame cells globals oldpsp target argv inputtop options olderr
 bottom identity size ext running brun F).
Proof.
 intros. unfold V293_create_success_body_frame,V293_create_stack_arguments,
 V293_create_idle_running,V293_create_global_binding,Alvarmapsto,Alvarenv',Aptrmapsto.
 cbn [GoodFrm]. split;[apply V293_raw_cells_good_frame;exact H|tauto].
Qed.
Lemma V293_create_success_body_to_calls : forall bp bn bc table nesting reserved br p
 cells globals oldpsp target argv inputtop options olderr bottom identity size ext running brun F aop isr is cs,
 V293_create_prefix_state bp bn bc table nesting reserved br p(Vint32 Int.zero)(Vptr(br,Int.zero))
 (V293_create_success_body_frame cells globals oldpsp target argv inputtop options olderr
 bottom identity size ext running brun F) aop isr is cs ==>
 V293_hook_resource (((table,(4*Z.of_nat p)%Z),Tptr V293_tcb_type,Vptr(br,Int.zero))::cells)
 globals aop isr is cs ** LV 108%Z @ (Tptr Tint32) |->oldpsp **
 V293_create_stack_arguments target argv inputtop options
 (LV 209%Z @ Tint8 |->olderr ** LV 101%Z @ Tint8 |->V293_byteval p **
 LV 205%Z @ (Tptr Tint32) |->bottom ** LV 206%Z @ Tint16 |->identity **
 LV 207%Z @ Tint32 |->size ** LV 208%Z @ (Tptr Tvoid) |->ext **
 (V293_create_idle_running running brun **
 V293_create_prefix_kept bn bc nesting reserved br(V293_tcb_table_binding table ** F))).
Proof.
 intros bp bn bc table nesting reserved br p cells globals oldpsp target argv inputtop options olderr
 bottom identity size ext running brun F aop isr is cs s H.
 unfold V293_create_prefix_state,V293_create_prefix_cells,V293_create_prefix_bindings,
 V293_create_success_body_frame,V293_create_prefix_kept,V293_create_stack_arguments in *.
 cbn [V293_rdy_raw_cells]in H.
 assert(K:s |= (Alvarenv 101%Z Tint8(bp,0%Z) ** Amapsto(bp,0%Z)Tint8 true(V293_byteval p)) **
 ((OS[isr,false,is,cs] ** V293_rdy_raw_cells cells globals) **
 (<||aop||> ** Amapsto(table,(4*Z.of_nat p)%Z)(Tptr V293_tcb_type)true(Vptr(br,Int.zero)) **
 Amapsto(bn,0%Z)Tint8 true(V293_byteval 0) ** Amapsto(bc,0%Z)Tint32 true(Vint32 Int.zero) **
 Alvarenv 109%Z Tint32(bc,0%Z) ** V293_create_global_binding nesting Tint8 bn **
 V293_create_global_binding reserved Tint8 br ** V293_tcb_table_binding table **
 LV 108%Z @ (Tptr Tint32) |->oldpsp ** LV 201%Z @ Tint32 |->V293_task_selector target **
 LV 202%Z @ (Tptr Tvoid) |->argv ** LV 203%Z @ (Tptr Tint32) |->inputtop **
 LV 204%Z @ Tint16 |->options ** LV 209%Z @ Tint8 |->olderr **
 LV 205%Z @ (Tptr Tint32) |->bottom ** LV 206%Z @ Tint16 |->identity **
 LV 207%Z @ Tint32 |->size ** LV 208%Z @ (Tptr Tvoid) |->ext **
 V293_create_idle_running running brun ** F))).
 { clear -H. sep auto. }
 eapply astar_mono in K;[ |apply V293_create_raw_local|intros st HS;exact HS].
 eapply astar_mono in K;[ |intros st HS;exact HS| ].
 2:{ apply astar_mono;[apply V293_raw_cells_unmove_frame|intros st HS;exact HS]. }
 unfold V293_hook_resource. cbn [V293_rdy_raw_cells]. clear -K. sep auto.
Qed.

Theorem V293_OSTaskCreateExt_success_body_hoare : forall Spec sd li I tid f hook
 bp bnest bcpu table nesting reserved breserved cpuold bg bt base old p top bottom identity size ext options next
 bh bgrp br bn oldblock oldbase present oldprev g row n oldback R aop isr is cs
 (good:GoodFunAsrt R) F olderr oldpsp target argv inputtop running sched brun,
 GoodFrm R -> GoodFrm F -> p<13 -> V293_stack_argument_valid argv inputtop options ->
 V293_tcb_init_values_valid top bottom identity size ext options -> (R ==> CurLINV li tid) ->
 let cells:=V293_tcb_success_pre_owned table(Vptr(breserved,Int.zero))bg bt base old next
 bh bgrp br bn oldblock oldbase present p oldprev g row n oldback in
 let globals:=V293_tcb_success_global_bindings table bg bh bgrp br bn ** R in
 let before:=@mkfunasrt
 (V293_tcb_success_external table bg bh bgrp br bn cells R aop isr is cs)
 (V293_tcb_success_external_good table bg bh bgrp br bn cells R aop isr is cs good) in
 let fp:=V293_tcb_snapshot_fpre(Vptr(bt,Int.repr base))
 (V293_tcb_empty_fpre bg R aop isr is cs good)
 (V293_tcb_success_fpre table(Vptr(breserved,Int.zero))bg bt base old p top bottom identity size ext options next
 bh bgrp br bn oldblock oldbase present oldprev g row n oldback R aop isr is cs good) in
 let fq:=V293_tcb_snapshot_fpost(Vptr(bt,Int.repr base))
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
 (V293_create_stack_kept target argv inputtop
 (V293_create_prefix_kept bnest bcpu nesting reserved breserved(V293_tcb_table_binding table ** F))))) Afalse
 (V293_create_prefix_state bp bnest bcpu table nesting reserved breserved p cpuold Vnull
 (V293_create_success_body_frame(tl cells)globals oldpsp target argv inputtop options olderr
 bottom identity size ext running brun F) aop isr is cs)
 (V293_CreateExt_body 92%Z nesting reserved running sched hook f) Afalse tid.
Proof.
 intros Spec sd li I tid f hook bp bnest bcpu table nesting reserved breserved cpuold bg bt base old p top bottom identity size ext options next
 bh bgrp br bn oldblock oldbase present oldprev g row n oldback R aop isr is cs good
 F olderr oldpsp target argv inputtop running sched brun RFrame Frame Range StackValid Valid HR cells globals before fp fq Hook TCB.
 unfold V293_CreateExt_body,V293_TaskCreateExt_body.
 apply V293_OSTaskCreateExt_prefix_hoare.
 - exact Range.
 - apply V293_create_success_body_frame_good;[ |exact Frame].
   unfold globals. cbn [V293_tcb_success_global_bindings GoodFrm]. tauto.
 - unfold V293_create_success_body_frame. apply V293_star_CurLINV_l.
   apply V293_raw_cells_CurLINV. unfold globals. apply V293_star_CurLINV_r. exact HR.
 - eapply conseq_rule with(p:=getasrt before ** LV 108%Z @ (Tptr Tint32) |->oldpsp **
     V293_create_stack_arguments target argv inputtop options
     (LV 209%Z @ Tint8 |->olderr ** LV 101%Z @ Tint8 |->V293_byteval p **
     LV 205%Z @ (Tptr Tint32) |->bottom ** LV 206%Z @ Tint16 |->identity **
     LV 207%Z @ Tint32 |->size ** LV 208%Z @ (Tptr Tvoid) |->ext **
     (V293_create_idle_running running brun **
      V293_create_prefix_kept bnest bcpu nesting reserved breserved(V293_tcb_table_binding table ** F))))(q:=Afalse).
   + unfold before,V293_tcb_success_external. cbn [getasrt]. unfold cells. cbn [V293_tcb_success_pre_owned tl].
     apply V293_create_success_body_to_calls.
   + intros s H;exact H.
   + eapply V293_OSTaskCreateExt_stack_success_hoare with(good:=good)(before:=before).
     * apply V293_create_prefix_kept_good. cbn [V293_tcb_table_binding GoodFrm]. tauto.
     * exact StackValid.
     * unfold before. cbn [getasrt]. unfold V293_tcb_success_external.
       apply V293_hook_resource_linv. apply V293_star_CurLINV_r. exact HR.
     * lia.
     * exact Valid.
     * exact HR.
     * exact Hook.
     * exact TCB.
Qed.
