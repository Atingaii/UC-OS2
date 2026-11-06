(* Standard successful TaskCreateExt builders; original full body, 12 cells,
   exact declaration domain. Restricted IE=false and OSRunning=0, not WFIFun. *)
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


Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateBodySuccess.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateEmptyInternal.
Require Import CertiOS.tactics.hoareforward.init_spec.
Require Import CertiOS.certiucos.v293.proofs.V293InitAllRecords.

Definition V293_create_success_external table bg bh bgrp br bn bnest breserved brun cells R aop isr is cs :=
 Agvarenv 99%Z Tint8(bnest,0%Z) ** Agvarenv 97%Z Tint8(breserved,0%Z) **
 Agvarenv 98%Z Tint8(brun,0%Z) ** Amapsto(bnest,0%Z)Tint8 true(V293_byteval 0) **
 Amapsto(brun,0%Z)Tint8 false(Vint32 Int.zero) **
 V293_tcb_success_external table bg bh bgrp br bn cells R aop isr is cs.
Lemma V293_create_success_external_good : forall table bg bh bgrp br bn bnest breserved brun cells R aop isr is cs,
 GoodFunAsrt R -> GoodFunAsrt(V293_create_success_external table bg bh bgrp br bn bnest breserved brun cells R aop isr is cs).
Proof.
 intros. pose proof(V293_tcb_success_external_good table bg bh bgrp br bn cells R aop isr is cs H)as G.
 cbn[V293_create_success_external GoodFunAsrt]. tauto.
Qed.
Definition V293_create_success_saved bnest breserved brun :=
 Agvarenv 99%Z Tint8(bnest,0%Z) ** Agvarenv 97%Z Tint8(breserved,0%Z) **
 Agvarenv 98%Z Tint8(brun,0%Z) ** Amapsto(bnest,0%Z)Tint8 true(V293_byteval 0) **
 Amapsto(brun,0%Z)Tint8 false(Vint32 Int.zero).
Lemma V293_create_success_saved_good : forall bnest breserved brun,
 GoodFunAsrt(V293_create_success_saved bnest breserved brun).
Proof. intros. cbn [V293_create_success_saved GoodFunAsrt]. tauto. Qed.
Definition V293_create_success_fpre table bg bh bgrp br bn bnest breserved brun cells
 p target argv inputtop identity bottom size ext options R aop isr is cs(good:GoodFunAsrt R) : fpre :=
 fun vl lg tid=>@mkfunasrt
 ([|vl=V293_create_internal_values target argv inputtop p identity bottom size ext options|] **
 V293_create_success_external table bg bh bgrp br bn bnest breserved brun cells R aop isr is cs)
 (conj I(V293_create_success_external_good table bg bh bgrp br bn bnest breserved brun cells R aop isr is cs good)).
(* The caller's function post retains the ENTIRE exact snapshot callee post.
   No caller-local identifier or declaration-domain predicate enters fpost. *)
Definition V293_create_success_fpost bnest breserved brun (fq:fpost) arguments head : fpost :=
 fun vl result lg tid=>@mkfunasrt
 ([|result=Some(Vint32 Int.zero)|] **
 getasrt(fq arguments(Some(Vint32 Int.zero))[logic_val head]tid) **
 V293_create_success_saved bnest breserved brun)
 (conj I(conj(getprop(fq arguments(Some(Vint32 Int.zero))[logic_val head]tid))
 (V293_create_success_saved_good bnest breserved brun))).

Lemma V293_create_success_no_shadow : forall le x,
 eq_dom_env le(getlenvdom V293_create_internal_declarations) ->
 (91<=x<=99)%Z -> get le x=None.
Proof.
 intros le x Domain Range. destruct(get le x)as [[b tp] | ] eqn:E;[ |reflexivity].
 exfalso. pose proof(proj2(Domain x tp)(ex_intro _ b E))as Bad.
 cbn[V293_create_internal_declarations V293_CreateExt_parameters V293_CreateExt_locals
 revlcons getlenvdom]in Bad.
 repeat destruct Bad as [Bad | Bad];try contradiction;inversion Bad;lia.
Qed.
Lemma V293_create_success_global_view : forall x tp b,
 (91<=x<=99)%Z ->
 Agvarenv x tp(b,0%Z) ** V293_create_internal_domain ==>
 V293_create_global_binding x tp b ** V293_create_internal_domain.
Proof.
 intros x tp b Range s H. unfold V293_create_internal_domain in *.
 apply astar_comm in H. apply astar_l_adomlenv_elim in H. destruct H as[Domain H].
 apply astar_comm. apply astar_l_adomlenv_intro;[ |exact Domain].
 unfold V293_create_global_binding. split;[exact H| ].
 apply anotinlenv_intro;[destruct_s s;simpl in *;join auto| ]. intros[v E].
 pose proof(V293_create_success_no_shadow _ x Domain Range)as No.
 change(EnvMod.get(getlenv s)x=None)in No. rewrite No in E. discriminate.
Qed.
Lemma V293_create_success_entry : forall target argv inputtop p identity bottom size ext options
 cpu err psp bp bc table bg bh bgrp br bn bnest breserved brun cells R aop isr is cs,
 (Alvarenv 101%Z Tint8(bp,0%Z) ** Amapsto(bp,0%Z)Tint8 true(V293_byteval p)) **
 ((Alvarenv 109%Z Tint32(bc,0%Z) ** Amapsto(bc,0%Z)Tint32 true cpu) **
 (LV 209%Z @ Tint8 |->err ** LV 108%Z @ (Tptr Tint32) |->psp **
 (V293_create_internal_other_parameters target argv inputtop identity bottom size ext options **
 (V293_create_success_external table bg bh bgrp br bn bnest breserved brun
 (((table,(4*Z.of_nat p)%Z),Tptr V293_tcb_type,Vnull)::cells)R aop isr is cs **
 V293_create_internal_domain)))) ==>
 V293_create_prefix_state bp bnest bc table 99%Z 97%Z breserved p cpu Vnull
 (V293_create_success_body_frame cells(V293_tcb_success_global_bindings table bg bh bgrp br bn ** R)
 psp target argv inputtop options err bottom identity size ext 98%Z brun V293_create_internal_domain) aop isr is cs.
Proof.
 intros target argv inputtop p identity bottom size ext options cpu err psp bp bc table bg bh bgrp br bn
 bnest breserved brun cells R aop isr is cs s H.
 unfold V293_create_success_external,V293_tcb_success_external,V293_hook_resource in H.
 cbn[V293_rdy_raw_cells]in H.
 assert(K:s |= (Agvarenv 99%Z Tint8(bnest,0%Z) ** V293_create_internal_domain) **
 (Agvarenv 97%Z Tint8(breserved,0%Z) ** Agvarenv 98%Z Tint8(brun,0%Z) **
 Alvarenv 101%Z Tint8(bp,0%Z) ** Alvarenv 109%Z Tint32(bc,0%Z) **
 Amapsto(bp,0%Z)Tint8 true(V293_byteval p) ** Amapsto(bc,0%Z)Tint32 true cpu **
 Amapsto(bnest,0%Z)Tint8 true(V293_byteval 0) **
 Amapsto(brun,0%Z)Tint8 false(Vint32 Int.zero) **
 Amapsto(table,(4*Z.of_nat p)%Z)(Tptr V293_tcb_type)true Vnull **
 LV 209%Z @ Tint8 |->err ** LV 108%Z @ (Tptr Tint32) |->psp **
 V293_create_internal_other_parameters target argv inputtop identity bottom size ext options **
 <||aop||> ** V293_rdy_raw_cells cells(OS[isr,false,is,cs] **
 (V293_tcb_success_global_bindings table bg bh bgrp br bn ** R)))).
 { clear -H. sep auto. }
 eapply astar_mono in K;[ |apply V293_create_success_global_view;lia|intros st HS;exact HS].
 assert(K2:s |= (Agvarenv 97%Z Tint8(breserved,0%Z) ** V293_create_internal_domain) **
 (Agvarenv 98%Z Tint8(brun,0%Z) ** V293_create_global_binding 99%Z Tint8 bnest **
 Alvarenv 101%Z Tint8(bp,0%Z) ** Alvarenv 109%Z Tint32(bc,0%Z) **
 Amapsto(bp,0%Z)Tint8 true(V293_byteval p) ** Amapsto(bc,0%Z)Tint32 true cpu **
 Amapsto(bnest,0%Z)Tint8 true(V293_byteval 0) **
 Amapsto(brun,0%Z)Tint8 false(Vint32 Int.zero) **
 Amapsto(table,(4*Z.of_nat p)%Z)(Tptr V293_tcb_type)true Vnull **
 LV 209%Z @ Tint8 |->err ** LV 108%Z @ (Tptr Tint32) |->psp **
 V293_create_internal_other_parameters target argv inputtop identity bottom size ext options **
 <||aop||> ** V293_rdy_raw_cells cells(OS[isr,false,is,cs] **
 (V293_tcb_success_global_bindings table bg bh bgrp br bn ** R)))).
 { clear -K. sep auto. }
 eapply astar_mono in K2;[ |apply V293_create_success_global_view;lia|intros st HS;exact HS].
 assert(K3:s |= (Agvarenv 98%Z Tint8(brun,0%Z) ** V293_create_internal_domain) **
 ((V293_create_global_binding 99%Z Tint8 bnest ** V293_create_global_binding 97%Z Tint8 breserved) **
 Alvarenv 101%Z Tint8(bp,0%Z) ** Alvarenv 109%Z Tint32(bc,0%Z) **
 Amapsto(bp,0%Z)Tint8 true(V293_byteval p) ** Amapsto(bc,0%Z)Tint32 true cpu **
 Amapsto(bnest,0%Z)Tint8 true(V293_byteval 0) **
 Amapsto(brun,0%Z)Tint8 false(Vint32 Int.zero) **
 Amapsto(table,(4*Z.of_nat p)%Z)(Tptr V293_tcb_type)true Vnull **
 LV 209%Z @ Tint8 |->err ** LV 108%Z @ (Tptr Tint32) |->psp **
 V293_create_internal_other_parameters target argv inputtop identity bottom size ext options **
 <||aop||> ** V293_rdy_raw_cells cells(OS[isr,false,is,cs] **
 (V293_tcb_success_global_bindings table bg bh bgrp br bn ** R)))).
 { clear -K2. sep auto. }
 eapply astar_mono in K3;[ |apply V293_create_success_global_view;lia|intros st HS;exact HS].

 assert(Raw:s |= V293_rdy_raw_cells cells(OS[isr,false,is,cs] **
 (V293_tcb_success_global_bindings table bg bh bgrp br bn ** R)) ** Atrue).
 { clear -K3. sep auto. }
 assert(Tg:get(getgenv s)92%Z=Some(table,Tarray(Tptr V293_tcb_type)13)).
 { refine(V293_star_env_l _ _ (fun ge le=>get ge 92%Z=Some(table,Tarray(Tptr V293_tcb_type)13)) _ s Raw).
   apply V293_raw_cells_frame_env with(E:=fun ge le=>get ge 92%Z=Some(table,Tarray(Tptr V293_tcb_type)13)). apply V293_star_env_r with(E:=fun ge le=>get ge 92%Z=Some(table,Tarray(Tptr V293_tcb_type)13)).
   apply V293_star_env_l with(E:=fun ge le=>get ge 92%Z=Some(table,Tarray(Tptr V293_tcb_type)13)). unfold V293_tcb_success_global_bindings.
   apply V293_star_env_r with(E:=fun ge le=>get ge 92%Z=Some(table,Tarray(Tptr V293_tcb_type)13)). apply V293_star_env_l with(E:=fun ge le=>get ge 92%Z=Some(table,Tarray(Tptr V293_tcb_type)13)).
   intros st[actual[E[B _]]]. inversion B;subst actual. exact E. }
 pose proof(@astar_l_agvarenv_intro s 92%Z(Tarray(Tptr V293_tcb_type)13)(table,0%Z)
 _ K3(conj eq_refl Tg))as K4.

 assert(K5:s |= (Agvarenv 92%Z(Tarray(Tptr V293_tcb_type)13)(table,0%Z) **
 V293_create_internal_domain) **
 (V293_rdy_raw_cells cells(OS[isr,false,is,cs] **
 (V293_tcb_success_global_bindings table bg bh bgrp br bn ** R)) ** V293_create_global_binding 98%Z Tint8 brun **
 (V293_create_global_binding 99%Z Tint8 bnest ** V293_create_global_binding 97%Z Tint8 breserved) **
 Alvarenv 101%Z Tint8(bp,0%Z) ** Alvarenv 109%Z Tint32(bc,0%Z) **
 Amapsto(bp,0%Z)Tint8 true(V293_byteval p) ** Amapsto(bc,0%Z)Tint32 true cpu **
 Amapsto(bnest,0%Z)Tint8 true(V293_byteval 0) **
 Amapsto(brun,0%Z)Tint8 false(Vint32 Int.zero) **
 Amapsto(table,(4*Z.of_nat p)%Z)(Tptr V293_tcb_type)true Vnull **
 LV 209%Z @ Tint8 |->err ** LV 108%Z @ (Tptr Tint32) |->psp **
 V293_create_internal_other_parameters target argv inputtop identity bottom size ext options ** <||aop||>)).
 { clear -K4. sep auto. }
 eapply astar_mono in K5.
 2:{ apply V293_create_success_global_view;lia. }
 2:{ intros st HS;exact HS. }
 unfold V293_create_global_binding at 1 in K5. fold V293_tcb_table_binding in K5.
 assert(K6:s |= V293_rdy_raw_cells cells(OS[isr,false,is,cs] **
 (V293_tcb_success_global_bindings table bg bh bgrp br bn ** R)) **
 (V293_tcb_table_binding table ** V293_create_internal_domain **
 V293_create_global_binding 98%Z Tint8 brun **
 (V293_create_global_binding 99%Z Tint8 bnest ** V293_create_global_binding 97%Z Tint8 breserved) **
 Alvarenv 101%Z Tint8(bp,0%Z) ** Alvarenv 109%Z Tint32(bc,0%Z) **
 Amapsto(bp,0%Z)Tint8 true(V293_byteval p) ** Amapsto(bc,0%Z)Tint32 true cpu **
 Amapsto(bnest,0%Z)Tint8 true(V293_byteval 0) **
 Amapsto(brun,0%Z)Tint8 false(Vint32 Int.zero) **
 Amapsto(table,(4*Z.of_nat p)%Z)(Tptr V293_tcb_type)true Vnull **
 LV 209%Z @ Tint8 |->err ** LV 108%Z @ (Tptr Tint32) |->psp **
 V293_create_internal_other_parameters target argv inputtop identity bottom size ext options ** <||aop||>)).
 { clear -K5. sep auto. }
 eapply astar_mono in K6;[ |apply V293_raw_cells_move_frame|intros st HS;exact HS].
 unfold V293_create_prefix_state,V293_create_prefix_cells,V293_create_prefix_bindings,
 V293_create_success_body_frame,V293_create_stack_arguments,V293_create_idle_running.
 cbn[V293_rdy_raw_cells]. unfold V293_create_internal_other_parameters in K6 |- *.
 clear -K6. sep auto.

Qed.

Lemma V293_create_success_kept_return : forall bnest bc breserved table,
 V293_create_prefix_kept bnest bc 99%Z 97%Z breserved
 (V293_tcb_table_binding table ** V293_create_internal_domain) ==>
 LV 109%Z @ Tint32 |->Vint32 Int.zero **
 (Amapsto(bnest,0%Z)Tint8 true(V293_byteval 0) **
 Agvarenv 99%Z Tint8(bnest,0%Z) ** Agvarenv 97%Z Tint8(breserved,0%Z) **
 V293_create_internal_domain).
Proof.
 intros bnest bc breserved table s H.
 unfold V293_create_prefix_kept in H. cbn[V293_rdy_raw_cells]in H.
 assert(K:s |= (V293_create_global_binding 99%Z Tint8 bnest **
 V293_create_global_binding 97%Z Tint8 breserved ** V293_tcb_table_binding table) **
 ((Alvarenv 109%Z Tint32(bc,0%Z) ** Amapsto(bc,0%Z)Tint32 true(Vint32 Int.zero)) **
 (Amapsto(bnest,0%Z)Tint8 true(V293_byteval 0) ** V293_create_internal_domain))).
 { clear -H. sep auto. }
 assert(EmptyGlobals:forall st,
 st |= V293_create_global_binding 99%Z Tint8 bnest **
 V293_create_global_binding 97%Z Tint8 breserved ** V293_tcb_table_binding table ->
 st |= Agvarenv 99%Z Tint8(bnest,0%Z) ** Agvarenv 97%Z Tint8(breserved,0%Z)).
 { intros st HS. clear -HS.
   eapply astar_mono with(P':=Agvarenv 99%Z Tint8(bnest,0%Z))
   (Q':=Agvarenv 97%Z Tint8(breserved,0%Z) ** Aemp) in HS.
   2:{ intros st0[G N];exact G. }
   2:{ apply astar_mono.
       - intros st0[G N];exact G.
       - intros st0[G N]. clear -G. destruct_s st0. simpl in *. join auto. }
   clear -HS. sep auto. }

 eapply astar_mono in K;[ |exact EmptyGlobals| ].
 2:{ apply astar_mono;[apply V293_create_raw_local|intros st HS;exact HS]. }
 clear -K. sep auto.
Qed.
Lemma V293_create_success_exit : forall target argv inputtop p top identity bottom size ext options
 bnest bc table breserved brun callee result,
 V293_create_success_return 98%Z brun
 (callee ** V293_create_tcb_arguments p top bottom identity size ext options
 (V293_create_stack_kept target argv inputtop
 (V293_create_prefix_kept bnest bc 99%Z 97%Z breserved
 (V293_tcb_table_binding table ** V293_create_internal_domain))))result ==>
 V293_create_internal_post_cells **
 ([|result=Some(Vint32 Int.zero)|] ** callee **
 V293_create_success_saved bnest breserved brun) ** V293_create_internal_domain.
Proof.
 intros target argv inputtop p top identity bottom size ext options bnest bc table breserved brun callee result s H.
 unfold V293_create_success_return in H. apply astar_l_apure_elim in H. destruct H as[Code H].
 unfold V293_create_success_state,V293_create_idle_running,V293_create_tcb_arguments,
 V293_create_stack_kept in H.
 assert(K:s |= (V293_create_prefix_kept bnest bc 99%Z 97%Z breserved
 (V293_tcb_table_binding table ** V293_create_internal_domain)) **
 (V293_create_global_binding 98%Z Tint8 brun ** Amapsto(brun,0%Z)Tint8 false(Vint32 Int.zero) **
 callee ** LV 209%Z @ Tint8 |->Vint32 Int.zero **
 LV 101%Z @ Tint8 |->V293_byteval p ** LV 108%Z @ (Tptr Tint32) |->top **
 LV 205%Z @ (Tptr Tint32) |->bottom ** LV 206%Z @ Tint16 |->identity **
 LV 207%Z @ Tint32 |->size ** LV 208%Z @ (Tptr Tvoid) |->ext ** LV 204%Z @ Tint16 |->options **
 LV 201%Z @ Tint32 |->V293_task_selector target ** LV 202%Z @ (Tptr Tvoid) |->argv **
 LV 203%Z @ (Tptr Tint32) |->inputtop)).
 { clear -H. sep auto. }
 eapply astar_mono in K;[ |apply V293_create_success_kept_return|intros st HS;exact HS].
 assert(K2:s |= V293_create_global_binding 98%Z Tint8 brun **
 (LV 109%Z @ Tint32 |->Vint32 Int.zero **
 Amapsto(bnest,0%Z)Tint8 true(V293_byteval 0) **
 Agvarenv 99%Z Tint8(bnest,0%Z) ** Agvarenv 97%Z Tint8(breserved,0%Z) **
 V293_create_internal_domain ** Amapsto(brun,0%Z)Tint8 false(Vint32 Int.zero) **
 callee ** LV 209%Z @ Tint8 |->Vint32 Int.zero **
 LV 101%Z @ Tint8 |->V293_byteval p ** LV 108%Z @ (Tptr Tint32) |->top **
 LV 205%Z @ (Tptr Tint32) |->bottom ** LV 206%Z @ Tint16 |->identity **
 LV 207%Z @ Tint32 |->size ** LV 208%Z @ (Tptr Tvoid) |->ext ** LV 204%Z @ Tint16 |->options **
 LV 201%Z @ Tint32 |->V293_task_selector target ** LV 202%Z @ (Tptr Tvoid) |->argv **
 LV 203%Z @ (Tptr Tint32) |->inputtop)).
 { clear -K. sep auto. }
 eapply astar_mono in K2;[ |intros st[G N];exact G|intros st HS;exact HS].
 assert(Ret:s |= V293_create_internal_pre_cells target argv inputtop p identity bottom size ext options **
 (callee ** V293_create_success_saved bnest breserved brun ** V293_create_internal_domain)).
 { unfold V293_create_internal_pre_cells,V293_create_internal_locals,V293_create_success_saved.
   clear -K2. sep auto. }
 eapply astar_mono in Ret;[ |apply V293_create_internal_pre_to_post|intros st HS;exact HS].
 clear -Ret Code. sep auto.
Qed.

Theorem V293_OSTaskCreateExt_success_internal_resources : forall Spec sd li I tid f hook
 bnest table breserved bg bt base old p top bottom identity size ext options next
 bh bgrp br bn oldblock oldbase present oldprev g row n oldback R aop isr is cs
 (good:GoodFunAsrt R) target argv inputtop sched brun,
 GoodFrm R -> p<13 -> V293_stack_argument_valid argv inputtop options ->
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

 InfRules Spec sd li I (fun result=>V293_create_internal_post_cells **
 getasrt(V293_create_success_fpost bnest breserved brun fq
 (V293_tcb_success_arguments p top bottom identity size ext options)(Vptr(bt,Int.repr base))
 (V293_create_internal_values target argv inputtop p identity bottom size ext options)result[]tid) **
 V293_create_internal_domain) Afalse (V293_create_internal_pre_cells target argv inputtop p identity bottom size ext options **
 V293_create_success_external table bg bh bgrp br bn bnest breserved brun
 (V293_tcb_success_pre_owned table Vnull bg bt base old next bh bgrp br bn oldblock oldbase
 present p oldprev g row n oldback)R aop isr is cs ** V293_create_internal_domain)
 (V293_CreateExt_body 92%Z 99%Z 97%Z 98%Z sched hook f) Afalse tid.
Proof.
 intros Spec sd li I tid f hook bnest table breserved bg bt base old p top bottom identity size ext options next
 bh bgrp br bn oldblock oldbase present oldprev g row n oldback R aop isr is cs good
 target argv inputtop sched brun Frame Range StackValid Valid HR cells globals before fp fq Hook TCB.
 eapply conseq_rule.
 - apply V293_create_internal_unpack.
 - intros s H;exact H.
 - apply ex_intro_rule. intro cpu. apply ex_intro_rule. intro err.
   apply ex_intro_rule. intro psp. apply ex_intro_rule. intro bp. apply ex_intro_rule. intro bc.
   eapply conseq_rule;[apply V293_create_success_entry|intros s H;exact H| ].
   eapply r_conseq_rule with(r:=V293_create_success_return 98%Z brun
   (getasrt(fq(V293_tcb_success_arguments p top bottom identity size ext options)
   (Some(Vint32 Int.zero))[logic_val(Vptr(bt,Int.repr base))]tid) **
   V293_create_tcb_arguments p top bottom identity size ext options
   (V293_create_stack_kept target argv inputtop
   (V293_create_prefix_kept bnest bc 99%Z 97%Z breserved
   (V293_tcb_table_binding table ** V293_create_internal_domain)))))(ri:=Afalse).
   + intro result. cbn[V293_create_success_fpost getasrt]. apply V293_create_success_exit.
   + intros s H;exact H.
   + eapply V293_OSTaskCreateExt_success_body_hoare with(good:=good)
     (bt:=bt)(base:=base)(old:=old)(next:=next)(bh:=bh)(bgrp:=bgrp)(br:=br)(bn:=bn)
     (oldblock:=oldblock)(oldbase:=oldbase)(present:=present)(oldprev:=oldprev)
     (g:=g)(row:=row)(n:=n)(oldback:=oldback).
     * exact Frame.
     * apply V293_create_internal_domain_good.
     * exact Range.
     * exact StackValid.
     * exact Valid.
     * exact HR.
     * exact Hook.
     * exact TCB.
Qed.

Theorem V293_OSTaskCreateExt_success_internal_contract : forall P creator Spec sd li I tid f hook
 bnest table breserved bg bt base old p top bottom identity size ext options next
 bh bgrp br bn oldblock oldbase present oldprev g row n oldback R aop isr is cs
 (good:GoodFunAsrt R) target argv inputtop sched brun vl lg pre post,
 GoodFrm R -> p<13 -> V293_stack_argument_valid argv inputtop options ->
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

 P creator=Some(V293_CreateExt_function 92%Z 99%Z 97%Z 98%Z sched hook f) ->
 Some pre=BuildPreI P creator vl lg (V293_create_success_fpre table bg bh bgrp br bn bnest breserved brun
 (V293_tcb_success_pre_owned table Vnull bg bt base old next bh bgrp br bn oldblock oldbase
 present p oldprev g row n oldback)p target argv inputtop identity bottom size ext options R aop isr is cs good) tid ->
 Some post=BuildRetI P creator vl lg (V293_create_success_fpost bnest breserved brun fq
 (V293_tcb_success_arguments p top bottom identity size ext options)(Vptr(bt,Int.repr base))) tid ->
 InfRules Spec sd li I post Afalse pre
 (V293_CreateExt_body 92%Z 99%Z 97%Z 98%Z sched hook f) Afalse tid.
Proof.
 intros P creator Spec sd li I tid f hook bnest table breserved bg bt base old p top bottom identity size ext options next
 bh bgrp br bn oldblock oldbase present oldprev g row n oldback R aop isr is cs good
 target argv inputtop sched brun vl lg pre post Frame Range StackValid Valid HR cells globals before fp fq Hook TCB Code Pre Post.
 unfold BuildPreI in Pre. rewrite Code in Pre. cbn[V293_CreateExt_function]in Pre.
 destruct(dl_vl_match V293_CreateExt_parameters(rev vl))eqn:Typed;[ |discriminate].
 fold V293_create_internal_declarations in Pre.
 destruct(buildp V293_create_internal_declarations vl)as[owned | ]eqn:Owned;[ |discriminate].
 change(Some pre=Some(owned **
 ([|rev vl=V293_create_internal_values target argv inputtop p identity bottom size ext options|] **
 V293_create_success_external table bg bh bgrp br bn bnest breserved brun
 (V293_tcb_success_pre_owned table Vnull bg bt base old next bh bgrp br bn oldblock oldbase
 present p oldprev g row n oldback)R aop isr is cs) ** V293_create_internal_domain))in Pre.
 inversion Pre;subst pre.
 unfold BuildRetI in Post. rewrite Code in Post.
 change(Some post=Some(fun result=>V293_create_internal_post_cells **
 getasrt(V293_create_success_fpost bnest breserved brun fq
 (V293_tcb_success_arguments p top bottom identity size ext options)(Vptr(bt,Int.repr base))
 (V293_create_internal_values target argv inputtop p identity bottom size ext options)result[]tid) **
 V293_create_internal_domain))in Post. inversion Post;subst post.
 eapply conseq_rule with(p:=(owned **
 V293_create_success_external table bg bh bgrp br bn bnest breserved brun
 (V293_tcb_success_pre_owned table Vnull bg bt base old next bh bgrp br bn oldblock oldbase
 present p oldprev g row n oldback)R aop isr is cs ** V293_create_internal_domain) **
 [|rev vl=V293_create_internal_values target argv inputtop p identity bottom size ext options|]).
 - intros s H. clear -H. sep auto.
 - intros s H;exact H.
 - apply pure_split_rule. intro Args.
   assert(VL:vl=rev(V293_create_internal_values target argv inputtop p identity bottom size ext options)).
   { rewrite <-Args. symmetry. apply rev_involutive. }
   subst vl. rewrite V293_create_internal_buildp in Owned. inversion Owned;subst owned.
   eapply V293_OSTaskCreateExt_success_internal_resources with(good:=good)
    (bt:=bt)(base:=base)(old:=old)(next:=next)(bh:=bh)(bgrp:=bgrp)(br:=br)(bn:=bn)
    (oldblock:=oldblock)(oldbase:=oldbase)(present:=present)(oldprev:=oldprev)
    (g:=g)(row:=row)(n:=n)(oldback:=oldback);eassumption.
Qed.
