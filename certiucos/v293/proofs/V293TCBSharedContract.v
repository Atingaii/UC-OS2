Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
(* Standard function builders for the shared allocator body. Local declaration
   facts stay outside both CPU Hook contracts. Freshness and Hook bodies remain
   explicit obligations; this is not a whole-program correctness theorem. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.code.V293OSTCBInitFunction.
Require Import CertiOS.certiucos.v293.proofs.V293TCBHookFrame.
Require Import CertiOS.certiucos.v293.proofs.V293TCBSuccessInternal.
Require Import CertiOS.certiucos.v293.proofs.V293TCBHookCall.
Require Import CertiOS.certiucos.v293.proofs.V293TCBSuccessHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TCBEmptyEnabled.
Require Import CertiOS.certiucos.v293.proofs.V293TCBEmptyInternal.
Require Import CertiOS.certiucos.v293.proofs.V293TCBEmptyHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TCBFieldsHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitFields.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293TCBAllocatedFields.
Require Import CertiOS.certiucos.v293.proofs.V293TCBEnabledPublication.
Require Import CertiOS.certiucos.v293.proofs.V293TCBEnabledHook.
Require Import CertiOS.certiucos.v293.proofs.V293TCBPriorityHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TCBPublishHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateReservationOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateJointShared.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293NullBytes.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293InitTCBClear.
Require Import CertiOS.certiucos.v293.proofs.V293InitAllRecords.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.hoareforward.init_spec.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateTCBCall.
Require Import CertiOS.certiucos.v293.code.V293OSTaskCreateExtCalls.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Definition V293_tcb_shared_external table bf bh bg br bn Q aop ir si ci :=
 V293_tcb_success_global_bindings table bf bh bg br bn **
 (<||aop||> ** OS[ir,true,si,ci] ** Q).
Lemma V293_tcb_shared_external_good : forall table bf bh bg br bn Q aop ir si ci,
 GoodFunAsrt Q -> GoodFunAsrt(V293_tcb_shared_external table bf bh bg br bn Q aop ir si ci).
Proof. intros;cbn[V293_tcb_shared_external V293_tcb_success_global_bindings GoodFunAsrt];tauto. Qed.
Definition V293_tcb_shared_fpre table reserved bf bh bg br bn p top bottom identity size ext options R aop ir si ci
 (good:GoodFunAsrt R) : fpre := fun vl lg tid => @mkfunasrt
 ([|vl=V293_tcb_success_arguments p top bottom identity size ext options|] **
 V293_tcb_shared_external table bf bh bg br bn(V293_create_owned_share table reserved p ** R)aop ir si ci)
 (conj I(V293_tcb_shared_external_good table bf bh bg br bn _ aop ir si ci
 (V293_tcb_hook_owner_accepted table reserved p R good))).
Definition V293_tcb_shared_fpost table reserved bf bh bg br bn p R aop ir si ci
 (good:GoodFunAsrt R) : fpost := fun vl result lg tid => @mkfunasrt
 (([|result=Some(Vint32(Int.repr 66))|] **
 V293_tcb_shared_external table bf bh bg br bn(V293_create_owned_share table reserved p ** R)aop ir si ci) \\//
 ([|result=Some(Vint32 Int.zero)|] ** V293_tcb_shared_external table bf bh bg br bn R aop ir si ci))
 (conj (conj I(V293_tcb_shared_external_good table bf bh bg br bn _ aop ir si ci
 (V293_tcb_hook_owner_accepted table reserved p R good)))
 (conj I(V293_tcb_shared_external_good table bf bh bg br bn R aop ir si ci good))).

Lemma V293_tcb_shared_bindings_open : forall table bf bu bc bp bs bb bi bz be bo bh bg br bn,
 V293_hook_bindings table bf bu bc bp bs bb bi bz be bo bh bg br bn ==>
 V293_tcb_empty_bindings bf bc bu **
 (V293_tcb_fields_bindings 108%Z 101%Z 102%Z 103%Z 104%Z 105%Z 106%Z 107%Z bc bp bs bb bi bz be bo **
 (V293_tcb_table_binding table ** V293_tcb_publication_globals bh bg br bn)).
Proof.
 intros table bf bu bc bp bs bb bi bz be bo bh bg br bn s H.
 unfold V293_hook_bindings,V293_tcb_success_bindings,V293_tcb_success_extra,
 V293_tcb_fields_bindings,V293_tcb_table_binding,V293_pub_bindings in H.
 unfold V293_tcb_empty_bindings,V293_tcb_fields_bindings,V293_tcb_table_binding,V293_tcb_publication_globals.
 destruct s as [[[[[[ge le] M] ir] aux] O] op].
 repeat match goal with HX:_ |= _ ** _ |- _ =>
   apply sat_split in HX;destruct HX as(?&?&?&?&?&?&?&?) end.
 repeat match goal with HX:_ |= _ //\\ _ |- _ => destruct HX as[? ?] end.
 repeat match goal with
 | HX:_ |= Alvarenv _ _ _ |- _ => apply alvarenv_elim in HX;destruct HX as[? ?]
 | HX:_ |= Agvarenv _ _ _ |- _ => apply agvarenv_elim in HX;destruct HX as[? ?]
 | HX:_ |= A_notin_lenv _ |- _ => apply anotinlenv_elim in HX;destruct HX as[? ?] end.
 assert(E:(ge,le,M,ir,aux,O,op) |= Aemp)by(simpl in *;join auto).
 repeat (apply V293_tcb_internal_empty_star;[exact E| | ]).
 all:repeat match goal with |- _ |= _ //\\ _ => split end.
 all:first [apply alvarenv_intro;[exact E|idtac] |
 apply agvarenv_intro;[exact E|idtac] |
 apply anotinlenv_intro;[exact E|idtac]].
 all:cbn[getlenv getgenv substmo substaskst get_lenv get_genv get_smem fst snd]in *;auto.

Qed.
Lemma V293_tcb_shared_bindings_close : forall table bf bu bc bp bs bb bi bz be bo bh bg br bn,
 V293_tcb_empty_bindings bf bc bu **
 (V293_tcb_fields_bindings 108%Z 101%Z 102%Z 103%Z 104%Z 105%Z 106%Z 107%Z bc bp bs bb bi bz be bo **
 (V293_tcb_table_binding table ** V293_tcb_publication_globals bh bg br bn)) ==>
 V293_tcb_success_local_bindings bu bc bp bs bb bi bz be bo **
 V293_tcb_success_global_bindings table bf bh bg br bn.
Proof.
 intros table bf bu bc bp bs bb bi bz be bo bh bg br bn s H.
 unfold V293_tcb_empty_bindings,V293_tcb_fields_bindings,V293_tcb_table_binding,V293_tcb_publication_globals in H.
 unfold V293_tcb_success_local_bindings,V293_tcb_success_global_bindings.
 sep auto. all:destruct_s s;simpl in *;repeat split;join auto.
 all:congruence.
Qed.

Lemma V293_tcb_shared_internal_entry : forall table bf bu bc bp bs bb bi bz be bo bh bg br bn
 p top bottom identity size ext options pc cpu Q aop ir si ci,
 V293_rdy_raw_cells
 (V293_tcb_success_local_cells bu bc bp bs bb bi bz be bo p top bottom identity size ext options pc cpu)
 (V293_tcb_success_local_bindings bu bc bp bs bb bi bz be bo **
 (V293_tcb_shared_external table bf bh bg br bn Q aop ir si ci ** V293_tcb_internal_domain)) ==>
 V293_tcb_enabled_state bf bc bu pc cpu
 (V293_tcb_allocated_inputs bc bp bs bb bi bz be bo p top bottom identity size ext options
 (V293_tcb_table_binding table ** (V293_tcb_publication_globals bh bg br bn ** Q)))aop ir si ci ** V293_tcb_internal_domain.
Proof.
 intros table bf bu bc bp bs bb bi bz be bo bh bg br bn p top bottom identity size ext options pc cpu Q aop ir si ci s H.
 unfold V293_tcb_shared_external in H.
 assert(E:s |= V293_rdy_raw_cells
 (V293_tcb_success_local_cells bu bc bp bs bb bi bz be bo p top bottom identity size ext options pc cpu)
 (((V293_tcb_success_local_bindings bu bc bp bs bb bi bz be bo **
 V293_tcb_success_global_bindings table bf bh bg br bn) ** V293_tcb_internal_domain) **
 (<||aop||> ** OS[ir,true,si,ci] ** Q))).
 { eapply V293_raw_cells_mono;[ |exact H]. intros st HS;clear -HS;sep auto. }
 eapply V293_raw_cells_mono in E.
 2:{ apply astar_mono;[apply V293_tcb_success_bindings_from_domain|intros st HS;exact HS]. }
 eapply V293_raw_cells_mono in E.
 2:{ apply astar_mono;[apply astar_mono;[apply V293_tcb_shared_bindings_open|intros st HS;exact HS]|intros st HS;exact HS]. }
 unfold V293_tcb_enabled_state,V293_tcb_enabled_resources,V293_tcb_allocated_inputs.
 cbn[V293_tcb_success_local_cells V293_rdy_raw_cells]in E|-*.
 clear -E;sep auto.
Qed.

Lemma V293_tcb_shared_internal_exit : forall table bf bu bc bp bs bb bi bz be bo bh bg br bn
 p top bottom identity size ext options pc cpu Q aop ir si ci,
 V293_tcb_enabled_state bf bc bu pc cpu
 (V293_tcb_allocated_inputs bc bp bs bb bi bz be bo p top bottom identity size ext options
 (V293_tcb_table_binding table ** (V293_tcb_publication_globals bh bg br bn ** Q)))aop ir si ci ==>
 V293_tcb_internal_post_cells ** V293_tcb_shared_external table bf bh bg br bn Q aop ir si ci.
Proof.
 intros table bf bu bc bp bs bb bi bz be bo bh bg br bn p top bottom identity size ext options pc cpu Q aop ir si ci s H.
 unfold V293_tcb_enabled_state,V293_tcb_enabled_resources,V293_tcb_allocated_inputs in H.
 assert(E:s |= V293_rdy_raw_cells
 (V293_tcb_success_local_cells bu bc bp bs bb bi bz be bo p top bottom identity size ext options pc cpu)
 ((V293_tcb_empty_bindings bf bc bu **
 (V293_tcb_fields_bindings 108%Z 101%Z 102%Z 103%Z 104%Z 105%Z 106%Z 107%Z bc bp bs bb bi bz be bo **
 (V293_tcb_table_binding table ** V293_tcb_publication_globals bh bg br bn))) **
 (<||aop||> ** OS[ir,true,si,ci] ** Q))).
 { cbn[V293_tcb_success_local_cells V293_rdy_raw_cells]in H|-*;clear -H;sep auto. }
 eapply V293_raw_cells_mono in E.
 2:{ apply astar_mono;[apply V293_tcb_shared_bindings_close|intros st HS;exact HS]. }
 assert(F:s |= V293_rdy_raw_cells
 (V293_tcb_success_local_cells bu bc bp bs bb bi bz be bo p top bottom identity size ext options pc cpu)
 (V293_tcb_success_local_bindings bu bc bp bs bb bi bz be bo) **
 V293_tcb_shared_external table bf bh bg br bn Q aop ir si ci).
 { apply astar_comm. apply V293_raw_cells_move_frame. eapply V293_raw_cells_mono;[ |exact E].
   intros st HS. unfold V293_tcb_shared_external;clear -HS;sep auto. }
 eapply astar_mono;[apply V293_tcb_success_internal_pack|intros st HS;exact HS|exact F].
Qed.

Theorem V293_OS_TCBInit_shared_internal_resources : forall Spec sd li tid hi hc tcbtable table reserved bf bh bg br bn nesting
 p top bottom identity size ext options R aop si ci (good:GoodFunAsrt R),
 GoodI(V293_create_joint_inv tcbtable bf table bh bg br bn nesting reserved)sd li ->
 p<13 -> (gettopis si<=INUM)%nat -> GoodFrm R ->
 V293_tcb_init_values_valid top bottom identity size ext options -> (R ==> CurLINV li tid) ->
 Spec hi=Some(V293_tcb_enabled_hook_fpre p top bottom identity size ext options
 (V293_create_owned_share table reserved p ** R)aop(fun _=>false)si ci tid
 (V293_tcb_hook_owner_accepted table reserved p R good),
 V293_tcb_enabled_hook_fpost p top bottom identity size ext options
 (V293_create_owned_share table reserved p ** R)aop(fun _=>false)si ci tid
 (V293_tcb_hook_owner_accepted table reserved p R good),(Tvoid,[Tptr V293_tcb_type])) ->
 Spec hc=Some(V293_tcb_enabled_hook_fpre p top bottom identity size ext options R aop(fun _=>false)si ci tid
 (proj2(V293_tcb_hook_owner_accepted table reserved p R good)),
 V293_tcb_enabled_hook_fpost p top bottom identity size ext options R aop(fun _=>false)si ci tid
 (proj2(V293_tcb_hook_owner_accepted table reserved p R good)),(Tvoid,[Tptr V293_tcb_type])) ->
 (forall b off next s,s |= V293_tcb_allocated_initialized b off next p top bottom identity size ext options **
 (V293_create_owned_share table reserved p ** Atrue) -> (b,off)<>reserved) ->
 InfRules Spec sd li(V293_create_joint_inv tcbtable bf table bh bg br bn nesting reserved)
 (fun result=>V293_tcb_internal_post_cells **
 getasrt(V293_tcb_shared_fpost table reserved bf bh bg br bn p R aop(fun _=>false)si ci good []result[]tid) ** V293_tcb_internal_domain)Afalse
 (V293_tcb_internal_pre_cells(V293_byteval p)top bottom identity size ext options **
 V293_tcb_shared_external table bf bh bg br bn(V293_create_owned_share table reserved p ** R)aop(fun _=>false)si ci **
 V293_tcb_internal_domain)(V293_TCBInit_function_body hi hc)Afalse tid.
Proof.
 intros Spec sd li tid hi hc tcbtable table reserved bf bh bg br bn nesting
 p top bottom identity size ext options R aop si ci good GI Range Bound Frame Valid HR FirstLookup SecondLookup Fresh.
 eapply conseq_rule.
 - apply V293_tcb_success_internal_unpack.
 - intros s H;exact H.
 - apply ex_intro_rule. intro pc. apply ex_intro_rule. intro cpu.
   apply ex_intro_rule. intro bo. apply ex_intro_rule. intro be.
   apply ex_intro_rule. intro bz. apply ex_intro_rule. intro bi.
   apply ex_intro_rule. intro bb. apply ex_intro_rule. intro bs.
   apply ex_intro_rule. intro bp. apply ex_intro_rule. intro bc.
   apply ex_intro_rule. intro bu.
   eapply conseq_rule with(q:=Afalse ** V293_tcb_internal_domain).
   + apply V293_tcb_shared_internal_entry.
   + intros s H;clear -H;destruct_s s;simpl in *;join auto.
   + eapply r_conseq_rule with
     (r:=fun result=>(V293_tcb_internal_post_cells **
 getasrt(V293_tcb_shared_fpost table reserved bf bh bg br bn p R aop(fun _=>false)si ci good []result[]tid)) ** V293_tcb_internal_domain)
     (ri:=Afalse ** V293_tcb_internal_domain).
     * intros result s H;clear -H;sep auto.
     * intros s H;clear -H;destruct_s s;simpl in *;join auto.
     * apply frame_rule_all.
       -- exact GI.
       -- apply V293_tcb_success_body_good.
       -- apply V293_tcb_internal_domain_frame.
       -- unfold V293_tcb_enabled_state,V293_tcb_enabled_resources.
          do 5 apply V293_star_CurLINV_r. apply V293_tcb_allocated_inputs_linv.
          do 3 apply V293_star_CurLINV_r;exact HR.
       -- eapply conseq_rule with
          (p:=V293_tcb_enabled_state bf bc bu pc cpu
          (V293_tcb_allocated_inputs bc bp bs bb bi bz be bo p top bottom identity size ext options
          (V293_tcb_table_binding table ** (V293_create_owned_share table reserved p **
          (V293_tcb_publication_globals bh bg br bn ** R))))aop(fun _=>false)si ci).
          ++ intros s H. unfold V293_tcb_enabled_state,V293_tcb_enabled_resources,V293_tcb_allocated_inputs in *.
             cbn[V293_rdy_raw_cells]in *;clear -H;sep auto.
          ++ intros s H;exact H.
          ++ eapply V293_OS_TCBInit_creator_joint_hook_framed with
          (good:=V293_tcb_hook_owner_accepted table reserved p R good);try eassumption.
             ** intros s H.
                assert(E:s |= V293_tcb_internal_post_cells **
               V293_tcb_shared_external table bf bh bg br bn(V293_create_owned_share table reserved p ** R)aop(fun _=>false)si ci).
             { eapply V293_tcb_shared_internal_exit.
               unfold V293_tcb_enabled_state,V293_tcb_enabled_resources,V293_tcb_allocated_inputs in *.
               cbn[V293_rdy_raw_cells]in *;clear -H;sep auto. }
             eapply astar_mono;[intros st HS;exact HS| |exact E].
             intros st HS. cbn[V293_tcb_shared_fpost getasrt]. left.
             apply astar_l_apure_intro;[exact HS|reflexivity].
             ** intros b off next s H.
             assert(E:s |= V293_tcb_allocated_initialized b off next p top bottom identity size ext options **
              (V293_create_owned_share table reserved p ** Atrue)).
             { unfold V293_tcb_enabled_state,V293_tcb_enabled_resources,V293_tcb_allocated_inputs in H.
               cbn[V293_rdy_raw_cells]in H;clear -H;sep auto. }
             eapply Fresh;exact E.
             ** intros b off s H.
             pose proof(V293_tcb_shared_internal_exit table bf bu bc bp bs bb bi bz be bo bh bg br bn
               p top bottom identity size ext options(Vptr(b,off))(Vint32 Int.zero)R aop(fun _=>false)si ci s H)as E.
             eapply astar_mono;[intros st HS;exact HS| |exact E].
             intros st HS. cbn[V293_tcb_shared_fpost getasrt]. right.
             apply astar_l_apure_intro;[exact HS|reflexivity].
Qed.

Theorem V293_OS_TCBInit_shared_internal_contract : forall P f vl lg pre post Spec sd li tid hi hc tcbtable table reserved bf bh bg br bn nesting
 p top bottom identity size ext options R aop si ci (good:GoodFunAsrt R),
 GoodI(V293_create_joint_inv tcbtable bf table bh bg br bn nesting reserved)sd li ->
 p<13 -> (gettopis si<=INUM)%nat -> GoodFrm R ->
 V293_tcb_init_values_valid top bottom identity size ext options -> (R ==> CurLINV li tid) ->
 Spec hi=Some(V293_tcb_enabled_hook_fpre p top bottom identity size ext options
 (V293_create_owned_share table reserved p ** R)aop(fun _=>false)si ci tid
 (V293_tcb_hook_owner_accepted table reserved p R good),
 V293_tcb_enabled_hook_fpost p top bottom identity size ext options
 (V293_create_owned_share table reserved p ** R)aop(fun _=>false)si ci tid
 (V293_tcb_hook_owner_accepted table reserved p R good),(Tvoid,[Tptr V293_tcb_type])) ->
 Spec hc=Some(V293_tcb_enabled_hook_fpre p top bottom identity size ext options R aop(fun _=>false)si ci tid
 (proj2(V293_tcb_hook_owner_accepted table reserved p R good)),
 V293_tcb_enabled_hook_fpost p top bottom identity size ext options R aop(fun _=>false)si ci tid
 (proj2(V293_tcb_hook_owner_accepted table reserved p R good)),(Tvoid,[Tptr V293_tcb_type])) ->
 (forall b off next s,s |= V293_tcb_allocated_initialized b off next p top bottom identity size ext options **
 (V293_create_owned_share table reserved p ** Atrue) -> (b,off)<>reserved) ->
 P f=Some(V293_TCBInit_function hi hc) ->
 Some pre=BuildPreI P f vl lg
 (V293_tcb_shared_fpre table reserved bf bh bg br bn p top bottom identity size ext options R aop(fun _=>false)si ci good)tid ->
 Some post=BuildRetI P f vl lg
 (V293_tcb_shared_fpost table reserved bf bh bg br bn p R aop(fun _=>false)si ci good)tid ->
 InfRules Spec sd li(V293_create_joint_inv tcbtable bf table bh bg br bn nesting reserved)
 post Afalse pre(V293_TCBInit_function_body hi hc)Afalse tid.
Proof.
 intros P f vl lg pre post Spec sd li tid hi hc tcbtable table reserved bf bh bg br bn nesting
 p top bottom identity size ext options R aop si ci good GI Range Bound Frame Valid HR FirstLookup SecondLookup Fresh Code Pre Post.
 unfold BuildPreI in Pre. rewrite Code in Pre. cbn[V293_TCBInit_function]in Pre.
 destruct(dl_vl_match V293_TCBInit_parameters(rev vl))eqn:Typed;[idtac|discriminate].
 pose proof(dl_vl_match_dv_same_length _ _ Typed)as Length.
 rewrite rev_length in Length. cbn[V293_TCBInit_parameters decllen]in Length.
 destruct vl as [ |v7 vl];[discriminate Length|idtac].
 destruct vl as [ |v6 vl];[discriminate Length|idtac].
 destruct vl as [ |v5 vl];[discriminate Length|idtac].
 destruct vl as [ |v4 vl];[discriminate Length|idtac].
 destruct vl as [ |v3 vl];[discriminate Length|idtac].
 destruct vl as [ |v2 vl];[discriminate Length|idtac].
 destruct vl as [ |v1 vl];[discriminate Length|idtac].
 destruct vl;[idtac|discriminate Length].
 fold V293_tcb_internal_declarations in Pre. rewrite V293_tcb_internal_buildp in Pre.
 change(Some pre=Some(V293_tcb_internal_pre_cells v1 v2 v3 v4 v5 v6 v7 **
 ([|[v1;v2;v3;v4;v5;v6;v7]=V293_tcb_success_arguments p top bottom identity size ext options|] **
 V293_tcb_shared_external table bf bh bg br bn(V293_create_owned_share table reserved p ** R)aop(fun _=>false)si ci) ** V293_tcb_internal_domain))in Pre.
 inversion Pre;subst pre.
 unfold BuildRetI in Post. rewrite Code in Post.
 change(Some post=Some(fun result=>V293_tcb_internal_post_cells ** getasrt(V293_tcb_shared_fpost table reserved bf bh bg br bn p R aop(fun _=>false)si ci good []result[]tid) ** V293_tcb_internal_domain))in Post.
 inversion Post;subst post.
 eapply conseq_rule with(p:=V293_tcb_internal_pre_cells(V293_byteval p)top bottom identity size ext options **
 V293_tcb_shared_external table bf bh bg br bn(V293_create_owned_share table reserved p ** R)aop(fun _=>false)si ci ** V293_tcb_internal_domain).
 - intros s H.
   assert(K:s |= [|[v1;v2;v3;v4;v5;v6;v7]=V293_tcb_success_arguments p top bottom identity size ext options|] **
   (V293_tcb_internal_pre_cells v1 v2 v3 v4 v5 v6 v7 ** V293_tcb_shared_external table bf bh bg br bn(V293_create_owned_share table reserved p ** R)aop(fun _=>false)si ci ** V293_tcb_internal_domain)).
   { clear -H;sep auto. }
   apply astar_l_apure_elim in K. destruct K as[Args K].
   unfold V293_tcb_success_arguments in Args. inversion Args;subst;exact K.
 - intros s H;exact H.
 - eapply V293_OS_TCBInit_shared_internal_resources;eassumption.
Qed.

(* The real creator evaluates seven expressions and stores the return in err.
   This is a call-rule theorem; the callee body obligation above uses the SAME
   pre/post pair. Hook implementations and WFIFun are not asserted here. *)
Lemma V293_tcb_shared_external_linv : forall table bf bh bg br bn Q aop ir si ci li tid,
 (Q ==> CurLINV li tid) ->
 V293_tcb_shared_external table bf bh bg br bn Q aop ir si ci ==> CurLINV li tid.
Proof.
 intros table bf bh bg br bn Q aop ir si ci li tid HR. unfold V293_tcb_shared_external.
 do 3 apply V293_star_CurLINV_r;assumption.
Qed.
Lemma V293_tcb_shared_retpost : forall table reserved bf bh bg br bn p R aop ir si ci good,
 retpost(V293_tcb_shared_fpost table reserved bf bh bg br bn p R aop ir si ci good).
Proof.
 intros table reserved bf bh bg br bn p R aop ir si ci good st args result ghosts task H.
 cbn[V293_tcb_shared_fpost getasrt]in H. destruct H as[H|H];
 apply astar_l_apure_elim in H;destruct H as[Code _];rewrite Code;discriminate.
Qed.
Theorem V293_TaskCreateExt_TCB_shared_call : forall Spec sd li I r ri tid f
 table reserved bf bh bg br bn p top bottom identity size ext options R aop ir si ci
 (good:GoodFunAsrt R) F olderr,
 GoodFrm F -> p<256 -> V293_tcb_init_values_valid top bottom identity size ext options ->
 (R ==> CurLINV li tid) ->
 Spec f=Some(V293_tcb_shared_fpre table reserved bf bh bg br bn p top bottom identity size ext options R aop ir si ci good,
 V293_tcb_shared_fpost table reserved bf bh bg br bn p R aop ir si ci good,
 (Tint8,rev V293_TCBInit_argument_types)) ->
 InfRules Spec sd li I r ri
 (V293_tcb_shared_external table bf bh bg br bn(V293_create_owned_share table reserved p ** R)aop ir si ci **
 LV 209%Z @ Tint8 |->olderr ** V293_create_tcb_arguments p top bottom identity size ext options F)
 (V293_TaskCreateExt_TCB_call 209%Z f 101%Z 108%Z 205%Z 206%Z 207%Z 208%Z 204%Z)
 (EX result:val,
 getasrt(V293_tcb_shared_fpost table reserved bf bh bg br bn p R aop ir si ci good
 (V293_tcb_success_arguments p top bottom identity size ext options)(Some result)[]tid) **
 LV 209%Z @ Tint8 |->result ** V293_create_tcb_arguments p top bottom identity size ext options F)tid.
Proof.
 intros Spec sd li I r ri tid f table reserved bf bh bg br bn p top bottom identity size ext options
 R aop ir si ci good F olderr Frame Range Valid HR Lookup.
 unfold V293_TaskCreateExt_TCB_call.
 eapply calle_rule_lvar with
 (pre:=V293_tcb_shared_fpre table reserved bf bh bg br bn p top bottom identity size ext options R aop ir si ci good)
 (post:=V293_tcb_shared_fpost table reserved bf bh bg br bn p R aop ir si ci good)
 (tp:=Tint8)(tl:=rev V293_TCBInit_argument_types)
 (vl:=V293_tcb_success_arguments p top bottom identity size ext options)(logicl:=[])(v':=olderr)
 (p:=V293_create_tcb_arguments p top bottom identity size ext options F).
 - apply V293_create_tcb_arguments_good;exact Frame.
 - apply V293_tcb_shared_retpost.
 - exact Lookup.
 - intros s H. cbn[V293_tcb_shared_fpre getasrt].
   apply astar_mono with
   (P:=V293_tcb_shared_external table bf bh bg br bn(V293_create_owned_share table reserved p ** R)aop ir si ci)
   (Q:=LV 209%Z @ Tint8 |->olderr ** V293_create_tcb_arguments p top bottom identity size ext options F).
   + intros st HS. apply astar_l_apure_intro;[exact HS|reflexivity].
   + intros st HS;exact HS.
   + exact H.
 - intros s H. eapply V293_create_tcb_arguments_read with
   (F:=V293_tcb_shared_external table bf bh bg br bn(V293_create_owned_share table reserved p ** R)aop ir si ci **
   LV 209%Z @ Tint8 |->olderr ** F);[exact Range|exact Valid| ].
   cbn[V293_tcb_shared_fpre getasrt]in H.
   unfold V293_create_tcb_arguments in *;clear -H;sep auto.
 - apply V293_create_tcb_argument_types;assumption.
 - cbn[V293_tcb_shared_fpre getasrt]. apply V293_star_CurLINV_r.
   apply V293_tcb_shared_external_linv. apply V293_star_CurLINV_r;exact HR.
 - intros s[result H]. cbn[V293_tcb_shared_fpost getasrt]in H.
   destruct H as[H|H];apply astar_l_apure_elim in H;destruct H as[_ H].
   + eapply V293_tcb_shared_external_linv;[apply V293_star_CurLINV_r;exact HR|exact H].
   + eapply V293_tcb_shared_external_linv;[exact HR|exact H].
Qed.
