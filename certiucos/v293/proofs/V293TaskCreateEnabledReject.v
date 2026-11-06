(* Enabled-IE early exits. Shared bytes are borrowed only after encrit1
   and returned by excrit1. Original full function body is unchanged. *)
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateRejectInternal.
Require Import CertiOS.certiucos.v293.proofs.V293TimeAccess.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateSuccessInternal.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateBodyFailure.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateExtPrefix.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateEmptyInternal.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitFields.
Require Import CertiOS.certiucos.v293.proofs.V293TCBSuccessHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.code.V293OSTaskCreateExtFunction.
Require Import CertiOS.certiucos.v293.code.V293OSTaskCreateExtPrefix.
Require Import CertiOS.certiucos.v293.code.V293OSTaskCreateExtSuffix.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.tactics.hoareforward.init_spec.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.proofs.V293InitAllRecords.
Require Import CertiOS.certiucos.v293.proofs.V293TCBEmptyInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293TCBPriorityHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TCBFieldsHoare.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.


Definition V293_create_enabled_locals bp bc p cpu F :=
 V293_rdy_raw_cells([((bp,0%Z),Tint8,V293_byteval p);((bc,0%Z),Tint32,cpu)])
 (Alvarenv 101%Z Tint8(bp,0%Z) ** Alvarenv 109%Z Tint32(bc,0%Z) ** F).
Definition V293_create_enabled_state bp bc p cpu F aop ir si ci :=
 <||aop||> ** OS[ir,true,si,ci] ** V293_create_enabled_locals bp bc p cpu F.
Definition V293_create_enabled_return k bp bc p F aop ir si ci : retasrt :=
 fun result=>[|result=Some(Vint32(Int.repr(V293_create_rejection_code k)))|] **
 V293_create_enabled_state bp bc p(Vint32 Int.zero)F aop ir si ci.
Definition V293_create_borrowed k table bn p n slot K :=
 V293_rdy_raw_cells(V293_create_rejection_extra_cells k table bn p n slot)
 (V293_create_rejection_globals k table bn ** K).

Lemma V293_create_enabled_good : forall bp bc p cpu F,
 GoodFrm F -> GoodFrm(V293_create_enabled_locals bp bc p cpu F).
Proof. intros. cbn[V293_create_enabled_locals V293_rdy_raw_cells GoodFrm]. tauto. Qed.
Lemma V293_create_enabled_env : forall bp bc p cpu F s,
 s |= V293_create_enabled_locals bp bc p cpu F ->
 get(getlenv s)101%Z=Some(bp,Tint8) /\ get(getlenv s)109%Z=Some(bc,Tint32).
Proof.
 intros bp bc p cpu F s H.
 assert(P:s |= Alvarenv 101%Z Tint8(bp,0%Z) ** Atrue).
 { unfold V293_create_enabled_locals in H. cbn[V293_rdy_raw_cells]in H. clear -H;sep auto. }
 assert(C:s |= Alvarenv 109%Z Tint32(bc,0%Z) ** Atrue).
 { unfold V293_create_enabled_locals in H. cbn[V293_rdy_raw_cells]in H. clear -H;sep auto. }
 split.
 - refine(V293_star_env_l _ _ (fun ge le=>get le 101%Z=Some(bp,Tint8)) _ s P). intros st[actual[E[B _]]]. inversion B;subst;exact E.
 - refine(V293_star_env_l _ _ (fun ge le=>get le 109%Z=Some(bc,Tint32)) _ s C). intros st[actual[E[B _]]]. inversion B;subst;exact E.
Qed.
Lemma V293_create_enabled_cpu : forall Spec sd li I r ri tid bp bc p old F aop ir si ci,
 (F ==> CurLINV li tid) ->
 InfRules Spec sd li I r ri
 (V293_create_enabled_state bp bc p old F aop ir si ci)
 (sassign(evar 109%Z)(econst32 Int.zero))
 (V293_create_enabled_state bp bc p(Vint32 Int.zero)F aop ir si ci)tid.
Proof.
 intros. unfold V293_create_enabled_state,V293_create_enabled_locals.
 eapply conseq_rule with
 (p:=<||aop||> ** V293_rdy_raw_cells([((bp,0%Z),Tint8,V293_byteval p);((bc,0%Z),Tint32,old)])
 (OS[ir,true,si,ci] ** (Alvarenv 101%Z Tint8(bp,0%Z) ** Alvarenv 109%Z Tint32(bc,0%Z) ** F)))
 (q:=<||aop||> ** V293_rdy_raw_cells([((bp,0%Z),Tint8,V293_byteval p);((bc,0%Z),Tint32,Vint32 Int.zero)])
 (OS[ir,true,si,ci] ** (Alvarenv 101%Z Tint8(bp,0%Z) ** Alvarenv 109%Z Tint32(bc,0%Z) ** F))).
 - cbn[V293_rdy_raw_cells]. intros s H1;sep auto.
 - cbn[V293_rdy_raw_cells]. intros s H1;sep auto.
 - eapply V293_raw_assign_hoare with(before:=[((bp,0%Z),Tint8,V293_byteval p)])(a:=(bc,0%Z))(rt:=Tint32).
   + reflexivity.
   + apply eq_int;auto.
   + intros s Owned.
     assert(C:s |= Alvarenv 109%Z Tint32(bc,0%Z) ** Atrue).
     { cbn[V293_rdy_raw_cells app]in Owned. clear -Owned;sep auto. }
     assert(Bc:get(getlenv s)109%Z=Some(bc,Tint32)).
     { refine(V293_star_env_l _ _ (fun ge le=>get le 109%Z=Some(bc,Tint32)) _ s C). intros st[actual[E[B _]]]. inversion B;subst;exact E. }
     destruct s as [[[[[[ge le] M] irq] aux] O] op].
     change(get le 109%Z=Some(bc,Tint32))in Bc.
     cbn[sat getsmem get_smem evaladdr evaltype evalval get_lenv].
     cbv delta[env var memory.ident Modules.ident]in *. rewrite Bc.
     repeat split;try reflexivity;discriminate.
   + apply V293_star_CurLINV_r. do 2 apply V293_star_CurLINV_r. exact H.
Qed.
Lemma V293_create_enabled_priority : forall k bp bc p n cpu F aop ir si ci s,
 V293_create_rejection_valid k p n ->
 s |= V293_create_enabled_state bp bc p cpu F aop ir si ci ->
 evalval(ebinop olt(econst32(Int.repr 12))(ecast(evar 101%Z)Tint32))(getsmem s)=
 Some(Vint32(if Z.eqb(V293_create_rejection_code k)42%Z then Int.one else Int.zero)) /\
 evaltype(ebinop olt(econst32(Int.repr 12))(ecast(evar 101%Z)Tint32))(getsmem s)=Some Tint32.
Proof.
 intros k bp bc p n cpu F aop ir si ci s Range Owned.
 assert(L:s |= V293_create_enabled_locals bp bc p cpu F ** Atrue).
 { unfold V293_create_enabled_state in Owned. clear -Owned;sep auto. }
 assert(Bp:get(getlenv s)101%Z=Some(bp,Tint8)).
 { refine(V293_star_env_l _ _ (fun ge le=>get le 101%Z=Some(bp,Tint8)) _ s L). intros st H1. exact(proj1(V293_create_enabled_env _ _ _ _ _ st H1)). }
 destruct s as [[[[[[ge le] M] irq] aux] O] op].
 cbn[getlenv getgenv get_lenv get_genv get_smem]in *.
 assert(PBound:p<256)by(destruct k;cbn[V293_create_rejection_valid]in Range;lia).
 pose proof(V293_byte_type p PBound)as PValid.
 assert(Load:load Tint8 M(bp,0%Z)=Some(V293_byteval p)).
 { change(load Tint8(getmem(ge,le,M,irq,aux,O,op))(bp,0%Z)=Some(V293_byteval p)).
   eapply V293_star_load_l;[ |exact L]. unfold V293_create_enabled_locals.
   intros st H1. eapply V293_rdy_raw_load with(cells:=[((bp,0%Z),Tint8,V293_byteval p);((bc,0%Z),Tint32,cpu)]);
   [left;reflexivity|exact PValid|exact H1]. }
 cbn[getsmem get_smem]. split.
 - cbn[evalval evaltype get_lenv get_genv get_mem].
   cbv delta[env var memory.ident Modules.ident]in *. rewrite Bp.
   cbn beta iota. rewrite Load.
   cbn[cast_eval V293_byteval is_int_type bop_eval cmp_val cmpu].
   destruct k;cbn[V293_create_rejection_code]in *.
   + unfold Int.ltu. rewrite !Int.unsigned_repr by(unfold Int.max_unsigned,Int.modulus,Int.wordsize;cbn;lia).
     destruct(zlt 12(Z.of_nat p));[reflexivity|cbn[V293_create_rejection_valid]in Range;lia].
   + rewrite V293_create_priority_guard_false by(cbn[V293_create_rejection_valid]in Range;lia). reflexivity.
   + rewrite V293_create_priority_guard_false by exact Range. reflexivity.
 - V293_rdy_eval.
Qed.
Lemma V293_create_enabled_ret : forall Spec sd li I tid k bp bc p F aop ir si ci,
 InfRules Spec sd li I(V293_create_enabled_return k bp bc p F aop ir si ci)Afalse
 (V293_create_enabled_state bp bc p(Vint32 Int.zero)F aop ir si ci)
 (srete(econst32(Int.repr(V293_create_rejection_code k))))Afalse tid.
Proof.
 intros. apply rete_rule with(v:=Vint32(Int.repr(V293_create_rejection_code k)))(t:=Tint32).
 intros s H. split.
 - unfold V293_create_enabled_return. apply astar_l_apure_intro;[exact H|reflexivity].
 - destruct_s s. destruct k;cbn[sat V293_create_rejection_code];repeat split;try reflexivity;discriminate.
Qed.

(* A resource equivalence, not an assumed statement execution. It is checked
   with a concrete nonempty physical ISR invariant in the independent probe. *)
Lemma V293_create_enabled_enter : forall Spec sd li I r ri tid
 k bp bc table bn p n slot cpu F K aop ir si ci,
 (gettopis si<=INUM)%nat -> GoodFrm F ->
 (Aisr ir ** invlth_isr I 0(gettopis si) ==> Aisr ir ** V293_create_borrowed k table bn p n slot K) ->
 (V293_create_rejection_globals k table bn ** F ==> V293_create_rejection_views k table bn ** F) ->
 InfRules Spec sd li I r ri
 (V293_create_enabled_state bp bc p cpu F aop ir si ci)(sprim encrit)
 (V293_create_rejection_state k bp bc table bn p n slot cpu(K ** F)aop ir si(true::ci))tid.
Proof.
 intros Spec sd li I r ri tid k bp bc table bn p n slot cpu F K aop ir si ci Bound Frame Open Views.
 unfold V293_create_enabled_state. eapply conseq_rule with
 (p:=<||aop||> ** OS[ir,true,si,ci] ** ATopis(gettopis si) ** [|(gettopis si<=INUM)%nat|] **
 V293_create_enabled_locals bp bc p cpu F)
 (q:=<||aop||> ** OS[ir,false,si,true::ci] ** invlth_isr I 0(gettopis si) **
 V293_create_enabled_locals bp bc p cpu F).
 - intros s H. assert(S:s |= Ais si ** Atrue)by(sep auto).
   pose proof(V293_time_topis si Atrue s S)as Top.
   apply astar_l_atopis_elim in Top. destruct Top as[Top _].
   pose proof(@astar_l_atopis_intro s(gettopis si)_ H Top)as HT. clear H;rename HT into H. sep auto.
 - intros s H.
   assert(B:s |= (Aisr ir ** invlth_isr I 0(gettopis si)) **
   (<||aop||> ** Aie false ** Ais si ** Acs(true::ci) ** V293_create_enabled_locals bp bc p cpu F))by(sep auto).
   eapply astar_mono in B;[ |exact Open|intros st HS;exact HS].
   unfold V293_create_borrowed,V293_create_enabled_locals in B.
   assert(V:s |= (V293_create_rejection_globals k table bn ** F) **
   (<||aop||> ** OS[ir,false,si,true::ci] **
   V293_rdy_raw_cells(V293_create_rejection_extra_cells k table bn p n slot)K **
   Amapsto(bp,0%Z)Tint8 true(V293_byteval p) ** Amapsto(bc,0%Z)Tint32 true cpu **
   Alvarenv 101%Z Tint8(bp,0%Z) ** Alvarenv 109%Z Tint32(bc,0%Z))).
   { destruct k;cbn[V293_create_rejection_extra_cells V293_rdy_raw_cells]in *;clear -B;sep auto. }
   eapply astar_mono in V;[ |exact Views|intros st HS;exact HS].
   unfold V293_create_rejection_state,V293_create_rejection_cells,V293_create_rejection_bindings.
   destruct k;cbn[V293_create_rejection_extra_cells V293_rdy_raw_cells]in *;clear -V;sep auto.
 - apply encrit1_rule. apply V293_create_enabled_good;exact Frame.
Qed.
Lemma V293_create_enabled_exit : forall Spec sd li I r ri tid
 k bp bc table bn p n slot cpu F K aop ir si ci,
 GoodFrm F -> (F ==> CurLINV li tid) ->
 (Aisr ir ** V293_create_borrowed k table bn p n slot K ==> Aisr ir ** invlth_isr I 0(gettopis si)) ->
 InfRules Spec sd li I r ri
 (V293_create_rejection_state k bp bc table bn p n slot cpu(K ** F)aop ir si(true::ci))(sprim excrit)
 (V293_create_enabled_state bp bc p cpu F aop ir si ci)tid.
Proof.
 intros Spec sd li I r ri tid k bp bc table bn p n slot cpu F K aop ir si ci Frame HR Close.
 eapply conseq_rule with
 (p:=<||aop||> ** OS[ir,false,si,true::ci] ** ATopis(gettopis si) ** invlth_isr I 0(gettopis si) **
 V293_create_enabled_locals bp bc p cpu F)
 (q:=<||aop||> ** OS[ir,true,si,ci] ** V293_create_enabled_locals bp bc p cpu F).
 - intros s H. unfold V293_create_rejection_state,V293_create_rejection_cells,V293_create_rejection_bindings in H.
   assert(V:s |= V293_create_rejection_views k table bn **
   (<||aop||> ** OS[ir,false,si,true::ci] **
   V293_rdy_raw_cells(V293_create_rejection_extra_cells k table bn p n slot)K **
   V293_create_enabled_locals bp bc p cpu F)).
   { unfold V293_create_enabled_locals. destruct k;cbn[V293_create_rejection_extra_cells V293_rdy_raw_cells]in *;clear -H;sep auto. }
   eapply astar_mono in V;[ |apply V293_create_reject_drop_views|intros st HS;exact HS].
   assert(B:s |= (Aisr ir ** V293_create_borrowed k table bn p n slot K) **
   (<||aop||> ** Aie false ** Ais si ** Acs(true::ci) ** V293_create_enabled_locals bp bc p cpu F)).
   { unfold V293_create_borrowed. destruct k;cbn[V293_create_rejection_extra_cells V293_rdy_raw_cells]in *;clear -V;sep auto. }
   eapply astar_mono in B;[ |exact Close|intros st HS;exact HS].
   assert(S:s |= Ais si ** Atrue)by(clear -B;sep auto).
   pose proof(V293_time_topis si Atrue s S)as Top.
   apply astar_l_atopis_elim in Top. destruct Top as[Top _].
   pose proof(@astar_l_atopis_intro s(gettopis si)_ B Top)as HT. clear -HT;sep auto.
 - unfold V293_create_enabled_state. intros s H;exact H.
 - apply excrit1_rule.
   + apply V293_create_enabled_good;exact Frame.
   + unfold V293_create_enabled_locals. do 2 apply V293_star_CurLINV_r.
     do 2 apply V293_star_CurLINV_r. exact HR.
Qed.

Theorem V293_OSTaskCreateExt_enabled_rejection_body : forall Spec sd li I tid
 k bp bc table bn p n slot cpu F K aop ir si ci sched hook tcb,
 V293_create_rejection_valid k p n -> (gettopis si<=INUM)%nat ->
 GoodFrm F -> (F ==> CurLINV li tid) ->
 (k<>V293_create_bad_priority ->
 Aisr ir ** invlth_isr I 0(gettopis si) <==> Aisr ir ** V293_create_borrowed k table bn p n slot K) ->
 (V293_create_rejection_globals k table bn ** F ==> V293_create_rejection_views k table bn ** F) ->
 InfRules Spec sd li I(V293_create_enabled_return k bp bc p F aop ir si ci)Afalse
 (V293_create_enabled_state bp bc p cpu F aop ir si ci)
 (V293_CreateExt_body 92%Z 99%Z 97%Z 98%Z sched hook tcb)Afalse tid.
Proof.
 intros Spec sd li I tid k bp bc table bn p n slot cpu F K aop ir si ci sched hook tcb Range Bound Frame HR Borrow Views.
 assert(Priority:forall s,s |= V293_create_enabled_state bp bc p(Vint32 Int.zero)F aop ir si ci ->
 evalval(ebinop olt(econst32(Int.repr 12))(ecast(evar 101%Z)Tint32))(getsmem s)=
 Some(Vint32(if Z.eqb(V293_create_rejection_code k)42%Z then Int.one else Int.zero)) /\
 evaltype(ebinop olt(econst32(Int.repr 12))(ecast(evar 101%Z)Tint32))(getsmem s)=Some Tint32).
 { intros s H. eapply V293_create_enabled_priority;eassumption. }
 assert(Nesting:k<>V293_create_bad_priority -> forall s,
 s |= V293_create_rejection_state k bp bc table bn p n slot(Vint32 Int.zero)(K ** F)aop ir si(true::ci) ->
 evalval(ebinop olt(econst32 Int.zero)(ecast(evar 99%Z)Tint32))(getsmem s)=
 Some(Vint32(if Z.eqb(V293_create_rejection_code k)60%Z then Int.one else Int.zero)) /\
 evaltype(ebinop olt(econst32 Int.zero)(ecast(evar 99%Z)Tint32))(getsmem s)=Some Tint32).
 { intros Needed s H. unfold V293_create_rejection_state in H.
   apply astar_l_aop'_elim in H. destruct H as[_ H]. eapply V293_create_rejection_nesting;eassumption. }
 unfold V293_CreateExt_body,V293_TaskCreateExt_body,V293_TaskCreateExt_prefix.
 eapply seq_rule. { apply V293_create_enabled_cpu. exact HR. }
 destruct k.
 - eapply seq_rule with(p':=Afalse);[ |apply pfalse_rule].
   apply V293_create_reject_if_true;[exact Priority|apply(V293_create_enabled_ret _ _ _ _ _ V293_create_bad_priority)].
 - eapply seq_rule. { apply V293_create_reject_if_false;exact Priority. }
   eapply seq_rule.
   { eapply V293_create_enabled_enter;try eassumption.
     intros s H. apply(Borrow ltac:(discriminate));exact H. }
   eapply seq_rule with(p':=Afalse);[ |apply pfalse_rule].
   apply V293_create_reject_if_true.
   + exact(Nesting ltac:(discriminate)).
   + unfold V293_TaskCreateExt_irq_error. eapply seq_rule.
     * eapply V293_create_enabled_exit;try eassumption.
       intros s H. apply(Borrow ltac:(discriminate));exact H.
     * apply(V293_create_enabled_ret _ _ _ _ _ V293_create_from_isr).
 - eapply seq_rule. { apply V293_create_reject_if_false;exact Priority. }
   eapply seq_rule.
   { eapply V293_create_enabled_enter;try eassumption.
     intros s H. apply(Borrow ltac:(discriminate));exact H. }
   eapply seq_rule. { apply V293_create_reject_if_false;exact(Nesting ltac:(discriminate)). }
   eapply seq_rule.
   + apply V293_create_reject_if_false. intros s H.
     unfold V293_create_rejection_state in H. apply astar_l_aop'_elim in H. destruct H as[_ H].
     eapply V293_create_rejection_slot;[exact Range|exact H].
   + unfold V293_TaskCreateExt_occupied. eapply seq_rule.
     * eapply V293_create_enabled_exit;try eassumption.
       intros s H. apply(Borrow ltac:(discriminate));exact H.
     * apply(V293_create_enabled_ret _ _ _ _ _ V293_create_occupied_priority).
Qed.

Definition V293_create_enabled_external R aop ir si ci :=
 <||aop||> ** OS[ir,true,si,ci] ** R.
Lemma V293_create_enabled_external_good : forall R aop ir si ci,
 GoodFunAsrt R -> GoodFunAsrt(V293_create_enabled_external R aop ir si ci).
Proof. intros. cbn[V293_create_enabled_external GoodFunAsrt]. tauto. Qed.
Definition V293_create_enabled_fpre target argv inputtop p identity bottom size ext options
 R aop ir si ci(good:GoodFunAsrt R) : fpre :=
 fun vl lg tid=>@mkfunasrt
 ([|vl=V293_create_internal_values target argv inputtop p identity bottom size ext options|] **
 V293_create_enabled_external R aop ir si ci)
 (conj I(V293_create_enabled_external_good R aop ir si ci good)).
Definition V293_create_enabled_fpost k R aop ir si ci(good:GoodFunAsrt R) : fpost :=
 fun vl result lg tid=>@mkfunasrt
 ([|result=Some(Vint32(Int.repr(V293_create_rejection_code k)))|] **
 V293_create_enabled_external R aop ir si ci)
 (conj I(V293_create_enabled_external_good R aop ir si ci good)).

Lemma V293_create_enabled_frame_views : forall k table bn target argv inputtop identity bottom size ext options err psp R,
 V293_create_rejection_globals k table bn **
 V293_create_reject_frame target argv inputtop identity bottom size ext options err psp R ==>
 V293_create_rejection_views k table bn **
 V293_create_reject_frame target argv inputtop identity bottom size ext options err psp R.
Proof.
 intros k table bn target argv inputtop identity bottom size ext options err psp R.
 unfold V293_create_reject_frame. intros s H.
 assert(K:s |= (V293_create_rejection_globals k table bn ** V293_create_internal_domain) **
 (LV 209%Z @ Tint8 |->err ** LV 108%Z @ (Tptr Tint32) |->psp **
 V293_create_internal_other_parameters target argv inputtop identity bottom size ext options ** R))by(clear -H;sep auto).
 eapply astar_mono in K;[ |apply V293_create_reject_global_views|intros st HS;exact HS].
 clear -K;sep auto.
Qed.
Lemma V293_create_enabled_entry : forall target argv inputtop p identity bottom size ext options
 cpu err psp bp bc R aop ir si ci,
 (Alvarenv 101%Z Tint8(bp,0%Z) ** Amapsto(bp,0%Z)Tint8 true(V293_byteval p)) **
 ((Alvarenv 109%Z Tint32(bc,0%Z) ** Amapsto(bc,0%Z)Tint32 true cpu) **
 (LV 209%Z @ Tint8 |->err ** LV 108%Z @ (Tptr Tint32) |->psp **
 (V293_create_internal_other_parameters target argv inputtop identity bottom size ext options **
 (V293_create_enabled_external R aop ir si ci ** V293_create_internal_domain)))) ==>
 V293_create_enabled_state bp bc p cpu
 (V293_create_reject_frame target argv inputtop identity bottom size ext options err psp R)aop ir si ci.
Proof.
 intros target argv inputtop p identity bottom size ext options cpu err psp bp bc R aop ir si ci.
 unfold V293_create_enabled_state,V293_create_enabled_locals,V293_create_enabled_external,
 V293_create_reject_frame. cbn[V293_rdy_raw_cells]. intros s H;sep auto.
Qed.
Lemma V293_create_enabled_return_cells : forall k target argv inputtop p identity bottom size ext options
 err psp bp bc R aop ir si ci result,
 V293_create_enabled_return k bp bc p
 (V293_create_reject_frame target argv inputtop identity bottom size ext options err psp R)aop ir si ci result ==>
 V293_create_internal_post_cells **
 ([|result=Some(Vint32(Int.repr(V293_create_rejection_code k)))|] **
 V293_create_enabled_external R aop ir si ci) ** V293_create_internal_domain.
Proof.
 intros k target argv inputtop p identity bottom size ext options err psp bp bc R aop ir si ci result s H.
 unfold V293_create_enabled_return in H. apply astar_l_apure_elim in H. destruct H as[Code H].
 unfold V293_create_enabled_state,V293_create_enabled_locals,V293_create_reject_frame in H.
 assert(K:s |= ((Alvarenv 101%Z Tint8(bp,0%Z) ** Amapsto(bp,0%Z)Tint8 true(V293_byteval p)) **
 (Alvarenv 109%Z Tint32(bc,0%Z) ** Amapsto(bc,0%Z)Tint32 true(Vint32 Int.zero))) **
 (<||aop||> ** OS[ir,true,si,ci] ** R ** LV 209%Z @ Tint8 |->err **
 LV 108%Z @ (Tptr Tint32) |->psp **
 V293_create_internal_other_parameters target argv inputtop identity bottom size ext options ** V293_create_internal_domain)).
 { cbn[V293_rdy_raw_cells]in *;clear -H;sep auto. }
 eapply astar_mono in K;[ |apply astar_mono;apply V293_create_raw_local|intros st HS;exact HS].
 assert(Ret:s |= V293_create_internal_pre_cells target argv inputtop p identity bottom size ext options **
 (V293_create_enabled_external R aop ir si ci ** V293_create_internal_domain)).
 { unfold V293_create_internal_pre_cells,V293_create_internal_locals,V293_create_enabled_external,
 V293_create_internal_other_parameters in *;clear -K;sep auto. }
 eapply astar_mono in Ret;[ |apply V293_create_internal_pre_to_post|intros st HS;exact HS].
 clear -Ret Code;sep auto.
Qed.
Theorem V293_OSTaskCreateExt_enabled_rejection_resources : forall Spec sd li I tid
 k table bn p n slot K R aop ir si ci(good:GoodFunAsrt R)
 target argv inputtop identity bottom size ext options sched hook tcb,
 V293_create_rejection_valid k p n -> (gettopis si<=INUM)%nat ->
 GoodFrm R -> (R ==> CurLINV li tid) ->
 (k<>V293_create_bad_priority ->
 Aisr ir ** invlth_isr I 0(gettopis si) <==> Aisr ir ** V293_create_borrowed k table bn p n slot K) ->
 InfRules Spec sd li I
 (fun result=>V293_create_internal_post_cells **
 getasrt(V293_create_enabled_fpost k R aop ir si ci good
 (V293_create_internal_values target argv inputtop p identity bottom size ext options)result[]tid) ** V293_create_internal_domain)Afalse
 (V293_create_internal_pre_cells target argv inputtop p identity bottom size ext options **
 V293_create_enabled_external R aop ir si ci ** V293_create_internal_domain)
 (V293_CreateExt_body 92%Z 99%Z 97%Z 98%Z sched hook tcb)Afalse tid.
Proof.
 intros Spec sd li I tid k table bn p n slot K R aop ir si ci good target argv inputtop identity bottom size ext options sched hook tcb Range Bound Frame HR Borrow.
 eapply conseq_rule;[apply V293_create_internal_unpack|intros s H;exact H| ].
 apply ex_intro_rule. intro cpu. apply ex_intro_rule. intro err.
 apply ex_intro_rule. intro psp. apply ex_intro_rule. intro bp. apply ex_intro_rule. intro bc.
 eapply conseq_rule;[apply V293_create_enabled_entry|intros s H;exact H| ].
 eapply r_conseq_rule with(r:=V293_create_enabled_return k bp bc p
 (V293_create_reject_frame target argv inputtop identity bottom size ext options err psp R)aop ir si ci)(ri:=Afalse).
 - intro result. cbn[V293_create_enabled_fpost getasrt]. apply V293_create_enabled_return_cells.
 - intros s H;exact H.
 - eapply V293_OSTaskCreateExt_enabled_rejection_body with(K:=K);try eassumption.
   + apply V293_create_reject_frame_good;exact Frame.
   + unfold V293_create_reject_frame. do 3 apply V293_star_CurLINV_r.
     apply V293_star_CurLINV_l. exact HR.
   + apply V293_create_enabled_frame_views.
Qed.

Theorem V293_OSTaskCreateExt_enabled_rejection_contract : forall P creator Spec sd li I tid
 k table bn p n slot K R aop isr is cs(good:GoodFunAsrt R)
 target argv inputtop identity bottom size ext options sched hook tcb vl lg pre post,
 V293_create_rejection_valid k p n -> (gettopis is<=INUM)%nat -> GoodFrm R -> (R ==> CurLINV li tid) ->
 (k<>V293_create_bad_priority ->
 Aisr isr ** invlth_isr I 0(gettopis is) <==> Aisr isr ** V293_create_borrowed k table bn p n slot K) ->
 P creator=Some(V293_CreateExt_function 92%Z 99%Z 97%Z 98%Z sched hook tcb) ->
 Some pre=BuildPreI P creator vl lg
 (V293_create_enabled_fpre target argv inputtop p identity bottom size ext options R aop isr is cs good)tid ->
 Some post=BuildRetI P creator vl lg(V293_create_enabled_fpost k R aop isr is cs good)tid ->
 InfRules Spec sd li I post Afalse pre
 (V293_CreateExt_body 92%Z 99%Z 97%Z 98%Z sched hook tcb)Afalse tid.
Proof.
 intros P creator Spec sd li I tid k table bn p n slot K R aop isr is cs good
 target argv inputtop identity bottom size ext options sched hook tcb vl lg pre post Range Bound Frame HR Borrow Code Pre Post.
 unfold BuildPreI in Pre. rewrite Code in Pre. cbn[V293_CreateExt_function]in Pre.
 destruct(dl_vl_match V293_CreateExt_parameters(rev vl))eqn:Typed;[ |discriminate].
 fold V293_create_internal_declarations in Pre.
 destruct(buildp V293_create_internal_declarations vl)as[owned | ]eqn:Owned;[ |discriminate].
 change(Some pre=Some(owned **
 ([|rev vl=V293_create_internal_values target argv inputtop p identity bottom size ext options|] **
 V293_create_enabled_external R aop isr is cs) ** V293_create_internal_domain))in Pre.
 inversion Pre;subst pre.
 unfold BuildRetI in Post. rewrite Code in Post.
 change(Some post=Some(fun result=>V293_create_internal_post_cells **
 getasrt(V293_create_enabled_fpost k R aop isr is cs good
 (V293_create_internal_values target argv inputtop p identity bottom size ext options)result[]tid) ** V293_create_internal_domain))in Post.
 inversion Post;subst post.
 eapply conseq_rule with(p:=(owned ** V293_create_enabled_external R aop isr is cs **
 V293_create_internal_domain) ** [|rev vl=V293_create_internal_values target argv inputtop p identity bottom size ext options|]).
 - intros s H. clear -H;sep auto.
 - intros s H;exact H.
 - apply pure_split_rule. intro Args.
   assert(VL:vl=rev(V293_create_internal_values target argv inputtop p identity bottom size ext options)).
   { rewrite <-Args. symmetry;apply rev_involutive. }
   subst vl. rewrite V293_create_internal_buildp in Owned. inversion Owned;subst owned.
   eapply V293_OSTaskCreateExt_enabled_rejection_resources with(good:=good)(K:=K);eassumption.
Qed.

Print Assumptions V293_OSTaskCreateExt_enabled_rejection_contract.
