(* Full original OS_TCBInit, NULL free-head restriction, enabled interrupts.
   Head ownership lives only in the borrowed ISR invariant, not the caller.
   This does not establish the production invariant or nonempty allocation. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.proofs.V293TCBEmptyInternal.
Require Import CertiOS.certiucos.v293.proofs.V293TCBEmptyHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TimeAccess.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.code.V293OSTCBInitFunction.
Require Import CertiOS.certiucos.v293.code.V293OSTCBInitPrefix.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.tactics.hoareforward.init_spec.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List.
Import ListNotations.

Definition V293_tcb_enabled_resources bf bp bc pc cpu R :=
 V293_tcb_empty_bindings bf bp bc **
 (Amapsto(bp,0%Z)(Tptr V293_tcb_type)true pc **
 (Amapsto(bc,0%Z)Tint32 true cpu ** R)).
Definition V293_tcb_enabled_state bf bp bc pc cpu R aop ir si ci :=
 <||aop||> ** OS[ir,true,si,ci] ** V293_tcb_enabled_resources bf bp bc pc cpu R.
Definition V293_tcb_empty_pool bf K :=
 Amapsto(bf,0%Z)(Tptr V293_tcb_type)false Vnull ** K.
Definition V293_tcb_enabled_post bf bp bc R aop ir si ci result :=
 [|result=Some(Vint32(Int.repr 66))|] **
 V293_tcb_enabled_state bf bp bc Vnull(Vint32 Int.zero)R aop ir si ci.
Lemma V293_tcb_enabled_good : forall bf bp bc pc cpu R,
 GoodFrm R -> GoodFrm(V293_tcb_enabled_resources bf bp bc pc cpu R).
Proof. intros. cbn[V293_tcb_enabled_resources V293_tcb_empty_bindings GoodFrm];tauto. Qed.

Lemma V293_tcb_enabled_cpu : forall Spec sd li I r ri tid bf bp bc pc cpu R aop ir si ci,
 (R ==> CurLINV li tid) ->
 InfRules Spec sd li I r ri
 (V293_tcb_enabled_state bf bp bc pc cpu R aop ir si ci)
 (sassign(evar 109%Z)(econst32 Int.zero))
 (V293_tcb_enabled_state bf bp bc pc(Vint32 Int.zero)R aop ir si ci)tid.
Proof.
 intros Spec sd li I r ri tid bf bp bc pc cpu R aop ir si ci HR.
 unfold V293_tcb_enabled_state,V293_tcb_enabled_resources.
 eapply conseq_rule with
 (p:=<||aop||> ** (OS[ir,true,si,ci] **
 (V293_tcb_empty_bindings bf bp bc ** (Amapsto(bp,0%Z)(Tptr V293_tcb_type)true pc ** R))) **
 Amapsto(bc,0%Z)Tint32 true cpu)
 (q:=<||aop||> ** (OS[ir,true,si,ci] **
 (V293_tcb_empty_bindings bf bp bc ** (Amapsto(bp,0%Z)(Tptr V293_tcb_type)true pc ** R))) **
 Amapsto(bc,0%Z)Tint32 true(Vint32 Int.zero)).
 - intros s H;sep auto.
 - intros s H;sep auto.
 - eapply assign_rule with(tp2:=Tint32)(l:=(bc,Int.zero)).
   + apply eq_int;auto.
   + intros s H.
     assert(B:s |= V293_tcb_empty_bindings bf bp bc ** Atrue)by(clear -H;sep auto).
     destruct(V293_tcb_empty_env _ _ _ _ B)as(_&C&_).
     destruct s as [[[[[[ge le] M] irq] aux] O] op].
     change(get le 109%Z=Some(bc,Tint32))in C.
     cbn[sat getsmem evaladdr evaltype evalval get_smem get_lenv].
     cbv delta[env var memory.ident Modules.ident]in *. rewrite C.
     repeat split;try reflexivity;discriminate.
   + apply V293_star_CurLINV_l. repeat apply V293_star_CurLINV_r. exact HR.
Qed.

Lemma V293_tcb_enabled_enter : forall Spec sd li I r ri tid bf bp bc pc cpu K R aop ir si ci,
 (gettopis si<=INUM)%nat -> GoodFrm R ->
 (Aisr ir ** invlth_isr I 0(gettopis si) ==> Aisr ir ** V293_tcb_empty_pool bf K) ->
 InfRules Spec sd li I r ri
 (V293_tcb_enabled_state bf bp bc pc cpu R aop ir si ci)(sprim encrit)
 (V293_tcb_empty_state bf bp bc pc cpu(K ** R)aop ir si(true::ci))tid.
Proof.
 intros Spec sd li I r ri tid bf bp bc pc cpu K R aop ir si ci Bound Frame Open.
 unfold V293_tcb_enabled_state. eapply conseq_rule with
 (p:=<||aop||> ** OS[ir,true,si,ci] ** ATopis(gettopis si) ** [|(gettopis si<=INUM)%nat|] **
 V293_tcb_enabled_resources bf bp bc pc cpu R)
 (q:=<||aop||> ** OS[ir,false,si,true::ci] ** invlth_isr I 0(gettopis si) **
 V293_tcb_enabled_resources bf bp bc pc cpu R).
 - intros s H. assert(S:s |= Ais si ** Atrue)by(clear -H;sep auto).
   pose proof(V293_time_topis si Atrue s S)as Top.
   apply astar_l_atopis_elim in Top. destruct Top as[Top _].
   pose proof(@astar_l_atopis_intro s(gettopis si)_ H Top)as HT.
   clear -HT Bound;sep auto.
 - intros s H.
   assert(B:s |= (Aisr ir ** invlth_isr I 0(gettopis si)) **
    (<||aop||> ** Aie false ** Ais si ** Acs(true::ci) ** V293_tcb_enabled_resources bf bp bc pc cpu R))by(clear -H;sep auto).
   eapply astar_mono in B;[ |exact Open|intros st HS;exact HS].
   unfold V293_tcb_empty_pool,V293_tcb_enabled_resources,V293_tcb_empty_state,V293_tcb_empty_resources in *.
   clear -B;sep auto.
 - apply encrit1_rule. apply V293_tcb_enabled_good;exact Frame.
Qed.

Lemma V293_tcb_enabled_exit : forall Spec sd li I r ri tid bf bp bc pc cpu K R aop ir si ci,
 GoodFrm R -> (R ==> CurLINV li tid) ->
 (Aisr ir ** V293_tcb_empty_pool bf K ==> Aisr ir ** invlth_isr I 0(gettopis si)) ->
 InfRules Spec sd li I r ri
 (V293_tcb_empty_state bf bp bc pc cpu(K ** R)aop ir si(true::ci))(sprim excrit)
 (V293_tcb_enabled_state bf bp bc pc cpu R aop ir si ci)tid.
Proof.
 intros Spec sd li I r ri tid bf bp bc pc cpu K R aop ir si ci Frame HR Close.
 eapply conseq_rule with
 (p:=<||aop||> ** OS[ir,false,si,true::ci] ** ATopis(gettopis si) ** invlth_isr I 0(gettopis si) **
 V293_tcb_enabled_resources bf bp bc pc cpu R)
 (q:=<||aop||> ** OS[ir,true,si,ci] ** V293_tcb_enabled_resources bf bp bc pc cpu R).
 - intros s H.
   assert(B:s |= (Aisr ir ** V293_tcb_empty_pool bf K) **
    (<||aop||> ** Aie false ** Ais si ** Acs(true::ci) ** V293_tcb_enabled_resources bf bp bc pc cpu R)).
   { unfold V293_tcb_empty_pool,V293_tcb_enabled_resources,V293_tcb_empty_state,V293_tcb_empty_resources in *.
     clear -H;sep auto. }
   eapply astar_mono in B;[ |exact Close|intros st HS;exact HS].
   assert(S:s |= Ais si ** Atrue)by(clear -B;sep auto).
   pose proof(V293_time_topis si Atrue s S)as Top.
   apply astar_l_atopis_elim in Top. destruct Top as[Top _].
   pose proof(@astar_l_atopis_intro s(gettopis si)_ B Top)as HT. clear -HT;sep auto.
 - unfold V293_tcb_enabled_state. intros s H;exact H.
 - apply excrit1_rule.
   + apply V293_tcb_enabled_good;exact Frame.
   + unfold V293_tcb_enabled_resources. repeat apply V293_star_CurLINV_r. exact HR.
Qed.

Theorem V293_OS_TCBInit_empty_enabled_body : forall Spec sd li I tid hi hc
 bf bp bc pc cpu K R aop ir si ci,
 (gettopis si<=INUM)%nat -> GoodFrm R -> (R ==> CurLINV li tid) ->
 (Aisr ir ** invlth_isr I 0(gettopis si) ==> Aisr ir ** V293_tcb_empty_pool bf K) ->
 (Aisr ir ** V293_tcb_empty_pool bf K ==> Aisr ir ** invlth_isr I 0(gettopis si)) ->
 InfRules Spec sd li I(V293_tcb_enabled_post bf bp bc R aop ir si ci)Afalse
 (V293_tcb_enabled_state bf bp bc pc cpu R aop ir si ci)
 (V293_TCBInit_function_body hi hc)Afalse tid.
Proof.
 intros Spec sd li I tid hi hc bf bp bc pc cpu K R aop ir si ci Bound Frame HR Open Close.
 unfold V293_TCBInit_function_body. eapply seq_rule.
 - apply V293_tcb_enabled_cpu;exact HR.
 - unfold V293_TCBInit_prefix. eapply seq_rule.
   + apply V293_tcb_enabled_enter with(K:=K);assumption.
   + eapply seq_rule.
     * apply V293_tcb_empty_pointer_hoare. apply V293_star_CurLINV_r;exact HR.
     * eapply seq_rule with(p':=V293_tcb_empty_state bf bp bc Vnull(Vint32 Int.zero)(K ** R)aop ir si(true::ci)).
       -- eapply ift_rule with(tp:=Tint32).
          ++ intros s H. exists(Vint32 Int.zero).
             destruct(V293_tcb_empty_guard_eval _ _ _ _ _ _ _ _ _ _ H)as[V T].
             cbn[sat]. split;[exact V| ]. split;[exact T|discriminate].
          ++ intros s[H _];exact H.
          ++ eapply conseq_rule with(p:=Afalse)(q:=Afalse).
             ** intros s[H[v[V B]]].
                destruct(V293_tcb_empty_guard_eval _ _ _ _ _ _ _ _ _ _ H)as[Z _].
                rewrite Z in V. inversion V;subst v. discriminate B.
             ** intros s H;contradiction.
             ** apply pfalse_rule.
       -- unfold V293_TCBInit_empty. eapply seq_rule.
          ++ apply V293_tcb_enabled_exit;assumption.
          ++ apply rete_rule with(v:=Vint32(Int.repr 66))(t:=Tint32).
             intros s H. split.
             ** unfold V293_tcb_enabled_post. apply astar_l_apure_intro;[exact H|reflexivity].
             ** destruct s as [[[[[[ge le] M] irq] aux] O] op].
                cbn[sat evalval evaltype getsmem get_smem]. repeat split;try reflexivity;discriminate.
Qed.
Print Assumptions V293_OS_TCBInit_empty_enabled_body.

(* Exact seven-parameter/two-local interface; external resources contain no head bytes. *)
Definition V293_tcb_enabled_external bf R aop isr is cs :=
 Agvarenv 91%Z (Tptr V293_tcb_type) (bf,0%Z) **
 (<||aop||> ** OS[isr,true,is,cs] ** R).
Lemma V293_tcb_enabled_external_good : forall bf R aop isr is cs,
 GoodFunAsrt R -> GoodFunAsrt(V293_tcb_enabled_external bf R aop isr is cs).
Proof. intros. cbn [V293_tcb_enabled_external GoodFunAsrt]. tauto. Qed.
Definition V293_tcb_enabled_fpre bf R aop isr is cs (good:GoodFunAsrt R) : fpre :=
 fun vl lg tid => @mkfunasrt (V293_tcb_enabled_external bf R aop isr is cs)
 (V293_tcb_enabled_external_good bf R aop isr is cs good).
Definition V293_tcb_enabled_fpost bf R aop isr is cs (good:GoodFunAsrt R) : fpost :=
 fun vl result lg tid => @mkfunasrt
 ([|result=Some(Vint32(Int.repr 66))|] ** V293_tcb_enabled_external bf R aop isr is cs)
 (conj I (V293_tcb_enabled_external_good bf R aop isr is cs good)).

Lemma V293_tcb_enabled_internal_entry : forall bf bp bc pc cpu v1 v2 v3 v4 v5 v6 v7 R aop isr is cs,
 Alvarenv 108%Z (Tptr V293_tcb_type) (bp,0%Z) **
 (Amapsto (bp,0%Z) (Tptr V293_tcb_type) true pc **
 (Alvarenv 109%Z Tint32 (bc,0%Z) ** (Amapsto (bc,0%Z) Tint32 true cpu **
 (V293_tcb_internal_parameters v1 v2 v3 v4 v5 v6 v7 **
 (V293_tcb_enabled_external bf R aop isr is cs ** V293_tcb_internal_domain))))) ==>
 V293_tcb_enabled_state bf bp bc pc cpu
 (V293_tcb_empty_internal_frame v1 v2 v3 v4 v5 v6 v7 R) aop isr is cs.
Proof.
 intros bf bp bc pc cpu v1 v2 v3 v4 v5 v6 v7 R aop isr is cs s HS. unfold V293_tcb_enabled_external in HS.
 assert (Reordered : s |=
 ((Alvarenv 108%Z (Tptr V293_tcb_type) (bp,0%Z) **
 (Alvarenv 109%Z Tint32 (bc,0%Z) ** Agvarenv 91%Z (Tptr V293_tcb_type) (bf,0%Z))) **
 V293_tcb_internal_domain) **
 (Amapsto (bp,0%Z) (Tptr V293_tcb_type) true pc **
 (Amapsto (bc,0%Z) Tint32 true cpu **
 (<||aop||> ** OS[isr,true,is,cs] **
 (V293_tcb_internal_parameters v1 v2 v3 v4 v5 v6 v7 ** R))))).
 { clear -HS. sep auto. }
 eapply astar_mono in Reordered.
 2: { apply V293_tcb_empty_internal_bindings. }
 2: { intros st H;exact H. }
 unfold V293_tcb_enabled_state,V293_tcb_enabled_resources,V293_tcb_empty_internal_frame.
 clear -Reordered. sep auto.
Qed.

Lemma V293_tcb_enabled_internal_exit : forall bf bp bc v1 v2 v3 v4 v5 v6 v7 R aop isr is cs result,
 V293_tcb_enabled_post bf bp bc
 (V293_tcb_empty_internal_frame v1 v2 v3 v4 v5 v6 v7 R) aop isr is cs result ==>
 V293_tcb_internal_post_cells **
 ([|result=Some(Vint32(Int.repr 66))|] ** V293_tcb_enabled_external bf R aop isr is cs) **
 V293_tcb_internal_domain.
Proof.
 intros bf bp bc v1 v2 v3 v4 v5 v6 v7 R aop isr is cs result s H.
 unfold V293_tcb_enabled_post in H. apply astar_l_apure_elim in H.
 destruct H as [Code H].
 unfold V293_tcb_enabled_state,V293_tcb_enabled_resources,V293_tcb_empty_internal_frame in H.
 assert (EnvFrame : s |= V293_tcb_empty_bindings bf bp bc **
 (<||aop||> ** OS[isr,true,is,cs] **
 (Amapsto (bp,0%Z) (Tptr V293_tcb_type) true Vnull **
 (Amapsto (bc,0%Z) Tint32 true (Vint32 Int.zero) **
 (V293_tcb_internal_parameters v1 v2 v3 v4 v5 v6 v7 **
 (V293_tcb_internal_domain ** R)))))).
 { clear -H. sep auto. }
 eapply astar_mono in EnvFrame.
 2: { apply V293_tcb_empty_internal_return_bindings. }
 2: { intros st HS;exact HS. }
 clear H. rename EnvFrame into H.
 assert (Reordered : s |= V293_tcb_internal_parameters v1 v2 v3 v4 v5 v6 v7 **
 (((Alvarenv 108%Z (Tptr V293_tcb_type) (bp,0%Z) **
 Amapsto (bp,0%Z) (Tptr V293_tcb_type) true Vnull) **
 ((Alvarenv 109%Z Tint32 (bc,0%Z) **
 Amapsto (bc,0%Z) Tint32 true (Vint32 Int.zero)) ** Aemp)) **
 (V293_tcb_enabled_external bf R aop isr is cs ** V293_tcb_internal_domain))).
 { unfold V293_tcb_enabled_external. clear -H. sep auto. }
 eapply astar_mono in Reordered.
 2: { apply V293_tcb_internal_parameter_return. }
 2: { apply astar_mono;[ |intros st HS;exact HS].
      apply astar_mono;[apply V293_tcb_internal_local_return| ].
      apply astar_mono;[apply V293_tcb_internal_local_return|intros st HS;exact HS]. }
 unfold V293_tcb_internal_parameter_post,V293_tcb_internal_post_cells,V293_tcb_internal_locals in *.
 clear -Reordered Code. sep auto.

Qed.

Theorem V293_OS_TCBInit_empty_enabled_resources : forall Spec sd li I tid hi hc bf K R aop isr is cs
 v1 v2 v3 v4 v5 v6 v7,
 (gettopis is<=INUM)%nat -> GoodFrm R -> (R ==> CurLINV li tid) ->
 (Aisr isr ** invlth_isr I 0(gettopis is) ==> Aisr isr ** V293_tcb_empty_pool bf K) ->
 (Aisr isr ** V293_tcb_empty_pool bf K ==> Aisr isr ** invlth_isr I 0(gettopis is)) ->
 InfRules Spec sd li I
 (fun result => V293_tcb_internal_post_cells **
 ([|result=Some(Vint32(Int.repr 66))|] ** V293_tcb_enabled_external bf R aop isr is cs) **
 V293_tcb_internal_domain) Afalse
 (V293_tcb_internal_pre_cells v1 v2 v3 v4 v5 v6 v7 **
 V293_tcb_enabled_external bf R aop isr is cs ** V293_tcb_internal_domain)
 (V293_TCBInit_function_body hi hc) Afalse tid.
Proof.
 intros Spec sd li I tid hi hc bf K R aop isr is cs v1 v2 v3 v4 v5 v6 v7 Bound Frame HR Open Close.
 eapply conseq_rule.
 - intros s H. exact (V293_tcb_empty_internal_unpack v1 v2 v3 v4 v5 v6 v7
   (V293_tcb_enabled_external bf R aop isr is cs ** V293_tcb_internal_domain) s H).
 - intros s H;exact H.
 - apply ex_intro_rule. intro pc. apply ex_intro_rule. intro cpu.
   apply ex_intro_rule. intro bp. apply ex_intro_rule. intro bc.
   eapply conseq_rule;[apply V293_tcb_enabled_internal_entry|intros s H;exact H| ].
   eapply r_conseq_rule with (r:=V293_tcb_enabled_post bf bp bc
    (V293_tcb_empty_internal_frame v1 v2 v3 v4 v5 v6 v7 R) aop isr is cs) (ri:=Afalse).
   + intro result. apply V293_tcb_enabled_internal_exit.
   + intros s H;exact H.
   + apply V293_OS_TCBInit_empty_enabled_body with(K:=K).
     * exact Bound.
     * apply V293_tcb_empty_internal_frame_good;assumption.
     * apply V293_tcb_empty_internal_frame_linv;assumption.
     * exact Open.
     * exact Close.
Qed.

Theorem V293_OS_TCBInit_empty_enabled_contract : forall P f Spec sd li I tid hi hc
 bf K R aop isr is cs (good:GoodFunAsrt R) vl lg pre post,
 (gettopis is<=INUM)%nat -> GoodFrm R -> (R ==> CurLINV li tid) ->
 (Aisr isr ** invlth_isr I 0(gettopis is) ==> Aisr isr ** V293_tcb_empty_pool bf K) ->
 (Aisr isr ** V293_tcb_empty_pool bf K ==> Aisr isr ** invlth_isr I 0(gettopis is)) ->
 P f=Some(V293_TCBInit_function hi hc) ->
 Some pre=BuildPreI P f vl lg (V293_tcb_enabled_fpre bf R aop isr is cs good) tid ->
 Some post=BuildRetI P f vl lg (V293_tcb_enabled_fpost bf R aop isr is cs good) tid ->
 InfRules Spec sd li I post Afalse pre (V293_TCBInit_function_body hi hc) Afalse tid.
Proof.
 intros P f Spec sd li I tid hi hc bf K R aop isr is cs good vl lg pre post Bound Frame HR Open Close Code Pre Post.
 unfold BuildPreI in Pre. rewrite Code in Pre.
 cbn [V293_TCBInit_function] in Pre.
 destruct (dl_vl_match V293_TCBInit_parameters (rev vl)) eqn:Typed;[ |discriminate].
 pose proof(dl_vl_match_dv_same_length _ _ Typed) as Length.
 rewrite rev_length in Length. cbn [V293_TCBInit_parameters decllen] in Length.
 destruct vl as [ |v7 vl];[discriminate Length| ].
 destruct vl as [ |v6 vl];[discriminate Length| ].
 destruct vl as [ |v5 vl];[discriminate Length| ].
 destruct vl as [ |v4 vl];[discriminate Length| ].
 destruct vl as [ |v3 vl];[discriminate Length| ].
 destruct vl as [ |v2 vl];[discriminate Length| ].
 destruct vl as [ |v1 vl];[discriminate Length| ].
 destruct vl;[ |discriminate Length].
 fold V293_tcb_internal_declarations in Pre.
 rewrite V293_tcb_internal_buildp in Pre.
 change (Some pre=Some(V293_tcb_internal_pre_cells v1 v2 v3 v4 v5 v6 v7 **
 V293_tcb_enabled_external bf R aop isr is cs ** V293_tcb_internal_domain)) in Pre.
 inversion Pre;subst pre.
 unfold BuildRetI in Post. rewrite Code in Post.
 change (Some post=Some(fun result => V293_tcb_internal_post_cells **
 ([|result=Some(Vint32(Int.repr 66))|] ** V293_tcb_enabled_external bf R aop isr is cs) **
 V293_tcb_internal_domain)) in Post.
 inversion Post;subst post.
 apply V293_OS_TCBInit_empty_enabled_resources with(K:=K);assumption.
Qed.

Print Assumptions V293_OS_TCBInit_empty_enabled_contract.
