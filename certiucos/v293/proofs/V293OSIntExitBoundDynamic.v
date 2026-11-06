Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitBody.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitResourceCodec.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitResourceBridge.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitChangedInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitUnifiedInternal.
Require Import CertiOS.certiucos.v293.proofs.V293SpecEmbedding.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedJoint.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCritical.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedISRContext.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedSwitch.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedShared.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitBoundarySwitch.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitBuilders.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptExitEnvironment.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptFunctionEnvironment.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntEnterInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewInternal.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.certiucos.v293.code.V293OSIntEnter.
Require Import CertiOS.certiucos.v293.code.V293OSSchedNew.
Require Import CertiOS.framework.proof.auxdef.
Require Import CertiOS.framework.proof.toptheorem.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import Coq.Lists.List.
Import ListNotations.
Local Open Scope nat_scope.

Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitAllInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedStoragePrefix.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchStorage.
Require Import CertiOS.tactics.sepauto.seplog_tactics.

Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitDynamic.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitReadyInternal.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyStorageInvariant.

Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitReadyDynamic.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitExactInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedExactLocal.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedExactJoint.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptReadyLocal.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptReadyEnvironment.

Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitQuietExact.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitExactDynamic.

Require Import CertiOS.certiucos.v293.proofs.V293OSSchedAllExactJoint.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedISRExact.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitSameExactInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitSameInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitQuietExactDynamic.

Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitBoundInternal.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptBindings.
Section BoundDynamic.
Variables unmap group rows high table target current counter running nesting lock saved:var.
Variables bt bg br bh bp bo bc bk brun bn bl:block.
Variable rest:list(addr*type).
Variable extra:asrt.
Variable EG:GoodFunAsrt extra.
Let tp:=V293_tcb_type.
Let Inv0:=V293_ready_dynamic_exit_inv target bt bg br bh bp bc bk brun bn bl rest.
Let li:=V293_irq_bound_li running nesting lock brun bn bl.
Let Hli:=V293_irq_bound_good running nesting lock brun bn bl.
Let changedfq x:=V293_bound_builder_fpost unmap group rows high table target current counter running nesting lock
 bt bg br bh bp bo bc bk brun bn bl rest(V293_caop x)(V293_cstack x)(V293_ccritical x)extra EG.
Definition V293_bound_dynamic_changed_fpost:fpost:=fun vl result lg t=>
 match V293_changed_decode lg with
 | Some x=>changedfq x vl result nil t
 | None=>@mkfunasrt Afalse Logic.I end.
Let changedpre:=V293_ready_dynamic_changed_fpre unmap group rows high table target current counter running nesting lock
 bt bg br bh bp bo bc bk brun bn bl rest extra EG.
Let cfp:=V293_sched_exact_fpre unmap group rows high bt bg br bh li V293_opened_inv Hli.
Let cfq:=V293_sched_exact_fpost unmap group rows high bt bg br bh li V293_opened_inv Hli.
Let ifp:=V293_ISR_exact_sched_fpre unmap group rows high bt bg br bh li Inv0 Hli.
Let ifq:=V293_ISR_exact_sched_fpost unmap group rows high bt bg br bh li Inv0 Hli.
Let sfp:=V293_all_exact_joint_sched_fpre unmap group rows high bt bg br bh li V293_opened_inv Inv0 Hli.
Let sfq:=V293_all_exact_joint_sched_fpost unmap group rows high bt bg br bh li V293_opened_inv Inv0 Hli.
Let cexitfp:=V293_ready_dynamic_changed_fpre unmap group rows high table target current counter running nesting lock
 bt bg br bh bp bo bc bk brun bn bl rest extra EG.
Let cexitfq:=V293_bound_dynamic_changed_fpost.
Let qfp:=V293_quiet_exact_exit_fpre running nesting lock brun bn bl li extra Hli EG.
Let qfq:=V293_quiet_exact_exit_fpost running nesting lock brun bn bl li extra Hli EG.
Let xfp:=V293_same_exact_exit_fpre unmap group rows high table target current counter nesting lock running
 bt bg br bh bp bo bc bk bn bl brun tp li extra Hli EG.
Let xfq:=V293_same_exact_exit_fpost unmap group rows high table target current counter nesting lock running
 bt bg br bh bp bo bc bk bn bl brun tp li extra Hli EG.
Definition V293_bound_dynamic_fpre:fpre:=fun vl lg t=>
 match V293_exit_path lg with
 | Some(true,args)=>cexitfp vl args t
 | Some(false,args)=>match V293_exit_path args with
   | Some(true,qlg)=>qfp vl qlg t
   | Some(false,slg)=>xfp vl slg t
   | None=>@mkfunasrt Afalse Logic.I end
 | None=>@mkfunasrt Afalse Logic.I end.
Definition V293_bound_dynamic_fpost:fpost:=fun vl result lg t=>
 match V293_exit_path lg with
 | Some(true,args)=>cexitfq vl result args t
 | Some(false,args)=>match V293_exit_path args with
   | Some(true,qlg)=>qfq vl result qlg t
   | Some(false,slg)=>xfq vl result slg t
   | None=>@mkfunasrt Afalse Logic.I end
 | None=>@mkfunasrt Afalse Logic.I end.
Lemma V293_bound_dynamic_changed_contract : forall P f Spec sched_id vl lg t pre post,
 table<>saved ->high<>saved ->target<>saved ->current<>saved ->
 counter<>saved ->nesting<>saved ->lock<>saved ->running<>saved ->GoodFrm extra ->
 Spec sched_id=Some(cfp,cfq,(Tvoid,nil)) ->
 P f=Some(V293_exit_boundary_function running nesting lock saved table high target current counter sched_id
 (V293_interrupt_handoff high current target)) ->
 Some pre=BuildPreI P f vl lg changedpre t ->
 Some post=BuildRetI P f vl lg V293_bound_dynamic_changed_fpost t ->
 InfRules Spec V293_scheduler li Inv0 post Afalse pre
 (V293_exit_boundary_body running nesting lock saved table high target current counter sched_id
 (V293_interrupt_handoff high current target)) Afalse t.
Proof.
 intros P f Spec sched_id vl lg t pre post T H G C K N L R GF Lookup Code Pre Post.
 unfold BuildPreI in Pre;rewrite Code in Pre;destruct vl as[ |v vl].
 2:{ assert(E:dl_vl_match dnil(rev(v::vl))=false).
     { destruct(rev(v::vl))eqn:Rev;[ |reflexivity].
       apply(f_equal(@rev val))in Rev;rewrite rev_involutive in Rev;discriminate. }
     unfold V293_exit_boundary_function in Pre;rewrite E in Pre;discriminate. }
 change(Some pre=Some(V293_exit_builder_cells saved **
 getasrt(changedpre nil lg t) ** V293_exit_builder_domain saved))in Pre.
 unfold BuildRetI in Post;rewrite Code in Post.
 change(Some post=Some(fun result=>V293_exit_builder_cells saved **
 getasrt(V293_bound_dynamic_changed_fpost nil result lg t) ** V293_exit_builder_domain saved))in Post.
 unfold changedpre,V293_ready_dynamic_changed_fpre in Pre;unfold V293_bound_dynamic_changed_fpost in Post.
 destruct(V293_changed_decode lg)as[x| ]eqn:Decode.
 - inversion Pre;subst pre;inversion Post;subst post.
   eapply (V293_OSIntExit_bound_builder_contract
     unmap group rows high table target current counter running nesting lock saved
     bt bg br bh bp bo bc bk brun bn bl
     (Z.to_nat(Int.unsigned(V293_clo x)))(Z.to_nat(Int.unsigned(V293_chi x)))
     (Z.to_nat(Int.unsigned(V293_ccurrent x)))(Z.to_nat(Int.unsigned(V293_cnest x)))
     (V293_centries x)rest(V293_ctasks x)(V293_cevents x)(V293_cnow x)(V293_chigh x)(V293_cout x)
     (V293_ccounter x)(V293_caop x)(V293_cstack x)(V293_ccritical x)extra EG
     P f Spec sched_id nil nil t);try eassumption;
     unfold BuildPreI,BuildRetI;rewrite Code;reflexivity.
 - inversion Pre;subst pre;eapply conseq_rule with(p:=Afalse)(q:=Afalse).
   + intros st HS;apply astar_comm in HS;apply astar_assoc_elim in HS;
     apply astar_l_afalse_elim in HS;exact HS.
   + intros st HS;exact HS.
   + apply pfalse_rule.
Qed.

Theorem V293_OSIntExit_bound_dynamic_contract : forall P f Spec sched_id vl lg t pre post,
 table<>saved ->high<>saved ->target<>saved ->current<>saved ->
 counter<>saved ->nesting<>saved ->lock<>saved ->running<>saved ->GoodFrm extra ->
 Spec sched_id=Some(sfp,sfq,(Tvoid,nil)) ->
 P f=Some(V293_exit_boundary_function running nesting lock saved table high target current counter sched_id
 (V293_interrupt_handoff high current target)) ->
 Some pre=BuildPreI P f vl lg V293_bound_dynamic_fpre t ->
 Some post=BuildRetI P f vl lg V293_bound_dynamic_fpost t ->
 InfRules Spec V293_scheduler li Inv0 post Afalse pre
 (V293_exit_boundary_body running nesting lock saved table high target current counter sched_id
 (V293_interrupt_handoff high current target)) Afalse t.
Proof.
 intros P f Spec sched_id vl lg t pre post T H G C K N L R GF Lookup Code Pre Post.
 unfold BuildPreI in Pre;rewrite Code in Pre;destruct vl as[ |v vl].
 2:{ assert(E:dl_vl_match dnil(rev(v::vl))=false).
     { destruct(rev(v::vl))eqn:Rev;[ |reflexivity].
       apply(f_equal(@rev val))in Rev;rewrite rev_involutive in Rev;discriminate. }
     unfold V293_exit_boundary_function in Pre;rewrite E in Pre;discriminate. }
 change(Some pre=Some(V293_exit_builder_cells saved **
 getasrt(V293_bound_dynamic_fpre nil lg t) ** V293_exit_builder_domain saved))in Pre.
 unfold BuildRetI in Post;rewrite Code in Post.
 change(Some post=Some(fun result=>V293_exit_builder_cells saved **
 getasrt(V293_bound_dynamic_fpost nil result lg t) ** V293_exit_builder_domain saved))in Post.
 unfold V293_bound_dynamic_fpre in Pre;unfold V293_bound_dynamic_fpost in Post.
 destruct(V293_exit_path lg)as[[outer args]| ]eqn:Outer.
 - destruct outer.
   + eapply V293_InfRules_spec_embedding with(source:=V293_spec_override Spec sched_id cfp cfq(Tvoid,nil)).
     * eapply V293_bound_dynamic_changed_contract with(vl:=nil)(lg:=args);try eassumption.
       -- unfold V293_spec_override;destruct(Z.eq_dec sched_id sched_id);[reflexivity|contradiction].
       -- unfold BuildPreI;rewrite Code;exact Pre.
       -- unfold BuildRetI;rewrite Code;exact Post.
     * apply(V293_exact_critical_to_all_joint unmap group rows high bt bg br bh li V293_opened_inv Inv0 Hli);exact Lookup.
     * apply V293_exit_handoff_void_calls.
   + destruct(V293_exit_path args)as[[inner slg]| ]eqn:Inner.
     * destruct inner.
       -- eapply V293_OSIntExit_quiet_exact_builder_contract with(vl:=nil)(lg:=slg);try eassumption;
          unfold BuildPreI,BuildRetI;rewrite Code;try exact Post;exact Pre.
       -- eapply V293_InfRules_spec_embedding with(source:=V293_spec_override Spec sched_id ifp ifq(Tvoid,nil)).
          ++ eapply V293_OSIntExit_same_exact_builder_contract with(vl:=nil)(lg:=slg);try eassumption.
             ** unfold V293_spec_override;destruct(Z.eq_dec sched_id sched_id);[reflexivity|contradiction].
             ** unfold BuildPreI;rewrite Code;exact Pre.
             ** unfold BuildRetI;rewrite Code;exact Post.
          ++ apply(V293_exact_ISR_to_all_joint unmap group rows high bt bg br bh li V293_opened_inv Inv0 Hli);exact Lookup.
          ++ apply V293_exit_handoff_void_calls.
     * inversion Pre;subst pre;eapply conseq_rule with(p:=Afalse)(q:=Afalse).
       -- intros st HS;apply astar_comm in HS;apply astar_assoc_elim in HS;apply astar_l_afalse_elim in HS;exact HS.
       -- intros st HS;exact HS.
       -- apply pfalse_rule.
 - inversion Pre;subst pre;eapply conseq_rule with(p:=Afalse)(q:=Afalse).
   + intros st HS;apply astar_comm in HS;apply astar_assoc_elim in HS;apply astar_l_afalse_elim in HS;exact HS.
   + intros st HS;exact HS.
   + apply pfalse_rule.
Qed.
Lemma V293_bound_dynamic_pre_local : forall vl lg t,
 getasrt(V293_bound_dynamic_fpre vl lg t) ==>CurLINV li t.
Proof.
 intros vl lg t;unfold V293_bound_dynamic_fpre.
 destruct(V293_exit_path lg)as[[outer args]| ];[destruct outer| ].
 - unfold cexitfp,V293_ready_dynamic_changed_fpre.
   destruct(V293_changed_decode args)as[x| ];cbn[getasrt].
   + intros st H;eapply V293_bound_builder_pre_local;exact H.
   + intros st H;contradiction.
 - destruct(V293_exit_path args)as[[inner sub]| ];[destruct inner| ].
   + unfold qfp,V293_quiet_exact_exit_fpre,V293_quiet_exact_exit_pre.
     destruct(V293_quiet_exit_index sub)as[[[[[[[[run nest]locked]aop]enabled]ir]si]ci]| ];cbn[getasrt].
     * intros st H.
       assert(C:st |=p_local li t nil ** Atrue)
       by(unfold V293_quiet_exact_external,V293_exit_cells,V293_interrupt_cells in H;
          cbn[V293_rdy_raw_cells]in H;clear -H;sep auto).
       eapply V293_star_CurLINV_l;[apply V293_exact_local_weakens|exact C].
     * intros st H;contradiction.
   + unfold xfp,V293_same_exact_exit_fpre,V293_same_exact_exit_pre.
     destruct(V293_same_exit_index sub)as[[[[[enabled ir]si]ci]x]| ];cbn[getasrt].
     * intros st H.
       assert(C:st |=p_local li t nil ** Atrue)
       by(unfold V293_same_exact_exit_external,V293_same_exact_exit_memory in H;clear -H;sep auto).
       eapply V293_star_CurLINV_l;[apply V293_exact_local_weakens|exact C].
     * intros st H;contradiction.
   + intros st H;contradiction.
 - intros st H;contradiction.
Qed.
Lemma V293_bound_dynamic_post_local : forall vl result lg t,
 getasrt(V293_bound_dynamic_fpost vl result lg t) ==>CurLINV li t.
Proof.
 intros vl result lg t;unfold V293_bound_dynamic_fpost.
 destruct(V293_exit_path lg)as[[outer args]| ];[destruct outer| ].
 - unfold cexitfq,V293_bound_dynamic_changed_fpost.
   destruct(V293_changed_decode args)as[x| ];cbn[getasrt].
   + intros st H;eapply V293_bound_builder_post_local;exact H.
   + intros st H;contradiction.
 - destruct(V293_exit_path args)as[[inner sub]| ];[destruct inner| ].
   + unfold qfq,V293_quiet_exact_exit_fpost,V293_quiet_exact_exit_post.
     destruct(V293_quiet_exit_index sub)as[[[[[[[[run nest]locked]aop]enabled]ir]si]ci]| ];cbn[getasrt].
     * intros st H.
       assert(C:st |=p_local li t nil ** Atrue)
       by(unfold V293_quiet_exact_external,V293_exit_cells,V293_interrupt_cells in H;
          cbn[V293_rdy_raw_cells]in H;clear -H;sep auto).
       eapply V293_star_CurLINV_l;[apply V293_exact_local_weakens|exact C].
     * intros st H;contradiction.
   + unfold xfq,V293_same_exact_exit_fpost,V293_same_exact_exit_post.
     destruct(V293_same_exit_index sub)as[[[[[enabled ir]si]ci]x]| ];cbn[getasrt].
     * intros st H.
       assert(C:st |=p_local li t nil ** Atrue)
       by(unfold V293_same_exact_exit_external,V293_same_exact_exit_memory in H;clear -H;sep auto).
       eapply V293_star_CurLINV_l;[apply V293_exact_local_weakens|exact C].
     * intros st H;contradiction.
   + intros st H;contradiction.
 - intros st H;contradiction.
Qed.
Theorem V293_OSIntExit_bound_dynamic_call : forall Spec sd RI r ri exit t lg callerframe,
 GoodFrm callerframe ->
 Spec exit=Some(V293_bound_dynamic_fpre,V293_bound_dynamic_fpost,(Tvoid,nil)) ->
 InfRules Spec sd li RI r ri
 (getasrt(V293_bound_dynamic_fpre nil lg t) ** callerframe)
 (scall exit nil)
 (EX result:option val,getasrt(V293_bound_dynamic_fpost nil result lg t) ** callerframe)t.
Proof.
 intros Spec sd RI r ri exit t lg callerframe GF Lookup.
 eapply call_rule with(pre:=V293_bound_dynamic_fpre)(post:=V293_bound_dynamic_fpost)
 (vl:=nil)(logicl:=lg)(tp:=Tvoid)(tl:=nil).
 - exact GF.
 - exact Lookup.
 - intros st H;exact H.
 - intros st H;reflexivity.
 - reflexivity.
 - apply V293_bound_dynamic_pre_local.
 - intros st[result H];eapply V293_bound_dynamic_post_local;exact H.
Qed.
End BoundDynamic.
Section BoundDynamicEnvironment.
Variables unmap group rows high table target current counter running nesting lock saved:var.
Variables bt bg br bh bp bo bc bk brun bn bl:block.
Variable rest:list(addr*type).
Variable extra:asrt.
Variable EG:GoodFunAsrt extra.
Let tp:=V293_tcb_type.
Let Inv0:=V293_ready_dynamic_exit_inv target bt bg br bh bp bc bk brun bn bl rest.
Let li:=V293_irq_bound_li running nesting lock brun bn bl.
Let Hli:=V293_irq_bound_good running nesting lock brun bn bl.
Let efp:=V293_enter_bound_fpre running nesting lock brun bn bl Aemp Logic.I.
Let efq:=V293_enter_bound_fpost running nesting lock brun bn bl Aemp Logic.I.
Let xfp:=V293_bound_dynamic_fpre unmap group rows high table target current counter running nesting lock
 bt bg br bh bp bo bc bk brun bn bl rest extra EG.
Let xfq:=V293_bound_dynamic_fpost unmap group rows high table target current counter running nesting lock
 bt bg br bh bp bo bc bk brun bn bl rest extra EG.
Let sfp:=V293_all_exact_joint_sched_fpre unmap group rows high bt bg br bh li V293_opened_inv Inv0 Hli.
Let sfq:=V293_all_exact_joint_sched_fpost unmap group rows high bt bg br bh li V293_opened_inv Inv0 Hli.
Definition V293_bound_dynamic_spec exit enter sched:funspec:=
 fun f=>if Z.eq_dec f exit then Some(xfp,xfq,(Tvoid,nil))
 else if Z.eq_dec f enter then Some(efp,efq,(Tvoid,nil))
 else if Z.eq_dec f sched then Some(sfp,sfq,(Tvoid,nil))else None.
Lemma V293_bound_dynamic_domains : forall exit enter sched y,
 EqDom(V293_ready_irq_unit unmap group rows high table target current counter running nesting lock saved exit enter sched y)(V293_bound_dynamic_spec exit enter sched).
Proof.
 intros exit enter sched y f.
 unfold V293_ready_irq_unit,V293_exit_env_unit,V293_irq_internal_unit,pumerge,
 V293_OSIntEnter_unit,V293_OSSchedNew_internal_unit,V293_bound_dynamic_spec.
 destruct(Z.eq_dec f exit),(Z.eq_dec f enter),(Z.eq_dec f sched);
 split;intros[x H];try discriminate;eexists;reflexivity.
Qed.
Theorem V293_bound_dynamic_WFFunEnv : forall exit enter sched y,
 exit<>enter ->exit<>sched ->enter<>sched ->
 unmap<>y ->group<>y ->rows<>y ->high<>y ->
 table<>saved ->high<>saved ->target<>saved ->current<>saved ->
 counter<>saved ->nesting<>saved ->lock<>saved ->running<>saved ->
 GoodFrm extra ->
 WFFunEnv(V293_ready_irq_unit unmap group rows high table target current counter running nesting lock saved exit enter sched y)(V293_bound_dynamic_spec exit enter sched)
 V293_scheduler li Inv0.
Proof.
 intros exit enter sched y XE XS ES UY GY RY HY T H G C K N L R GF.
 pose proof(V293_exit_env_entries exit enter sched running nesting unmap group rows high y saved
 (V293_exit_boundary_body running nesting lock saved table high target current counter sched
 (V293_interrupt_handoff high current target)) XE XS ES)as(CodeX&CodeE&CodeS).
 assert(Sched:V293_bound_dynamic_spec exit enter sched sched=Some(sfp,sfq,(Tvoid,nil))).
 { unfold V293_bound_dynamic_spec;repeat destruct Z.eq_dec;try congruence;reflexivity. }
 split;[apply V293_bound_dynamic_domains| ].
 intros f pre post t tl Lookup;unfold V293_bound_dynamic_spec in Lookup.
 destruct(Z.eq_dec f exit)as[E|NE].
 - subst f;inversion Lookup;subst pre post t tl.
   exists dnil;exists(dcons saved Tint32 dnil).
   exists(V293_exit_boundary_body running nesting lock saved table high target current counter sched
   (V293_interrupt_handoff high current target)).
   split;[exact CodeX| ];split;[constructor| ];split;[reflexivity| ].
   intros vl p q lg t Pre Post.
   eapply V293_OSIntExit_bound_dynamic_contract;try eassumption.
 - destruct(Z.eq_dec f enter)as[E|NEE].
   + subst f;inversion Lookup;subst pre post t tl.
     exists dnil;exists dnil;exists(V293_OSIntEnter_body running nesting).
     split;[exact CodeE| ];split;[constructor| ];split;[reflexivity| ].
     intros vl p q lg t Pre Post.
     eapply V293_OSIntEnter_bound_contract;try eassumption.
   + destruct(Z.eq_dec f sched)as[E|NES];[ |discriminate].
     subst f;inversion Lookup;subst pre post t tl.
     exists dnil;exists(dcons y Tint8 dnil);exists(V293_OSSchedNew_body unmap group rows high y).
     split;[exact CodeS| ];split;[constructor| ];split;[reflexivity| ].
     intros vl p q lg t Pre Post.
     eapply(V293_OSSchedNew_all_exact_joint_contract unmap group rows high bt bg br bh
     li V293_opened_inv Inv0 Hli);try eassumption.
Qed.
Theorem V293_bound_dynamic_WFIFun : forall exit enter sched y,
 exit<>enter ->exit<>sched ->enter<>sched ->
 unmap<>y ->group<>y ->rows<>y ->high<>y ->
 table<>saved ->high<>saved ->target<>saved ->current<>saved ->
 counter<>saved ->nesting<>saved ->lock<>saved ->running<>saved ->
 GoodFrm extra ->
 WFIFun(V293_ready_irq_unit unmap group rows high table target current counter running nesting lock saved exit enter sched y)(V293_bound_dynamic_spec exit enter sched)
 V293_scheduler Inv0 li.
Proof.
 intros;destruct(V293_bound_dynamic_WFFunEnv exit enter sched y
 H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14)as[Dom Body].
 split;[exact Dom| ];intros f p q t tl Lookup.
 destruct(Body f p q t tl Lookup)as(d1&d2&s&Code&Types&Decls&Checked).
 exists d1;exists d2;exists s;auto.
Qed.
End BoundDynamicEnvironment.
