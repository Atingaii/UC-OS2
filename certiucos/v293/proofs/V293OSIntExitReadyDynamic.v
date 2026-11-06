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

(* Dynamic snapshots and one scheduler specification use the ready invariant. *)
Section ReadyDynamicExit.
Variables unmap group rows high table target current counter running nesting lock saved:var.
Variables bt bg br bh bp bo bc bk brun bn bl:block.
Let tp:=V293_tcb_type.
Variable rest:list(addr*type).
Variable extra:asrt.
Variable EG:GoodFunAsrt extra.
Definition V293_ready_dynamic_exit_inv:=
 V293_ready_builder_inv target bt bg br bh bp bc bk brun bn bl rest.
Let Inv0:=V293_ready_dynamic_exit_inv.
Theorem V293_ready_dynamic_exit_inv_good :
 GoodI Inv0 V293_scheduler V293_shared_li.
Proof. apply V293_ready_storage_good. Qed.
Let changedfp x:=V293_ready_builder_fpre unmap group rows high table target current counter running nesting lock
 bt bg br bh bp bo bc bk brun bn bl
 (Z.to_nat(Int.unsigned(V293_clo x)))(Z.to_nat(Int.unsigned(V293_chi x)))
 (Z.to_nat(Int.unsigned(V293_ccurrent x)))(Z.to_nat(Int.unsigned(V293_cnest x)))
 (V293_centries x)rest(V293_ctasks x)(V293_cevents x)(V293_cnow x)(V293_chigh x)(V293_cout x)
 (V293_ccounter x)(V293_caop x)(V293_cstack x)(V293_ccritical x)extra EG.
Let changedfq x:=V293_ready_builder_fpost unmap group rows high table target current counter running nesting lock
 bt bg br bh bp bo bc bk brun bn bl rest(V293_caop x)(V293_cstack x)(V293_ccritical x)extra EG.
Definition V293_ready_dynamic_changed_fpre:fpre:=fun vl lg t=>
 match V293_changed_decode lg with
 | Some x=>changedfp x vl nil t
 | None=>@mkfunasrt Afalse Logic.I end.
Definition V293_ready_dynamic_changed_fpost:fpost:=fun vl result lg t=>
 match V293_changed_decode lg with
 | Some x=>changedfq x vl result nil t
 | None=>@mkfunasrt Afalse Logic.I end.
Let Hli:=V293_switch_li_good.
Let cfp:=V293_critical_fpre unmap group rows high bt bg br bh V293_shared_li V293_opened_inv Hli.
Let cfq:=V293_critical_fpost unmap group rows high bt bg br bh V293_shared_li V293_opened_inv Hli.
Let ifp:=V293_ISR_sched_fpre unmap group rows high bt bg br bh V293_shared_li Inv0 Hli.
Let ifq:=V293_ISR_sched_fpost unmap group rows high bt bg br bh V293_shared_li Inv0 Hli.
Let jfp:=V293_joint_sched_fpre unmap group rows high bt bg br bh V293_shared_li V293_opened_inv Inv0 Hli.
Let jfq:=V293_joint_sched_fpost unmap group rows high bt bg br bh V293_shared_li V293_opened_inv Inv0 Hli.
Let quietsamefp:=V293_unified_exit_fpre unmap group rows high table target current counter nesting lock running
 bt bg br bh bp bo bc bk bn bl brun tp V293_shared_li extra Hli EG.
Let quietsamefq:=V293_unified_exit_fpost unmap group rows high table target current counter nesting lock running
 bt bg br bh bp bo bc bk bn bl brun tp V293_shared_li extra Hli EG.
Definition V293_ready_dynamic_exit_fpre:fpre:=fun vl lg t=>
 match V293_exit_path lg with
 | Some(true,args)=>V293_ready_dynamic_changed_fpre vl args t
 | Some(false,args)=>quietsamefp vl args t
 | None=>@mkfunasrt Afalse Logic.I end.
Definition V293_ready_dynamic_exit_fpost:fpost:=fun vl result lg t=>
 match V293_exit_path lg with
 | Some(true,args)=>V293_ready_dynamic_changed_fpost vl result args t
 | Some(false,args)=>quietsamefq vl result args t
 | None=>@mkfunasrt Afalse Logic.I end.

Lemma V293_ready_dynamic_changed_builder_contract : forall P f Spec sched_id vl lg t pre post,
 table<>saved ->high<>saved ->target<>saved ->current<>saved ->
 counter<>saved ->nesting<>saved ->lock<>saved ->running<>saved ->GoodFrm extra ->
 Spec sched_id=Some(cfp,cfq,(Tvoid,nil)) ->
 P f=Some(V293_exit_boundary_function running nesting lock saved table high target current counter sched_id
 (V293_interrupt_handoff high current target)) ->
 Some pre=BuildPreI P f vl lg V293_ready_dynamic_changed_fpre t ->
 Some post=BuildRetI P f vl lg V293_ready_dynamic_changed_fpost t ->
 InfRules Spec V293_scheduler V293_shared_li Inv0 post Afalse pre
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
 getasrt(V293_ready_dynamic_changed_fpre nil lg t) ** V293_exit_builder_domain saved))in Pre.
 unfold BuildRetI in Post;rewrite Code in Post.
 change(Some post=Some(fun result=>V293_exit_builder_cells saved **
 getasrt(V293_ready_dynamic_changed_fpost nil result lg t) ** V293_exit_builder_domain saved))in Post.
 unfold V293_ready_dynamic_changed_fpre in Pre;unfold V293_ready_dynamic_changed_fpost in Post.
 destruct(V293_changed_decode lg)as[x| ]eqn:Decode.
 - inversion Pre;subst pre;inversion Post;subst post.
   eapply (V293_OSIntExit_ready_builder_contract
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

Theorem V293_OSIntExit_ready_dynamic_builder_contract : forall P f Spec sched_id vl lg t pre post,
 table<>saved ->high<>saved ->target<>saved ->current<>saved ->
 counter<>saved ->nesting<>saved ->lock<>saved ->running<>saved ->GoodFrm extra ->
 Spec sched_id=Some(jfp,jfq,(Tvoid,nil)) ->
 P f=Some(V293_exit_boundary_function running nesting lock saved table high target current counter sched_id
 (V293_interrupt_handoff high current target)) ->
 Some pre=BuildPreI P f vl lg V293_ready_dynamic_exit_fpre t ->
 Some post=BuildRetI P f vl lg V293_ready_dynamic_exit_fpost t ->
 InfRules Spec V293_scheduler V293_shared_li Inv0 post Afalse pre
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
 getasrt(V293_ready_dynamic_exit_fpre nil lg t) ** V293_exit_builder_domain saved))in Pre.
 unfold BuildRetI in Post;rewrite Code in Post.
 change(Some post=Some(fun result=>V293_exit_builder_cells saved **
 getasrt(V293_ready_dynamic_exit_fpost nil result lg t) ** V293_exit_builder_domain saved))in Post.
 unfold V293_ready_dynamic_exit_fpre in Pre;unfold V293_ready_dynamic_exit_fpost in Post.
 destruct(V293_exit_path lg)as[[changed args]| ]eqn:Path.
 - destruct changed.
   + eapply V293_InfRules_spec_embedding with(source:=V293_spec_override Spec sched_id cfp cfq (Tvoid,nil)).
     * eapply V293_ready_dynamic_changed_builder_contract with(vl:=nil)(lg:=args);try eassumption.
       -- unfold V293_spec_override;destruct(Z.eq_dec sched_id sched_id);[reflexivity|contradiction].
       -- unfold BuildPreI;rewrite Code;exact Pre.
       -- unfold BuildRetI;rewrite Code;exact Post.
     * apply (V293_critical_to_joint unmap group rows high bt bg br bh V293_shared_li V293_opened_inv Inv0 Hli);exact Lookup.
     * apply V293_exit_handoff_void_calls.
   + eapply V293_InfRules_spec_embedding with(source:=V293_spec_override Spec sched_id ifp ifq (Tvoid,nil)).
     * eapply (V293_OSIntExit_unified_builder_contract
       unmap group rows high table target current counter nesting lock running saved
       bt bg br bh bp bo bc bk bn bl brun tp V293_shared_li extra Hli EG
       P f (V293_spec_override Spec sched_id ifp ifq (Tvoid,nil)) V293_scheduler Inv0 sched_id
       (V293_interrupt_handoff high current target) nil args t pre post);try eassumption.
       -- unfold V293_spec_override;destruct(Z.eq_dec sched_id sched_id);[reflexivity|contradiction].
       -- unfold BuildPreI;rewrite Code;exact Pre.
       -- unfold BuildRetI;rewrite Code;exact Post.
     * apply (V293_ISR_to_joint unmap group rows high bt bg br bh V293_shared_li V293_opened_inv Inv0 Hli);exact Lookup.
     * apply V293_exit_handoff_void_calls.
 - inversion Pre;subst pre;eapply conseq_rule with(p:=Afalse)(q:=Afalse).
   + intros st HS;apply astar_comm in HS;apply astar_assoc_elim in HS;
     apply astar_l_afalse_elim in HS;exact HS.
   + intros st HS;exact HS.
   + apply pfalse_rule.
Qed.


Definition V293_ready_dynamic_exit_env_spec exit enter sched : funspec :=
 fun f=>if Z.eq_dec f exit then Some(V293_ready_dynamic_exit_fpre,V293_ready_dynamic_exit_fpost,(Tvoid,nil))
 else if Z.eq_dec f enter then Some
 (V293_interrupt_fpre running nesting brun bn V293_shared_li Hli,
  V293_interrupt_fpost running nesting brun bn V293_shared_li Hli,(Tvoid,nil))
 else if Z.eq_dec f sched then Some(jfp,jfq,(Tvoid,nil)) else None.
Let unit exit enter sched y :=
 V293_exit_env_unit exit enter sched running nesting unmap group rows high y saved
 (V293_exit_boundary_body running nesting lock saved table high target current counter sched
  (V293_interrupt_handoff high current target)).
Lemma V293_ready_dynamic_exit_env_domains : forall exit enter sched y,
 EqDom(unit exit enter sched y)(V293_ready_dynamic_exit_env_spec exit enter sched).
Proof.
 intros exit enter sched y f.
 unfold unit,V293_exit_env_unit,V293_irq_internal_unit,pumerge,V293_OSIntEnter_unit,
 V293_OSSchedNew_internal_unit,V293_ready_dynamic_exit_env_spec.
 destruct(Z.eq_dec f exit), (Z.eq_dec f enter), (Z.eq_dec f sched);
 split;intros[x H];try discriminate;eexists;reflexivity.
Qed.

(* One ambient invariant and one scheduler lookup serve all three paths. *)
Theorem V293_ready_dynamic_exit_env_WFFunEnv : forall exit enter sched y,
 exit<>enter ->exit<>sched ->enter<>sched ->
 unmap<>y ->group<>y ->rows<>y ->high<>y ->
 table<>saved ->high<>saved ->target<>saved ->current<>saved ->
 counter<>saved ->nesting<>saved ->lock<>saved ->running<>saved ->
 GoodFrm extra ->
 WFFunEnv(unit exit enter sched y)(V293_ready_dynamic_exit_env_spec exit enter sched)V293_scheduler V293_shared_li Inv0.
Proof.
 intros exit enter sched y XE XS ES UY GY RY HY T H G C K N L R GF.
 pose proof(V293_exit_env_entries exit enter sched running nesting unmap group rows high y saved
 (V293_exit_boundary_body running nesting lock saved table high target current counter sched
 (V293_interrupt_handoff high current target)) XE XS ES)as(CodeX&CodeE&CodeS).
 assert(Sched:V293_ready_dynamic_exit_env_spec exit enter sched sched=Some(jfp,jfq,(Tvoid,nil))).
 { unfold V293_ready_dynamic_exit_env_spec;repeat destruct Z.eq_dec;try congruence;reflexivity. }
 split;[apply V293_ready_dynamic_exit_env_domains| ].
 intros f pre post t tl Lookup. unfold V293_ready_dynamic_exit_env_spec in Lookup.
 destruct(Z.eq_dec f exit)as[E|NE].
 - subst f;inversion Lookup;subst pre post t tl.
   exists dnil;exists(dcons saved Tint32 dnil).
   exists(V293_exit_boundary_body running nesting lock saved table high target current counter sched
    (V293_interrupt_handoff high current target)).
   split;[exact CodeX| ]. split;[constructor| ]. split;[reflexivity| ].
   intros vl p q lg t Pre Post.
   eapply V293_OSIntExit_ready_dynamic_builder_contract;try eassumption.
 - destruct(Z.eq_dec f enter)as[E|NEE].
   + subst f;inversion Lookup;subst pre post t tl.
     exists dnil;exists dnil;exists(V293_OSIntEnter_body running nesting).
     split;[exact CodeE| ]. split;[constructor| ]. split;[reflexivity| ].
     intros vl p q lg t Pre Post. eapply V293_OSIntEnter_internal_contract;try eassumption.
   + destruct(Z.eq_dec f sched)as[E|NES];[ |discriminate].
     subst f;inversion Lookup;subst pre post t tl.
     exists dnil;exists(dcons y Tint8 dnil);exists(V293_OSSchedNew_body unmap group rows high y).
     split;[exact CodeS| ]. split;[constructor| ]. split;[reflexivity| ].
     intros vl p q lg t Pre Post. eapply (V293_OSSchedNew_joint_contract unmap group rows high bt bg br bh V293_shared_li V293_opened_inv Inv0 Hli);try eassumption.
Qed.
Lemma V293_ready_dynamic_exit_env_WFIFun : forall exit enter sched y,
 exit<>enter ->exit<>sched ->enter<>sched ->
 unmap<>y ->group<>y ->rows<>y ->high<>y ->
 table<>saved ->high<>saved ->target<>saved ->current<>saved ->
 counter<>saved ->nesting<>saved ->lock<>saved ->running<>saved ->
 GoodFrm extra ->
 WFIFun(unit exit enter sched y)(V293_ready_dynamic_exit_env_spec exit enter sched)V293_scheduler Inv0 V293_shared_li.
Proof.
 intros. destruct(V293_ready_dynamic_exit_env_WFFunEnv exit enter sched y
 H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14)as[Dom Body].
 split;[exact Dom| ]. intros f p q t tl Lookup.
 destruct(Body f p q t tl Lookup)as(d1&d2&s&Code&Types&Decls&Checked).
 exists d1;exists d2;exists s;auto.
Qed.
End ReadyDynamicExit.
