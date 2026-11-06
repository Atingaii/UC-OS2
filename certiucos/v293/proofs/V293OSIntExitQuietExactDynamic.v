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

Section QuietExactDynamic.
Variables unmap group rows high table target current counter running nesting lock saved:var.
Variables bt bg br bh bp bo bc bk brun bn bl:block.
Variable rest:list(addr*type).
Variable extra:asrt.
Variable EG:GoodFunAsrt extra.
Let Inv0:=V293_ready_dynamic_exit_inv target bt bg br bh bp bc bk brun bn bl rest.
Let Hli:=V293_switch_li_good.
Let oldfp:=V293_ready_dynamic_exit_fpre unmap group rows high table target current counter running nesting lock
 bt bg br bh bp bo bc bk brun bn bl rest extra EG.
Let oldfq:=V293_exact_dynamic_exit_fpost unmap group rows high table target current counter running nesting lock
 bt bg br bh bp bo bc bk brun bn bl rest extra EG.
Let qfp:=V293_quiet_exact_exit_fpre running nesting lock brun bn bl V293_shared_li extra Hli EG.
Let qfq:=V293_quiet_exact_exit_fpost running nesting lock brun bn bl V293_shared_li extra Hli EG.
Let sfp:=V293_exact_joint_sched_fpre unmap group rows high bt bg br bh V293_shared_li V293_opened_inv Inv0 Hli.
Let sfq:=V293_exact_joint_sched_fpost unmap group rows high bt bg br bh V293_shared_li V293_opened_inv Inv0 Hli.
(* The two existing proof tags are reused; no runtime branch is added. *)
Definition V293_quiet_exact_dynamic_fpre:fpre:=fun vl lg t=>
 match V293_exit_path lg with
 | Some(false,args)=>match V293_exit_path args with
   | Some(true,qlg)=>qfp vl qlg t
   | _=>oldfp vl lg t end
 | _=>oldfp vl lg t end.
Definition V293_quiet_exact_dynamic_fpost:fpost:=fun vl result lg t=>
 match V293_exit_path lg with
 | Some(false,args)=>match V293_exit_path args with
   | Some(true,qlg)=>qfq vl result qlg t
   | _=>oldfq vl result lg t end
 | _=>oldfq vl result lg t end.
Lemma V293_quiet_exact_dynamic_changed_kept : forall vl result args t,
 getasrt(V293_quiet_exact_dynamic_fpre vl(logic_ie true::args)t)=
 getasrt(oldfp vl(logic_ie true::args)t) /\
 getasrt(V293_quiet_exact_dynamic_fpost vl result(logic_ie true::args)t)=
 getasrt(oldfq vl result(logic_ie true::args)t).
Proof. intros;split;reflexivity. Qed.
Lemma V293_quiet_exact_dynamic_same_kept : forall vl result args t,
 getasrt(V293_quiet_exact_dynamic_fpre vl(logic_ie false::logic_ie false::args)t)=
 getasrt(oldfp vl(logic_ie false::logic_ie false::args)t) /\
 getasrt(V293_quiet_exact_dynamic_fpost vl result(logic_ie false::logic_ie false::args)t)=
 getasrt(oldfq vl result(logic_ie false::logic_ie false::args)t).
Proof. intros;split;reflexivity. Qed.
Theorem V293_OSIntExit_quiet_exact_dynamic_contract : forall P f Spec sched_id vl lg t pre post,
 table<>saved ->high<>saved ->target<>saved ->current<>saved ->
 counter<>saved ->nesting<>saved ->lock<>saved ->running<>saved ->GoodFrm extra ->
 Spec sched_id=Some(sfp,sfq,(Tvoid,nil)) ->
 P f=Some(V293_exit_boundary_function running nesting lock saved table high target current counter sched_id
 (V293_interrupt_handoff high current target)) ->
 Some pre=BuildPreI P f vl lg V293_quiet_exact_dynamic_fpre t ->
 Some post=BuildRetI P f vl lg V293_quiet_exact_dynamic_fpost t ->
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
 getasrt(V293_quiet_exact_dynamic_fpre nil lg t) ** V293_exit_builder_domain saved))in Pre.
 unfold BuildRetI in Post;rewrite Code in Post.
 change(Some post=Some(fun result=>V293_exit_builder_cells saved **
 getasrt(V293_quiet_exact_dynamic_fpost nil result lg t) ** V293_exit_builder_domain saved))in Post.
 unfold V293_quiet_exact_dynamic_fpre in Pre;unfold V293_quiet_exact_dynamic_fpost in Post.
 destruct(V293_exit_path lg)as[[outer args]| ]eqn:Outer.
 - destruct outer.
   + eapply V293_OSIntExit_exact_dynamic_builder_contract with(vl:=nil)(lg:=lg);try eassumption;
     unfold BuildPreI,BuildRetI;rewrite Code;try exact Post;exact Pre.
   + destruct(V293_exit_path args)as[[inner qlg]| ]eqn:Inner.
     * destruct inner.
       -- eapply V293_OSIntExit_quiet_exact_builder_contract with(vl:=nil)(lg:=qlg);try eassumption;
          unfold BuildPreI,BuildRetI;rewrite Code;try exact Post;exact Pre.
       -- eapply V293_OSIntExit_exact_dynamic_builder_contract with(vl:=nil)(lg:=lg);try eassumption;
          unfold BuildPreI,BuildRetI;rewrite Code;try exact Post;exact Pre.
     * eapply V293_OSIntExit_exact_dynamic_builder_contract with(vl:=nil)(lg:=lg);try eassumption;
       unfold BuildPreI,BuildRetI;rewrite Code;try exact Post;exact Pre.
 - eapply V293_OSIntExit_exact_dynamic_builder_contract with(vl:=nil)(lg:=lg);try eassumption;
   unfold BuildPreI,BuildRetI;rewrite Code;try exact Post;exact Pre.
Qed.
Theorem V293_OSIntExit_quiet_exact_dynamic_call : forall Spec sd RI r ri exit t
 run nest locked aop enabled ir si ci callerframe,
 run<256 ->nest<256 ->locked<256 ->GoodFrm callerframe ->
 Spec exit=Some(V293_quiet_exact_dynamic_fpre,V293_quiet_exact_dynamic_fpost,(Tvoid,nil)) ->
 let lg:=logic_ie false::logic_ie true::V293_quiet_exit_args run nest locked aop enabled ir si ci in
 InfRules Spec sd V293_shared_li RI r ri
 (getasrt(V293_quiet_exact_dynamic_fpre nil lg t) ** callerframe)
 (scall exit nil)
 (EX result:option val,getasrt(V293_quiet_exact_dynamic_fpost nil result lg t) ** callerframe)t.
Proof.
 intros Spec sd RI r ri exit t run nest locked aop enabled ir si ci callerframe Run Nest Lock GF Lookup lg.
 eapply call_rule with(pre:=V293_quiet_exact_dynamic_fpre)(post:=V293_quiet_exact_dynamic_fpost)
 (vl:=nil)(logicl:=lg)(tp:=Tvoid)(tl:=nil).
 - exact GF.
 - exact Lookup.
 - intros st H;exact H.
 - intros st H;reflexivity.
 - reflexivity.
 - unfold lg,V293_quiet_exact_dynamic_fpre,V293_exit_path,qfp,V293_quiet_exact_exit_fpre,
   V293_quiet_exact_exit_pre;rewrite V293_quiet_exit_roundtrip by assumption.
   intros st H;cbn[getasrt]in H.
   assert(C:st |=p_local V293_shared_li t nil ** Atrue).
   { unfold V293_quiet_exact_external,V293OSIntExitHoare.V293_exit_cells,
     V293OSIntEnterInternal.V293_interrupt_cells in H;cbn[V293InitRdyList.V293_rdy_raw_cells]in H;clear -H;sep auto. }
   eapply V293_star_CurLINV_l;[apply V293_exact_local_weakens|exact C].
 - intros st[result H];unfold lg,V293_quiet_exact_dynamic_fpost,V293_exit_path,qfq,
   V293_quiet_exact_exit_fpost,V293_quiet_exact_exit_post in H;
   rewrite V293_quiet_exit_roundtrip in H by assumption;cbn[getasrt]in H.
   assert(C:st |=p_local V293_shared_li t nil ** Atrue).
   { unfold V293_quiet_exact_external,V293OSIntExitHoare.V293_exit_cells,
     V293OSIntEnterInternal.V293_interrupt_cells in H;cbn[V293InitRdyList.V293_rdy_raw_cells]in H;clear -H;sep auto. }
   eapply V293_star_CurLINV_l;[apply V293_exact_local_weakens|exact C].
Qed.
End QuietExactDynamic.

Section QuietExactDynamicEnvironment.
Variables unmap group rows high table target current counter running nesting lock saved:var.
Variables bt bg br bh bp bo bc bk brun bn bl:block.
Variable rest:list(addr*type).
Variable extra:asrt.
Variable EG:GoodFunAsrt extra.
Let tp:=V293_tcb_type.
Let Inv0:=V293_ready_dynamic_exit_inv target bt bg br bh bp bc bk brun bn bl rest.
Let Hli:=V293_switch_li_good.
Let prefix:=V293_ready_irq_prefix bt bh bc bk.
Let suffix:=V293_ready_irq_suffix bl rest.
Let efp:=V293_enter_local_fpre br bg bp brun bn running nesting target tp
 prefix suffix.
Let efq:=V293_enter_local_fpost br bg bp brun bn running nesting target tp
 prefix suffix.
Let xfp:=V293_quiet_exact_dynamic_fpre unmap group rows high table target current counter running nesting lock
 bt bg br bh bp bo bc bk brun bn bl rest extra EG.
Let xfq:=V293_quiet_exact_dynamic_fpost unmap group rows high table target current counter running nesting lock
 bt bg br bh bp bo bc bk brun bn bl rest extra EG.
Let sfp:=V293_exact_joint_sched_fpre unmap group rows high bt bg br bh V293_shared_li V293_opened_inv Inv0 Hli.
Let sfq:=V293_exact_joint_sched_fpost unmap group rows high bt bg br bh V293_shared_li V293_opened_inv Inv0 Hli.
Definition V293_quiet_exact_dynamic_spec exit enter sched:funspec:=
 fun f=>if Z.eq_dec f exit then Some(xfp,xfq,(Tvoid,nil))
 else if Z.eq_dec f enter then Some(efp,efq,(Tvoid,nil))
 else if Z.eq_dec f sched then Some(sfp,sfq,(Tvoid,nil))else None.
Lemma V293_quiet_exact_dynamic_domains : forall exit enter sched y,
 EqDom(V293_ready_irq_unit unmap group rows high table target current counter running nesting lock saved exit enter sched y)(V293_quiet_exact_dynamic_spec exit enter sched).
Proof.
 intros exit enter sched y f.
 unfold V293_ready_irq_unit,V293_exit_env_unit,V293_irq_internal_unit,pumerge,
 V293_OSIntEnter_unit,V293_OSSchedNew_internal_unit,V293_quiet_exact_dynamic_spec.
 destruct(Z.eq_dec f exit),(Z.eq_dec f enter),(Z.eq_dec f sched);
 split;intros[x H];try discriminate;eexists;reflexivity.
Qed.
Theorem V293_quiet_exact_dynamic_WFFunEnv : forall exit enter sched y,
 exit<>enter ->exit<>sched ->enter<>sched ->
 unmap<>y ->group<>y ->rows<>y ->high<>y ->
 table<>saved ->high<>saved ->target<>saved ->current<>saved ->
 counter<>saved ->nesting<>saved ->lock<>saved ->running<>saved ->
 GoodFrm extra ->
 WFFunEnv(V293_ready_irq_unit unmap group rows high table target current counter running nesting lock saved exit enter sched y)(V293_quiet_exact_dynamic_spec exit enter sched)
 V293_scheduler V293_shared_li Inv0.
Proof.
 intros exit enter sched y XE XS ES UY GY RY HY T H G C K N L R GF.
 pose proof(V293_exit_env_entries exit enter sched running nesting unmap group rows high y saved
 (V293_exit_boundary_body running nesting lock saved table high target current counter sched
 (V293_interrupt_handoff high current target)) XE XS ES)as(CodeX&CodeE&CodeS).
 assert(Sched:V293_quiet_exact_dynamic_spec exit enter sched sched=Some(sfp,sfq,(Tvoid,nil))).
 { unfold V293_quiet_exact_dynamic_spec;repeat destruct Z.eq_dec;try congruence;reflexivity. }
 split;[apply V293_quiet_exact_dynamic_domains| ].
 intros f pre post t tl Lookup;unfold V293_quiet_exact_dynamic_spec in Lookup.
 destruct(Z.eq_dec f exit)as[E|NE].
 - subst f;inversion Lookup;subst pre post t tl.
   exists dnil;exists(dcons saved Tint32 dnil).
   exists(V293_exit_boundary_body running nesting lock saved table high target current counter sched
   (V293_interrupt_handoff high current target)).
   split;[exact CodeX| ];split;[constructor| ];split;[reflexivity| ].
   intros vl p q lg t Pre Post.
   eapply V293_OSIntExit_quiet_exact_dynamic_contract;try eassumption.
 - destruct(Z.eq_dec f enter)as[E|NEE].
   + subst f;inversion Lookup;subst pre post t tl.
     exists dnil;exists dnil;exists(V293_OSIntEnter_body running nesting).
     split;[exact CodeE| ];split;[constructor| ];split;[reflexivity| ].
     intros vl p q lg t Pre Post.
     unfold Inv0;rewrite <-V293_ready_irq_inv_layout.
     eapply V293_OSIntEnter_local_contract;try eassumption.
   + destruct(Z.eq_dec f sched)as[E|NES];[ |discriminate].
     subst f;inversion Lookup;subst pre post t tl.
     exists dnil;exists(dcons y Tint8 dnil);exists(V293_OSSchedNew_body unmap group rows high y).
     split;[exact CodeS| ];split;[constructor| ];split;[reflexivity| ].
     intros vl p q lg t Pre Post.
     eapply(V293_OSSchedNew_exact_joint_contract unmap group rows high bt bg br bh
     V293_shared_li V293_opened_inv Inv0 Hli);try eassumption.
Qed.
Theorem V293_quiet_exact_dynamic_WFIFun : forall exit enter sched y,
 exit<>enter ->exit<>sched ->enter<>sched ->
 unmap<>y ->group<>y ->rows<>y ->high<>y ->
 table<>saved ->high<>saved ->target<>saved ->current<>saved ->
 counter<>saved ->nesting<>saved ->lock<>saved ->running<>saved ->
 GoodFrm extra ->
 WFIFun(V293_ready_irq_unit unmap group rows high table target current counter running nesting lock saved exit enter sched y)(V293_quiet_exact_dynamic_spec exit enter sched)
 V293_scheduler Inv0 V293_shared_li.
Proof.
 intros;destruct(V293_quiet_exact_dynamic_WFFunEnv exit enter sched y
 H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14)as[Dom Body].
 split;[exact Dom| ];intros f p q t tl Lookup.
 destruct(Body f p q t tl Lookup)as(d1&d2&s&Code&Types&Decls&Checked).
 exists d1;exists d2;exists s;auto.
Qed.
Theorem V293_quiet_exact_dynamic_Enter_call : forall exit enter sched r ri aop si ci tid,
 exit<>enter ->
 InfRules(V293_quiet_exact_dynamic_spec exit enter sched)V293_scheduler V293_shared_li Inv0 r ri
 (V293_enter_local_boundary br bg bp brun bn running nesting target tp
 prefix suffix aop si ci tid ** A_dom_lenv nil)
 (scall enter nil)
 (V293_enter_local_boundary br bg bp brun bn running nesting target tp
 prefix suffix aop si ci tid ** A_dom_lenv nil)tid.
Proof.
 intros;unfold Inv0;rewrite <-V293_ready_irq_inv_layout;apply V293_OSIntEnter_local_call.
 unfold V293_quiet_exact_dynamic_spec;repeat destruct Z.eq_dec;try congruence;reflexivity.
Qed.
End QuietExactDynamicEnvironment.
