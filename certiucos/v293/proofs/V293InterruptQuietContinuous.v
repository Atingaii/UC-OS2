Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitReadyBody.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchState.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitResourceBridge.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitChangedInternal.
Require Import CertiOS.certiucos.v293.proofs.V293SpecEmbedding.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedJoint.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCritical.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedISRContext.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedShared.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitBoundarySwitch.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitBuilders.
Require Import CertiOS.framework.proof.auxdef.
Require Import Coq.Lists.List.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitAllInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedStoragePrefix.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitDynamic.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitReadyDynamic.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitExactInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedExactJoint.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptReadyLocal.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitExactDynamic.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedISRExact.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitSameExactInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitSameInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitQuietExactDynamic.
(* A continuous quiet interrupt path under an explicit control snapshot. *)
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitAllExactDynamic.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntEnterOpenExact.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptReadyEnvironment.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptReadyBoundary.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptSourceRoundtrip.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitQuietExact.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitUnifiedInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitResourceCodec.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedAllExactJoint.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedSwitch.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedExactLocal.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntEnterInternal.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyTaskInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyStorageInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchStorage.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitReadyInternal.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptExitEnvironment.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptFunctionEnvironment.
Require Import CertiOS.certiucos.v293.code.V293OSIntEnter.
Require Import CertiOS.certiucos.v293.code.V293OSSchedNew.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewInternal.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.framework.proof.toptheorem.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.sep_combine_lemmas.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.
Section OpenExactEnvironment.
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
Let efp:=V293_enter_open_fpre running nesting lock brun bn bl extra EG.
Let efq:=V293_enter_open_fpost running nesting lock brun bn bl extra EG.
Let xfp:=V293_all_exact_dynamic_fpre unmap group rows high table target current counter running nesting lock
 bt bg br bh bp bo bc bk brun bn bl rest extra EG.
Let xfq:=V293_all_exact_dynamic_fpost unmap group rows high table target current counter running nesting lock
 bt bg br bh bp bo bc bk brun bn bl rest extra EG.
Let sfp:=V293_all_exact_joint_sched_fpre unmap group rows high bt bg br bh V293_shared_li V293_opened_inv Inv0 Hli.
Let sfq:=V293_all_exact_joint_sched_fpost unmap group rows high bt bg br bh V293_shared_li V293_opened_inv Inv0 Hli.
Definition V293_open_exact_irq_spec exit enter sched:funspec:=
 fun f=>if Z.eq_dec f exit then Some(xfp,xfq,(Tvoid,nil))
 else if Z.eq_dec f enter then Some(efp,efq,(Tvoid,nil))
 else if Z.eq_dec f sched then Some(sfp,sfq,(Tvoid,nil))else None.
Lemma V293_open_exact_irq_domains : forall exit enter sched y,
 EqDom(V293_ready_irq_unit unmap group rows high table target current counter running nesting lock saved exit enter sched y)(V293_open_exact_irq_spec exit enter sched).
Proof.
 intros exit enter sched y f.
 unfold V293_ready_irq_unit,V293_exit_env_unit,V293_irq_internal_unit,pumerge,
 V293_OSIntEnter_unit,V293_OSSchedNew_internal_unit,V293_open_exact_irq_spec.
 destruct(Z.eq_dec f exit),(Z.eq_dec f enter),(Z.eq_dec f sched);
 split;intros[x H];try discriminate;eexists;reflexivity.
Qed.
Theorem V293_open_exact_irq_WFFunEnv : forall exit enter sched y,
 exit<>enter ->exit<>sched ->enter<>sched ->
 unmap<>y ->group<>y ->rows<>y ->high<>y ->
 table<>saved ->high<>saved ->target<>saved ->current<>saved ->
 counter<>saved ->nesting<>saved ->lock<>saved ->running<>saved ->
 GoodFrm extra ->
 WFFunEnv(V293_ready_irq_unit unmap group rows high table target current counter running nesting lock saved exit enter sched y)(V293_open_exact_irq_spec exit enter sched)
 V293_scheduler V293_shared_li Inv0.
Proof.
 intros exit enter sched y XE XS ES UY GY RY HY T H G C K N L R GF.
 pose proof(V293_exit_env_entries exit enter sched running nesting unmap group rows high y saved
 (V293_exit_boundary_body running nesting lock saved table high target current counter sched
 (V293_interrupt_handoff high current target)) XE XS ES)as(CodeX&CodeE&CodeS).
 assert(Sched:V293_open_exact_irq_spec exit enter sched sched=Some(sfp,sfq,(Tvoid,nil))).
 { unfold V293_open_exact_irq_spec;repeat destruct Z.eq_dec;try congruence;reflexivity. }
 split;[apply V293_open_exact_irq_domains| ].
 intros f pre post t tl Lookup;unfold V293_open_exact_irq_spec in Lookup.
 destruct(Z.eq_dec f exit)as[E|NE].
 - subst f;inversion Lookup;subst pre post t tl.
   exists dnil;exists(dcons saved Tint32 dnil).
   exists(V293_exit_boundary_body running nesting lock saved table high target current counter sched
   (V293_interrupt_handoff high current target)).
   split;[exact CodeX| ];split;[constructor| ];split;[reflexivity| ].
   intros vl p q lg t Pre Post.
   eapply V293_OSIntExit_all_exact_dynamic_contract;try eassumption.
 - destruct(Z.eq_dec f enter)as[E|NEE].
   + subst f;inversion Lookup;subst pre post t tl.
     exists dnil;exists dnil;exists(V293_OSIntEnter_body running nesting).
     split;[exact CodeE| ];split;[constructor| ];split;[reflexivity| ].
     intros vl p q lg t Pre Post.
     eapply V293_OSIntEnter_open_contract;try eassumption.
   + destruct(Z.eq_dec f sched)as[E|NES];[ |discriminate].
     subst f;inversion Lookup;subst pre post t tl.
     exists dnil;exists(dcons y Tint8 dnil);exists(V293_OSSchedNew_body unmap group rows high y).
     split;[exact CodeS| ];split;[constructor| ];split;[reflexivity| ].
     intros vl p q lg t Pre Post.
     eapply(V293_OSSchedNew_all_exact_joint_contract unmap group rows high bt bg br bh
     V293_shared_li V293_opened_inv Inv0 Hli);try eassumption.
Qed.
Theorem V293_open_exact_irq_WFIFun : forall exit enter sched y,
 exit<>enter ->exit<>sched ->enter<>sched ->
 unmap<>y ->group<>y ->rows<>y ->high<>y ->
 table<>saved ->high<>saved ->target<>saved ->current<>saved ->
 counter<>saved ->nesting<>saved ->lock<>saved ->running<>saved ->
 GoodFrm extra ->
 WFIFun(V293_ready_irq_unit unmap group rows high table target current counter running nesting lock saved exit enter sched y)(V293_open_exact_irq_spec exit enter sched)
 V293_scheduler Inv0 V293_shared_li.
Proof.
 intros;destruct(V293_open_exact_irq_WFFunEnv exit enter sched y
 H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14)as[Dom Body].
 split;[exact Dom| ];intros f p q t tl Lookup.
 destruct(Body f p q t tl Lookup)as(d1&d2&s&Code&Types&Decls&Checked).
 exists d1;exists d2;exists s;auto.
Qed.
End OpenExactEnvironment.

Section AllExactQuietCall.
Variables unmap group rows high table target current counter running nesting lock saved:var.
Variables bt bg br bh bp bo bc bk brun bn bl:block.
Variable rest:list(addr*type).
Variable extra:asrt.
Variable EG:GoodFunAsrt extra.
Let tp:=V293_tcb_type.
Let Inv0:=V293_ready_dynamic_exit_inv target bt bg br bh bp bc bk brun bn bl rest.
Let Hli:=V293_switch_li_good.
Let cfp:=V293_sched_exact_fpre unmap group rows high bt bg br bh V293_shared_li V293_opened_inv Hli.
Let cfq:=V293_sched_exact_fpost unmap group rows high bt bg br bh V293_shared_li V293_opened_inv Hli.
Let ifp:=V293_ISR_exact_sched_fpre unmap group rows high bt bg br bh V293_shared_li Inv0 Hli.
Let ifq:=V293_ISR_exact_sched_fpost unmap group rows high bt bg br bh V293_shared_li Inv0 Hli.
Let sfp:=V293_all_exact_joint_sched_fpre unmap group rows high bt bg br bh V293_shared_li V293_opened_inv Inv0 Hli.
Let sfq:=V293_all_exact_joint_sched_fpost unmap group rows high bt bg br bh V293_shared_li V293_opened_inv Inv0 Hli.
Let cexitfp:=V293_ready_dynamic_changed_fpre unmap group rows high table target current counter running nesting lock
 bt bg br bh bp bo bc bk brun bn bl rest extra EG.
Let cexitfq:=V293_exact_dynamic_changed_fpost unmap group rows high table target current counter running nesting lock
 bt bg br bh bp bo bc bk brun bn bl rest extra EG.
Let qfp:=V293_quiet_exact_exit_fpre running nesting lock brun bn bl V293_shared_li extra Hli EG.
Let qfq:=V293_quiet_exact_exit_fpost running nesting lock brun bn bl V293_shared_li extra Hli EG.
Let allfp:=V293_all_exact_dynamic_fpre unmap group rows high table target current counter running nesting lock
 bt bg br bh bp bo bc bk brun bn bl rest extra EG.
Let allfq:=V293_all_exact_dynamic_fpost unmap group rows high table target current counter running nesting lock
 bt bg br bh bp bo bc bk brun bn bl rest extra EG.
Theorem V293_OSIntExit_all_exact_quiet_call : forall Spec sd RI r ri exit t
 run nest locked aop enabled ir si ci callerframe,
 run<256 ->nest<256 ->locked<256 ->GoodFrm callerframe ->
 Spec exit=Some(allfp,allfq,(Tvoid,nil)) ->
 let lg:=logic_ie false::logic_ie true::V293_quiet_exit_args run nest locked aop enabled ir si ci in
 InfRules Spec sd V293_shared_li RI r ri
 (getasrt(allfp nil lg t) ** callerframe)
 (scall exit nil)
 (EX result:option val,getasrt(allfq nil result lg t) ** callerframe)t.
Proof.
 intros Spec sd RI r ri exit t run nest locked aop enabled ir si ci callerframe Run Nest Lock GF Lookup lg.
 eapply call_rule with(pre:=allfp)(post:=allfq)
 (vl:=nil)(logicl:=lg)(tp:=Tvoid)(tl:=nil).
 - exact GF.
 - exact Lookup.
 - intros st H;exact H.
 - intros st H;reflexivity.
 - reflexivity.
 - unfold lg,allfp,V293_all_exact_dynamic_fpre,V293_exit_path,qfp,V293_quiet_exact_exit_fpre,
   V293_quiet_exact_exit_pre;rewrite V293_quiet_exit_roundtrip by assumption.
   intros st H;cbn[getasrt]in H.
   assert(C:st |=p_local V293_shared_li t nil ** Atrue).
   { unfold V293_quiet_exact_external,V293OSIntExitHoare.V293_exit_cells,
     V293OSIntEnterInternal.V293_interrupt_cells in H;cbn[V293InitRdyList.V293_rdy_raw_cells]in H;clear -H;sep auto. }
   eapply V293_star_CurLINV_l;[apply V293_exact_local_weakens|exact C].
 - intros st[result H];unfold lg,allfq,V293_all_exact_dynamic_fpost,V293_exit_path,qfq,
   V293_quiet_exact_exit_fpost,V293_quiet_exact_exit_post in H;
   rewrite V293_quiet_exit_roundtrip in H by assumption;cbn[getasrt]in H.
   assert(C:st |=p_local V293_shared_li t nil ** Atrue).
   { unfold V293_quiet_exact_external,V293OSIntExitHoare.V293_exit_cells,
     V293OSIntEnterInternal.V293_interrupt_cells in H;cbn[V293InitRdyList.V293_rdy_raw_cells]in H;clear -H;sep auto. }
   eapply V293_star_CurLINV_l;[apply V293_exact_local_weakens|exact C].
Qed.
End AllExactQuietCall.

Require Import CertiOS.certiucos.v293.proofs.V293InterruptReadyLocal.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptReadyEnter.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitNondispatch.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitHoare.

Lemma V293_quiet_pair_depth : forall run nest,
 (run=1 ->nest<255) ->
 V293_exit_quiet_depth run(V293_interrupt_nest_after run nest)=nest.
Proof.
 intros run nest Room;unfold V293_exit_quiet_depth,V293_interrupt_nest_after,V293_exit_depth.
 destruct(Nat.eqb run 1)eqn:E;simpl;[ |reflexivity].
 apply Nat.eqb_eq in E;subst run;assert(Nat.ltb nest 255=true)by(apply Nat.ltb_lt;auto).
 rewrite H;reflexivity.
Qed.
Lemma V293_quiet_pair_valid : forall run nest locked si,
 run<256 ->nest<256 ->locked<256 ->gettopis si<=INUM ->
 (run=1 ->nest<255) ->(run=1 ->1<=nest \/ 0<locked) ->
 V293_quiet_exit_valid run(V293_interrupt_nest_after run nest)locked si.
Proof.
 intros run nest locked si R N L Top Room Quiet.
 unfold V293_quiet_exit_valid;repeat split;try assumption.
 - apply V293_interrupt_nest_bound;assumption.
 - intro E;subst run;unfold V293_interrupt_nest_after;simpl.
   assert(Nat.ltb nest 255=true)by(apply Nat.ltb_lt;auto);rewrite H.
   specialize(Quiet eq_refl);lia.
Qed.
Theorem V293_quiet_pair_saturation_counterexample :
 V293_interrupt_nest_after 1 255=255 /\
 V293_exit_quiet_depth 1(V293_interrupt_nest_after 1 255)=254 /\
 V293_exit_quiet_depth 1(V293_interrupt_nest_after 1 255)<>255.
Proof. vm_compute;repeat split;discriminate. Qed.

Section QuietPair.
Variables unmap group rows high table target current counter running nesting lock:var.
Variables bt bg br bh bp bo bc bk brun bn bl:block.
Variable rest:list(addr*type).
Let Inv0:=V293_ready_dynamic_exit_inv target bt bg br bh bp bc bk brun bn bl rest.
Let efp:=V293_enter_open_fpre running nesting lock brun bn bl Aemp Logic.I.
Let efq:=V293_enter_open_fpost running nesting lock brun bn bl Aemp Logic.I.
Let xfp:=V293_all_exact_dynamic_fpre unmap group rows high table target current counter running nesting lock
 bt bg br bh bp bo bc bk brun bn bl rest Aemp Logic.I.
Let xfq:=V293_all_exact_dynamic_fpost unmap group rows high table target current counter running nesting lock
 bt bg br bh bp bo bc bk brun bn bl rest Aemp Logic.I.
Let ext:=V293_enter_open_external running nesting lock brun bn bl Aemp.
Let qext:=V293_quiet_exact_external running nesting lock brun bn bl V293_shared_li Aemp.
Definition V293_quiet_pair_half run:=Amapsto(brun,0%Z)Tint8 false(V293_byteval run).
Lemma V293_quiet_pair_split : forall run nest locked aop enabled ir si ci t callerframe,
 ext run nest locked aop enabled ir si ci t ** callerframe ==>
 qext run nest locked aop enabled ir si ci t ** (V293_quiet_pair_half run ** callerframe).
Proof.
 intros run nest locked aop enabled ir si ci t callerframe;unfold ext,qext,V293_enter_open_external,V293_quiet_exact_external,
 V293OSIntExitHoare.V293_exit_cells,V293OSIntEnterInternal.V293_interrupt_cells;
 cbn[V293_rdy_raw_cells];intros s H.
 assert(P:s |=Amapsto(brun,0%Z)Tint8 true(V293_byteval run) **
 (<||aop||> ** OS[ir,enabled,si,ci] ** (V293_quiet_globals running nesting lock brun bn bl **
 (Amapsto(bn,0%Z)Tint8 true(V293_byteval nest) **
 (Amapsto(bl,0%Z)Tint8 true(V293_byteval locked) **
 (p_local V293_shared_li t nil ** Aemp ** callerframe))))))by(sep auto).
 eapply astar_mono in P;[ |apply separate_rw2ro|intros st K;exact K].
 unfold V293_quiet_pair_half;clear H;sep auto.
Qed.
Lemma V293_quiet_pair_combine : forall run nest locked aop enabled ir si ci t callerframe,
 qext run nest locked aop enabled ir si ci t ** (V293_quiet_pair_half run ** callerframe) ==>
 ext run nest locked aop enabled ir si ci t ** callerframe.
Proof.
 intros run nest locked aop enabled ir si ci t callerframe;unfold ext,qext,V293_enter_open_external,V293_quiet_exact_external,
 V293OSIntExitHoare.V293_exit_cells,V293OSIntEnterInternal.V293_interrupt_cells,V293_quiet_pair_half;
 cbn[V293_rdy_raw_cells];intros s H.
 assert(P:s |= (Amapsto(brun,0%Z)Tint8 false(V293_byteval run) **
 Amapsto(brun,0%Z)Tint8 false(V293_byteval run)) **
 (<||aop||> ** OS[ir,enabled,si,ci] ** (V293_quiet_globals running nesting lock brun bn bl **
 (Amapsto(bn,0%Z)Tint8 true(V293_byteval nest) **
 (Amapsto(bl,0%Z)Tint8 true(V293_byteval locked) **
 (p_local V293_shared_li t nil ** Aemp ** callerframe))))))by(sep auto).
 eapply astar_mono in P;[ |apply combine_ro2rw_p1|intros st K;exact K].
 clear H;sep auto.
Qed.
Theorem V293_interrupt_quiet_exit_after_enter : forall Spec sd RI r ri exit t run nest locked
 aop enabled ir si ci callerframe,
 run<256 ->nest<256 ->locked<256 ->gettopis si<=INUM ->
 (run=1 ->nest<255) ->(run=1 ->1<=nest \/ 0<locked) ->GoodFrm callerframe ->
 Spec exit=Some(xfp,xfq,(Tvoid,nil)) ->
 InfRules Spec sd V293_shared_li RI r ri
 (ext run(V293_interrupt_nest_after run nest)locked aop enabled ir si ci t ** callerframe)
 (scall exit nil)
 (ext run nest locked aop enabled ir si ci t ** callerframe)t.
Proof.
 intros Spec sd RI r ri exit t run nest locked aop enabled ir si ci callerframe
 Run Nest Lock Top Room Quiet GF Exit.
 set(n:=V293_interrupt_nest_after run nest).
   assert(N:n<256)by(apply V293_interrupt_nest_bound;assumption).
   assert(Q:V293_quiet_exit_valid run n locked si)by(apply V293_quiet_pair_valid;assumption).
   set(lg:=logic_ie false::logic_ie true::V293_quiet_exit_args run n locked aop enabled ir si ci).
   assert(P:getasrt(xfp nil lg t)=[|V293_quiet_exit_valid run n locked si|] ** qext run n locked aop enabled ir si ci t).
   { unfold xfp,lg,V293_all_exact_dynamic_fpre,V293_exit_path,V293_quiet_exact_exit_fpre,V293_quiet_exact_exit_pre.
     rewrite V293_quiet_exit_roundtrip by assumption;reflexivity. }
   assert(F:forall result,getasrt(xfq nil result lg t)=[|result=None|] **
   qext run(V293_exit_quiet_depth run n)locked aop enabled ir si ci t).
   { intro result;unfold xfq,lg,V293_all_exact_dynamic_fpost,V293_exit_path,V293_quiet_exact_exit_fpost,V293_quiet_exact_exit_post.
     rewrite V293_quiet_exit_roundtrip by assumption;reflexivity. }
   eapply conseq_rule with(p:=getasrt(xfp nil lg t) ** (V293_quiet_pair_half run ** callerframe))
   (q:=EX result:option val,getasrt(xfq nil result lg t) ** (V293_quiet_pair_half run ** callerframe)).
   + rewrite P;intros s H;apply V293_quiet_pair_split in H;sep auto.
   + intros s[result H];rewrite F in H.
     assert(K:s |=qext run(V293_exit_quiet_depth run n)locked aop enabled ir si ci t **
      (V293_quiet_pair_half run ** callerframe))by(sep auto).
     unfold n in K;rewrite V293_quiet_pair_depth in K by assumption.
     apply V293_quiet_pair_combine;exact K.
   + apply V293_OSIntExit_all_exact_quiet_call;try assumption.
     unfold V293_quiet_pair_half;split;[exact Logic.I|exact GF].
Qed.
Theorem V293_interrupt_quiet_pair : forall Spec sd RI r ri enter exit t run nest locked
 aop enabled ir si ci callerframe,
 run<256 ->nest<256 ->locked<256 ->gettopis si<=INUM ->
 (run=1 ->nest<255) ->(run=1 ->1<=nest \/ 0<locked) ->GoodFrm callerframe ->
 Spec enter=Some(efp,efq,(Tvoid,nil)) ->Spec exit=Some(xfp,xfq,(Tvoid,nil)) ->
 InfRules Spec sd V293_shared_li RI r ri
 (ext run nest locked aop enabled ir si ci t ** callerframe)
 (sseq(scall enter nil)(scall exit nil))
 (ext run nest locked aop enabled ir si ci t ** callerframe)t.
Proof.
 intros;eapply seq_rule;[apply(V293_OSIntEnter_open_call running nesting lock brun bn bl Aemp Logic.I);assumption| ].
 apply V293_interrupt_quiet_exit_after_enter;assumption.
Qed.
End QuietPair.

Section QuietReadyIRQ.
Variables unmap group rows high table target current counter running nesting lock:var.
Variables bt bg br bh bp bo bc bk brun bn bl:block.
Variable rest:list(addr*type).
Let prefix:=V293_ready_irq_prefix bt bh bc bk.
Let cells:=prefix++[((brun,0%Z),Tint8);((bn,0%Z),Tint8);((bl,0%Z),Tint8)]++rest.
Let Inv0:=V293_ready_dynamic_exit_inv target bt bg br bh bp bc bk brun bn bl rest.
Let efp:=V293_enter_open_fpre running nesting lock brun bn bl Aemp Logic.I.
Let efq:=V293_enter_open_fpost running nesting lock brun bn bl Aemp Logic.I.
Let xfp:=V293_all_exact_dynamic_fpre unmap group rows high table target current counter running nesting lock
 bt bg br bh bp bo bc bk brun bn bl rest Aemp Logic.I.
Let xfq:=V293_all_exact_dynamic_fpost unmap group rows high table target current counter running nesting lock
 bt bg br bh bp bo bc bk brun bn bl rest Aemp Logic.I.
Definition V293_quiet_irq_kept := V293ReadyTaskInvariant.V293_ready_core br bg bp **
 (V293_dispatch_cell target V293_tcb_type ** (V293_storage prefix ** V293_storage rest)).
Definition V293_quiet_irq_physical run nest locked t :=
 V293_quiet_globals running nesting lock brun bn bl **
 (Amapsto(brun,0%Z)Tint8 true(V293_byteval run) **
 (Amapsto(bn,0%Z)Tint8 true(V293_byteval nest) **
 (Amapsto(bl,0%Z)Tint8 true(V293_byteval locked) **
 (p_local V293_shared_li t nil ** (V293_quiet_irq_kept ** A_dom_lenv nil))))).
Definition V293_quiet_irq_snapshot run nest locked aop enabled ir si ci t :=
 V293_enter_open_external running nesting lock brun bn bl Aemp run nest locked aop enabled ir si ci t **
 (V293_quiet_irq_kept ** A_dom_lenv nil).
Lemma V293_quiet_irq_kept_good : GoodFrm V293_quiet_irq_kept.
Proof.
 unfold V293_quiet_irq_kept;split.
 - unfold V293_ready_core;cbn[GoodFrm];intros ct ts es now.
   unfold V293_shared_ready_records;split.
   + split.
     * unfold CurTid;intro tq;unfold Agvarmapsto,Agvarenv',Aptrmapsto;cbn[GoodFrm];auto.
     * unfold V293_shared_fields;cbn[GoodFrm];auto.
   + apply V293_ready_payload_frame.
 - split.
   + unfold V293_dispatch_cell;intro v;cbn[GoodFrm];split;[exact Logic.I| ].
     unfold Agvarmapsto,Agvarenv',Aptrmapsto;cbn[GoodFrm];auto.
   + split;apply V293_storage_frame_good.
Qed.
Lemma V293_quiet_irq_physical_good : forall run nest locked t,
 GoodFrm(V293_quiet_irq_physical run nest locked t).
Proof.
 intros;unfold V293_quiet_irq_physical;split.
 - unfold V293_quiet_globals;cbn[GoodFrm];auto.
 - split;[exact Logic.I| ];split;[exact Logic.I| ];split;[exact Logic.I| ];split.
   + apply V293_exact_local_frame;apply V293_switch_li_good.
   + split;[apply V293_quiet_irq_kept_good|exact Logic.I].
Qed.
Lemma V293_quiet_irq_snapshot_close : forall run nest locked i si aop t,
 run<256 ->nest<256 ->locked<256 ->
 V293_quiet_irq_snapshot run nest locked aop false(fun _:hid=>false)(i::si)nil t ==>
 V293_irq_ready_closed br bg bp target V293_tcb_type cells i si aop t nil.
Proof.
 intros run nest locked i si aop t Run Nest Lock s H.
 assert(Globals:V293_quiet_globals running nesting lock brun bn bl ==>Aemp).
 { intros st [G _];apply agvarenv_elim in G;exact(proj2 G). }
 unfold V293_quiet_irq_snapshot,V293_enter_open_external,V293_quiet_irq_kept in H.
 eapply astar_mono in H;[ |apply astar_mono;[intros st K;exact K|apply astar_mono;[intros st K;exact K|apply astar_mono;[exact Globals|intros st K;exact K]]]|intros st K;exact K].
 assert(P:s |= (Amapsto(brun,0%Z)Tint8 true(V293_byteval run) **
 (Amapsto(bn,0%Z)Tint8 true(V293_byteval nest) **
 Amapsto(bl,0%Z)Tint8 true(V293_byteval locked))) **
 (<||aop||> ** OS[(fun _:hid=>false),false,i::si,nil] **
 (p_local V293_shared_li t nil ** (V293ReadyTaskInvariant.V293_ready_core br bg bp **
 (V293_dispatch_cell target V293_tcb_type ** (V293_storage prefix ** (V293_storage rest ** A_dom_lenv nil)))))))by(sep auto).
 eapply astar_mono in P;[ |apply astar_mono;[apply V293_storage_byte_close;exact Run|apply astar_mono;apply V293_storage_byte_close;assumption]|intros st K;exact K].
 assert(P2:s |= (V293_storage prefix ** V293_storage([((brun,0%Z),Tint8);((bn,0%Z),Tint8);((bl,0%Z),Tint8)]++rest)) **
 (<||aop||> ** OS[(fun _:hid=>false),false,i::si,nil] **
 (p_local V293_shared_li t nil ** (V293ReadyTaskInvariant.V293_ready_core br bg bp **
 (V293_dispatch_cell target V293_tcb_type ** A_dom_lenv nil)))))by(cbn[app V293_storage];clear H;sep auto).
 eapply astar_mono in P2;[ |apply V293_storage_append|intros st K;exact K].
 apply V293_irq_ready_open_close.
 unfold V293_irq_ready_open,V293_irq_ready_frame,V293_ready_storage_core,V293_ready_storage_extra,cells.
 clear H P;sep auto.
Qed.
Theorem V293_interrupt_quiet_continuous : forall Spec enter exit intspec i ir si t ret id run nest locked,
 run<256 ->nest<256 ->locked<256 ->gettopis(i::si)<=INUM ->
 (run=1 ->nest<255) ->(run=1 ->1<=nest \/ 0<locked) ->
 Spec enter=Some(efp,efq,(Tvoid,nil)) ->Spec exit=Some(xfp,xfq,(Tvoid,nil)) ->
 Some ret=BuildintRet i intspec ir si Inv0 V293_shared_li t nil ->
 (forall j,ir j=false) ->(0<=Int.unsigned id<Z.of_nat INUM)%Z ->i=Z.to_nat(Int.unsigned id) ->
 InfRules Spec V293_scheduler V293_shared_li Inv0 arfalse ret
 (V293_quiet_irq_snapshot run nest locked(spec_done None)false(isrupd ir i true)(i::si)nil t)
 (V293_irq_source_wrapper enter exit id)Afalse t.
Proof.
 intros Spec enter exit intspec i ir si t ret id run nest locked Run Nest Lock Top Room Quiet Enter Exit Ret Clear Bound Index.
 unfold V293_irq_source_wrapper;eapply seq_rule with
 (p':=V293_quiet_irq_snapshot run nest locked(spec_done None)false(fun _:hid=>false)(i::si)nil t).
 - eapply conseq_rule with
   (p:=<||spec_done None||> ** OS[isrupd ir i true,false,i::si,nil] ** V293_quiet_irq_physical run nest locked t)
   (q:=<||spec_done None||> ** OS[isrupd(isrupd ir i true)i false,false,i::si,nil] ** V293_quiet_irq_physical run nest locked t).
   + unfold V293_quiet_irq_snapshot,V293_enter_open_external,V293_quiet_irq_physical;intros s H;sep auto.
   + rewrite V293_irq_clear_update by assumption.
     unfold V293_quiet_irq_snapshot,V293_enter_open_external,V293_quiet_irq_physical;intros s H;sep auto.
   + apply eoi_ieoff_rule;[exact Bound|exact Index|apply V293_quiet_irq_physical_good].
 - eapply seq_rule.
   + unfold V293_quiet_irq_snapshot;apply(V293_OSIntEnter_open_call running nesting lock brun bn bl Aemp Logic.I);try assumption.
     split;[apply V293_quiet_irq_kept_good|exact Logic.I].
   + eapply seq_rule with(p':=V293_quiet_irq_snapshot run nest locked(spec_done None)false(fun _:hid=>false)(i::si)nil t).
     * unfold V293_quiet_irq_snapshot;apply(V293_interrupt_quiet_exit_after_enter
       unmap group rows high table target current counter running nesting lock bt bg br bh bp bo bc bk brun bn bl rest);try assumption.
       split;[apply V293_quiet_irq_kept_good|exact Logic.I].
     * eapply conseq_rule with(p:=V293_irq_ready_closed br bg bp target V293_tcb_type cells i si(spec_done None)t nil).
       -- apply V293_quiet_irq_snapshot_close;assumption.
       -- intros s H;exact H.
       -- apply V293_irq_ready_exint with(intspec:=intspec)(ir:=ir);assumption.
Qed.
End QuietReadyIRQ.
