(* The full normalized changed-priority body, on the opened clear-ISR,
   interrupt-disabled boundary. Shared control bytes are not a switch frame. *)
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitDispatchHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitSamePriority.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TimeAccess.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitBody.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickDelayHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedStoragePrefix.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedStorageTail.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchStorage.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedSwitch.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import CertiOS.tactics.sepauto.sep_combine_lemmas.
Require Import Coq.Lists.List Lia.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitHandoffHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitBoundarySwitch.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchState.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedShared.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedChange.
Require Import CertiOS.certiucos.v293.code.V293OSSchedChange.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCritical.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedPrefix.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedISRContext.
Require Import CertiOS.certiucos.v293.code.V293OSIntExit.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitNondispatch.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitDispatch.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntEnterInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedGuards.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Import ListNotations.
Local Open Scope nat_scope.

Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitChangedBody.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitBuilders.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitResourceBridge.

Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitReadyBody.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitChangedInternal.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyStorageInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyTaskInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitReadyDispatch.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitReadyHandoff.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.code.V293ReadyTable.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitReadyInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitExact.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedExactLocal.
Require Import CertiOS.certiucos.v293.code.V293OSSchedNew.
Section ExactBuilders.
Variables unmap group rows high table target current counter running nesting lock saved:var.
Variables bt bg br bh bp bo bc bk brun bn bl:block.
Let tp:=V293_tcb_type.
Variables lo hi nc nest:nat.
Variable entries:list val.
Variable rest:list(addr*type).
Variable tasks:TcbMod.map.
Variable events:EcbMod.map.
Variable now:int32.
Variables hv out:val.
Variable c:int32.
Variable aop:spec_code.
Variable si:list hid.
Variable ci:list bool.
Variable extra:asrt.
Variable EG:GoodFunAsrt extra.
Let globals:=V293_exit_builder_globals table target current counter nesting lock running tp bp bo bc bk bn bl brun.
Let caller:=V293_exit_caller_bindings high table target tp bp bo current counter nesting lock bc bk bn bl.
Let frame:=extra ** V293_exit_builder_domain saved.
Let inv:=V293_ready_builder_inv target bt bg br bh bp bc bk brun bn bl rest.
Definition V293_exact_builder_post t(result:option val):=
 [|result=None|] ** (<||aop||> **
 ((SWINV inv ** p_local V293_shared_li t nil) **
 ((Ais si ** Acs ci) **
 (V293_sched_globals unmap group rows high bt bg br bh ** (globals ** extra))))).
Lemma V293_exact_builder_post_good : forall t result,
 GoodFunAsrt(V293_exact_builder_post t result).
Proof.
 intros;unfold V293_exact_builder_post.
 split;[exact Logic.I| ];split;[exact Logic.I| ];split.
 - split;[unfold SWINV,isrclr,invlth_isr;cbn[GoodFunAsrt];repeat split;try exact Logic.I;
   intros;apply V293_starinv_function_assertion|apply V293_exact_local_good;exact V293_switch_li_good].
 - split;[cbn[GoodFunAsrt];tauto| ];split.
   + unfold V293_sched_globals;cbn[GoodFunAsrt];tauto.
   + split;[apply V293_exit_builder_globals_good|exact EG].
Qed.
Definition V293_exact_builder_fpost:fpost.
Proof.
 intros vl result lg t;refine(@mkfunasrt(V293_exact_builder_post t result)_).
 apply V293_exact_builder_post_good.
Defined.
Let valid t:=V293_changed_builder_valid tp lo hi nc nest entries tasks t.
Let entry t:=V293_ready_builder_pre unmap group rows high table target current counter running nesting lock bt bg br bh bp bo bc bk brun bn bl lo hi nc nest entries rest tasks events now hv out c aop si ci extra t.
Let external t:=V293_ready_builder_external unmap group rows high table target current counter running nesting lock bt bg br bh bp bo bc bk brun bn bl lo hi nc nest entries rest tasks events now hv out c aop si ci extra t.
Let fp:=V293_ready_builder_fpre unmap group rows high table target current counter running nesting lock bt bg br bh bp bo bc bk brun bn bl lo hi nc nest entries rest tasks events now hv out c aop si ci extra EG.
Let data bs t value:=
 V293_exit_ready_body_data unmap group rows high table target current counter running nesting lock saved
 bt bg br bh bp bo bc bk brun bn bl bs lo hi nc entries rest t tasks events now frame nest hv out c value.
Let returned bs t:=
 V293_exit_exact_body_post unmap group rows high table target current counter running nesting lock saved
 bt bg br bh bp bo bc bk brun bn bl bs rest t aop si frame ci.
Lemma V293_exact_builder_pack : forall bs t result,
 [|result=None|] ** returned bs t ==>
 V293_exit_builder_cells saved ** V293_exact_builder_post t result ** V293_exit_builder_domain saved.
Proof.
 intros bs t result st Held.
 unfold returned,V293_exit_exact_body_post in Held.
 assert(U:st |= V293_handoff_binding high bh ** ((caller ** V293_handoff_binding running brun) **
 ([|result=None|] ** (<||aop||> ** ((SWINV inv ** p_local V293_shared_li t nil) **
 ((Ais si ** Acs ci) ** (V293_sched_globals unmap group rows high bt bg br bh **
 (V293_time_cell true saved bs(Vint32 Int.zero) ** (extra ** V293_exit_builder_domain saved))))))))).
 { unfold caller,V293_exit_caller_bindings,V293_exit_guard_bindings,
 V293_exit_ready_body_bindings,V293_handoff_binding,frame,inv,V293_ready_builder_inv in *;
 clear -Held;sep auto. }
 eapply astar_mono in U;[apply astar_l_aemp_elim in U| |intros s HS;exact HS].
 2:{ intros s[Bind _];apply agvarenv_elim in Bind;exact(proj2 Bind). }
 eapply astar_mono in U;[ |apply V293_exit_builder_forget_names|intros s HS;exact HS].
 unfold V293_exact_builder_post,V293_exit_builder_cells,V293_time_cell,V293_time_binding,
 Alvarmapsto,Alvarenv',Aptrmapsto in *.
 cbn[addrval_to_addr]in *;clear -U;sep auto.
Qed.
Theorem V293_OSIntExit_exact_builder_contract : forall P f Spec sched_id vl lg t pre post,
 table<>saved ->high<>saved ->target<>saved ->current<>saved ->
 counter<>saved ->nesting<>saved ->lock<>saved ->running<>saved ->GoodFrm extra ->
 Spec sched_id=Some
 (V293_sched_exact_fpre unmap group rows high bt bg br bh V293_shared_li V293_opened_inv V293_switch_li_good,
 V293_sched_exact_fpost unmap group rows high bt bg br bh V293_shared_li V293_opened_inv V293_switch_li_good,(Tvoid,nil)) ->
 P f=Some(V293_exit_boundary_function running nesting lock saved table high target current counter sched_id
 (V293_interrupt_handoff high current target)) ->
 Some pre=BuildPreI P f vl lg fp t ->
 Some post=BuildRetI P f vl lg V293_exact_builder_fpost t ->
 InfRules Spec V293_scheduler V293_shared_li inv post Afalse pre
 (V293_exit_boundary_body running nesting lock saved table high target current counter sched_id
 (V293_interrupt_handoff high current target)) Afalse t.
Proof.
 intros P f Spec sched_id vl lg t pre post T H G C K N L R GF Lookup Body Pre Post.
 unfold BuildPreI in Pre;rewrite Body in Pre.
 destruct vl as[ |v vl].
 2:{ assert(E:dl_vl_match dnil(rev(v::vl))=false).
     { destruct(rev(v::vl))eqn:Rev;[ |reflexivity].
       apply(f_equal(@rev val))in Rev;rewrite rev_involutive in Rev;discriminate. }
     unfold V293_exit_boundary_function in Pre;rewrite E in Pre;discriminate. }
 change(Some pre=Some(V293_exit_builder_cells saved ** entry t ** V293_exit_builder_domain saved))in Pre.
 inversion Pre;subst pre.
 unfold BuildRetI in Post;rewrite Body in Post.
 change(Some post=Some(fun result=>V293_exit_builder_cells saved ** V293_exact_builder_post t result ** V293_exit_builder_domain saved))in Post.
 inversion Post;subst post.
 unfold entry,V293_ready_builder_pre.
 eapply conseq_rule with(p:=(V293_exit_builder_cells saved ** external t **
 V293_exit_builder_domain saved) ** [|valid t|]).
 - intros st HS;clear -HS;sep auto.
 - intros st HS;exact HS.
 - apply pure_split_rule;intros[Low[High[Ready[Cur[Nest[Different[Bitmap[Table[Pointer Member]]]]]]]]].
   eapply conseq_rule;[apply V293_ready_builder_unpack;assumption|intros st HS;exact HS| ].
   apply ex_intro_rule;intro old;apply ex_intro_rule;intro bs.
   eapply r_conseq_rule with(r:=fun result=>[|result=None|] ** returned bs t).
   + intro result;apply V293_exact_builder_pack.
   + intros st HS;exact HS.
   + unfold data,returned,inv,V293_ready_builder_inv.
     apply V293_OSIntExit_exact_body;try assumption.
     unfold frame,V293_exit_builder_domain;cbn[GoodFrm];tauto.
Qed.
(* The two original normalized function bodies share one ambient invariant.
   This fixed changed-case specification does not replace the dynamic table. *)
Definition V293_exit_exact_unit exit sched_id y:progunit:=
 fun f=>if Z.eq_dec f exit then
 Some(V293_exit_boundary_function running nesting lock saved table high target current counter sched_id
 (V293_interrupt_handoff high current target))
 else if Z.eq_dec f sched_id then Some(V293_OSSchedNew_function unmap group rows high y)else None.
Definition V293_exit_exact_spec exit sched_id:funspec:=
 fun f=>if Z.eq_dec f exit then Some(fp,V293_exact_builder_fpost,(Tvoid,nil))
 else if Z.eq_dec f sched_id then Some
 (V293_sched_exact_fpre unmap group rows high bt bg br bh V293_shared_li V293_opened_inv V293_switch_li_good,
 V293_sched_exact_fpost unmap group rows high bt bg br bh V293_shared_li V293_opened_inv V293_switch_li_good,
 (Tvoid,nil))else None.
Theorem V293_OSIntExit_exact_WFFunEnv : forall exit sched_id y,
 exit<>sched_id ->unmap<>y ->group<>y ->rows<>y ->high<>y ->
 table<>saved ->high<>saved ->target<>saved ->current<>saved ->
 counter<>saved ->nesting<>saved ->lock<>saved ->running<>saved ->GoodFrm extra ->
 WFFunEnv(V293_exit_exact_unit exit sched_id y)(V293_exit_exact_spec exit sched_id)
 V293_scheduler V293_shared_li inv.
Proof.
 intros exit sched_id y Dist UY GY RY HY T H G C K N L R GF.
 assert(CodeX:V293_exit_exact_unit exit sched_id y exit=Some
 (V293_exit_boundary_function running nesting lock saved table high target current counter sched_id
 (V293_interrupt_handoff high current target))).
 { unfold V293_exit_exact_unit;repeat destruct Z.eq_dec;try congruence;reflexivity. }
 assert(CodeS:V293_exit_exact_unit exit sched_id y sched_id=Some(V293_OSSchedNew_function unmap group rows high y)).
 { unfold V293_exit_exact_unit;repeat destruct Z.eq_dec;try congruence;reflexivity. }
 assert(Callee:V293_exit_exact_spec exit sched_id sched_id=Some
 (V293_sched_exact_fpre unmap group rows high bt bg br bh V293_shared_li V293_opened_inv V293_switch_li_good,
 V293_sched_exact_fpost unmap group rows high bt bg br bh V293_shared_li V293_opened_inv V293_switch_li_good,
 (Tvoid,nil))).
 { unfold V293_exit_exact_spec;repeat destruct Z.eq_dec;try congruence;reflexivity. }
 split.
 - intro f;unfold V293_exit_exact_unit,V293_exit_exact_spec.
   destruct(Z.eq_dec f exit), (Z.eq_dec f sched_id);
   split;intros[x E];try discriminate;eexists;reflexivity.
 - intros f p q ty tl Lookup;unfold V293_exit_exact_spec in Lookup.
   destruct(Z.eq_dec f exit)as[E|NE].
   + subst f;inversion Lookup;subst p q ty tl.
     exists dnil;exists(dcons saved Tint32 dnil).
     exists(V293_exit_boundary_body running nesting lock saved table high target current counter sched_id
     (V293_interrupt_handoff high current target)).
     split;[exact CodeX| ];split;[constructor| ];split;[reflexivity| ].
     intros vl p q lg tid Pre Post;eapply V293_OSIntExit_exact_builder_contract;try eassumption.
   + destruct(Z.eq_dec f sched_id)as[E|NEs];[ |discriminate].
     subst f;inversion Lookup;subst p q ty tl.
     exists dnil;exists(dcons y Tint8 dnil);exists(V293_OSSchedNew_body unmap group rows high y).
     split;[exact CodeS| ];split;[constructor| ];split;[reflexivity| ].
     intros vl p q lg tid Pre Post;eapply V293_OSSchedNew_exact_contract;try eassumption.
Qed.
Lemma V293_exact_builder_pre_local : forall t,
 entry t ==>CurLINV V293_shared_li t.
Proof.
 intros t st H;unfold entry,V293_ready_builder_pre,V293_ready_builder_external,
 V293_ready_builder_memory in H.
 apply V293_full_current_local with(tp:=tp)(R:=Atrue);clear -H;sep auto.
Qed.
Lemma V293_exact_builder_post_local : forall t result,
 V293_exact_builder_post t result ==>CurLINV V293_shared_li t.
Proof.
 intros t result st H;unfold V293_exact_builder_post in H.
 eapply V293_star_CurLINV_r;[ |exact H].
 eapply V293_star_CurLINV_r;eapply V293_star_CurLINV_l;eapply V293_star_CurLINV_r.
 apply V293_exact_local_weakens.
Qed.
Theorem V293_OSIntExit_exact_call : forall Spec sd RI r ri exit tid callerframe,
 GoodFrm callerframe ->
 Spec exit=Some(fp,V293_exact_builder_fpost,(Tvoid,nil)) ->
 InfRules Spec sd V293_shared_li RI r ri
 (entry tid ** callerframe)(scall exit nil)
 (EX result:option val,V293_exact_builder_post tid result ** callerframe)tid.
Proof.
 intros Spec sd RI r ri exit tid callerframe GF Lookup.
 eapply call_rule with(pre:=fp)(post:=V293_exact_builder_fpost)
 (vl:=nil)(logicl:=nil)(tp:=Tvoid)(tl:=nil).
 - exact GF.
 - exact Lookup.
 - intros st H;exact H.
 - intros st H;reflexivity.
 - reflexivity.
 - apply V293_exact_builder_pre_local.
 - intros st[result H];apply V293_exact_builder_post_local with(result:=result);exact H.
Qed.
End ExactBuilders.
