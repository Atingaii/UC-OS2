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
Section ReadyBuilders.
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
Definition V293_ready_builder_inv:=
 V293_ready_storage_inv br bg bp target tp
 (((bk,0%Z),Tint32)::((bh,0%Z),Tint8)::((bc,0%Z),Tint8)::
 (V293_array_cells bt 0 1 Tint8(length V293_ready_table)++
 ([((brun,0%Z),Tint8);((bn,0%Z),Tint8);((bl,0%Z),Tint8)]++rest))).
Let valid t:=V293_changed_builder_valid tp lo hi nc nest entries tasks t.
Definition V293_ready_builder_memory t:=
 GV OSTCBCur@(Tptr tp)|->Vptr t **
 (V293_shared_fields t tasks events now ** (GV target@(Tptr tp)|->out **
 (V293_inputs_full bt bg br lo hi ** (PV(bh,Int.zero)@Tint8|->hv **
 (V293_array true bp 0 4(Tptr tp)entries **
 (Amapsto(bc,0%Z)Tint8 true(V293_byteval nc) ** (PV(bk,Int.zero)@Tint32|->Vint32 c **
 (V293_storage rest ** (V293_sched_globals unmap group rows high bt bg br bh ** (extra ** V293_owned_task_records tasks)))))))))).
Definition V293_ready_builder_external t:=
 <||sched;;aop||> ** OS[(fun _:hid=>false),false,si,ci] **
 (V293_ready_builder_memory t ** (globals **
 (Amapsto(brun,0%Z)Tint8 true(V293_byteval 1) **
 V293_rdy_raw_cells(V293_exit_cells bn bl nest 0)Aemp))).
Definition V293_ready_builder_pre t:=
 [|valid t|] ** V293_ready_builder_external t.
Definition V293_ready_builder_post t(result:option val):=
 [|result=None|] ** (<||aop||> ** SWINVt V293_ready_builder_inv t ** Ais si ** Acs ci **
 (V293_sched_globals unmap group rows high bt bg br bh ** (globals ** (extra ** Atrue)))).
Lemma V293_ready_builder_memory_good : forall t,
 GoodFunAsrt(V293_ready_builder_memory t).
Proof.
 intros. assert(A:GoodFunAsrt(V293_array true bp 0 4(Tptr tp)entries)).
 { generalize 0%Z;induction entries;intros;cbn[V293_array GoodFunAsrt];auto. }
 assert(Owned:GoodFunAsrt(V293_owned_task_records tasks)).
 { apply V293_inv_function_assertion;unfold V293_owned_task_records;apply V293_task_list_good. }
 unfold V293_ready_builder_memory,V293_shared_fields,V293_inputs_full,
 Agvarmapsto,Agvarenv',Aptrmapsto,V293_sched_globals.
 cbn[GoodFunAsrt];repeat split;try exact Logic.I;try exact EG;try exact A;try exact Owned;
 apply V293_inv_function_assertion;apply V293_storage_good.
Qed.
Lemma V293_ready_builder_external_good : forall t,
 GoodFunAsrt(V293_ready_builder_external t).
Proof.
 intros;unfold V293_ready_builder_external.
 split;[exact Logic.I| ];split;[cbn[GoodFunAsrt];tauto| ].
 split;[apply V293_ready_builder_memory_good| ].
 split;[apply V293_exit_builder_globals_good| ].
 unfold V293_exit_cells,V293_interrupt_cells;cbn[V293_rdy_raw_cells GoodFunAsrt];tauto.
Qed.
Lemma V293_ready_builder_post_good : forall t result,
 GoodFunAsrt(V293_ready_builder_post t result).
Proof.
 intros;unfold V293_ready_builder_post,SWINVt,SWINV,isrclr,invlth_isr,
 Agvarmapsto,Agvarenv',Aptrmapsto,V293_sched_globals.
 cbn[GoodFunAsrt];repeat split;try exact Logic.I;try exact EG;
 try apply V293_exit_builder_globals_good;intros;
 repeat split;try exact Logic.I;apply V293_starinv_function_assertion.
Qed.
Definition V293_ready_builder_fpre:fpre.
Proof.
 intros vl lg t;refine(@mkfunasrt(V293_ready_builder_pre t)_).
 split;[exact Logic.I|apply V293_ready_builder_external_good].
Defined.
Definition V293_ready_builder_fpost:fpost.
Proof.
 intros vl result lg t;refine(@mkfunasrt(V293_ready_builder_post t result)_).
 apply V293_ready_builder_post_good.
Defined.

Let data bs t value:=
 V293_exit_ready_body_data unmap group rows high table target current counter running nesting lock saved
 bt bg br bh bp bo bc bk brun bn bl bs lo hi nc entries rest t tasks events now frame nest hv out c value.
Let resumed bs t:=
 V293_exit_ready_body_resumed unmap group rows high table target current counter running nesting lock saved
 bt bg br bh bp bo bc bk brun bn bl bs rest t aop si frame ci.
Lemma V293_ready_builder_unpack : forall t,
 table<>saved ->high<>saved ->target<>saved ->current<>saved ->
 counter<>saved ->nesting<>saved ->lock<>saved ->running<>saved ->
 V293_exit_builder_cells saved ** V293_ready_builder_external t **
 V293_exit_builder_domain saved ==>
 EX old:val,EX bs:block,<||sched;;aop||> ** OS[(fun _:hid=>false),false,si,ci] ** data bs t old.
Proof.
 intros t T H G C K N L R st Held.
 assert(U:st |= (globals ** V293_exit_builder_domain saved) **
 (V293_exit_builder_cells saved ** (<||sched;;aop||> ** OS[(fun _:hid=>false),false,si,ci] **
 (V293_ready_builder_memory t ** (Amapsto(brun,0%Z)Tint8 true(V293_byteval 1) **
 V293_rdy_raw_cells(V293_exit_cells bn bl nest 0)Aemp))))).
 { unfold V293_ready_builder_external in Held;clear -Held;sep auto. }
 eapply astar_mono in U.
 2:{ apply V293_exit_builder_names with(high:=high);assumption. }
 2:{ intros s HS;exact HS. }
 assert(V:st |= (V293_sched_globals unmap group rows high bt bg br bh **
 V293_prefix_bindings table high target tp bp bo) **
 ((V293_handoff_binding current bc **
 (V293_counter_bindings counter bk ** V293_exit_guard_bindings nesting lock bn bl)) **
 ((V293_handoff_binding running brun ** V293_exit_builder_domain saved) **
 (V293_exit_builder_cells saved ** (<||sched;;aop||> ** OS[(fun _:hid=>false),false,si,ci] **
 (GV OSTCBCur@(Tptr tp)|->Vptr t **
 (V293_shared_fields t tasks events now ** (GV target@(Tptr tp)|->out **
 (V293_inputs_full bt bg br lo hi ** (PV(bh,Int.zero)@Tint8|->hv **
 (V293_array true bp 0 4(Tptr tp)entries **
 (Amapsto(bc,0%Z)Tint8 true(V293_byteval nc) ** (PV(bk,Int.zero)@Tint32|->Vint32 c **
 (V293_storage rest ** ((extra ** V293_owned_task_records tasks) ** (Amapsto(brun,0%Z)Tint8 true(V293_byteval 1) **
 V293_rdy_raw_cells(V293_exit_cells bn bl nest 0)Aemp)))))))))))))))).
 { unfold V293_ready_builder_memory,V293_exit_caller_bindings,V293_handoff_binding in *;clear -U;sep auto. }
 eapply astar_mono in V;[ |apply V293OSIntExitChangedInternal.V293_changed_builder_high_binding|intros s HS;exact HS].
 unfold data,V293_exit_ready_body_data,V293_exit_ready_body_core,V293_exit_ready_body_bindings,
 V293_exit_guard_bindings,V293_handoff_byte,V293_counter_cell,
 V293_exit_builder_cells,Alvarmapsto,Alvarenv',Aptrmapsto,
 V293_time_cell,V293_time_binding,frame in *.
 unfold V293_exit_cells,V293_interrupt_cells in *;cbn[V293_rdy_raw_cells]in *.
 cbn[addrval_to_addr]in *;clear -V;sep auto.
Qed.
Lemma V293_ready_builder_pack : forall bs t result,
 [|result=None|] ** resumed bs t ==>
 V293_exit_builder_cells saved ** V293_ready_builder_post t result ** V293_exit_builder_domain saved.
Proof.
 intros bs t result st Held.
 unfold resumed,V293_exit_ready_body_resumed,V293_ready_dispatch_resumed,
 V293_ready_exit_resumed in Held.
 assert(U:st |= (caller ** V293_handoff_binding running brun) **
 ([|result=None|] ** (<||aop||> ** SWINVt V293_ready_builder_inv t ** Ais si ** Acs ci **
 (V293_sched_globals unmap group rows high bt bg br bh **
 (V293_time_cell true saved bs(Vint32 Int.zero) ** (extra ** (V293_exit_builder_domain saved ** Atrue))))))).
 { unfold caller,V293_exit_caller_bindings,V293_exit_guard_bindings,
 V293_exit_ready_body_bindings,V293_handoff_binding,frame in *;clear -Held;sep auto. }
 eapply astar_mono in U;[ |apply V293_exit_builder_forget_names|intros s HS;exact HS].
 unfold V293_ready_builder_post,V293_exit_builder_cells,V293_time_cell,V293_time_binding,
 Alvarmapsto,Alvarenv',Aptrmapsto in *.
 cbn[addrval_to_addr]in *;clear -U;sep auto.
Qed.

Theorem V293_OSIntExit_ready_builder_contract : forall P f Spec sched_id vl lg t pre post,
 table<>saved ->high<>saved ->target<>saved ->current<>saved ->
 counter<>saved ->nesting<>saved ->lock<>saved ->running<>saved ->GoodFrm extra ->
 Spec sched_id=Some
 (V293_critical_fpre unmap group rows high bt bg br bh V293_shared_li V293_opened_inv V293_switch_li_good,
 V293_critical_fpost unmap group rows high bt bg br bh V293_shared_li V293_opened_inv V293_switch_li_good,(Tvoid,nil)) ->
 P f=Some(V293_exit_boundary_function running nesting lock saved table high target current counter sched_id
 (V293_interrupt_handoff high current target)) ->
 Some pre=BuildPreI P f vl lg V293_ready_builder_fpre t ->
 Some post=BuildRetI P f vl lg V293_ready_builder_fpost t ->
 InfRules Spec V293_scheduler V293_shared_li V293_ready_builder_inv post Afalse pre
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
 change(Some pre=Some(V293_exit_builder_cells saved ** V293_ready_builder_pre t ** V293_exit_builder_domain saved))in Pre.
 inversion Pre;subst pre.
 unfold BuildRetI in Post;rewrite Body in Post.
 change(Some post=Some(fun result=>V293_exit_builder_cells saved ** V293_ready_builder_post t result ** V293_exit_builder_domain saved))in Post.
 inversion Post;subst post.
 unfold V293_ready_builder_pre.
 eapply conseq_rule with(p:=(V293_exit_builder_cells saved ** V293_ready_builder_external t **
 V293_exit_builder_domain saved) ** [|valid t|]).
 - intros st HS;clear -HS;sep auto.
 - intros st HS;exact HS.
 - apply pure_split_rule;intros[Low[High[Ready[Cur[Nest[Different[Bitmap[Table[Pointer Member]]]]]]]]].
   eapply conseq_rule;[apply V293_ready_builder_unpack;assumption|intros st HS;exact HS| ].
   apply ex_intro_rule;intro old;apply ex_intro_rule;intro bs.
   eapply r_conseq_rule with(r:=fun result=>[|result=None|] ** resumed bs t).
   + intro result;apply V293_ready_builder_pack.
   + intros st HS;exact HS.
   + unfold data,resumed,V293_ready_builder_inv.
     apply V293_OSIntExit_ready_body;try assumption.
     unfold frame,V293_exit_builder_domain;cbn[GoodFrm];tauto.
Qed.
End ReadyBuilders.
