Require Import CertiOS.certiucos.v293.code.V293OSIntEnter.
Require Import CertiOS.certiucos.v293.code.V293OSSchedNew.
Require Import CertiOS.framework.proof.toptheorem.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitResourceBridge.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitBuilders.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitChangedInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitReadyInternal.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptReadyEnvironment.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptExitEnvironment.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptFunctionEnvironment.
(* Bound LocalInv is derived from the original body resources, including running. *)
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitHandoffHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitBoundarySwitch.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedStoragePrefix.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedStorageTail.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchStorage.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchState.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedShared.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedChange.
Require Import CertiOS.certiucos.v293.code.V293OSSchedChange.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCritical.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedPrefix.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedSwitch.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.sep_combine_lemmas.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitDispatchHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitReadyHandoff.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyTaskInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyStorageInvariant.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.code.V293ReadyTable.

Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitReadyDispatch.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedExactPrefix.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedExactLocal.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitReadyBody.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitChangedBody.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntEnterInternal.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitBody.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitNondispatch.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitDispatch.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedGuards.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TimeAccess.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickDelayHoare.

Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitLocalDispatch.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitExact.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptBindings.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitUnifiedInternal.
Lemma V293_local_storage_resumed_excrit : forall Spec li r ri tid aop br bg bp cells target tp si ci P,
 GoodFrm P ->
 InfRules Spec V293_scheduler li(V293_ready_storage_inv br bg bp target tp cells)r ri
 (<||aop||> ** SWINVt(V293_ready_storage_inv br bg bp target tp cells)tid ** Ais si ** Acs(false::ci) ** P)
 (sprim excrit)
 (<||aop||> ** SWINVt(V293_ready_storage_inv br bg bp target tp cells)tid ** Ais si ** Acs ci ** P)tid.
Proof.
 intros Spec li r ri tid aop br bg bp cells target tp si ci P GP.
 eapply conseq_rule with
 (p:=<||aop||> ** OS[(fun _:hid=>false),false,si,false::ci] **
   (V293_ready_storage_full br bg bp target tp cells tid ** P))
 (q:=<||aop||> ** OS[(fun _:hid=>false),false,si,ci] **
   (V293_ready_storage_full br bg bp target tp cells tid ** P)).
 - intros st H.
   assert(S:st |= SWINVt(V293_ready_storage_inv br bg bp target tp cells)tid **
    (<||aop||> ** (Ais si ** (Acs(false::ci) ** P))))by(clear -H;sep auto).
   eapply astar_mono in S;[ |apply V293_ready_storage_full_open|intros s HS;exact HS].
   unfold V293_shared_flags in S;sep normal in S;sep destruct S.
   assert(T:st |= isrclr ** Atrue)by(clear -S;sep auto).
   eapply astar_mono in T;[ |apply V293_ready_isr_clear|intros s HS;exact HS].
   apply astar_l_aisr_elim in T as[T _].
   pose proof(@astar_l_aisr_intro st(fun _:hid=>false)_ S T)as ST.
   clear S;rename ST into S;sep auto.
   all: destruct S as[ir[AI[Clear Empty]]];exact Empty.
 - intros st H.
   assert(S:st |= OS[(fun _:hid=>false),false,si,ci] **
    (<||aop||> ** (V293_ready_storage_full br bg bp target tp cells tid ** P)))by(clear -H;sep auto).
   eapply astar_mono in S;[ |apply V293_disabled_clear_flags|intros s HS;exact HS].
   assert(T:st |= (V293_shared_flags ** V293_ready_storage_full br bg bp target tp cells tid) **
    (<||aop||> ** (Ais si ** (Acs ci ** P))))by(clear -S;sep auto).
   eapply astar_mono in T;[ |apply V293_ready_storage_full_close|intros s HS;exact HS].
   clear -T;sep auto.
 - apply excrit2_rule;split;[apply V293_ready_storage_full_frame|exact GP].
Qed.

Section BoundBody.
Variables unmap group rows high table target current counter running nesting lock saved:var.
Variables bt bg br bh bp bo bc bk brun bn bl bs:block.
Let tp:=V293_tcb_type.
Let li:=V293_irq_bound_li running nesting lock brun bn bl.
Let Hli:=V293_irq_bound_good running nesting lock brun bn bl.
Let globals:=V293_quiet_globals running nesting lock brun bn bl.
Variables lo hi nc:nat.
Variable entries:list val.
Variable rest:list(addr*type).
Variable tid:Modules.tid.
Variable tasks:TcbMod.map.
Variable events:EcbMod.map.
Variable now:int32.
Variable aop:spec_code.
Variable si:list hid.
Variable ci:list bool.
Variable px:asrt.
Let controls:= [((brun,0%Z),Tint8);((bn,0%Z),Tint8);((bl,0%Z),Tint8)].
Let returned:=controls++rest.
Let arrays:=V293_array_cells bt 0 1 Tint8(length V293_ready_table)++returned.
Let cells:=((bk,0%Z),Tint32)::((bh,0%Z),Tint8)::((bc,0%Z),Tint8)::arrays.
Let inv:=V293_ready_storage_inv br bg bp target tp cells.
Local Notation bodybindings := (V293_exit_ready_body_bindings nesting lock bn bl).
Local Notation core := (V293_exit_ready_body_core unmap group rows high table target current counter nesting lock
 bt bg br bh bp bo bc bk bn bl lo hi nc entries rest tid tasks events now px).
Local Notation bodydata := (V293_exit_ready_body_data unmap group rows high table target current counter running nesting lock saved
 bt bg br bh bp bo bc bk brun bn bl bs lo hi nc entries rest tid tasks events now px).
Let env:=V293_sched_globals unmap group rows high bt bg br bh **
 (V293_prefix_bindings table high target tp bp bo **
 (V293_handoff_binding high bh ** bodybindings)).
Let dispatchpx:=bodybindings ** (V293_handoff_binding running brun **
 (V293_time_cell true saved bs(Vint32 Int.zero) ** px)).
Definition V293_exit_bound_body_resumed critical:=
 V293_exit_exact_dispatch_resumed unmap group rows high table target current counter
 bt bg br bh bp bo bc bk returned tid aop si critical dispatchpx.
Let private:=V293_counter_bindings counter bk **
 ((V293_handoff_binding high bh ** V293_handoff_binding current bc) **
 ((V293_sched_globals unmap group rows high bt bg br bh **
 V293_prefix_bindings table high target tp bp bo) ** dispatchpx)).
Definition V293_exit_bound_body_post critical:=
 <||aop||> ** ((SWINV inv ** p_local li tid nil) **
 ((Ais si ** Acs critical) ** private)).
Lemma V293_bound_current_from_names : forall st,
 st |=CurTid tid ** Atrue ->st |=globals ** Atrue ->st |=CurLINV li tid.
Proof.
 intros st Current Names.
 pose proof(V293_bound_dispatch_add_globals running nesting lock brun bn bl _ st Names Current)as S.
 eapply astar_mono in S;[ |intros s HS;exact HS|apply astar_mono;
 [apply V293_current_to_exact_local|intros s HS;exact HS]].
 apply V293_irq_bound_current with(extra:=Atrue).
 assert(T:st |= (p_local V293_shared_li tid nil ** globals) ** Atrue)by(clear -S;sep auto).
 eapply astar_mono;[apply V293_irq_bound_local_close|intros s HS;exact HS|exact T].
Qed.
Lemma V293_bound_core_frame_local : forall hv out c R,
 core hv out c ** (V293_handoff_binding running brun ** R) ==>CurLINV li tid.
Proof.
 intros hv out c R st H.
 assert(C:st |=CurTid tid ** Atrue).
 { assert(S:st |= (GV OSTCBCur@(Tptr tp)|->Vptr tid) ** Atrue)
   by(unfold V293_exit_ready_body_core in H;clear -H;sep auto).
   eapply astar_mono in S;[ |apply GV_separate_rw|intros s HS;exact HS].
   unfold CurTid;clear -S;sep auto. }
 apply V293_bound_current_from_names;[exact C| ].
 assert(N:st |=V293_quiet_bindings running nesting lock brun bn bl ** Atrue).
 { unfold V293_exit_ready_body_core,V293_exit_ready_body_bindings,
   V293_quiet_bindings,V293_exit_guard_bindings in H|-*;clear -H;sep auto. }
 eapply astar_mono;[apply V293_quiet_forget_names|intros s HS;exact HS|exact N].
Qed.
Lemma V293_exit_bound_body_post_pack : forall critical,
 V293_exit_bound_body_resumed critical ==>V293_exit_bound_body_post critical.
Proof.
 intros critical st H.
 assert(Names:st |=globals ** Atrue).
 { assert(N:st |=V293_quiet_bindings running nesting lock brun bn bl ** Atrue).
   { unfold V293_exit_bound_body_resumed,V293_exit_exact_dispatch_resumed,
     V293_ready_exit_resumed,dispatchpx,V293_exit_ready_body_bindings,
     V293_quiet_bindings,V293_exit_guard_bindings in H|-*;clear -H;sep auto. }
   eapply astar_mono;[apply V293_quiet_forget_names|intros s HS;exact HS|exact N]. }
 unfold V293_exit_bound_body_resumed,V293_exit_exact_dispatch_resumed,V293_ready_exit_resumed,SWINVt in H.
 fold(CurTid tid)in H.
 assert(S:st |=CurTid tid ** (<||aop||> ** (SWINV inv ** ((Ais si ** Acs critical) ** private))))
 by(unfold private;clear -H;sep auto).
 eapply astar_mono in S;[ |apply V293_current_to_exact_local|intros s HS;exact HS].
 pose proof(V293_bound_dispatch_add_globals running nesting lock brun bn bl _ st Names S)as T.
 assert(U:st |= (p_local V293_shared_li tid nil ** globals) **
 (<||aop||> ** (SWINV inv ** ((Ais si ** Acs critical) ** private))))by(clear -T;sep auto).
 eapply astar_mono in U;[ |apply V293_irq_bound_local_close|intros s HS;exact HS].
 unfold V293_exit_bound_body_post;clear -U;sep auto.
Qed.

Theorem V293_OSIntExit_bound_body : forall Spec sched_id nest hv out c old,
 lo<256 ->hi<256 ->(exists p,V293_bitmap_ready lo hi p) ->nc<256 ->nest<=1 ->
 V293_ready_select lo hi(V293_ready_group lo hi)<>nc ->
 V293_bitmap_tasks lo hi tasks ->V293_priority_table entries tasks ->
 Forall(fun v=>rule_type_val_match(Tptr tp)v=true)entries ->indom tasks tid ->GoodFrm px ->
 Spec sched_id=Some
 (V293_sched_exact_fpre unmap group rows high bt bg br bh li V293_opened_inv Hli,
 V293_sched_exact_fpost unmap group rows high bt bg br bh li V293_opened_inv Hli,(Tvoid,nil)) ->
 InfRules Spec V293_scheduler li inv
 (fun v=>[|v=None|] ** V293_exit_bound_body_post ci) Afalse
 (<||sched;;aop||> ** OS[(fun _:hid=>false),false,si,ci] **
 bodydata nest hv out c old)
 (V293_exit_boundary_body running nesting lock saved table high target current counter sched_id
 (V293_interrupt_handoff high current target)) Afalse tid.
Proof.
 intros Spec sched_id nest hv out c old Low High Ready Cur Nest Different Bitmap Table Pointer Member GP Lookup.
 unfold V293_exit_boundary_body.
 eapply seq_rule with(p':=<||sched;;aop||> ** OS[(fun _:hid=>false),false,si,ci] **
 bodydata nest hv out c(Vint32 Int.zero)).
 - eapply conseq_rule;[ | |apply(V293_time_zero Spec V293_scheduler li inv _ _ tid(sched;;aop)
  (V293_handoff_byte running brun 1 **
  (V293_rdy_raw_cells(V293_exit_cells bn bl nest 0)(core hv out c) **
  OS[(fun _:hid=>false),false,si,ci]))saved bs old)].
   + unfold V293_exit_ready_body_data;intros st H;sep auto.
   + unfold V293_exit_ready_body_data;intros st H;sep auto.
   + intros st H;apply V293_bound_core_frame_local with(hv:=hv)(out:=out)(c:=c)(R:=Atrue).
     unfold V293_exit_cells,V293_interrupt_cells,V293_handoff_byte in H;
     cbn[V293_rdy_raw_cells]in H;clear -H;sep auto.
 - eapply seq_rule with(p':=V293_exit_bound_body_resumed ci).
   + eapply V293_tick_known_ift_hoare with(flag:=true).
     * intros st H.
       assert(G:st |= (V293_handoff_binding running brun **
        Amapsto(brun,0%Z)Tint8 true(V293_byteval 1)) ** Atrue)
        by(unfold V293_exit_ready_body_data,V293_handoff_byte in H;clear -H;sep auto).
       eapply astar_mono in G;[ |apply astar_mono;[intros s HS;exact HS|apply separate_rw2ro]|intros s HS;exact HS].
       assert(B:st |= V293_guard_cell running brun 1 ** Atrue)
        by(unfold V293_guard_cell,V293_handoff_binding in *;clear -G;sep auto).
       destruct(V293_exit_running_eval running brun 1 Atrue st ltac:(lia)B)as[V T].
       split;[exact V|split;[exact T|discriminate]].
     * eapply seq_rule.
       -- apply encrit2_rule;apply V293_exit_ready_body_data_good;exact GP.
       -- eapply seq_rule with(p':=V293_exit_bound_body_resumed(false::ci)).
          ++ eapply conseq_rule with
             (p:=<||sched;;aop||> ** V293_rdy_raw_cells(V293_exit_cells bn bl nest 0)
              (core hv out c **
              (V293_time_cell true saved bs(Vint32 Int.zero) **
              (V293_handoff_byte running brun 1 ** OS[(fun _:hid=>false),false,si,false::ci])))).
             ** unfold V293_exit_ready_body_data,V293_exit_cells,V293_interrupt_cells;
                cbn[V293_rdy_raw_cells];intros st H;sep auto.
             ** intros st H;exact H.
             ** pose proof(V293_OSIntExit_nesting_dispatch_hoare Spec V293_scheduler li inv (fun v=>[|v=None|] ** V293_exit_bound_body_post ci) Afalse tid(sched;;aop)
                 nesting lock bn bl nest 0
                 (core hv out c **
                 (V293_time_cell true saved bs(Vint32 Int.zero) **
                 (V293_handoff_byte running brun 1 ** OS[(fun _:hid=>false),false,si,false::ci])))
                 (V293_exit_boundary_dispatch table high target current counter sched_id(V293_interrupt_handoff high current target))
                 (V293_exit_bound_body_resumed(false::ci))ltac:(lia)ltac:(lia))as Dispatch.
                assert(E:V293_exit_enabled nest 0=true)by(apply V293_exit_enabled_iff;lia).
                rewrite E in Dispatch;apply Dispatch.
                --- apply V293_star_env_l;apply V293_exit_ready_body_core_env.
                --- intros st H;apply V293_bound_core_frame_local with(hv:=hv)(out:=out)(c:=c)(R:=Atrue).
                    unfold V293_handoff_byte in H;clear -H;sep auto.
                --- intros Depth Locked.
                    eapply conseq_rule with(p:=V293_exit_bound_dispatch_entry unmap group rows high table target current counter running nesting lock saved
                     bt bg br bh bp bo bc bk brun bn bl bs lo hi nc entries rest tid tasks events now aop si(false::ci)px out c).
                    +++ intros st H;apply V293OSIntExitLocalDispatch.V293_exit_bound_body_lend with(hv:=hv);try assumption.
                        rewrite Depth in H. unfold V293_exit_ready_body_data,V293_exit_cells,V293_interrupt_cells in *;
                        cbn[V293_rdy_raw_cells]in *;clear -H;sep auto.
                    +++ intros st H;exact H.
                    +++ apply V293_OSIntExit_bound_dispatch;assumption.
          ++ unfold V293_exit_bound_body_resumed,V293_exit_exact_dispatch_resumed,
             V293_ready_exit_resumed.
             apply V293_local_storage_resumed_excrit.
             unfold dispatchpx,V293_exit_ready_body_bindings,V293_handoff_binding,
              V293_counter_bindings,V293_sched_globals,V293_prefix_bindings.
             cbn[GoodFrm];repeat split;try exact I;try apply V293_time_cell_good;exact GP.
   + apply ret_rule;intros st H;apply astar_l_apure_intro;
     [apply V293_exit_bound_body_post_pack;exact H|reflexivity].
Qed.
End BoundBody.
Section BoundBuilders.
Variables unmap group rows high table target current counter running nesting lock saved:var.
Variables bt bg br bh bp bo bc bk brun bn bl:block.
Let tp:=V293_tcb_type.
Let li:=V293_irq_bound_li running nesting lock brun bn bl.
Let Hli:=V293_irq_bound_good running nesting lock brun bn bl.
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
Definition V293_bound_builder_post t(result:option val):=
 [|result=None|] ** (<||aop||> **
 ((SWINV inv ** p_local li t nil) **
 ((Ais si ** Acs ci) **
 (V293_sched_globals unmap group rows high bt bg br bh ** (globals ** extra))))).
Lemma V293_bound_builder_post_good : forall t result,
 GoodFunAsrt(V293_bound_builder_post t result).
Proof.
 intros;unfold V293_bound_builder_post.
 split;[exact Logic.I| ];split;[exact Logic.I| ];split.
 - split;[unfold SWINV,isrclr,invlth_isr;cbn[GoodFunAsrt];repeat split;try exact Logic.I;
   intros;apply V293_starinv_function_assertion|apply V293_exact_local_good;exact Hli].
 - split;[cbn[GoodFunAsrt];tauto| ];split.
   + unfold V293_sched_globals;cbn[GoodFunAsrt];tauto.
   + split;[apply V293_exit_builder_globals_good|exact EG].
Qed.
Definition V293_bound_builder_fpost:fpost.
Proof.
 intros vl result lg t;refine(@mkfunasrt(V293_bound_builder_post t result)_).
 apply V293_bound_builder_post_good.
Defined.
Let valid t:=V293_changed_builder_valid tp lo hi nc nest entries tasks t.
Let entry t:=V293_ready_builder_pre unmap group rows high table target current counter running nesting lock bt bg br bh bp bo bc bk brun bn bl lo hi nc nest entries rest tasks events now hv out c aop si ci extra t.
Let external t:=V293_ready_builder_external unmap group rows high table target current counter running nesting lock bt bg br bh bp bo bc bk brun bn bl lo hi nc nest entries rest tasks events now hv out c aop si ci extra t.
Let fp:=V293_ready_builder_fpre unmap group rows high table target current counter running nesting lock bt bg br bh bp bo bc bk brun bn bl lo hi nc nest entries rest tasks events now hv out c aop si ci extra EG.
Let data bs t value:=
 V293_exit_ready_body_data unmap group rows high table target current counter running nesting lock saved
 bt bg br bh bp bo bc bk brun bn bl bs lo hi nc entries rest t tasks events now frame nest hv out c value.
Let returned bs t:=
 V293_exit_bound_body_post unmap group rows high table target current counter running nesting lock saved
 bt bg br bh bp bo bc bk brun bn bl bs rest t aop si frame ci.
Lemma V293_bound_builder_pack : forall bs t result,
 [|result=None|] ** returned bs t ==>
 V293_exit_builder_cells saved ** V293_bound_builder_post t result ** V293_exit_builder_domain saved.
Proof.
 intros bs t result st Held.
 unfold returned,V293_exit_bound_body_post in Held.
 assert(U:st |= V293_handoff_binding high bh ** ((caller ** V293_handoff_binding running brun) **
 ([|result=None|] ** (<||aop||> ** ((SWINV inv ** p_local li t nil) **
 ((Ais si ** Acs ci) ** (V293_sched_globals unmap group rows high bt bg br bh **
 (V293_time_cell true saved bs(Vint32 Int.zero) ** (extra ** V293_exit_builder_domain saved))))))))).
 { unfold caller,V293_exit_caller_bindings,V293_exit_guard_bindings,
 V293_exit_ready_body_bindings,V293_handoff_binding,frame,inv,V293_ready_builder_inv in *;
 clear -Held;sep auto. }
 eapply astar_mono in U;[apply astar_l_aemp_elim in U| |intros s HS;exact HS].
 2:{ intros s[Bind _];apply agvarenv_elim in Bind;exact(proj2 Bind). }
 eapply astar_mono in U;[ |apply V293_exit_builder_forget_names|intros s HS;exact HS].
 unfold V293_bound_builder_post,V293_exit_builder_cells,V293_time_cell,V293_time_binding,
 Alvarmapsto,Alvarenv',Aptrmapsto in *.
 cbn[addrval_to_addr]in *;clear -U;sep auto.
Qed.
Theorem V293_OSIntExit_bound_builder_contract : forall P f Spec sched_id vl lg t pre post,
 table<>saved ->high<>saved ->target<>saved ->current<>saved ->
 counter<>saved ->nesting<>saved ->lock<>saved ->running<>saved ->GoodFrm extra ->
 Spec sched_id=Some
 (V293_sched_exact_fpre unmap group rows high bt bg br bh li V293_opened_inv Hli,
 V293_sched_exact_fpost unmap group rows high bt bg br bh li V293_opened_inv Hli,(Tvoid,nil)) ->
 P f=Some(V293_exit_boundary_function running nesting lock saved table high target current counter sched_id
 (V293_interrupt_handoff high current target)) ->
 Some pre=BuildPreI P f vl lg fp t ->
 Some post=BuildRetI P f vl lg V293_bound_builder_fpost t ->
 InfRules Spec V293_scheduler li inv post Afalse pre
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
 change(Some post=Some(fun result=>V293_exit_builder_cells saved ** V293_bound_builder_post t result ** V293_exit_builder_domain saved))in Post.
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
   + intro result;apply V293_bound_builder_pack.
   + intros st HS;exact HS.
   + unfold data,returned,inv,V293_ready_builder_inv.
     apply V293_OSIntExit_bound_body;try assumption.
     unfold frame,V293_exit_builder_domain;cbn[GoodFrm];tauto.
Qed.
Lemma V293_bound_builder_pre_local : forall t,
 entry t ==>CurLINV li t.
Proof.
 intros t st H.
 assert(C:st |=CurTid t ** Atrue).
 { assert(S:st |= (GV OSTCBCur@(Tptr tp)|->Vptr t) ** Atrue).
   { unfold entry,V293_ready_builder_pre,V293_ready_builder_external,
     V293_ready_builder_memory in H;clear -H;sep auto. }
   eapply astar_mono in S;[ |apply GV_separate_rw|intros s HS;exact HS].
   unfold CurTid;clear -S;sep auto. }
 assert(N:st |=V293_quiet_globals running nesting lock brun bn bl ** Atrue).
 { assert(B:st |=globals ** Atrue)
   by(unfold entry,V293_ready_builder_pre,V293_ready_builder_external in H;clear -H;sep auto).
   eapply astar_mono;[ |intros s HS;exact HS|exact B].
   intros s G;unfold globals,V293_exit_builder_globals in G.
   destruct G as[_[_[_[_[GN[GL GR]]]]]].
   unfold V293_quiet_globals;split;[exact GR|split;assumption]. }
 pose proof(V293_bound_dispatch_add_globals running nesting lock brun bn bl _ st N C)as S.
 eapply astar_mono in S;[ |intros s HS;exact HS|apply astar_mono;
 [apply V293_current_to_exact_local|intros s HS;exact HS]].
 apply V293_irq_bound_current with(extra:=Atrue).
 assert(T:st |= (p_local V293_shared_li t nil ** V293_quiet_globals running nesting lock brun bn bl) ** Atrue)
 by(clear -S;sep auto).
 eapply astar_mono;[apply V293_irq_bound_local_close|intros s HS;exact HS|exact T].
Qed.
Lemma V293_bound_builder_post_local : forall t result,
 V293_bound_builder_post t result ==>CurLINV li t.
Proof.
 intros t result st H;unfold V293_bound_builder_post in H.
 eapply V293_star_CurLINV_r;[ |exact H].
 eapply V293_star_CurLINV_r;eapply V293_star_CurLINV_l;eapply V293_star_CurLINV_r.
 apply V293_exact_local_weakens.
Qed.
Theorem V293_OSIntExit_bound_call : forall Spec sd RI r ri exit tid callerframe,
 GoodFrm callerframe ->
 Spec exit=Some(fp,V293_bound_builder_fpost,(Tvoid,nil)) ->
 InfRules Spec sd li RI r ri
 (entry tid ** callerframe)(scall exit nil)
 (EX result:option val,V293_bound_builder_post tid result ** callerframe)tid.
Proof.
 intros Spec sd RI r ri exit tid callerframe GF Lookup.
 eapply call_rule with(pre:=fp)(post:=V293_bound_builder_fpost)
 (vl:=nil)(logicl:=nil)(tp:=Tvoid)(tl:=nil).
 - exact GF.
 - exact Lookup.
 - intros st H;exact H.
 - intros st H;reflexivity.
 - reflexivity.
 - apply V293_bound_builder_pre_local.
 - intros st[result H];apply V293_bound_builder_post_local with(result:=result);exact H.
Qed.
Let efp:=V293_enter_bound_fpre running nesting lock brun bn bl Aemp Logic.I.
Let efq:=V293_enter_bound_fpost running nesting lock brun bn bl Aemp Logic.I.
Let sfp:=V293_sched_exact_fpre unmap group rows high bt bg br bh li V293_opened_inv Hli.
Let sfq:=V293_sched_exact_fpost unmap group rows high bt bg br bh li V293_opened_inv Hli.
Definition V293_bound_irq_spec exit enter sched:funspec:=
 fun f=>if Z.eq_dec f exit then Some(fp,V293_bound_builder_fpost,(Tvoid,nil))
 else if Z.eq_dec f enter then Some(efp,efq,(Tvoid,nil))
 else if Z.eq_dec f sched then Some(sfp,sfq,(Tvoid,nil))else None.
Let program exit enter sched y:=
 V293_ready_irq_unit unmap group rows high table target current counter running nesting lock saved exit enter sched y.
Theorem V293_bound_irq_WFFunEnv : forall exit enter sched y,
 exit<>enter ->exit<>sched ->enter<>sched ->
 unmap<>y ->group<>y ->rows<>y ->high<>y ->
 table<>saved ->high<>saved ->target<>saved ->current<>saved ->
 counter<>saved ->nesting<>saved ->lock<>saved ->running<>saved ->GoodFrm extra ->
 WFFunEnv(program exit enter sched y)(V293_bound_irq_spec exit enter sched)
 V293_scheduler li inv.
Proof.
 intros exit enter sched y XE XS ES UY GY RY HY T H G C K N L R GF.
 pose proof(V293_exit_env_entries exit enter sched running nesting unmap group rows high y saved
 (V293_exit_boundary_body running nesting lock saved table high target current counter sched
 (V293_interrupt_handoff high current target)) XE XS ES)as(CodeX&CodeE&CodeS).
 assert(Callee:V293_bound_irq_spec exit enter sched sched=Some(sfp,sfq,(Tvoid,nil))).
 { unfold V293_bound_irq_spec;repeat destruct Z.eq_dec;try congruence;reflexivity. }
 split.
 - intro f;unfold program,V293_ready_irq_unit,V293_exit_env_unit,V293_irq_internal_unit,pumerge,
   V293_OSIntEnter_unit,V293_OSSchedNew_internal_unit,V293_bound_irq_spec.
   destruct(Z.eq_dec f exit),(Z.eq_dec f enter),(Z.eq_dec f sched);
   split;intros[x E];try discriminate;eexists;reflexivity.
 - intros f pre post ty tl Lookup;unfold V293_bound_irq_spec in Lookup.
   destruct(Z.eq_dec f exit)as[E|NE].
   + subst f;inversion Lookup;subst pre post ty tl.
     exists dnil;exists(dcons saved Tint32 dnil).
     exists(V293_exit_boundary_body running nesting lock saved table high target current counter sched
     (V293_interrupt_handoff high current target)).
     split;[exact CodeX| ];split;[constructor| ];split;[reflexivity| ].
     intros vl p q lg t Pre Post;eapply V293_OSIntExit_bound_builder_contract;try eassumption.
   + destruct(Z.eq_dec f enter)as[E|NEE].
     * subst f;inversion Lookup;subst pre post ty tl.
       exists dnil;exists dnil;exists(V293_OSIntEnter_body running nesting).
       split;[exact CodeE| ];split;[constructor| ];split;[reflexivity| ].
       intros vl p q lg t Pre Post;eapply V293_OSIntEnter_bound_contract;try eassumption.
     * destruct(Z.eq_dec f sched)as[E|NES];[ |discriminate].
       subst f;inversion Lookup;subst pre post ty tl.
       exists dnil;exists(dcons y Tint8 dnil);exists(V293_OSSchedNew_body unmap group rows high y).
       split;[exact CodeS| ];split;[constructor| ];split;[reflexivity| ].
       intros vl p q lg t Pre Post;eapply V293_OSSchedNew_exact_contract;try eassumption.
Qed.
Theorem V293_bound_irq_WFIFun : forall exit enter sched y,
 exit<>enter ->exit<>sched ->enter<>sched ->
 unmap<>y ->group<>y ->rows<>y ->high<>y ->
 table<>saved ->high<>saved ->target<>saved ->current<>saved ->
 counter<>saved ->nesting<>saved ->lock<>saved ->running<>saved ->GoodFrm extra ->
 WFIFun(program exit enter sched y)(V293_bound_irq_spec exit enter sched)
 V293_scheduler inv li.
Proof.
 intros;destruct(V293_bound_irq_WFFunEnv exit enter sched y
 H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14)as[Dom Body].
 split;[exact Dom| ];intros f p q ty tl Lookup.
 destruct(Body f p q ty tl Lookup)as(d1&d2&s&Code&Types&Decls&Checked).
 exists d1;exists d2;exists s;auto.
Qed.
End BoundBuilders.
