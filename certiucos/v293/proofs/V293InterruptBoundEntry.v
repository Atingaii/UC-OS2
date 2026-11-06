Require Import CertiOS.certiucos.v293.proofs.V293OSSchedPrefix.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptReadyEnvironment.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchState.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitReadyDynamic.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.code.V293ReadyTable.
(* Strong dispatch resources close into the actual outermost interrupt builder. *)
Require Import CertiOS.certiucos.v293.proofs.V293InterruptChangedContinuous.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptSameContinuous.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptBindings.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptQuietContinuous.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptReadyEnter.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntEnterOpenExact.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitReadyDispatch.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitBuilders.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyTaskInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyStorageInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchStorage.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedStoragePrefix.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.sep_combine_lemmas.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Lemma V293_outer_active_isr_inv : forall ir si,
 Aisr ir ** Ais(0::si) ==> isr_inv ** (Aisr ir ** Ais(0::si)).
Proof.
 intros ir si st H;pose proof H as Meta.
 apply astar_l_aisr_elim in Meta;destruct Meta as[ISR Meta].
 apply ais_elim in Meta;destruct Meta as[Stack Empty].
 assert(Inv:st|=isr_inv).
 { unfold isr_inv;exists ir;split.
   - apply aisr_intro;assumption.
   - exists 0;split.
     + apply atopis_intro;[exact Empty|unfold gettopis;rewrite Stack;reflexivity].
     + apply apure_intro;[exact Empty|intros;lia]. }
 apply V293_exit_empty_star;assumption.
Qed.
Lemma V293_outer_entry_pre : forall Inv0 li ir si aop t,
 (<||aop||> ** OS[isrupd ir 0 true,false,0::si,nil] **
 (getinv(Inv0 0) ** (A_dom_lenv nil ** p_local li t nil))) ==>
 ipreasrt' 0 ir si aop Inv0 ** p_local li t nil.
Proof.
 intros Inv0 li ir si aop t st H.
 assert(P:st|=(Aisr(isrupd ir 0 true) ** Ais(0::si)) **
 (<||aop||> ** Aie false ** Acs nil **
 (getinv(Inv0 0) ** (A_dom_lenv nil ** p_local li t nil))))by(sep auto).
 eapply astar_mono in P;[ |apply V293_outer_active_isr_inv|intros s K;exact K].
 unfold ipreasrt',invlth_noisr;cbn[starinv_noisr Nat.sub];clear H;sep auto.
Qed.

Section DispatchEntry.
Variables unmap group rows high table target current counter running nesting lock:var.
Variables bt bg br bh bp bo bc bk brun bn bl:block.
Variable rest:list(addr*type).
Variables lo hi nc:nat.
Variable entries:list val.
Variable tasks:TcbMod.map.
Variable events:EcbMod.map.
Variable now:int32.
Variables hv out:val.
Variable c:int32.
Let tp:=V293_tcb_type.
Let li:=V293_irq_bound_li running nesting lock brun bn bl.
Let Inv0:=V293_ready_dynamic_exit_inv target bt bg br bh bp bc bk brun bn bl rest.
Let oldsnapshot:=V293_quiet_irq_snapshot target running nesting lock bt bg br bh bp bc bk brun bn bl rest.
Let snapshot:=V293_irq_bound_snapshot target running nesting lock bt bg br bh bp bc bk brun bn bl rest.
Let changed:=V293_changed_irq_snapshot unmap group rows high table target current counter running nesting lock
 bt bg br bh bp bo bc bk brun bn bl rest lo hi nc entries tasks events now hv out c.
Let same:=V293_same_irq_snapshot unmap group rows high table target current counter running nesting lock
 bt bg br bh bp bo bc bk brun bn bl rest lo hi nc entries tasks events now hv out c.

Lemma V293_changed_entry_kept : forall nest aop ir si t,
 V293_ready_rel lo hi entries tasks ->
 Forall(fun v=>rule_type_val_match(Tptr tp)v=true)entries ->nc<256 ->
 rule_type_val_match Tint8 hv=true ->rule_type_val_match(Tptr tp)out=true ->
 changed nest aop ir si t ==>oldsnapshot 1 nest 0(sched;;aop)false ir si nil t.
Proof.
 intros nest aop ir si t Rel Types Cur High Output st H.
 apply V293_changed_enter_split in H.
 assert(P:st|=(V293_inputs_full bt bg br lo hi **
 (V293_array true bp 0 4(Tptr tp)entries **
 (V293_owned_task_records tasks ** V293_storage nil))) **
 (V293_enter_open_external running nesting lock brun bn bl Aemp 1 nest 0(sched;;aop)false ir si nil t **
 (GV OSTCBCur@(Tptr tp)|-r->Vptr t ** (V293_shared_fields t tasks events now **
 (GV target@(Tptr tp)|->out ** (PV(bh,Int.zero)@Tint8|->hv **
 (Amapsto(bc,0%Z)Tint8 true(V293_byteval nc) **
 (PV(bk,Int.zero)@Tint32|->Vint32 c ** (V293_storage rest ** A_dom_lenv nil))))))))).
 { unfold V293_changed_enter_frame,V293_changed_enter_payload,V293_exit_builder_globals in H.
   cbn[V293_storage];unfold tp in *;sep auto.
   assert(G:V293_exit_builder_globals table target current counter nesting lock running
    V293_tcb_type bp bo bc bk bn bl brun ==>Aemp).
   { intros s[B _];apply agvarenv_elim in B;exact(proj2 B). }
   unfold V293_exit_builder_globals in G.
   assert(S:V293_sched_globals unmap group rows high bt bg br bh ==>Aemp).
   { intros s[B _];apply agvarenv_elim in B;exact(proj2 B). }
   eapply astar_mono in H;[ |exact G|exact S].
   sep auto. }
 eapply astar_mono in P;[ |apply V293_retained_arrays_ready;assumption|intros s K;exact K].
 rewrite app_nil_r in P.
 assert(Core:st|=V293ReadyTaskInvariant.V293_ready_core br bg bp **
 (V293_enter_open_external running nesting lock brun bn bl Aemp 1 nest 0(sched;;aop)false ir si nil t **
 (GV target@(Tptr tp)|->out ** (PV(bh,Int.zero)@Tint8|->hv **
 (Amapsto(bc,0%Z)Tint8 true(V293_byteval nc) **
 (PV(bk,Int.zero)@Tint32|->Vint32 c **
 (V293_storage(V293_array_cells bt 0 1 Tint8(length V293_ready_table)) **
 (V293_storage rest ** A_dom_lenv nil)))))))).
 { unfold V293ReadyTaskInvariant.V293_ready_core,V293_shared_ready_records,CurTid;clear H;sep auto. }
 unfold oldsnapshot,V293_quiet_irq_snapshot,V293_quiet_irq_kept,V293_dispatch_cell,V293_ready_irq_prefix;
 cbn[V293_storage];unfold V293_storage_cell;clear H P;sep auto;
 try(apply V293_byte_type;exact Cur);try exact High;try exact Output;reflexivity.
Qed.
Lemma V293_same_entry_kept : forall nest aop ir si t,
 V293_ready_rel lo hi entries tasks ->
 Forall(fun v=>rule_type_val_match(Tptr tp)v=true)entries ->nc<256 ->
 rule_type_val_match Tint8 hv=true ->rule_type_val_match(Tptr tp)out=true ->
 same nest aop ir si t ==>oldsnapshot 1 nest 0 aop false ir si nil t.
Proof.
 intros nest aop ir si t Rel Types Cur High Output st H.
 apply V293_same_irq_enter_split in H.
 assert(P:st|=(V293_inputs_full bt bg br lo hi **
 (V293_array true bp 0 4(Tptr tp)entries **
 (V293_owned_task_records tasks ** V293_storage nil))) **
 (V293_enter_open_external running nesting lock brun bn bl Aemp 1 nest 0 aop false ir si nil t **
 (CurTid t ** (V293_shared_fields t tasks events now **
 (GV target@(Tptr tp)|->out ** (PV(bh,Int.zero)@Tint8|->hv **
 (Amapsto(bc,0%Z)Tint8 true(V293_byteval nc) **
 (PV(bk,Int.zero)@Tint32|->Vint32 c ** (V293_storage rest ** A_dom_lenv nil))))))))).
 { unfold V293_same_irq_payload in H;cbn[V293_storage];unfold tp in *;sep auto.
   assert(G:V293_prefix_output V293_tcb_type bo out **
    (V293_sched_globals unmap group rows high bt bg br bh **
    V293_exit_builder_globals table target current counter nesting lock running
    V293_tcb_type bp bo bc bk bn bl brun) ==>
    GV target@(Tptr V293_tcb_type)|->out).
   { intros s K.
     eapply astar_mono in K;[ |intros s2 H2;exact H2|apply V293_same_irq_bindings_target].
     unfold Agvarmapsto;exists bo;unfold V293_prefix_output in K;
     unfold Agvarenv',Aptrmapsto;cbn[addrval_to_addr];sep auto. }
   eapply G;sep auto. }
 eapply astar_mono in P;[ |apply V293_retained_arrays_ready;assumption|intros s K;exact K].
 rewrite app_nil_r in P.
 assert(Core:st|=V293ReadyTaskInvariant.V293_ready_core br bg bp **
 (V293_enter_open_external running nesting lock brun bn bl Aemp 1 nest 0 aop false ir si nil t **
 (GV target@(Tptr tp)|->out ** (PV(bh,Int.zero)@Tint8|->hv **
 (Amapsto(bc,0%Z)Tint8 true(V293_byteval nc) **
 (PV(bk,Int.zero)@Tint32|->Vint32 c **
 (V293_storage(V293_array_cells bt 0 1 Tint8(length V293_ready_table)) **
 (V293_storage rest ** A_dom_lenv nil)))))))).
 { unfold V293ReadyTaskInvariant.V293_ready_core,V293_shared_ready_records;clear H;sep auto. }
 unfold oldsnapshot,V293_quiet_irq_snapshot,V293_quiet_irq_kept,V293_dispatch_cell,V293_ready_irq_prefix;
 cbn[V293_storage];unfold V293_storage_cell;clear H P;sep auto;
 try(apply V293_byte_type;exact Cur);try exact High;try exact Output;reflexivity.
Qed.
Lemma V293_bound_outer_snapshot_pre : forall run nest locked aop ir si t,
 run<256 ->nest<256 ->locked<256 ->
 snapshot run nest locked aop false(isrupd ir 0 true)(0::si)nil t ==>
 ipreasrt' 0 ir si aop Inv0 **p_local li t nil.
Proof.
 intros run nest locked aop ir si t Run Nest Lock st H.
 unfold snapshot,V293_irq_bound_snapshot,V293_enter_bound_external,V293_quiet_irq_kept in H.
 assert(P:st|=(Amapsto(brun,0%Z)Tint8 true(V293_byteval run) **
 (Amapsto(bn,0%Z)Tint8 true(V293_byteval nest) **
 Amapsto(bl,0%Z)Tint8 true(V293_byteval locked))) **
 (<||aop||> ** OS[isrupd ir 0 true,false,0::si,nil] **
 (V293ReadyTaskInvariant.V293_ready_core br bg bp **
 (V293_dispatch_cell target tp ** (V293_storage(V293_ready_irq_prefix bt bh bc bk) **
 (V293_storage rest ** (A_dom_lenv nil **p_local li t nil)))))))by(unfold li;sep auto).
 eapply astar_mono in P;[ |apply astar_mono;
 [apply V293_storage_byte_close;exact Run|apply astar_mono;apply V293_storage_byte_close;assumption]|intros s K;exact K].
 assert(P2:st|=(V293_storage(V293_ready_irq_prefix bt bh bc bk) **
 V293_storage([((brun,0%Z),Tint8);((bn,0%Z),Tint8);((bl,0%Z),Tint8)]++rest)) **
 (<||aop||> ** OS[isrupd ir 0 true,false,0::si,nil] **
 (V293ReadyTaskInvariant.V293_ready_core br bg bp **
 (V293_dispatch_cell target tp ** (A_dom_lenv nil **p_local li t nil)))))
 by(cbn[app V293_storage];clear H;sep auto).
 eapply astar_mono in P2;[ |apply V293_storage_append|intros s K;exact K].
 apply V293_outer_entry_pre.
 change(getinv(Inv0 0))with(V293_ready_storage_core br bg bp target tp
 (V293_ready_irq_prefix bt bh bc bk++[((brun,0%Z),Tint8);((bn,0%Z),Tint8);((bl,0%Z),Tint8)]++rest)).
 unfold V293_ready_storage_core,V293_ready_storage_extra;clear H P;sep auto.
Qed.
Theorem V293_changed_entry_BuildintPre : forall nest aop ir si t intspec pre,
 V293_ready_rel lo hi entries tasks ->
 Forall(fun v=>rule_type_val_match(Tptr tp)v=true)entries ->nc<256 ->nest<256 ->
 rule_type_val_match Tint8 hv=true ->rule_type_val_match(Tptr tp)out=true ->
 intspec 0=Some(sched;;aop) ->Some pre=BuildintPre 0 intspec ir si Inv0 li t nil ->
 changed nest aop(isrupd ir 0 true)(0::si)t ==>pre.
Proof.
 intros nest aop ir si t intspec pre Rel Types Cur Nest High Output Spec Builder st H.
 unfold BuildintPre in Builder;rewrite Spec in Builder;inversion Builder;subst pre.
 apply V293_bound_outer_snapshot_pre with(run:=1)(nest:=nest)(locked:=0);try lia.
 apply V293_irq_bound_snapshot_pack;apply V293_changed_entry_kept;assumption.
Qed.
Theorem V293_same_entry_BuildintPre : forall nest aop ir si t intspec pre,
 V293_ready_rel lo hi entries tasks ->
 Forall(fun v=>rule_type_val_match(Tptr tp)v=true)entries ->nc<256 ->nest<256 ->
 rule_type_val_match Tint8 hv=true ->rule_type_val_match(Tptr tp)out=true ->
 intspec 0=Some aop ->Some pre=BuildintPre 0 intspec ir si Inv0 li t nil ->
 same nest aop(isrupd ir 0 true)(0::si)t ==>pre.
Proof.
 intros nest aop ir si t intspec pre Rel Types Cur Nest High Output Spec Builder st H.
 unfold BuildintPre in Builder;rewrite Spec in Builder;inversion Builder;subst pre.
 apply V293_bound_outer_snapshot_pre with(run:=1)(nest:=nest)(locked:=0);try lia.
 apply V293_irq_bound_snapshot_pack;apply V293_same_entry_kept;assumption.
Qed.
End DispatchEntry.

