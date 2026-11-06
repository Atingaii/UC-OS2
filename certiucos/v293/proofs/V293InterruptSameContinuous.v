(* Continuous same-priority wrapper with borrowed resources returned to Inv. *)
Require Import CertiOS.certiucos.v293.proofs.V293InterruptChangedContinuous.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptQuietContinuous.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntEnterOpenExact.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitAllExactDynamic.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitSameExactInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitSameInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitResourceCodec.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntEnterInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitReadyDispatch.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitReadyDynamic.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitBuilders.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitUnifiedInternal.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptReadyEnvironment.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptReadyBoundary.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptSourceRoundtrip.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyStorageInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyTaskInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchStorage.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchState.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedStoragePrefix.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedPrefix.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedSwitch.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedExactLocal.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.code.V293ReadyTable.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.sep_combine_lemmas.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Section SameContinuous.
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
Let cells:=V293_ready_irq_prefix bt bh bc bk++
 [((brun,0%Z),Tint8);((bn,0%Z),Tint8);((bl,0%Z),Tint8)]++rest.
Let Inv0:=V293_ready_dynamic_exit_inv target bt bg br bh bp bc bk brun bn bl rest.
Let globals:=V293_exit_builder_globals table target current counter nesting lock running tp bp bo bc bk bn bl brun.
Let sg:=V293_sched_globals unmap group rows high bt bg br bh.
Let efp:=V293_enter_open_fpre running nesting lock brun bn bl Aemp Logic.I.
Let efq:=V293_enter_open_fpost running nesting lock brun bn bl Aemp Logic.I.
Let xfp:=V293_all_exact_dynamic_fpre unmap group rows high table target current counter running nesting lock
 bt bg br bh bp bo bc bk brun bn bl rest Aemp Logic.I.
Let xfq:=V293_all_exact_dynamic_fpost unmap group rows high table target current counter running nesting lock
 bt bg br bh bp bo bc bk brun bn bl rest Aemp Logic.I.
Definition V293_same_irq_read_full:=
 V293_inputs_full bt bg br lo hi ** (V293_array true bp 0 4(Tptr tp)entries **
 (Amapsto(bc,0%Z)Tint8 true(V293_byteval nc) ** Amapsto(brun,0%Z)Tint8 true(V293_byteval 1))).
Definition V293_same_irq_read_half:=
 V293_sched_inputs bt bg br lo hi(V293_ready_group lo hi) **
 (V293_array false bp 0 4(Tptr tp)entries **
 (Amapsto(bc,0%Z)Tint8 false(V293_byteval nc) ** Amapsto(brun,0%Z)Tint8 false(V293_byteval 1))).
Lemma V293_same_irq_read_borrow : V293_same_irq_read_full ==>
 V293_same_irq_read_half ** V293_same_irq_read_half.
Proof.
 intros st H;unfold V293_same_irq_read_full in H.
 eapply astar_mono in H;[ |apply V293_inputs_borrow|apply astar_mono;
 [apply V293_array_borrow|apply astar_mono;apply separate_rw2ro]].
 unfold V293_same_irq_read_half;sep auto.
Qed.
Lemma V293_same_irq_read_reunite : V293_same_irq_read_half ** V293_same_irq_read_half ==>
 V293_same_irq_read_full.
Proof.
 intros st H;unfold V293_same_irq_read_half in H.
 assert(P:st |=
 (V293_sched_inputs bt bg br lo hi(V293_ready_group lo hi) ** V293_sched_inputs bt bg br lo hi(V293_ready_group lo hi)) **
 ((V293_array false bp 0 4(Tptr tp)entries ** V293_array false bp 0 4(Tptr tp)entries) **
 ((Amapsto(bc,0%Z)Tint8 false(V293_byteval nc) ** Amapsto(bc,0%Z)Tint8 false(V293_byteval nc)) **
 (Amapsto(brun,0%Z)Tint8 false(V293_byteval 1) ** Amapsto(brun,0%Z)Tint8 false(V293_byteval 1)))))by(sep auto).
 unfold V293_same_irq_read_full;eapply astar_mono;[apply V293_inputs_reunite|apply astar_mono;
 [apply V293_array_reunite|apply astar_mono;apply combine_ro2rw_p1]|exact P].
Qed.
Definition V293_same_irq_payload t:=
 CurTid t ** (V293_shared_fields t tasks events now **
 (V293_prefix_output tp bo out ** (PV(bh,Int.zero)@Tint8|->hv **
 (PV(bk,Int.zero)@Tint32|->Vint32 c ** (V293_owned_task_records tasks **
 (V293_storage rest ** (sg ** (globals ** A_dom_lenv nil)))))))).
Definition V293_same_irq_physical nest t:=
 p_local V293_shared_li t nil ** (V293_same_irq_payload t **
 (V293_same_irq_read_full ** (Amapsto(bn,0%Z)Tint8 true(V293_byteval nest) **
 Amapsto(bl,0%Z)Tint8 true(V293_byteval 0)))).
Definition V293_same_irq_snapshot nest aop ir si t:=
 <||aop||> ** OS[ir,false,si,nil] ** V293_same_irq_physical nest t.
Lemma V293_same_irq_payload_good : forall t,GoodFrm(V293_same_irq_payload t).
Proof.
 intros;unfold V293_same_irq_payload,CurTid,V293_shared_fields,V293_prefix_output,sg,globals,
 V293_sched_globals,V293_exit_builder_globals,Agvarmapsto,Agvarenv',Aptrmapsto.
 cbn[GoodFrm];repeat split;try exact Logic.I;try(apply V293_owned_tasks_frame);apply V293_storage_frame_good.
Qed.
Lemma V293_same_irq_physical_good : forall nest t,GoodFrm(V293_same_irq_physical nest t).
Proof.
 intros;unfold V293_same_irq_physical;split.
 - unfold p_local,LINV,V293_shared_li,CurTid,Agvarmapsto,Agvarenv',Aptrmapsto;cbn[GoodFrm];auto.
 - split;[apply V293_same_irq_payload_good| ].
   unfold V293_same_irq_read_full,V293_inputs_full;cbn[GoodFrm];repeat split;try exact Logic.I;apply V293_array_good.
Qed.
Let enterframe t:=V293_same_irq_payload t **
 (V293_inputs_full bt bg br lo hi ** (V293_array true bp 0 4(Tptr tp)entries **
 Amapsto(bc,0%Z)Tint8 true(V293_byteval nc))).
Lemma V293_same_irq_enter_split : forall nest aop ir si t,
 V293_same_irq_snapshot nest aop ir si t ==>
 V293_enter_open_external running nesting lock brun bn bl Aemp 1 nest 0 aop false ir si nil t ** enterframe t.
Proof.
 intros nest aop ir si t st H.
 assert(P:st |= globals ** (<||aop||> ** OS[ir,false,si,nil] **
 (p_local V293_shared_li t nil ** (CurTid t ** (V293_shared_fields t tasks events now **
 (V293_prefix_output tp bo out ** (PV(bh,Int.zero)@Tint8|->hv **
 (PV(bk,Int.zero)@Tint32|->Vint32 c ** (V293_owned_task_records tasks **
 (V293_storage rest ** (sg ** (A_dom_lenv nil **
 (V293_same_irq_read_full ** (Amapsto(bn,0%Z)Tint8 true(V293_byteval nest) **
 Amapsto(bl,0%Z)Tint8 true(V293_byteval 0)))))))))))))))
 by(unfold V293_same_irq_snapshot,V293_same_irq_physical,V293_same_irq_payload in H;sep auto).
 eapply astar_mono in P;[ |apply V293_changed_globals_split|intros s K;exact K].
 unfold V293_enter_open_external,enterframe,V293_same_irq_payload,V293_same_irq_read_full in *;clear H;sep auto.
Qed.
Lemma V293_same_irq_enter_combine : forall nest aop ir si t,
 V293_enter_open_external running nesting lock brun bn bl Aemp 1 nest 0 aop false ir si nil t ** enterframe t ==>
 V293_same_irq_snapshot nest aop ir si t.
Proof.
 intros nest aop ir si t st H.
 assert(Q:V293_quiet_globals running nesting lock brun bn bl ==>Aemp).
 { intros s[Binding _];apply agvarenv_elim in Binding;exact(proj2 Binding). }
 unfold V293_enter_open_external in H.
 eapply astar_mono in H;[ |apply astar_mono;[intros s K;exact K|apply astar_mono;[intros s K;exact K|apply astar_mono;[exact Q|intros s K;exact K]]]|intros s K;exact K].
 unfold V293_same_irq_snapshot,V293_same_irq_physical,enterframe,V293_same_irq_read_full;sep auto.
Qed.
Theorem V293_interrupt_same_enter_call : forall Spec sd RI r ri enter aop ir si t,
 Spec enter=Some(efp,efq,(Tvoid,nil)) ->
 InfRules Spec sd V293_shared_li RI r ri
 (V293_same_irq_snapshot 0 aop ir si t)(scall enter nil)
 (V293_same_irq_snapshot 1 aop ir si t)t.
Proof.
 intros;eapply conseq_rule;[apply V293_same_irq_enter_split|apply V293_same_irq_enter_combine| ].
 change(InfRules Spec sd V293_shared_li RI r ri
 (V293_enter_open_external running nesting lock brun bn bl Aemp 1 0 0 aop false ir si nil t ** enterframe t)
 (scall enter nil)
 (V293_enter_open_external running nesting lock brun bn bl Aemp 1(V293_interrupt_nest_after 1 0)0 aop false ir si nil t ** enterframe t)t).
 apply(V293_OSIntEnter_open_call running nesting lock brun bn bl Aemp Logic.I);try lia.
 - unfold enterframe;split;[apply V293_same_irq_payload_good| ].
   unfold V293_inputs_full;cbn[GoodFrm];repeat split;try exact Logic.I;apply V293_array_good.
 - exact H.
Qed.
Definition V293_same_irq_index aop:=V293_mk_exit_snapshot lo hi nc 1 0 c out Vundef Vundef entries tasks aop.
Let ext nest highval output aop si t:=V293_same_exact_exit_external
 unmap group rows high table target current counter nesting lock running
 bt bg br bh bp bo bc bk bn bl brun tp V293_shared_li Aemp
 false(fun _:hid=>false)si nil lo hi entries tasks nc nest highval output c aop t.
Definition V293_same_irq_reserve t:=
 CurTid t ** (Aabsdata curtid(oscurt t) **
 (Aabsdata absecblsid(absecblist events) ** (Aabsdata ostmid(ostm now) **
 (V293_same_irq_read_half ** (V293_owned_task_records tasks ** (V293_storage rest ** A_dom_lenv nil)))))).
Lemma V293_same_irq_reserve_good : forall t,GoodFrm(V293_same_irq_reserve t).
Proof.
 intros;unfold V293_same_irq_reserve,V293_same_irq_read_half,V293_sched_inputs,CurTid,Agvarmapsto,Agvarenv',Aptrmapsto;
 repeat rewrite V293_read_bytes_array;
 cbn[GoodFrm];repeat split;try exact Logic.I;
 try apply V293_array_good;try apply V293_owned_tasks_frame;try apply V293_storage_frame_good.
Qed.
Lemma V293_same_irq_exit_borrow : forall aop si t,
 V293_same_irq_snapshot 1 aop(fun _:hid=>false)si t ==>
 ext 1 hv out aop si t ** V293_same_irq_reserve t.
Proof.
 intros aop si t st H.
 assert(P:st |= V293_same_irq_read_full **
 (<||aop||> ** OS[(fun _:hid=>false),false,si,nil] **
 (p_local V293_shared_li t nil ** (V293_same_irq_payload t **
 (Amapsto(bn,0%Z)Tint8 true(V293_byteval 1) ** Amapsto(bl,0%Z)Tint8 true(V293_byteval 0))))))
 by(unfold V293_same_irq_snapshot,V293_same_irq_physical in H;sep auto).
 eapply astar_mono in P;[ |apply V293_same_irq_read_borrow|intros s K;exact K].
 unfold ext,V293_same_exact_exit_external,V293_same_exact_exit_memory,V293_same_irq_reserve,
 V293_same_irq_payload,V293_same_irq_read_half,V293_shared_fields,V293_exit_cells,V293_interrupt_cells in *;
 cbn[V293_rdy_raw_cells]in *;rewrite V293_read_pointers_array.
 clear H;sep auto.
Qed.
Lemma V293_same_irq_pre : forall aop si t,
 V293_same_exit_valid si(V293_same_irq_index aop) ->
 V293_same_irq_snapshot 1 aop(fun _:hid=>false)si t ==>
 getasrt(xfp nil(logic_ie false::logic_ie false::
 V293_same_exit_args false(fun _:hid=>false)si nil(V293_same_irq_index aop))t) ** V293_same_irq_reserve t.
Proof.
 intros aop si t Valid;pose proof(proj1(proj2 Valid))as Bound.
 unfold xfp,V293_all_exact_dynamic_fpre,V293_exit_path,V293_same_exact_exit_fpre,V293_same_exact_exit_pre.
 rewrite V293_same_exit_index_roundtrip by exact Bound;cbn[getasrt].
 intros st H;apply V293_same_irq_exit_borrow in H.
 unfold V293_same_irq_index,ext in *;cbn[V293_xlo V293_xhi V293_xcurrent V293_xnest V293_xold V293_xcounter V293_xentries V293_xtasks V293_xaop].
 sep auto.
Qed.
Lemma V293_same_irq_bindings_target : sg ** globals ==>
 Agvarenv target(Tptr tp)(bo,0%Z).
Proof.
 intros st H;assert(S:sg ==>Aemp).
 { intros s[Binding _];apply agvarenv_elim in Binding;exact(proj2 Binding). }
 assert(G:globals ==>Agvarenv target(Tptr tp)(bo,0%Z)).
 { intros s[T[G _]];exact G. }
 eapply astar_mono in H;[ |exact S|exact G];apply astar_l_aemp_elim in H;exact H.
Qed.
Lemma V293_same_irq_resources_close : forall aop i si t selected,
 V293_ready_rel lo hi entries tasks ->nc<256 ->
 Forall(fun v=>rule_type_val_match(Tptr tp)v=true)entries ->
 ext 0(V293_byteval nc)(Vptr selected)aop(i::si)t ** V293_same_irq_reserve t ==>
 V293_irq_ready_closed br bg bp target tp cells i si aop t nil.
Proof.
 intros aop i si t selected Rel Cur Types st H.
 assert(P:st |= (V293_same_irq_read_half ** V293_same_irq_read_half) **
 ((sg ** globals) ** (<||aop||> ** OS[(fun _:hid=>false),false,i::si,nil] **
 (p_local V293_shared_li t nil ** (CurTid t ** (V293_shared_fields t tasks events now **
 (V293_prefix_output tp bo(Vptr selected) ** (PV(bh,Int.zero)@Tint8|->V293_byteval nc **
 (PV(bk,Int.zero)@Tint32|->Vint32 c ** (V293_owned_task_records tasks **
 (V293_storage rest ** (Amapsto(bn,0%Z)Tint8 true(V293_byteval 0) **
 (Amapsto(bl,0%Z)Tint8 true(V293_byteval 0) ** A_dom_lenv nil))))))))))))).
 { unfold ext,V293_same_exact_exit_external,V293_same_exact_exit_memory,V293_same_irq_reserve,
 V293_same_irq_read_half,V293_shared_fields,V293_exit_cells,V293_interrupt_cells in *;
 cbn[V293_rdy_raw_cells]in *;rewrite V293_read_pointers_array in H;sep auto. }
 eapply astar_mono in P;[ |apply V293_same_irq_read_reunite|apply astar_mono;
 [apply V293_same_irq_bindings_target|intros s K;exact K]].
 assert(Target:V293_prefix_output tp bo(Vptr selected) ** Agvarenv target(Tptr tp)(bo,0%Z) ==>
 GV target@(Tptr tp)|->Vptr selected).
 { intros s K;unfold Agvarmapsto;exists bo;unfold V293_prefix_output in K;unfold Agvarenv',Aptrmapsto;cbn[addrval_to_addr];sep auto. }
 assert(T:st |= (V293_prefix_output tp bo(Vptr selected) ** Agvarenv target(Tptr tp)(bo,0%Z)) **
 (V293_same_irq_read_full ** (<||aop||> ** OS[(fun _:hid=>false),false,i::si,nil] **
 (p_local V293_shared_li t nil ** (CurTid t ** (V293_shared_fields t tasks events now **
 (PV(bh,Int.zero)@Tint8|->V293_byteval nc ** (PV(bk,Int.zero)@Tint32|->Vint32 c **
 (V293_owned_task_records tasks ** (V293_storage rest **
 (Amapsto(bn,0%Z)Tint8 true(V293_byteval 0) **
 (Amapsto(bl,0%Z)Tint8 true(V293_byteval 0) ** A_dom_lenv nil))))))))))))by(clear H;sep auto).
 eapply astar_mono in T;[ |exact Target|intros s K;exact K].
 assert(Storage:Amapsto(brun,0%Z)Tint8 true(V293_byteval 1) **
 (Amapsto(bn,0%Z)Tint8 true(V293_byteval 0) **
 (Amapsto(bl,0%Z)Tint8 true(V293_byteval 0) ** V293_storage rest)) ==>
 V293_storage([((brun,0%Z),Tint8);((bn,0%Z),Tint8);((bl,0%Z),Tint8)]++rest)).
 { intros s K;cbn[V293_storage app];unfold V293_storage_cell;sep auto;apply V293_byte_type;lia. }
 assert(S:st |=
 (Amapsto(brun,0%Z)Tint8 true(V293_byteval 1) **
 (Amapsto(bn,0%Z)Tint8 true(V293_byteval 0) **
 (Amapsto(bl,0%Z)Tint8 true(V293_byteval 0) ** V293_storage rest))) **
 ((V293_inputs_full bt bg br lo hi ** (V293_array true bp 0 4(Tptr tp)entries ** V293_owned_task_records tasks)) **
 (<||aop||> ** OS[(fun _:hid=>false),false,i::si,nil] **
 (p_local V293_shared_li t nil ** (CurTid t ** (V293_shared_fields t tasks events now **
 (GV target@(Tptr tp)|->Vptr selected ** (PV(bh,Int.zero)@Tint8|->V293_byteval nc **
 (Amapsto(bc,0%Z)Tint8 true(V293_byteval nc) **
 (PV(bk,Int.zero)@Tint32|->Vint32 c ** A_dom_lenv nil)))))))))).
 { unfold V293_same_irq_read_full in T;clear H P;sep auto. }
 eapply astar_mono in S;[ |exact Storage|intros s K;exact K].
 assert(A:st |=
 (V293_inputs_full bt bg br lo hi ** (V293_array true bp 0 4(Tptr tp)entries **
 (V293_owned_task_records tasks ** V293_storage([((brun,0%Z),Tint8);((bn,0%Z),Tint8);((bl,0%Z),Tint8)]++rest)))) **
 (<||aop||> ** OS[(fun _:hid=>false),false,i::si,nil] **
 (p_local V293_shared_li t nil ** (CurTid t ** (V293_shared_fields t tasks events now **
 (GV target@(Tptr tp)|->Vptr selected ** (PV(bh,Int.zero)@Tint8|->V293_byteval nc **
 (Amapsto(bc,0%Z)Tint8 true(V293_byteval nc) **
 (PV(bk,Int.zero)@Tint32|->Vint32 c ** A_dom_lenv nil)))))))))by(clear H P T;sep auto).
 eapply astar_mono in A;[ |apply V293_retained_arrays_ready;assumption|intros s K;exact K].
 assert(Core:st |=
 V293_ready_storage_core br bg bp target tp cells **
 (<||aop||> ** OS[(fun _:hid=>false),false,i::si,nil] **
 (A_dom_lenv nil ** p_local V293_shared_li t nil))).
 { unfold V293_ready_storage_core,V293ReadyTaskInvariant.V293_ready_core,V293_shared_ready_records,
 V293_ready_storage_extra,V293_dispatch_cell,cells,V293_ready_irq_prefix;
 cbn[V293_storage app];unfold V293_storage_cell;clear H P T S;sep auto;
 try(apply V293_byte_type;exact Cur);reflexivity. }
 apply V293_irq_ready_open_close.
 unfold V293_irq_ready_open,V293_irq_ready_frame;clear H P T S A;sep auto.
Qed.
Lemma V293_same_irq_post : forall aop i si t,
 V293_same_exit_valid(i::si)(V293_same_irq_index aop) ->
 Forall(fun v=>rule_type_val_match(Tptr tp)v=true)entries ->
 (EX result:option val,
 getasrt(xfq nil result(logic_ie false::logic_ie false::
 V293_same_exit_args false(fun _:hid=>false)(i::si)nil(V293_same_irq_index aop))t) ** V293_same_irq_reserve t) ==>
 V293_irq_ready_closed br bg bp target tp cells i si aop t nil.
Proof.
 intros aop i si t Valid Types st[result H];pose proof Valid as V.
 destruct Valid as[Stack[Bound[Nest[Lock[Ready[Bitmap[Table Same]]]]]]].
 unfold xfq,V293_all_exact_dynamic_fpost,V293_exit_path,V293_same_exact_exit_fpost,V293_same_exact_exit_post in H.
 rewrite V293_same_exit_index_roundtrip in H by exact Bound;cbn[getasrt]in H.
 sep normal in H;destruct H as[selected H].
 assert(P:st |= ext 0(V293_byteval nc)(Vptr selected)aop(i::si)t ** V293_same_irq_reserve t).
 { unfold ext,V293_same_irq_index in *;
 cbn[V293_xlo V293_xhi V293_xcurrent V293_xnest V293_xold V293_xcounter V293_xentries V293_xtasks V293_xaop]in *.
 rewrite Same in H;sep auto. }
 eapply V293_same_irq_resources_close;[ | |exact Types|exact P].
 - unfold V293_ready_rel;unfold V293_same_irq_index,V293_exit_snapshot_bounded in *;
   cbn[V293_xlo V293_xhi V293_xcurrent V293_xnest V293_xlocked V293_xentries V293_xtasks]in *;tauto.
 - unfold V293_same_irq_index,V293_exit_snapshot_bounded in Bound;
   cbn[V293_xlo V293_xhi V293_xcurrent V293_xnest V293_xlocked]in Bound;tauto.
Qed.
Theorem V293_interrupt_same_exit_after_enter : forall Spec sd RI r ri exit aop i si t,
 V293_same_exit_valid(i::si)(V293_same_irq_index aop) ->
 Forall(fun v=>rule_type_val_match(Tptr tp)v=true)entries ->
 Spec exit=Some(xfp,xfq,(Tvoid,nil)) ->
 InfRules Spec sd V293_shared_li RI r ri
 (V293_same_irq_snapshot 1 aop(fun _:hid=>false)(i::si)t)(scall exit nil)
 (V293_irq_ready_closed br bg bp target tp cells i si aop t nil)t.
Proof.
 intros Spec sd RI r ri exit aop i si t Valid Types Lookup.
 eapply conseq_rule;[apply V293_same_irq_pre;exact Valid|apply V293_same_irq_post;assumption| ].
 apply(V293_OSIntExit_all_exact_dynamic_same_call
 unmap group rows high table target current counter running nesting lock bt bg br bh bp bo bc bk brun bn bl rest Aemp Logic.I);
 [exact(proj1(proj2 Valid))|apply V293_same_irq_reserve_good|exact Lookup].
Qed.
Theorem V293_interrupt_same_pair : forall Spec sd RI r ri enter exit aop i si t,
 V293_same_exit_valid(i::si)(V293_same_irq_index aop) ->
 Forall(fun v=>rule_type_val_match(Tptr tp)v=true)entries ->
 Spec enter=Some(efp,efq,(Tvoid,nil)) ->Spec exit=Some(xfp,xfq,(Tvoid,nil)) ->
 InfRules Spec sd V293_shared_li RI r ri
 (V293_same_irq_snapshot 0 aop(fun _:hid=>false)(i::si)t)
 (sseq(scall enter nil)(scall exit nil))
 (V293_irq_ready_closed br bg bp target tp cells i si aop t nil)t.
Proof.
 intros;eapply seq_rule;[apply V293_interrupt_same_enter_call;exact H1| ].
 apply V293_interrupt_same_exit_after_enter;assumption.
Qed.
Theorem V293_interrupt_same_continuous : forall Spec enter exit intspec i ir si t ret id,
 V293_same_exit_valid(i::si)(V293_same_irq_index(spec_done None)) ->
 Forall(fun v=>rule_type_val_match(Tptr tp)v=true)entries ->
 Spec enter=Some(efp,efq,(Tvoid,nil)) ->Spec exit=Some(xfp,xfq,(Tvoid,nil)) ->
 Some ret=BuildintRet i intspec ir si Inv0 V293_shared_li t nil ->
 (forall j,ir j=false) ->(0<=Int.unsigned id<Z.of_nat INUM)%Z ->i=Z.to_nat(Int.unsigned id) ->
 InfRules Spec V293_scheduler V293_shared_li Inv0 arfalse ret
 (V293_same_irq_snapshot 0(spec_done None)(isrupd ir i true)(i::si)t)
 (V293_irq_source_wrapper enter exit id)Afalse t.
Proof.
 intros Spec enter exit intspec i ir si t ret id Valid Types Enter Exit Ret Clear Bound Index.
 unfold V293_irq_source_wrapper;eapply seq_rule with
 (p':=V293_same_irq_snapshot 0(spec_done None)(fun _:hid=>false)(i::si)t).
 - eapply conseq_rule with
   (p:=<||spec_done None||> ** OS[isrupd ir i true,false,i::si,nil] ** V293_same_irq_physical 0 t)
   (q:=<||spec_done None||> ** OS[isrupd(isrupd ir i true)i false,false,i::si,nil] ** V293_same_irq_physical 0 t).
   + unfold V293_same_irq_snapshot;intros s H;exact H.
   + rewrite V293_irq_clear_update by assumption;unfold V293_same_irq_snapshot;intros s H;exact H.
   + apply eoi_ieoff_rule;[exact Bound|exact Index|apply V293_same_irq_physical_good].
 - eapply seq_rule;[apply V293_interrupt_same_enter_call;exact Enter| ].
   eapply seq_rule;[apply V293_interrupt_same_exit_after_enter;assumption| ].
   apply V293_irq_ready_exint with(intspec:=intspec)(ir:=ir);assumption.
Qed.
End SameContinuous.
