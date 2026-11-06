Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitChangedInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitBuilders.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyTaskInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntEnterInternal.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptReadyEnvironment.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptSourceRoundtrip.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedStoragePrefix.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitDynamic.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyStorageInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitAllExactDynamic.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitLocalDispatch.
(* Conditional changed/same wrappers under one bound LocalInv. *)
Require Import CertiOS.certiucos.v293.proofs.V293InterruptChangedContinuous.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptSameContinuous.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptBindings.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitBoundDynamic.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitBoundInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntEnterOpenExact.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitSameExactInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitSameInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitUnifiedInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitResourceCodec.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptReadyBoundary.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitReadyDynamic.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedSwitch.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Section BoundResources.
Variables running nesting lock:var.
Variables brun bn bl:block.
Let li:=V293_irq_bound_li running nesting lock brun bn bl.
Let globals:=V293_quiet_globals running nesting lock brun bn bl.
Lemma V293_enter_open_to_bound : forall run nest locked aop enabled ir si ci t,
 V293_enter_open_external running nesting lock brun bn bl Aemp run nest locked aop enabled ir si ci t ==>
 V293_enter_bound_external running nesting lock brun bn bl Aemp run nest locked aop enabled ir si ci t.
Proof.
 intros run nest locked aop enabled ir si ci t st H.
 assert(P:st |=(p_local V293_shared_li t nil ** globals) **
 (<||aop||> ** OS[ir,enabled,si,ci] **
 (Amapsto(brun,0%Z)Tint8 true(V293_byteval run) **
 (Amapsto(bn,0%Z)Tint8 true(V293_byteval nest) **
 (Amapsto(bl,0%Z)Tint8 true(V293_byteval locked) ** Aemp)))))
 by(unfold V293_enter_open_external in H;sep auto).
 eapply astar_mono in P;[ |apply V293_irq_bound_local_close|intros s K;exact K].
 unfold V293_enter_bound_external;clear H;sep auto.
Qed.
Lemma V293_enter_bound_to_open : forall run nest locked aop enabled ir si ci t,
 V293_enter_bound_external running nesting lock brun bn bl Aemp run nest locked aop enabled ir si ci t ==>
 V293_enter_open_external running nesting lock brun bn bl Aemp run nest locked aop enabled ir si ci t.
Proof.
 intros run nest locked aop enabled ir si ci t st H.
 assert(P:st |=p_local li t nil **
 (<||aop||> ** OS[ir,enabled,si,ci] **
 (Amapsto(brun,0%Z)Tint8 true(V293_byteval run) **
 (Amapsto(bn,0%Z)Tint8 true(V293_byteval nest) **
 (Amapsto(bl,0%Z)Tint8 true(V293_byteval locked) ** Aemp)))))
 by(unfold V293_enter_bound_external in H;sep auto).
 eapply astar_mono in P;[ |apply V293_irq_bound_local_open|intros s K;exact K].
 unfold V293_enter_open_external;clear H;sep auto.
Qed.
Variables br bg bp:block.
Variable target:var.
Variable tp:type.
Variable cells:list(addr*type).
Let Inv0:=V293_ready_storage_inv br bg bp target tp cells.
Definition V293_bound_irq_closed i si aop t:=
 <||aop||> ** SWINV Inv0 ** Ais(i::si) ** Acs nil **
 (A_dom_lenv nil ** p_local li t nil).
Lemma V293_bound_irq_closed_pack : forall i si aop t,
 V293_irq_ready_closed br bg bp target tp cells i si aop t nil ** globals ==>
 V293_bound_irq_closed i si aop t.
Proof.
 intros i si aop t st H;unfold V293_irq_ready_closed in H.
 assert(P:st |=(p_local V293_shared_li t nil ** globals) **
 (<||aop||> ** SWINV Inv0 ** Ais(i::si) ** Acs nil ** A_dom_lenv nil))by(sep auto).
 eapply astar_mono in P;[ |apply V293_irq_bound_local_close|intros s K;exact K].
 unfold V293_bound_irq_closed;clear H;sep auto.
Qed.
Lemma V293_bound_irq_return_resources : forall i ir si t,
 (forall j,ir j=false) ->
 V293_bound_irq_closed i si(spec_done None)t ==>
 iretasrt' i ir si Inv0 ** p_local li t nil.
Proof.
 intros i ir si t Clear st H;unfold V293_bound_irq_closed in H.
 assert(P:st |=p_local li t nil **
 (<||spec_done None||> ** SWINV Inv0 ** Ais(i::si) ** Acs nil ** A_dom_lenv nil))by(sep auto).
 eapply astar_mono in P;[ |apply V293_irq_bound_local_open|intros s K;exact K].
 assert(S:st |=V293_irq_ready_closed br bg bp target tp cells i si(spec_done None)t nil ** globals)
 by(unfold V293_irq_ready_closed;clear H;sep auto).
 eapply astar_mono in S;[ |apply V293_irq_ready_return_resources;exact Clear|intros s K;exact K].
 assert(C:st |=iretasrt' i ir si Inv0 ** (p_local V293_shared_li t nil ** globals))by(clear H P;sep auto).
 eapply astar_mono in C;[ |intros s K;exact K|apply V293_irq_bound_local_close];exact C.
Qed.
End BoundResources.

Section BoundDispatchContinuous.
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
Let cells:=V293_ready_irq_prefix bt bh bc bk++
 [((brun,0%Z),Tint8);((bn,0%Z),Tint8);((bl,0%Z),Tint8)]++rest.
Let efp:=V293_enter_bound_fpre running nesting lock brun bn bl Aemp Logic.I.
Let efq:=V293_enter_bound_fpost running nesting lock brun bn bl Aemp Logic.I.
Let xfp:=V293_bound_dynamic_fpre unmap group rows high table target current counter running nesting lock
 bt bg br bh bp bo bc bk brun bn bl rest Aemp Logic.I.
Let xfq:=V293_bound_dynamic_fpost unmap group rows high table target current counter running nesting lock
 bt bg br bh bp bo bc bk brun bn bl rest Aemp Logic.I.
Let changed:=V293_changed_irq_snapshot unmap group rows high table target current counter running nesting lock
 bt bg br bh bp bo bc bk brun bn bl rest lo hi nc entries tasks events now hv out c.
Let cframe:=V293_changed_enter_frame unmap group rows high table target current counter running nesting lock
 bt bg br bh bp bo bc bk brun bn bl rest lo hi nc entries tasks events now hv out c.
Let same:=V293_same_irq_snapshot unmap group rows high table target current counter running nesting lock
 bt bg br bh bp bo bc bk brun bn bl rest lo hi nc entries tasks events now hv out c.
Let closed:=V293_bound_irq_closed running nesting lock brun bn bl br bg bp target tp cells.

Theorem V293_interrupt_bound_changed_enter : forall Spec sd RI r ri enter aop ir si t,
 Spec enter=Some(efp,efq,(Tvoid,nil)) ->
 InfRules Spec sd li RI r ri(changed 0 aop ir si t)(scall enter nil)(changed 1 aop ir si t)t.
Proof.
 intros Spec sd RI r ri enter aop ir si t Enter.
 eapply conseq_rule with
 (p:=V293_enter_bound_external running nesting lock brun bn bl Aemp 1 0 0(sched;;aop)false ir si nil t ** cframe t)
 (q:=V293_enter_bound_external running nesting lock brun bn bl Aemp 1 1 0(sched;;aop)false ir si nil t ** cframe t).
 - intros s H;apply V293_changed_enter_split in H.
   eapply astar_mono;[apply V293_enter_open_to_bound|intros st K;exact K|exact H].
 - intros s H;eapply astar_mono in H;[ |apply V293_enter_bound_to_open|intros st K;exact K].
   apply V293_changed_enter_combine;exact H.
 - change(InfRules Spec sd li RI r ri
   (V293_enter_bound_external running nesting lock brun bn bl Aemp 1 0 0(sched;;aop)false ir si nil t ** cframe t)
   (scall enter nil)
   (V293_enter_bound_external running nesting lock brun bn bl Aemp 1(V293_interrupt_nest_after 1 0)0(sched;;aop)false ir si nil t ** cframe t)t).
   apply(V293_OSIntEnter_bound_call running nesting lock brun bn bl Aemp Logic.I);try lia;try exact Enter.
   apply V293_changed_enter_frame_good.
Qed.
Lemma V293_bound_changed_pre : forall aop si t,
 V293_changed_builder_valid tp lo hi nc 1 entries tasks t ->
 changed 1 aop(fun _:hid=>false)si t ==>
 getasrt(xfp nil(logic_ie true::V293_changed_encode(V293_changed_irq_index lo hi nc entries tasks events now hv out c aop si))t) ** A_dom_lenv nil.
Proof.
 intros aop si t Valid;unfold xfp,V293_bound_dynamic_fpre,V293_exit_path.
 change(changed 1 aop(fun _:hid=>false)si t ==>
 getasrt(V293_all_exact_dynamic_fpre unmap group rows high table target current counter running nesting lock
 bt bg br bh bp bo bc bk brun bn bl rest Aemp Logic.I nil
 (logic_ie true::V293_changed_encode(V293_changed_irq_index lo hi nc entries tasks events now hv out c aop si))t) ** A_dom_lenv nil).
 apply V293_changed_irq_pre;exact Valid.
Qed.
Lemma V293_bound_changed_post : forall aop i si t,
 (EX result:option val,
 getasrt(xfq nil result(logic_ie true::V293_changed_encode(V293_changed_irq_index lo hi nc entries tasks events now hv out c aop(i::si)))t) ** A_dom_lenv nil) ==>
 closed i si aop t.
Proof.
 intros aop i si t st[result H].
 unfold xfq,V293_bound_dynamic_fpost,V293_exit_path,V293_bound_dynamic_changed_fpost in H.
 rewrite V293_changed_codec_roundtrip in H.
 unfold V293_changed_irq_index in H;cbn[V293_caop V293_cstack V293_ccritical]in H.
 change(st |=V293_bound_builder_post unmap group rows high table target current counter running nesting lock
 bt bg br bh bp bo bc bk brun bn bl rest aop(i::si)nil Aemp t result ** A_dom_lenv nil)in H.
 assert(G:V293_exit_builder_globals table target current counter nesting lock running tp bp bo bc bk bn bl brun ==>Aemp).
 { intros s[B _];apply agvarenv_elim in B;exact(proj2 B). }
 assert(S:V293_sched_globals unmap group rows high bt bg br bh ==>Aemp).
 { intros s[B _];apply agvarenv_elim in B;exact(proj2 B). }
 unfold V293_bound_builder_post in H.
 assert(P:st |= (V293_sched_globals unmap group rows high bt bg br bh **
 V293_exit_builder_globals table target current counter nesting lock running tp bp bo bc bk bn bl brun) **
 (<||aop||> ** SWINV Inv0 ** Ais(i::si) ** Acs nil ** (A_dom_lenv nil ** p_local li t nil)))by(sep auto).
 eapply astar_mono in P;[ |apply astar_mono;[exact S|exact G]|intros s K;exact K].
 unfold closed,V293_bound_irq_closed;clear H;sep auto.
Qed.
Theorem V293_interrupt_bound_changed_exit : forall Spec sd RI r ri exit aop i si t,
 V293_changed_builder_valid tp lo hi nc 1 entries tasks t ->
 Spec exit=Some(xfp,xfq,(Tvoid,nil)) ->
 InfRules Spec sd li RI r ri(changed 1 aop(fun _:hid=>false)(i::si)t)
 (scall exit nil)(closed i si aop t)t.
Proof.
 intros;eapply conseq_rule;[apply V293_bound_changed_pre;exact H|apply V293_bound_changed_post| ].
 apply V293_OSIntExit_bound_dynamic_call;[exact Logic.I|exact H0].
Qed.
Theorem V293_interrupt_bound_changed_continuous : forall Spec enter exit intspec i ir si t ret id,
 V293_changed_builder_valid tp lo hi nc 1 entries tasks t ->
 Spec enter=Some(efp,efq,(Tvoid,nil)) ->Spec exit=Some(xfp,xfq,(Tvoid,nil)) ->
 Some ret=BuildintRet i intspec ir si Inv0 li t nil ->
 (forall j,ir j=false) ->(0<=Int.unsigned id<Z.of_nat INUM)%Z ->i=Z.to_nat(Int.unsigned id) ->
 InfRules Spec V293_scheduler li Inv0 arfalse ret
 (changed 0(spec_done None)(isrupd ir i true)(i::si)t)
 (V293_irq_source_wrapper enter exit id)Afalse t.
Proof.
 intros Spec enter exit intspec i ir si t ret id Valid Enter Exit Ret Clear Bound Index.
 unfold V293_irq_source_wrapper;eapply seq_rule with
 (p':=changed 0(spec_done None)(fun _:hid=>false)(i::si)t).
 - eapply conseq_rule with
   (p:=<||sched;;spec_done None||> ** OS[isrupd ir i true,false,i::si,nil] **
   V293_changed_irq_physical unmap group rows high table target current counter running nesting lock
   bt bg br bh bp bo bc bk brun bn bl rest lo hi nc entries tasks events now hv out c 0 t)
   (q:=<||sched;;spec_done None||> ** OS[isrupd(isrupd ir i true)i false,false,i::si,nil] **
   V293_changed_irq_physical unmap group rows high table target current counter running nesting lock
   bt bg br bh bp bo bc bk brun bn bl rest lo hi nc entries tasks events now hv out c 0 t).
   + unfold changed,V293_changed_irq_snapshot;intros s H;exact H.
   + rewrite V293_irq_clear_update by assumption;unfold changed,V293_changed_irq_snapshot;intros s H;exact H.
   + apply eoi_ieoff_rule;[exact Bound|exact Index|apply V293_changed_irq_physical_good].
 - eapply seq_rule;[apply V293_interrupt_bound_changed_enter;exact Enter| ].
   eapply seq_rule;[apply V293_interrupt_bound_changed_exit;assumption| ].
   unfold BuildintRet in Ret;destruct(intspec i);[ |discriminate].
   inversion Ret;subst ret;apply iret_rule;apply V293_bound_irq_return_resources;exact Clear.
Qed.

Let sframe t:=V293_same_irq_payload unmap group rows high table target current counter running nesting lock
 bt bg br bh bp bo bc bk brun bn bl rest tasks events now hv out c t **
 (V293_inputs_full bt bg br lo hi ** (V293_array true bp 0 4(Tptr tp)entries **
 Amapsto(bc,0%Z)Tint8 true(V293_byteval nc))).
Let reserve:=V293_same_irq_reserve bt bg br bp bc brun rest lo hi nc entries tasks events now.
Let oldext nest highval output aop si t:=V293_same_exact_exit_external
 unmap group rows high table target current counter nesting lock running
 bt bg br bh bp bo bc bk bn bl brun tp V293_shared_li Aemp
 false(fun _:hid=>false)si nil lo hi entries tasks nc nest highval output c aop t.
Let newext nest highval output aop si t:=V293_same_exact_exit_external
 unmap group rows high table target current counter nesting lock running
 bt bg br bh bp bo bc bk bn bl brun tp li Aemp
 false(fun _:hid=>false)si nil lo hi entries tasks nc nest highval output c aop t.
Lemma V293_same_external_bound_pack : forall nest highval output aop si t,
 oldext nest highval output aop si t ==>newext nest highval output aop si t.
Proof.
 intros nest highval output aop si t st H.
 assert(E:st |=V293_exit_builder_globals table target current counter nesting lock running tp bp bo bc bk bn bl brun ** Atrue)
 by(unfold oldext,V293_same_exact_exit_external in H;sep auto).
 eapply astar_mono in E;[ |apply V293_changed_globals_split|intros s K;exact K].
 assert(B:st |=V293_quiet_globals running nesting lock brun bn bl ** Atrue)by(sep auto).
 pose proof(V293_bound_dispatch_add_globals running nesting lock brun bn bl _ _ B H)as P.
 unfold newext,oldext,V293_same_exact_exit_external,V293_same_exact_exit_memory,
 li,p_local,LINV,V293_irq_bound_li,V293_shared_li in *;clear H E B;sep auto;apply V293_irq_bound_good.
Qed.
Lemma V293_same_external_bound_open : forall nest highval output aop si t,
 newext nest highval output aop si t ==>
 oldext nest highval output aop si t ** V293_quiet_globals running nesting lock brun bn bl.
Proof.
 intros nest highval output aop si t st H.
 unfold newext,oldext,V293_same_exact_exit_external,V293_same_exact_exit_memory,
 li,p_local,LINV,V293_irq_bound_li,V293_shared_li in *;sep auto;apply V293_switch_li_good.
Qed.
Theorem V293_interrupt_bound_same_enter : forall Spec sd RI r ri enter aop ir si t,
 Spec enter=Some(efp,efq,(Tvoid,nil)) ->
 InfRules Spec sd li RI r ri(same 0 aop ir si t)(scall enter nil)(same 1 aop ir si t)t.
Proof.
 intros Spec sd RI r ri enter aop ir si t Enter.
 eapply conseq_rule with
 (p:=V293_enter_bound_external running nesting lock brun bn bl Aemp 1 0 0 aop false ir si nil t ** sframe t)
 (q:=V293_enter_bound_external running nesting lock brun bn bl Aemp 1 1 0 aop false ir si nil t ** sframe t).
 - intros s H;apply V293_same_irq_enter_split in H.
   eapply astar_mono;[apply V293_enter_open_to_bound|intros st K;exact K|exact H].
 - intros s H;eapply astar_mono in H;[ |apply V293_enter_bound_to_open|intros st K;exact K].
   apply V293_same_irq_enter_combine;exact H.
 - change(InfRules Spec sd li RI r ri
   (V293_enter_bound_external running nesting lock brun bn bl Aemp 1 0 0 aop false ir si nil t ** sframe t)
   (scall enter nil)
   (V293_enter_bound_external running nesting lock brun bn bl Aemp 1(V293_interrupt_nest_after 1 0)0 aop false ir si nil t ** sframe t)t).
   apply(V293_OSIntEnter_bound_call running nesting lock brun bn bl Aemp Logic.I);try lia;try exact Enter.
   unfold sframe;split;[apply V293_same_irq_payload_good| ].
   unfold V293_inputs_full;cbn[GoodFrm];repeat split;try exact Logic.I;apply V293_array_good.
Qed.
Lemma V293_bound_same_pre : forall aop si t,
 V293_same_exit_valid si(V293_same_irq_index lo hi nc entries tasks out c aop) ->
 same 1 aop(fun _:hid=>false)si t ==>
 getasrt(xfp nil(logic_ie false::logic_ie false::
 V293_same_exit_args false(fun _:hid=>false)si nil(V293_same_irq_index lo hi nc entries tasks out c aop))t) ** reserve t.
Proof.
 intros aop si t Valid;pose proof(proj1(proj2 Valid))as Bound.
 unfold xfp,V293_bound_dynamic_fpre,V293_exit_path,V293_same_exact_exit_fpre,V293_same_exact_exit_pre.
 rewrite V293_same_exit_index_roundtrip by exact Bound;cbn[getasrt].
 intros st H;apply V293_same_irq_exit_borrow in H.
 change(st |=oldext 1 hv out aop si t ** reserve t)in H.
 eapply astar_mono in H;[ |apply V293_same_external_bound_pack|intros s K;exact K].
 unfold newext,V293_same_irq_index in *;
 cbn[V293_xlo V293_xhi V293_xcurrent V293_xnest V293_xold V293_xcounter V293_xentries V293_xtasks V293_xaop];sep auto.
Qed.
Lemma V293_bound_same_post : forall aop i si t,
 V293_same_exit_valid(i::si)(V293_same_irq_index lo hi nc entries tasks out c aop) ->
 Forall(fun v=>rule_type_val_match(Tptr tp)v=true)entries ->
 (EX result:option val,
 getasrt(xfq nil result(logic_ie false::logic_ie false::
 V293_same_exit_args false(fun _:hid=>false)(i::si)nil(V293_same_irq_index lo hi nc entries tasks out c aop))t) ** reserve t) ==>
 closed i si aop t.
Proof.
 intros aop i si t Valid Types st[result H];pose proof Valid as V.
 destruct Valid as[Stack[Bound[Nest[Lock[Ready[Bitmap[Table Same]]]]]]].
 unfold xfq,V293_bound_dynamic_fpost,V293_exit_path,V293_same_exact_exit_fpost,V293_same_exact_exit_post in H.
 rewrite V293_same_exit_index_roundtrip in H by exact Bound;cbn[getasrt]in H.
 sep normal in H;destruct H as[selected H].
 assert(P:st |=newext 0(V293_byteval nc)(Vptr selected)aop(i::si)t ** reserve t).
 { unfold newext,V293_same_irq_index in *;
 cbn[V293_xlo V293_xhi V293_xcurrent V293_xnest V293_xold V293_xcounter V293_xentries V293_xtasks V293_xaop]in *.
 rewrite Same in H;sep auto. }
 eapply astar_mono in P;[ |apply V293_same_external_bound_open|intros s K;exact K].
 assert(Q:st |=(oldext 0(V293_byteval nc)(Vptr selected)aop(i::si)t ** reserve t) **
 V293_quiet_globals running nesting lock brun bn bl)by(clear H;sep auto).
 eapply astar_mono in Q;[ |apply V293_same_irq_resources_close|intros s K;exact K].
 - unfold closed;apply V293_bound_irq_closed_pack;exact Q.
 - unfold V293_ready_rel;unfold V293_same_irq_index,V293_exit_snapshot_bounded in *;
   cbn[V293_xlo V293_xhi V293_xcurrent V293_xnest V293_xlocked V293_xentries V293_xtasks]in *;tauto.
 - unfold V293_same_irq_index,V293_exit_snapshot_bounded in Bound;
   cbn[V293_xlo V293_xhi V293_xcurrent V293_xnest V293_xlocked]in Bound;tauto.
 - exact Types.
Qed.
Theorem V293_interrupt_bound_same_exit : forall Spec sd RI r ri exit aop i si t,
 V293_same_exit_valid(i::si)(V293_same_irq_index lo hi nc entries tasks out c aop) ->
 Forall(fun v=>rule_type_val_match(Tptr tp)v=true)entries ->
 Spec exit=Some(xfp,xfq,(Tvoid,nil)) ->
 InfRules Spec sd li RI r ri(same 1 aop(fun _:hid=>false)(i::si)t)
 (scall exit nil)(closed i si aop t)t.
Proof.
 intros;eapply conseq_rule;[apply V293_bound_same_pre;exact H|apply V293_bound_same_post;assumption| ].
 apply V293_OSIntExit_bound_dynamic_call;[apply V293_same_irq_reserve_good|exact H1].
Qed.
Theorem V293_interrupt_bound_same_continuous : forall Spec enter exit intspec i ir si t ret id,
 V293_same_exit_valid(i::si)(V293_same_irq_index lo hi nc entries tasks out c(spec_done None)) ->
 Forall(fun v=>rule_type_val_match(Tptr tp)v=true)entries ->
 Spec enter=Some(efp,efq,(Tvoid,nil)) ->Spec exit=Some(xfp,xfq,(Tvoid,nil)) ->
 Some ret=BuildintRet i intspec ir si Inv0 li t nil ->
 (forall j,ir j=false) ->(0<=Int.unsigned id<Z.of_nat INUM)%Z ->i=Z.to_nat(Int.unsigned id) ->
 InfRules Spec V293_scheduler li Inv0 arfalse ret
 (same 0(spec_done None)(isrupd ir i true)(i::si)t)
 (V293_irq_source_wrapper enter exit id)Afalse t.
Proof.
 intros Spec enter exit intspec i ir si t ret id Valid Types Enter Exit Ret Clear Bound Index.
 unfold V293_irq_source_wrapper;eapply seq_rule with
 (p':=same 0(spec_done None)(fun _:hid=>false)(i::si)t).
 - eapply conseq_rule with
   (p:=<||spec_done None||> ** OS[isrupd ir i true,false,i::si,nil] **
   V293_same_irq_physical unmap group rows high table target current counter running nesting lock
   bt bg br bh bp bo bc bk brun bn bl rest lo hi nc entries tasks events now hv out c 0 t)
   (q:=<||spec_done None||> ** OS[isrupd(isrupd ir i true)i false,false,i::si,nil] **
   V293_same_irq_physical unmap group rows high table target current counter running nesting lock
   bt bg br bh bp bo bc bk brun bn bl rest lo hi nc entries tasks events now hv out c 0 t).
   + unfold same,V293_same_irq_snapshot;intros s H;exact H.
   + rewrite V293_irq_clear_update by assumption;unfold same,V293_same_irq_snapshot;intros s H;exact H.
   + apply eoi_ieoff_rule;[exact Bound|exact Index|apply V293_same_irq_physical_good].
 - eapply seq_rule;[apply V293_interrupt_bound_same_enter;exact Enter| ].
   eapply seq_rule;[apply V293_interrupt_bound_same_exit;assumption| ].
   unfold BuildintRet in Ret;destruct(intspec i);[ |discriminate].
   inversion Ret;subst ret;apply iret_rule;apply V293_bound_irq_return_resources;exact Clear.
Qed.
End BoundDispatchContinuous.
