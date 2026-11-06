(* Continuous source wrapper on an outermost changed-priority entry. *)
Require Import CertiOS.certiucos.v293.proofs.V293InterruptQuietContinuous.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntEnterOpenExact.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitAllExactDynamic.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitExactDynamic.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitExactInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitReadyInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitReadyDynamic.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitChangedInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitDynamic.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitUnifiedInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitResourceCodec.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitReadyDispatch.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitBuilders.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptReadyLocal.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptReadyBoundary.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptReadyEnvironment.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptSourceRoundtrip.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyStorageInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchStorage.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedShared.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedStoragePrefix.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedSwitchPre.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedSwitch.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedPrefix.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCall.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedExactLocal.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitExact.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntEnterInternal.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.sep_combine_lemmas.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Section ChangedCall.
Variables unmap group rows high table target current counter running nesting lock:var.
Variables bt bg br bh bp bo bc bk brun bn bl:block.
Variable rest:list(addr*type).
Let fp:=V293_all_exact_dynamic_fpre unmap group rows high table target current counter running nesting lock
 bt bg br bh bp bo bc bk brun bn bl rest Aemp Logic.I.
Let fq:=V293_all_exact_dynamic_fpost unmap group rows high table target current counter running nesting lock
 bt bg br bh bp bo bc bk brun bn bl rest Aemp Logic.I.
Theorem V293_OSIntExit_all_exact_changed_call : forall Spec sd RI r ri exit t x callerframe,
 GoodFrm callerframe ->Spec exit=Some(fp,fq,(Tvoid,nil)) ->
 let lg:=logic_ie true::V293_changed_encode x in
 InfRules Spec sd V293_shared_li RI r ri
 (getasrt(fp nil lg t) ** callerframe)(scall exit nil)
 (EX result:option val,getasrt(fq nil result lg t) ** callerframe)t.
Proof.
 intros Spec sd RI r ri exit t x callerframe GF Lookup lg.
 eapply call_rule with(pre:=fp)(post:=fq)(vl:=nil)(logicl:=lg)(tp:=Tvoid)(tl:=nil).
 - exact GF.
 - exact Lookup.
 - intros st H;exact H.
 - intros st H;reflexivity.
 - reflexivity.
 - unfold fp,lg,V293_all_exact_dynamic_fpre,V293_exit_path,V293_ready_dynamic_changed_fpre.
   rewrite V293_changed_codec_roundtrip.
   apply V293_exact_builder_pre_local.
 - intros st[result H];unfold fq,lg,V293_all_exact_dynamic_fpost,V293_exit_path,
   V293_exact_dynamic_changed_fpost in H;rewrite V293_changed_codec_roundtrip in H.
   eapply V293_exact_builder_post_local;exact H.
Qed.
End ChangedCall.

Lemma V293_changed_current_combine : forall t tp,
 CurTid t ** GV OSTCBCur@(Tptr tp)|-r->Vptr t ==>
 GV OSTCBCur@(Tptr tp)|->Vptr t.
Proof.
 intros t tp st H;unfold CurTid in H.
 apply astar_l_aexists_elim in H;destruct H as[tq H].
 assert(G1:exists b,get(getgenv st)OSTCBCur=Some(b,Tptr tq)).
 { eapply V293_star_env_l with(E:=fun ge _=>exists b,get ge OSTCBCur=Some(b,Tptr tq));[ |exact H].
   intros s K;eapply V293_global_cell_type;exact K. }
 assert(G2:exists b,get(getgenv st)OSTCBCur=Some(b,Tptr tp)).
 { eapply V293_star_env_r with(E:=fun ge _=>exists b,get ge OSTCBCur=Some(b,Tptr tp));[ |exact H].
   intros s K;eapply V293_global_cell_type;exact K. }
 destruct G1 as[b1 G1];destruct G2 as[b2 G2];assert(tq=tp)by congruence;subst tq.
 eapply GV_combine_ro_p1;exact H.
Qed.
Section ChangedContinuous.
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
Let Inv0:=V293_ready_dynamic_exit_inv target bt bg br bh bp bc bk brun bn bl rest.
Let globals:=V293_exit_builder_globals table target current counter nesting lock running tp bp bo bc bk bn bl brun.
Let efp:=V293_enter_open_fpre running nesting lock brun bn bl Aemp Logic.I.
Let efq:=V293_enter_open_fpost running nesting lock brun bn bl Aemp Logic.I.
Let xfp:=V293_all_exact_dynamic_fpre unmap group rows high table target current counter running nesting lock
 bt bg br bh bp bo bc bk brun bn bl rest Aemp Logic.I.
Let xfq:=V293_all_exact_dynamic_fpost unmap group rows high table target current counter running nesting lock
 bt bg br bh bp bo bc bk brun bn bl rest Aemp Logic.I.
Let memory t:=V293_ready_builder_memory unmap group rows high target bt bg br bh bp bc bk
 lo hi nc entries rest tasks events now hv out c Aemp t.
(* This is exactly the existing memory tail after its full current pointer. *)
Definition V293_changed_enter_payload t:=
 V293_shared_fields t tasks events now ** (GV target@(Tptr tp)|->out **
 (V293_inputs_full bt bg br lo hi ** (PV(bh,Int.zero)@Tint8|->hv **
 (V293_array true bp 0 4(Tptr tp)entries **
 (Amapsto(bc,0%Z)Tint8 true(V293_byteval nc) ** (PV(bk,Int.zero)@Tint32|->Vint32 c **
 (V293_storage rest ** (V293_sched_globals unmap group rows high bt bg br bh **
 (Aemp ** V293_owned_task_records tasks))))))))).
Lemma V293_changed_enter_payload_frame : forall t,GoodFrm(V293_changed_enter_payload t).
Proof.
 intros;assert(A:GoodFrm(V293_array true bp 0 4(Tptr tp)entries)).
 { generalize 0%Z;induction entries;intros;cbn[V293_array GoodFrm];auto. }
 assert(Owned:GoodFrm(V293_owned_task_records tasks)).
 { apply V293_owned_tasks_frame. }
 unfold V293_changed_enter_payload,V293_shared_fields,V293_inputs_full,
 Agvarmapsto,Agvarenv',Aptrmapsto,V293_sched_globals.
 cbn[GoodFrm];repeat split;try exact Logic.I;try exact A;try exact Owned;apply V293_storage_frame_good.
Qed.
Definition V293_changed_enter_frame t:=
 GV OSTCBCur@(Tptr tp)|-r->Vptr t ** (V293_changed_enter_payload t ** (globals ** A_dom_lenv nil)).
Lemma V293_changed_enter_frame_good : forall t,GoodFrm(V293_changed_enter_frame t).
Proof.
 intros;unfold V293_changed_enter_frame;split.
 - unfold Agvarmapsto,Agvarenv',Aptrmapsto;cbn[GoodFrm];auto.
 - split;[apply V293_changed_enter_payload_frame| ].
   unfold globals,V293_exit_builder_globals;cbn[GoodFrm];tauto.
Qed.
Definition V293_changed_irq_physical nest t:=
 memory t ** (globals ** (Amapsto(brun,0%Z)Tint8 true(V293_byteval 1) **
 (Amapsto(bn,0%Z)Tint8 true(V293_byteval nest) **
 (Amapsto(bl,0%Z)Tint8 true(V293_byteval 0) ** A_dom_lenv nil)))).
Definition V293_changed_irq_snapshot nest aop ir si t:=
 <||sched;;aop||> ** OS[ir,false,si,nil] ** V293_changed_irq_physical nest t.
Lemma V293_changed_irq_physical_good : forall nest t,GoodFrm(V293_changed_irq_physical nest t).
Proof.
 intros;unfold V293_changed_irq_physical,memory,V293_ready_builder_memory.
 change(GoodFrm((GV OSTCBCur@(Tptr tp)|->Vptr t ** V293_changed_enter_payload t) **
 (globals ** (Amapsto(brun,0%Z)Tint8 true(V293_byteval 1) **
 (Amapsto(bn,0%Z)Tint8 true(V293_byteval nest) **
 (Amapsto(bl,0%Z)Tint8 true(V293_byteval 0) ** A_dom_lenv nil)))))).
 split;[split;[unfold Agvarmapsto,Agvarenv',Aptrmapsto;cbn[GoodFrm];auto|apply V293_changed_enter_payload_frame]| ].
 unfold globals,V293_exit_builder_globals;cbn[GoodFrm];tauto.
Qed.
Lemma V293_changed_globals_split : globals ==>
 V293_quiet_globals running nesting lock brun bn bl ** globals.
Proof.
 intros st G;pose proof G as E;unfold globals,V293_exit_builder_globals in E.
 destruct E as[T[G0[C[K[N[L R]]]]]].
 apply agvarenv_elim in T;destruct T as[_ Empty].
 apply V293_exit_empty_star;[exact Empty| |exact G].
 unfold V293_quiet_globals;repeat split;assumption.
Qed.
Lemma V293_changed_enter_split : forall nest aop ir si t,
 V293_changed_irq_snapshot nest aop ir si t ==>
 V293_enter_open_external running nesting lock brun bn bl Aemp
 1 nest 0(sched;;aop)false ir si nil t ** V293_changed_enter_frame t.
Proof.
 intros nest aop ir si t st H.
 unfold V293_changed_irq_snapshot,V293_changed_irq_physical,memory,V293_ready_builder_memory in H.
 assert(P:st |= GV OSTCBCur@(Tptr tp)|->Vptr t **
 (<||sched;;aop||> ** OS[ir,false,si,nil] **
 (V293_changed_enter_payload t ** (globals ** (Amapsto(brun,0%Z)Tint8 true(V293_byteval 1) **
 (Amapsto(bn,0%Z)Tint8 true(V293_byteval nest) **
 (Amapsto(bl,0%Z)Tint8 true(V293_byteval 0) ** A_dom_lenv nil)))))))
 by(unfold V293_changed_enter_payload;sep auto).
 eapply astar_mono in P;[ |apply GV_separate_rw|intros s K;exact K].
 unfold V293_enter_open_external,V293_changed_enter_frame,p_local,LINV,V293_shared_li.
 assert(P2:st |= globals ** ((GV OSTCBCur@(Tptr tp)|-r->Vptr t ** GV OSTCBCur@(Tptr tp)|-r->Vptr t) **
 (<||sched;;aop||> ** OS[ir,false,si,nil] ** (V293_changed_enter_payload t **
 (Amapsto(brun,0%Z)Tint8 true(V293_byteval 1) ** (Amapsto(bn,0%Z)Tint8 true(V293_byteval nest) **
 (Amapsto(bl,0%Z)Tint8 true(V293_byteval 0) ** A_dom_lenv nil)))))))by(sep auto).
 eapply astar_mono in P2;[ |apply V293_changed_globals_split|intros s K;exact K].
 unfold CurTid;clear H P;sep auto.
 all:exact V293_switch_li_good.
Qed.
Lemma V293_changed_enter_combine : forall nest aop ir si t,
 V293_enter_open_external running nesting lock brun bn bl Aemp
 1 nest 0(sched;;aop)false ir si nil t ** V293_changed_enter_frame t ==>
 V293_changed_irq_snapshot nest aop ir si t.
Proof.
 intros nest aop ir si t st H.
 assert(Q:V293_quiet_globals running nesting lock brun bn bl ==>Aemp).
 { intros s [Binding _];apply agvarenv_elim in Binding;exact(proj2 Binding). }
 unfold V293_enter_open_external in H.
 eapply astar_mono in H;[ |apply astar_mono;[intros s K;exact K|apply astar_mono;[intros s K;exact K|apply astar_mono;[exact Q|intros s K;exact K]]]|intros s K;exact K].
 unfold V293_changed_enter_frame,p_local,LINV,V293_shared_li in H.
 assert(P:st |= (CurTid t ** GV OSTCBCur@(Tptr tp)|-r->Vptr t) **
 (<||sched;;aop||> ** OS[ir,false,si,nil] **
 (V293_changed_enter_payload t ** (globals ** (Amapsto(brun,0%Z)Tint8 true(V293_byteval 1) **
 (Amapsto(bn,0%Z)Tint8 true(V293_byteval nest) **
 (Amapsto(bl,0%Z)Tint8 true(V293_byteval 0) ** A_dom_lenv nil)))))))by(sep auto;exact V293_switch_li_good).
 eapply astar_mono in P;[ |apply V293_changed_current_combine|intros s K;exact K].
 unfold V293_changed_irq_snapshot,V293_changed_irq_physical,memory,V293_ready_builder_memory,
 V293_changed_enter_payload in *;clear H;sep auto.
Qed.
Theorem V293_interrupt_changed_enter_call : forall Spec sd RI r ri enter aop ir si t,
 Spec enter=Some(efp,efq,(Tvoid,nil)) ->
 InfRules Spec sd V293_shared_li RI r ri
 (V293_changed_irq_snapshot 0 aop ir si t)(scall enter nil)
 (V293_changed_irq_snapshot 1 aop ir si t)t.
Proof.
 intros;eapply conseq_rule;[apply V293_changed_enter_split|apply V293_changed_enter_combine| ].
 change(InfRules Spec sd V293_shared_li RI r ri
 (V293_enter_open_external running nesting lock brun bn bl Aemp 1 0 0(sched;;aop)false ir si nil t ** V293_changed_enter_frame t)
 (scall enter nil)
 (V293_enter_open_external running nesting lock brun bn bl Aemp 1(V293_interrupt_nest_after 1 0)0(sched;;aop)false ir si nil t ** V293_changed_enter_frame t)t).
 apply(V293_OSIntEnter_open_call running nesting lock brun bn bl Aemp Logic.I);try lia;[apply V293_changed_enter_frame_good|exact H].
Qed.
Definition V293_changed_irq_index aop si:=V293_mk_changed_snapshot
 (Int.repr(Z.of_nat lo))(Int.repr(Z.of_nat hi))(Int.repr(Z.of_nat nc))Int.one
 entries tasks events now hv out c aop si nil.
Lemma V293_changed_irq_pre : forall aop si t,
 V293_changed_builder_valid tp lo hi nc 1 entries tasks t ->
 V293_changed_irq_snapshot 1 aop(fun _:hid=>false)si t ==>
 getasrt(xfp nil(logic_ie true::V293_changed_encode(V293_changed_irq_index aop si))t) ** A_dom_lenv nil.
Proof.
 intros aop si t Valid;pose proof Valid as V.
 destruct Valid as[L[H[R[N[D[Diff[B[T[Typed In]]]]]]]]].
 unfold xfp,V293_all_exact_dynamic_fpre,V293_exit_path,V293_ready_dynamic_changed_fpre.
 rewrite V293_changed_codec_roundtrip.
 unfold V293_changed_irq_index;cbn[V293_clo V293_chi V293_ccurrent V293_cnest V293_centries V293_ctasks
 V293_cevents V293_cnow V293_chigh V293_cout V293_ccounter V293_caop V293_cstack V293_ccritical].
 cbn[getasrt V293_ready_builder_fpre].
 repeat rewrite V293_sched_snapshot_roundtrip by lia.
 change(V293_changed_irq_snapshot 1 aop(fun _:hid=>false)si t ==>
 V293_ready_builder_pre unmap group rows high table target current counter running nesting lock
 bt bg br bh bp bo bc bk brun bn bl lo hi nc 1 entries rest tasks events now hv out c aop si nil Aemp t ** A_dom_lenv nil).
 intros st Held;unfold V293_changed_irq_snapshot,V293_changed_irq_physical,
 V293_ready_builder_pre,V293_ready_builder_external,V293OSIntExitHoare.V293_exit_cells,
 V293OSIntEnterInternal.V293_interrupt_cells,memory,globals in *;
 cbn[V293_rdy_raw_cells]in *.
 sep auto.
Qed.
Definition V293_changed_irq_return aop si t:=
 <||aop||> ** ((SWINV Inv0 ** p_local V293_shared_li t nil) **
 ((Ais si ** Acs nil) ** A_dom_lenv nil)).
Lemma V293_changed_irq_post : forall aop si t,
 (EX result:option val,
 getasrt(xfq nil result(logic_ie true::V293_changed_encode(V293_changed_irq_index aop si))t) ** A_dom_lenv nil) ==>
 V293_changed_irq_return aop si t.
Proof.
 intros aop si t st[result Held].
 unfold xfq,V293_all_exact_dynamic_fpost,V293_exit_path,V293_exact_dynamic_changed_fpost in Held.
 rewrite V293_changed_codec_roundtrip in Held.
 unfold V293_changed_irq_index in Held;cbn[V293_caop V293_cstack V293_ccritical]in Held.
 change(st |= V293_exact_builder_post unmap group rows high table target current counter running nesting lock
 bt bg br bh bp bo bc bk brun bn bl rest aop si nil Aemp t result ** A_dom_lenv nil)in Held.
 assert(G:globals ==>Aemp).
 { intros s [Binding _];apply agvarenv_elim in Binding;exact(proj2 Binding). }
 assert(S:V293_sched_globals unmap group rows high bt bg br bh ==>Aemp).
 { intros s [Binding _];apply agvarenv_elim in Binding;exact(proj2 Binding). }
 unfold V293_exact_builder_post in Held.
 assert(P:st |= (V293_sched_globals unmap group rows high bt bg br bh ** globals) **
 (<||aop||> ** ((SWINV Inv0 ** p_local V293_shared_li t nil) **
 ((Ais si ** Acs nil) ** A_dom_lenv nil))))by(sep auto).
 eapply astar_mono in P;[ |apply astar_mono;[exact S|exact G]|intros s K;exact K].
 unfold V293_changed_irq_return;clear Held;sep auto.
Qed.
Theorem V293_interrupt_changed_exit_after_enter : forall Spec sd RI r ri exit aop si t,
 V293_changed_builder_valid tp lo hi nc 1 entries tasks t ->
 Spec exit=Some(xfp,xfq,(Tvoid,nil)) ->
 InfRules Spec sd V293_shared_li RI r ri
 (V293_changed_irq_snapshot 1 aop(fun _:hid=>false)si t)(scall exit nil)
 (V293_changed_irq_return aop si t)t.
Proof.
 intros Spec sd RI r ri exit aop si t Valid Lookup.
 eapply conseq_rule;[apply V293_changed_irq_pre;exact Valid|apply V293_changed_irq_post| ].
 apply V293_OSIntExit_all_exact_changed_call;[exact Logic.I|exact Lookup].
Qed.
Theorem V293_interrupt_changed_pair : forall Spec sd RI r ri enter exit aop si t,
 V293_changed_builder_valid tp lo hi nc 1 entries tasks t ->
 Spec enter=Some(efp,efq,(Tvoid,nil)) ->Spec exit=Some(xfp,xfq,(Tvoid,nil)) ->
 InfRules Spec sd V293_shared_li RI r ri
 (V293_changed_irq_snapshot 0 aop(fun _:hid=>false)si t)
 (sseq(scall enter nil)(scall exit nil))(V293_changed_irq_return aop si t)t.
Proof.
 intros;eapply seq_rule;[apply V293_interrupt_changed_enter_call;exact H0| ].
 apply V293_interrupt_changed_exit_after_enter;assumption.
Qed.
Theorem V293_interrupt_changed_continuous : forall Spec enter exit intspec i ir si t ret id,
 V293_changed_builder_valid tp lo hi nc 1 entries tasks t ->
 Spec enter=Some(efp,efq,(Tvoid,nil)) ->Spec exit=Some(xfp,xfq,(Tvoid,nil)) ->
 Some ret=BuildintRet i intspec ir si Inv0 V293_shared_li t nil ->
 (forall j,ir j=false) ->(0<=Int.unsigned id<Z.of_nat INUM)%Z ->i=Z.to_nat(Int.unsigned id) ->
 InfRules Spec V293_scheduler V293_shared_li Inv0 arfalse ret
 (V293_changed_irq_snapshot 0(spec_done None)(isrupd ir i true)(i::si)t)
 (V293_irq_source_wrapper enter exit id)Afalse t.
Proof.
 intros Spec enter exit intspec i ir si t ret id Valid Enter Exit Ret Clear Bound Index.
 unfold V293_irq_source_wrapper;eapply seq_rule with
 (p':=V293_changed_irq_snapshot 0(spec_done None)(fun _:hid=>false)(i::si)t).
 - eapply conseq_rule with
   (p:=<||sched;;spec_done None||> ** OS[isrupd ir i true,false,i::si,nil] ** V293_changed_irq_physical 0 t)
   (q:=<||sched;;spec_done None||> ** OS[isrupd(isrupd ir i true)i false,false,i::si,nil] ** V293_changed_irq_physical 0 t).
   + unfold V293_changed_irq_snapshot;intros s H;exact H.
   + rewrite V293_irq_clear_update by assumption.
     unfold V293_changed_irq_snapshot;intros s H;exact H.
   + apply eoi_ieoff_rule;[exact Bound|exact Index|apply V293_changed_irq_physical_good].
 - eapply seq_rule;[apply V293_interrupt_changed_enter_call;exact Enter| ].
   eapply seq_rule;[apply V293_interrupt_changed_exit_after_enter;assumption| ].
   eapply conseq_rule with(p:=V293_irq_ready_closed br bg bp target tp
   (V293_ready_irq_prefix bt bh bc bk++[((brun,0%Z),Tint8);((bn,0%Z),Tint8);((bl,0%Z),Tint8)]++rest)
   i si(spec_done None)t nil).
   + unfold V293_changed_irq_return,V293_irq_ready_closed;intros s H;sep auto.
   + intros s H;exact H.
   + apply V293_irq_ready_exint with(intspec:=intspec)(ir:=ir);assumption.
Qed.
End ChangedContinuous.
