(* A complete nonempty builder fixture, with independent shared snapshot controls. *)
(* Same fixed program and one fixed Spec; logical-index ablations. *)
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickReturnTail.
Require Import CertiOS.audit.probes.V293TimeTickCallContextProbe.
Require Import CertiOS.audit.probes.V293TimeTickHookContractProbe.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickScanSlot.
Require Import CertiOS.audit.probes.V293TimeTickSwitchBoundaryProbe.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickStorage.
Require Import CertiOS.framework.proof.memory_prop.
Require Import CertiOS.framework.proof.lmachLib.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickSwitchBoundary.
Require Import CertiOS.audit.probes.V293TimeTickPostHookCoreProbe.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickPostHookCore.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickPostHookHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickSuffix.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickShared.
Require Import CertiOS.audit.probes.V293TimeTickChainOpenProbe.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickChainOpen.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickRecordReassembly.
Require Import CertiOS.certiucos.v293.proofs.V293TCBJointShared.
Require Import CertiOS.audit.probes.V293TimeTickWhileCoreProbe.
Require Import CertiOS.framework.proof.soundness.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickWhileCore.
Require Import CertiOS.audit.probes.V293TimeTickReadyChainProbe.
Require Import CertiOS.audit.probes.V293TimeTickWhileRecordsProbe.
Require Import CertiOS.audit.probes.V293TimeTickWhileSharedProbe.
Require Import CertiOS.audit.probes.V293TimeTickReadyUpdateProbe.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickReadyUpdate.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickWhileRecords.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickWhileShared.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickDelayHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickWhileHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickTaskBridge.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickLosslessFields.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickLoop.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickExpiry.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickReadyChain.
Require Import CertiOS.certiucos.v293.proofs.V293TimeReadyShared.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyTaskInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293SharedStateWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTargetWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTarget.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.certiucos.v293.code.V293OSTimeTick.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.audit.probes.V293TaskRecordOwnershipProbe.
Require Import CertiOS.audit.probes.V293ReadyTaskInvariantProbe.
Require Import CertiOS.audit.probes.V293TimeTickDelayHoareProbe.
Require Import CertiOS.audit.probes.V293TimeTickTraversalProbe.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.framework.proof.rulesoundlib.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List Coq.Sorting.Permutation Lia.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickCallContext.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickLifecycle.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCritical.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickLosslessFields.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickBodyHoare.
Require Import CertiOS.audit.probes.V293TimeTickReturnTailProbe.
Require Import CertiOS.certiucos.v293.proofs.V293TimeAccess.
Require Import CertiOS.audit.probes.V293TimeTickBodyHoareProbe.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickBuilderLocals.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickHookContract.
Import ListNotations.
Local Open Scope nat_scope.
Require Import CertiOS.audit.probes.V293TimeTickBuilderLocalsProbe.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickUniformSpec.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCall.
Local Open Scope nat_scope.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickSharedSnapshot.
Require Import CertiOS.framework.proof.auxdef.
Local Open Scope nat_scope.

Definition SNlogic clock run ct es si ci:=
 V293_tick_shared_logic clock(Int.repr(Z.of_nat run))ct es si ci.
Definition SNfpre:=V293_tick_shared_fpre WhileBindings WhileIdle Vnull
 93%positive 92%positive 94%positive 96%positive 98%positive 99%positive BLrest BLrest_good.
Definition SNfpost:=V293_tick_shared_fpost WhileBindings WhileIdle
 93%positive 92%positive 94%positive 96%positive 98%positive 99%positive BLrest BLrest_good.
Definition SNhpre:=V293_tick_shared_hook_pre WhileBindings WhileIdle Vnull
 93%positive 92%positive 94%positive 96%positive 98%positive 99%positive BLrest BLrest_good.
Definition SNhpost:=V293_tick_shared_hook_post WhileBindings WhileIdle Vnull
 93%positive 92%positive 94%positive 96%positive 98%positive 99%positive BLrest BLrest_good.
Definition SNspec:funspec:=fun f=>if Z.eq_dec f 2001%Z then Some(SNfpre,SNfpost,(Tvoid,[]))
 else if Z.eq_dec f 2002%Z then Some(SNhpre,SNhpost,(Tvoid,[]))else None.
Definition SNpre lg tid:=V293_tick_builder_cells 901%Z 904%Z ** getasrt(SNfpre nil lg tid) **
 V293_tick_builder_domain 901%Z 904%Z.
Definition SNpost lg tid result:=V293_tick_builder_cells 901%Z 904%Z ** getasrt(SNfpost nil result lg tid) **
 V293_tick_builder_domain 901%Z 904%Z.
Lemma SNdecode : forall clock run ct es si ci,run<256 ->
 V293_tick_shared_index(SNlogic clock run ct es si ci)=Some(clock,run,ct,es,si,ci).
Proof. intros;unfold SNlogic,V293_tick_shared_logic,V293_tick_shared_index;rewrite V293_sched_snapshot_roundtrip by assumption;reflexivity. Qed.
Lemma SNselected : forall clock run ct es si ci,run<256 ->gettopis si<=INUM ->
 SNpre(SNlogic clock run ct es si ci)ct=
 V293_tick_builder_pre WhileBindings WhileIdle Vnull ct es
 93%positive 92%positive 94%positive 96%positive 98%positive 99%positive run BLrest
 901%Z 904%Z clock(fun _=>false)si ci /\
 (forall result,SNpost(SNlogic clock run ct es si ci)ct result=
 V293_tick_builder_post WhileBindings WhileIdle
 93%positive 92%positive 94%positive 96%positive 98%positive 99%positive run BLrest
 901%Z 904%Z(fun _=>false)si ci result).
Proof.
 intros clock run ct es si ci Range Bound.
 assert(Guard:V293_tick_shared_guard run ct si ct=true)by(apply V293_tick_shared_guard_valid;auto).
 unfold SNpre,SNpost,SNfpre,SNfpost,V293_tick_shared_fpre,V293_tick_shared_fpost,getasrt,
 V293_tick_shared_pre_asrt,V293_tick_shared_post_asrt.
 rewrite SNdecode by exact Range;rewrite Guard;split;reflexivity.
Qed.
Theorem SNbuilders : forall lg tid,
 Some(SNpre lg tid)=BuildPreI CCprogram 2001%Z[]lg SNfpre tid /\
 Some(SNpost lg tid)=BuildRetI CCprogram 2001%Z[]lg SNfpost tid.
Proof. intros;split;reflexivity. Qed.
Lemma SNcur : forall owner,(CurTid owner ** BLrest) ==> CurLINV V293_witness_li owner.
Proof.
 unfold BLrest,CCrest,CurLINV,LINV,V293_witness_li;intros owner s Held.
 exists([]:list logicvar);clear -Held;sep auto.
Qed.
Theorem SNcontract : forall sd tid vl lg pre post,
 Some pre=BuildPreI CCprogram 2001%Z vl lg SNfpre tid ->
 Some post=BuildRetI CCprogram 2001%Z vl lg SNfpost tid ->
 InfRules SNspec sd V293_witness_li SCinv post Afalse pre BHbody Afalse tid.
Proof.
 intros sd tid vl lg pre post Pre Post.
 eapply V293_tick_shared_internal_contract with(Good:=BLrest_good);try exact Pre;try exact Post.
 - discriminate.
 - exact RUnoabs.
 - change(368+50<=4294967295)%Z;lia.
 - exact WhileBindingsValid.
 - exact WhileKeysUnique.
 - exact BLenv.
 - exact SNcur.
 - exact(proj1 BLframe).
 - exact(proj2 BLframe).
 - reflexivity.
 - reflexivity.
Qed.
Theorem SNsemantics : forall sd lg tid,
 simulation.RuleSem SNspec sd V293_witness_li SCinv(SNpost lg tid)Afalse(SNpre lg tid)BHbody Afalse tid.
Proof. intros;apply RuleSound;eapply SNcontract;[exact(proj1(SNbuilders lg tid))|exact(proj2(SNbuilders lg tid))]. Qed.

(* Shared physical storage and local bindings are independent of es/si/ci. *)
Definition SNphysical clock run:=
 V293_tick_builder_cells 901%Z 904%Z ** V293_tick_builder_domain 901%Z 904%Z **
 (((CurTid WhileReady ** V293_ready_payload 93%positive 92%positive 94%positive WhileOldTasks) **
 PV(96%positive,Int.zero)@Tint32|->Vint32 clock) **
 (V293_owned_record_cells(V293_tick_chain_missing WhileBindings WhileIdle) **
 (V293_owned_record_cells(V293_tick_post_hook_core_globals WhileBindings WhileIdle 98%positive 99%positive run) ** BLrest))).
Definition SNopened clock run es:=SNphysical clock run ** V293_shared_fields WhileReady WhileOldTasks es clock.
Lemma SNphysical_good : forall clock run,GoodFrm(SNphysical clock run).
Proof.
 intros;unfold SNphysical,V293_tick_builder_cells,V293_tick_builder_domain,Alvarmapsto,Alvarenv',
 Aptrmapsto,CurTid,Agvarmapsto,BLrest,BLglobals,CCrest,LINV,V293_witness_li.
 cbn[GoodFrm];repeat split;try exact I;try(apply V293_tick_cells_frame).
Qed.
Lemma SNopen : forall clock run s,
 s |= BLpre clock run ->s |= SNopened clock run ChainEvents.
Proof.
 intros clock run s Held.
 assert(K:s |= V293_tick_switch_view 93%positive 92%positive 94%positive 96%positive
 WhileReady WhileOldTasks ChainEvents clock **
 (V293_tick_builder_cells 901%Z 904%Z ** V293_tick_builder_domain 901%Z 904%Z **
 (V293_owned_record_cells(V293_tick_chain_missing WhileBindings WhileIdle) **
 (V293_owned_record_cells(V293_tick_post_hook_core_globals WhileBindings WhileIdle 98%positive 99%positive run) ** BLrest)))).
 { unfold BLpre,V293_tick_builder_pre,V293_tick_builder_resource,V293_tick_call_shared in Held;
 change(V293_tick_record_map false WhileBindings WhileIdle Vnull)with WhileOldTasks in Held;clear -Held;sep auto. }
 eapply astar_mono in K;[ |apply V293_tick_switch_open|intros st H;exact H].
 unfold SNopened,SNphysical,V293_shared_flags,isrclr in *;clear -K;
 sep normal in K;sep destruct K;sep split in K;sep auto.
 all: match goal with K : _ |= (_ //\\ _) ** _ |- _ =>
 apply astar_l_aconj_elim in K;destruct K as[K _];apply astar_l_aisr_elim in K;exact(proj2 K) end.
Qed.
Definition SNabs clock es:=set(PCabs clock)absecblsid(absecblist es).
Definition SNstate M O op si ci:RstateOP:=(PCge,CCle,M,(fun _=>false),(false,si,ci),O,op).
Lemma SNchange_events : forall clock run es,
 CCstate(BHmemory clock run)(PCabs clock)(PCcode run) |= SNopened clock run ChainEvents ->
 CCstate(BHmemory clock run)(SNabs clock es)(PCcode run) |= SNopened clock run es.
Proof.
 intros clock run es Held.
 assert(K:CCstate(BHmemory clock run)(PCabs clock)(PCcode run) |=
 Aabsdata absecblsid(absecblist ChainEvents) **
 (SNphysical clock run ** (Aabsdata curtid(oscurt WhileReady) **
 (Aabsdata abstcblsid(abstcblist WhileOldTasks) ** Aabsdata ostmid(ostm clock))))).
 { unfold SNopened,V293_shared_fields in Held;clear -Held;sep auto. }
 apply V293_shared_replace_slot with(new:=absecblist es)in K.
 unfold SNopened,V293_shared_fields,SNabs;clear -K;sep auto.
Qed.
Lemma SNclose : forall clock run es si ci M O,
 SNstate M O(PCcode run)si ci |= SNopened clock run es ->
 SNstate M O(PCcode run)si ci |=
 V293_tick_builder_pre WhileBindings WhileIdle Vnull WhileReady es
 93%positive 92%positive 94%positive 96%positive 98%positive 99%positive run BLrest
 901%Z 904%Z clock(fun _=>false)si ci.
Proof.
 intros clock run es si ci M O Held.
 assert(Flags:SNstate M O(PCcode run)si ci |= V293_shared_flags ** SNopened clock run es).
 { unfold V293_shared_flags.
   apply astar_l_aisr_intro with(i:=fun _=>false)in Held;[ |reflexivity].
   apply astar_l_aie_intro with(i:=false)in Held;[ |reflexivity].
   apply astar_l_atopis_intro with(i:=gettopis si)in Held;[ |reflexivity].
   assert(Clr:Aisr(fun _=>false) ==> isrclr).
   { intros st H;unfold isrclr;exists(fun _:hid=>false);split;[exact H| ].
     destruct st as[[[[[[g l]m]r]a]o]p0];cbn in *;tauto. }
   assert(K:SNstate M O(PCcode run)si ci |= Aisr(fun _=>false) ** (Aie false **
     ((EX n:nat,ATopis n) ** SNopened clock run es)))by(clear -Held;sep auto).
   assert(J:SNstate M O(PCcode run)si ci |= isrclr ** (Aie false **
    ((EX n:nat,ATopis n) ** SNopened clock run es))).
   { eapply astar_mono;[exact Clr|intros st H;exact H|exact K]. }
   clear -J;sep auto. }
 assert(View:SNstate M O(PCcode run)si ci |=
 V293_tick_switch_view 93%positive 92%positive 94%positive 96%positive WhileReady WhileOldTasks es clock **
 (V293_tick_builder_cells 901%Z 904%Z ** V293_tick_builder_domain 901%Z 904%Z **
 (V293_owned_record_cells(V293_tick_chain_missing WhileBindings WhileIdle) **
 (V293_owned_record_cells(V293_tick_post_hook_core_globals WhileBindings WhileIdle 98%positive 99%positive run) ** BLrest)))).
 { unfold SNopened,SNphysical in Flags.
   assert(K:SNstate M O(PCcode run)si ci |=
   (V293_shared_flags ** (((CurTid WhileReady ** V293_shared_fields WhileReady WhileOldTasks es clock) **
    V293_ready_payload 93%positive 92%positive 94%positive WhileOldTasks) **
    PV(96%positive,Int.zero)@Tint32|->Vint32 clock)) **
   (V293_tick_builder_cells 901%Z 904%Z ** V293_tick_builder_domain 901%Z 904%Z **
   (V293_owned_record_cells(V293_tick_chain_missing WhileBindings WhileIdle) **
   (V293_owned_record_cells(V293_tick_post_hook_core_globals WhileBindings WhileIdle 98%positive 99%positive run) ** BLrest))))by(clear -Flags;sep auto).
   eapply astar_mono;[ |intros st H;exact H|exact K].
   intros st H;split.
   - apply V293_time_ready_switch_close.
     unfold V293_time_ready_switch_core,V293_time_ready_switch_fields;clear -H;sep auto.
   - clear -H;sep auto. }
 assert(Control:SNstate M O(PCcode run)si ci |=
 Aop(PCcode run) ** OS[(fun _=>false),false,si,ci] **
 (V293_tick_switch_view 93%positive 92%positive 94%positive 96%positive WhileReady WhileOldTasks es clock **
 (V293_tick_builder_cells 901%Z 904%Z ** V293_tick_builder_domain 901%Z 904%Z **
 (V293_owned_record_cells(V293_tick_chain_missing WhileBindings WhileIdle) **
 (V293_owned_record_cells(V293_tick_post_hook_core_globals WhileBindings WhileIdle 98%positive 99%positive run) ** BLrest))))).
 { apply astar_l_aisr_intro with(i:=fun _=>false)in View;[ |reflexivity].
   apply astar_l_aie_intro with(i:=false)in View;[ |reflexivity].
   apply astar_l_ais_intro with(i:=si)in View;[ |reflexivity].
   apply astar_l_acs_intro with(i:=ci)in View;[ |reflexivity].
   apply astar_l_aop'_intro with(aop:=PCcode run)in View;[ |reflexivity].
   clear -View;sep auto. }
 unfold V293_tick_builder_pre,V293_tick_builder_resource,V293_tick_call_shared;
 change(V293_tick_record_map false WhileBindings WhileIdle Vnull)with WhileOldTasks;
 clear -Control;sep auto.
Qed.
Theorem SNallocated : forall clock run es si ci,run<256 ->gettopis si<=INUM ->
 SNstate(BHmemory clock run)(SNabs clock es)(PCcode run)si ci |=
 SNpre(SNlogic clock run WhileReady es si ci)WhileReady.
Proof.
 intros clock run es si ci Range Bound.
 pose proof(SNopen clock run _(proj2(BLallocated clock run Range)))as Open.
 apply SNchange_events with(es:=es)in Open.
 assert(Good:GoodFrm(SNopened clock run es)).
 { unfold SNopened;split;[apply SNphysical_good|unfold V293_shared_fields;cbn[GoodFrm];repeat split;exact I]. }
 pose proof(goodfrm_prop _ _ _ _ _ _ Good Open(fun _=>false)(false,si,ci)(PCcode run))as Shift.
 rewrite(proj1(SNselected clock run WhileReady es si ci Range Bound));apply SNclose;exact Shift.
Qed.

Lemma SNactual_fields : forall clock run ct es si ci s,run<256 ->gettopis si<=INUM ->
 s |= SNpre(SNlogic clock run ct es si ci)ct ->
 get(getabst s)curtid=Some(oscurt ct) /\ get(getabst s)absecblsid=Some(absecblist es).
Proof.
 intros clock run ct es si ci s Range Bound Held.
 rewrite(proj1(SNselected clock run ct es si ci Range Bound))in Held.
 assert(K:s |= V293_tick_switch_view 93%positive 92%positive 94%positive 96%positive
 ct(V293_tick_record_map false WhileBindings WhileIdle Vnull)es clock ** Atrue).
 { unfold V293_tick_builder_pre,V293_tick_builder_resource,V293_tick_call_shared in Held;clear -Held;sep auto. }
 assert(View:forall id value,
 (forall st,st |= V293_shared_fields ct(V293_tick_record_map false WhileBindings WhileIdle Vnull)es clock ->
 get(getabst st)id=Some value) ->get(getabst s)id=Some value).
 { intros id value Extract;eapply V293_star_abst_get_l;[ |exact K];intros st[_ H].
   eapply V293_star_abst_get_l;[exact Extract|exact H]. }
 split;apply View;intros st H;pose proof(V293_shared_fields_get _ _ _ _ st H)as F;tauto.
Qed.
Lemma SNactual_stacks : forall clock run ct es si ci s,run<256 ->gettopis si<=INUM ->
 s |= SNpre(SNlogic clock run ct es si ci)ct ->
 getis(gettaskst s)=si /\ getcs(gettaskst s)=ci.
Proof.
 intros clock run ct es si ci s Range Bound Held.
 rewrite(proj1(SNselected clock run ct es si ci Range Bound))in Held.
 assert(K:s |= Ais si ** (Acs ci ** Atrue)).
 { unfold V293_tick_builder_pre,V293_tick_builder_resource in Held;clear -Held;sep auto. }
 apply astar_l_ais_elim in K;destruct K as[SI K].
 apply astar_l_acs_elim in K;tauto.
Qed.
Theorem SNsame_endpoint_event_control : forall clock run,run<256 ->
 SNstate(BHmemory clock run)(SNabs clock ChainEvents)(PCcode run)[1][false] |=
 SNpre(SNlogic clock run WhileReady ChainEvents[1][false])WhileReady /\
 ~SNstate(BHmemory clock run)(SNabs clock ChainEvents)(PCcode run)[1][false] |=
 SNpre(SNlogic clock run WhileReady(EcbMod.emp)[1][false])WhileReady.
Proof.
 intros clock run Range;assert(Bound:gettopis ([1]:is)<=INUM)by(unfold INUM;cbn;lia).
 split;[apply SNallocated;assumption| ];intro Bad.
 pose proof(proj2(SNactual_fields _ _ _ _ _ _ _ Range Bound Bad))as E.
 change(Some(absecblist ChainEvents)=Some(absecblist EcbMod.emp))in E.
 inversion E as[Maps].

Qed.
Theorem SNsame_endpoint_is_control : forall clock run,run<256 ->
 SNstate(BHmemory clock run)(SNabs clock ChainEvents)(PCcode run)[1][false] |=
 SNpre(SNlogic clock run WhileReady ChainEvents[1][false])WhileReady /\
 ~SNstate(BHmemory clock run)(SNabs clock ChainEvents)(PCcode run)[1][false] |=
 SNpre(SNlogic clock run WhileReady ChainEvents[2][false])WhileReady.
Proof.
 intros clock run Range;split.
 - apply SNallocated;[exact Range|unfold INUM;cbn;lia].
 - intro Bad;pose proof(proj1(SNactual_stacks clock run WhileReady ChainEvents [2] [false] _ Range ltac:(unfold INUM;cbn;lia) Bad))as E;
   change([1]=[2])in E;discriminate.
Qed.
Theorem SNsame_endpoint_cs_control : forall clock run,run<256 ->
 SNstate(BHmemory clock run)(SNabs clock ChainEvents)(PCcode run)[1][false] |=
 SNpre(SNlogic clock run WhileReady ChainEvents[1][false])WhileReady /\
 ~SNstate(BHmemory clock run)(SNabs clock ChainEvents)(PCcode run)[1][false] |=
 SNpre(SNlogic clock run WhileReady ChainEvents[1][true])WhileReady.
Proof.
 intros clock run Range;split.
 - apply SNallocated;[exact Range|unfold INUM;cbn;lia].
 - intro Bad;pose proof(proj2(SNactual_stacks clock run WhileReady ChainEvents [1] [true] _ Range ltac:(unfold INUM;cbn;lia) Bad))as E;
   change([false]=[true])in E;discriminate.
Qed.
Theorem SNidentity_gate_control : forall clock run s,run<256 ->
 ~s |= SNpre(SNlogic clock run WhileHead ChainEvents[1][false])WhileReady.
Proof.
 intros clock run s Range Held.
 unfold SNpre,SNfpre,V293_tick_shared_fpre,getasrt,V293_tick_shared_pre_asrt in Held.
 rewrite SNdecode in Held by exact Range.
 assert(Gate:V293_tick_shared_guard run WhileHead[1]WhileReady=false).
 { unfold V293_tick_shared_guard;destruct(tid_eq_dec WhileHead WhileReady)as[E|E];[inversion E;vm_compute in H1;discriminate|reflexivity]. }
 rewrite Gate in Held;apply astar_comm in Held;apply astar_assoc_elim in Held;
 apply astar_l_afalse_elim in Held;exact Held.
Qed.
Theorem SNall_snapshots_same_spec : forall sd clock run ct es si ci,run<256 ->gettopis si<=INUM ->
 InfRules SNspec sd V293_witness_li SCinv
 (V293_tick_builder_post WhileBindings WhileIdle 93%positive 92%positive 94%positive 96%positive
 98%positive 99%positive run BLrest 901%Z 904%Z(fun _=>false)si ci)Afalse
 (V293_tick_builder_pre WhileBindings WhileIdle Vnull ct es 93%positive 92%positive 94%positive 96%positive
 98%positive 99%positive run BLrest 901%Z 904%Z clock(fun _=>false)si ci)BHbody Afalse ct.
Proof.
 intros sd clock run ct es si ci Range Bound;destruct(SNselected clock run ct es si ci Range Bound)as[Pre Post].
 rewrite <-Pre;eapply r_conseq_rule with(r:=SNpost(SNlogic clock run ct es si ci)ct).
 - intros result s H;rewrite Post in H;exact H.
 - intros s H;exact H.
 - eapply SNcontract;[exact(proj1(SNbuilders _ _))|exact(proj2(SNbuilders _ _))].
Qed.
Theorem SNfixed_entries :
 SNspec 2001%Z=Some(SNfpre,SNfpost,(Tvoid,[])) /\
 SNspec 2002%Z=Some(SNhpre,SNhpost,(Tvoid,[])).
Proof. split;reflexivity. Qed.
Theorem SNmissing_hook : forall ks m irq au,
 ~exists C' state',loststep CCprogram(curs(sfexec 2002%Z[][]),(kenil,ks))(m,irq,au)C' state'.
Proof. apply HCmissing_no_step. Qed.
Theorem SNno_EqDom : ~EqDom CCprogram SNspec.
Proof.
 intros Domain;specialize(Domain 2002%Z).
 change((exists(f:function),None=Some f)<->(exists(spec:fspec),Some(SNhpre,SNhpost,(Tvoid,[]))=Some spec))in Domain.
 destruct(proj2 Domain(ex_intro _ _ eq_refl))as[f Bad];discriminate.
Qed.
