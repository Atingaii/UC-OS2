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
Definition Ulogic clock run:=V293_tick_logic clock(Int.repr(Z.of_nat run)).
Definition Ufpre:=V293_tick_uniform_fpre WhileBindings WhileIdle Vnull WhileReady ChainEvents
 93%positive 92%positive 94%positive 96%positive 98%positive 99%positive BLrest
 (fun _=>false)[1][false] BLrest_good.
Definition Ufpost:=V293_tick_uniform_fpost WhileBindings WhileIdle
 93%positive 92%positive 94%positive 96%positive 98%positive 99%positive BLrest
 (fun _=>false)[1][false] BLrest_good.
Definition Uhpre:=V293_tick_uniform_hook_pre WhileBindings WhileIdle Vnull WhileReady ChainEvents
 93%positive 92%positive 94%positive 96%positive 98%positive 99%positive BLrest
 (fun _=>false)[1][false] BLrest_good.
Definition Uhpost:=V293_tick_uniform_hook_post WhileBindings WhileIdle Vnull WhileReady ChainEvents
 93%positive 92%positive 94%positive 96%positive 98%positive 99%positive BLrest
 (fun _=>false)[1][false] BLrest_good.
Definition Uspec:funspec:=fun f=>if Z.eq_dec f 2001%Z then Some(Ufpre,Ufpost,(Tvoid,[]))
 else if Z.eq_dec f 2002%Z then Some(Uhpre,Uhpost,(Tvoid,[]))else None.
Definition Upre lg:=V293_tick_builder_cells 901%Z 904%Z ** (getasrt(Ufpre nil lg WhileReady)) **
 V293_tick_builder_domain 901%Z 904%Z.
Definition Upost lg result:=V293_tick_builder_cells 901%Z 904%Z ** (getasrt(Ufpost nil result lg WhileReady)) **
 V293_tick_builder_domain 901%Z 904%Z.
Lemma Udecode : forall clock run,run<256 ->V293_tick_index(Ulogic clock run)=Some(clock,run).
Proof. intros;unfold Ulogic,V293_tick_logic,V293_tick_index;rewrite V293_sched_snapshot_roundtrip by assumption;reflexivity. Qed.
Lemma Uselected : forall clock run,run<256 ->
 Upre(Ulogic clock run)=BLpre clock run /\
 (forall result,Upost(Ulogic clock run)result=BLpost run result).
Proof.
 intros clock run Range;assert(B:Nat.ltb run 256=true)by(apply Nat.ltb_lt;exact Range).
 unfold Upre,Upost,Ufpre,Ufpost,V293_tick_uniform_fpre,V293_tick_uniform_fpost,getasrt,
 V293_tick_uniform_pre_asrt,V293_tick_uniform_post_asrt.
 rewrite Udecode by exact Range;rewrite B;split;reflexivity.
Qed.
Theorem Ubuilders : forall lg,
 Some(Upre lg)=BuildPreI CCprogram 2001%Z[]lg Ufpre WhileReady /\
 Some(Upost lg)=BuildRetI CCprogram 2001%Z[]lg Ufpost WhileReady.
Proof. intros;split;reflexivity. Qed.
Theorem Ucontract : forall sd vl lg pre post,
 Some pre=BuildPreI CCprogram 2001%Z vl lg Ufpre WhileReady ->
 Some post=BuildRetI CCprogram 2001%Z vl lg Ufpost WhileReady ->
 InfRules Uspec sd V293_witness_li SCinv post Afalse pre BHbody Afalse WhileReady.
Proof.
 intros sd vl lg pre post Pre Post.
 eapply V293_tick_uniform_internal_contract with(Good:=BLrest_good);try exact Pre;try exact Post.
 - discriminate.
 - exact RUnoabs.
 - change(368+50<=4294967295)%Z;lia.
 - exact WhileBindingsValid.
 - exact WhileKeysUnique.
 - exact BLenv.
 - exact BLcur.
 - exact(proj1 BLframe).
 - exact(proj2 BLframe).
 - change(1<=INUM)%nat;unfold INUM;lia.
 - reflexivity.
 - reflexivity.
 - reflexivity.
Qed.
Theorem Usemantics : forall sd lg,
 simulation.RuleSem Uspec sd V293_witness_li SCinv(Upost lg)Afalse(Upre lg)BHbody Afalse WhileReady.
Proof. intros;apply RuleSound;eapply Ucontract;[exact(proj1(Ubuilders lg))|exact(proj2(Ubuilders lg))]. Qed.
Theorem Uall_clock_run_same_spec : forall sd clock run,run<256 ->
 InfRules Uspec sd V293_witness_li SCinv(BLpost run)Afalse(BLpre clock run)BHbody Afalse WhileReady.
Proof.
 intros sd clock run Range;destruct(Uselected clock run Range)as[Pre Post].
 rewrite <-Pre.
 eapply r_conseq_rule with(r:=Upost(Ulogic clock run)).
 - intros result s H;rewrite Post in H;exact H.
 - intros s H;exact H.
 - eapply Ucontract;[exact(proj1(Ubuilders _))|exact(proj2(Ubuilders _))].
Qed.
Theorem Uallocated : forall clock run,run<256 ->
 CCstate(BHmemory clock run)(PCabs clock)(PCcode run) |= Upre(Ulogic clock run).
Proof. intros;rewrite(proj1(Uselected clock run H));exact(proj2(BLallocated clock run H)). Qed.
Lemma Uclock_slot : forall clock run s,
 s |= BLpre clock run ->get(getabst s)ostmid=Some(ostm clock).
Proof.
 intros clock run s Held.
 assert(K:s |= V293_tick_switch_view 93%positive 92%positive 94%positive 96%positive
 WhileReady(V293_tick_record_map false WhileBindings WhileIdle Vnull)ChainEvents clock ** Atrue).
 { unfold BLpre,V293_tick_builder_pre,V293_tick_builder_resource,V293_tick_call_shared in Held;clear -Held;sep auto. }
 eapply V293_star_abst_get_l;[ |exact K];intros st[_ View].
 eapply V293_star_abst_get_l;[ |exact View];intros st0 H.
 exact(proj2(proj2(proj2(V293_shared_fields_get _ _ _ _ st0 H)))).
Qed.
Lemma Urun_load : forall clock run s,
 s |= BLpre clock run ->load Tint8(getmem s)(98%positive,0%Z)=Some(V293_byteval run).
Proof.
 intros clock run s Held.
 assert(K:s |= V293_owned_record_cell((98%positive,0%Z),Tint8,V293_byteval run) ** Atrue).
 { unfold BLpre,V293_tick_builder_pre,V293_tick_builder_resource,V293_tick_call_shared,
 V293_tick_post_hook_core_globals in Held;cbn[V293_owned_record_cells]in Held;clear -Held;sep auto. }
 eapply V293_record_star_load_l;[apply V293_owned_record_cell_load|exact K].
Qed.
Theorem Usame_endpoint_clock_control : forall run,run<256 ->
 CCstate(BHmemory(Int.repr 37)run)(PCabs(Int.repr 37))(PCcode run) |= Upre(Ulogic(Int.repr 37)run) /\
 ~CCstate(BHmemory(Int.repr 37)run)(PCabs(Int.repr 37))(PCcode run) |= Upre(Ulogic(Int.repr 38)run).
Proof.
 intros run Range;split;[apply Uallocated;exact Range| ];intro Bad.
 rewrite(proj1(Uselected _ run Range))in Bad.
 pose proof(Uclock_slot _ _ _ Bad)as E.
 change(Some(ostm(Int.repr 37))=Some(ostm(Int.repr 38)))in E.
 inversion E as[Bits];vm_compute in Bits;discriminate.
Qed.
(* Both flags select the same stopped ghost branch; only the run index changes. *)
Theorem Usame_endpoint_run_control : forall clock,
 CCstate(BHmemory clock 0)(PCabs clock)(PCcode 0) |= Upre(Ulogic clock 0) /\
 ~CCstate(BHmemory clock 0)(PCabs clock)(PCcode 0) |= Upre(Ulogic clock 255).
Proof.
 intros clock;split;[apply Uallocated;lia| ];intro Bad.
 rewrite(proj1(Uselected clock 255 ltac:(lia)))in Bad.
 pose proof(Urun_load _ _ _ Bad)as Wrong.
 pose proof(Urun_load _ _ _(proj2(BLallocated clock 0 ltac:(lia))))as Actual.
 rewrite Actual in Wrong;vm_compute in Wrong;discriminate.
Qed.
Theorem Umalformed_or_out_of_range : forall s,
 ~s |= Upre nil /\ ~s |= Upre(Ulogic Int.zero 256).
Proof.
 intros s;split;intro Held;unfold Upre,Ufpre,V293_tick_uniform_fpre,getasrt,
 V293_tick_uniform_pre_asrt,Ulogic,V293_tick_logic,V293_tick_index in Held;
 change(s |= V293_tick_builder_cells 901%Z 904%Z ** Afalse ** V293_tick_builder_domain 901%Z 904%Z)in Held;
 apply astar_comm in Held;apply astar_assoc_elim in Held;apply astar_l_afalse_elim in Held;exact Held.
Qed.
Theorem Ustopped_post_nonvacuous : forall ks clock run,run<256 ->run<>1 ->exists Ms,
 CCexecution ks clock run Ms /\
 CCstate Ms(PCabs clock)(END None) |= Upost(Ulogic clock run)None /\
 ~CCstate Ms(PCabs clock)(END None) |= Upost(Ulogic clock run)(Some(Vint32 Int.zero)).
Proof.
 intros ks clock run Range Stopped;destruct(BLstopped_return_nonvacuous ks clock run Range Stopped)as(Ms&Exec&Post&Bad).
 destruct(Uselected clock run Range)as[_ Selected];exists Ms;split;[exact Exec| ];split;
 rewrite Selected;assumption.
Qed.
Theorem Umissing_hook : forall ks m irq au,
 ~exists C' state',loststep CCprogram(curs(sfexec 2002%Z[][]),(kenil,ks))(m,irq,au)C' state'.
Proof. apply HCmissing_no_step. Qed.

Theorem Ufixed_entries :
 Uspec 2001%Z=Some(Ufpre,Ufpost,(Tvoid,[])) /\
 Uspec 2002%Z=Some(Uhpre,Uhpost,(Tvoid,[])).
Proof. split;reflexivity. Qed.
Theorem Usame_stopped_code : PCcode 0=PCcode 255.
Proof. reflexivity. Qed.
Theorem Uno_EqDom : ~EqDom CCprogram Uspec.
Proof.
 intros Domain.
 specialize(Domain 2002%Z).
 change((exists (f:function), None=Some f)<->(exists (spec:fspec), Some(Uhpre,Uhpost,(Tvoid,[]))=Some spec))in Domain.
 destruct(proj2 Domain(ex_intro _ _ eq_refl))as[f Bad];discriminate.
Qed.
