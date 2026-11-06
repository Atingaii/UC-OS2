(* The old blocked task, at its actual allocated full-call cut point. *)
Require Import CertiOS.audit.probes.V293ActiveCallTraceProbe.
Require Import CertiOS.audit.probes.V293ActiveCallWitnessProbe.
Require Import CertiOS.audit.probes.V293ResumedReturnProgSimProbe.
Require Import CertiOS.audit.probes.V293ExitQuietCallProgSimProbe.
Require Import CertiOS.audit.probes.V293ExitNestingProgSimProbe.
Require Import CertiOS.audit.probes.V293CriticalReturnProgSimProbe.
Require Import CertiOS.audit.probes.V293ReadyCriticalGlobalProbe.
Require Import CertiOS.audit.probes.V293ReadySchedCallProbe.
Require Import CertiOS.audit.probes.V293HandoffProgSimProbe.
Require Import CertiOS.audit.probes.V293TaskRecordOwnershipProbe.
Require Import CertiOS.audit.probes.V293TaskRecordInvariantProbe.
Require Import CertiOS.audit.probes.V293OSIntExitDispatchCallProbe.
Require Import CertiOS.audit.probes.V293OSIntExitSwitchEntryProbe.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitSharedReturn.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitSharedReclose.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyCurrentInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyStorageInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyTaskInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyFullCall.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyCallGlobal.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyGlobalTrace.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchState.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchStorage.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTarget.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.framework.proof.auxdef.
Require Import CertiOS.framework.proof.join_prop.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.basetac.join_lib.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Require Import CertiOS.audit.probes.V293SharedSwitchReturnProbe.
Require Import CertiOS.audit.probes.V293SwitchReturnTaskSimProbe.
Require Import CertiOS.certiucos.v293.proofs.V293StorageSwitchPre.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTarget.
Require Import CertiOS.framework.proof.rulesoundlib.
Require Import CertiOS.framework.proof.lmachLib.
Require Import CertiOS.framework.proof.memory_prop.

Require CertiOS.tactics.hoareforward.symbolic_lemmas.

Import ListNotations.
Local Open Scope nat_scope.
Local Ltac st_env := cbn[getgenv];unfold QPge;
 rewrite map_get_set' by discriminate;reflexivity.

Require Import CertiOS.audit.probes.V293OldSwitchPacketProbe.
Require Import CertiOS.certiucos.v293.proofs.V293InvariantPendingTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293StoragePendingTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293CurrentReturnInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293ClientSkipTaskSim.
Require Import CertiOS.framework.proof.simulation.

Definition IWcore br :=V293_ready_storage_core 80%positive 81%positive 82%positive
 106%Z V293_tcb_type(STcells br).
Definition IWowned br bs :=Amapsto(bs,0%Z)Tint32 true(Vint32 Int.zero) **
 (IWcore br **CurTid OwnershipWaiting).
Definition IWframe :=Amapsto(98%positive,0%Z)Tint32 true(Vint32 Int.zero) **RCframe.
Definition IWpacket br bs M top ci ip A : Prop :=exists Mt Mf Ot Of,
 join Mt Mf M /\join Ot Of(RIabstract OwnershipWaiting) /\
 (QPge br,V293_cpu_lenv 120%Z bs,Mt,(fun _=>false),(false,nil,top::ci),Ot,spec_done None)|=IWowned br bs /\
 (QPge br,V293_cpu_lenv 120%Z bs,Mf,(fun _=>false),(false,nil,top::ci),Of,spec_done None)|=IWframe /\
 TaskSim(RCprogram,(CPpo,CGempty,ip))RPpending
 (QPge br,V293_cpu_lenv 120%Z bs,Mt,(fun _=>false),(false,nil,top::ci))
 (RCprogram,A)(SKIP,(kenil,kstop))Ot V293_shared_li(OPinv br)
 (fun st=>satp(fst st)(snd st)(RDYINV(OPinv br)OwnershipWaiting **LINV V293_shared_li OwnershipWaiting nil))OwnershipWaiting.

Lemma IWopen : forall br,
 SWINVt(OPinv br)OwnershipWaiting ==>IWcore br **CurTid OwnershipWaiting.
Proof.
 intros br st Held;unfold SWINVt,OPinv in Held;fold(CurTid OwnershipWaiting)in Held.
 eapply astar_mono in Held;[ |apply V293_ready_storage_switch_open|intros s H;exact H].
 assert(Empty:V293_shared_flags ==> Aemp).
 { intros s Flags;unfold V293_shared_flags in Flags.
   apply astar_l_aemp_elim.
   eapply astar_mono with(P:=isrclr **Aie false)(Q:=EX k:hid,ATopis k);
   [ |intros s0[k[_ E]];exact E|exact Flags].
   intros s0 F;apply astar_l_aemp_elim.
   eapply astar_mono with(P:=isrclr)(Q:=Aie false);
   [ |intros s1[_ E];exact E|exact F].
   intros s1[r[Flag Clear]];exact(proj2 Flag). }
 apply astar_l_aemp_elim.
 eapply astar_mono;[exact Empty|intros s K;exact K| ].
 clear Empty;unfold IWcore;sep auto.
Qed.

Lemma IWpartition : forall br bs M cs top ci ip A,
 (QPge br,V293_cpu_lenv 120%Z bs,M,(fun _=>false),(false,nil,false::cs),
 RIabstract OwnershipWaiting,spec_done None)|=OPpre br bs ->
 IWpacket br bs M top ci ip A.
Proof.
 intros br bs M cs top ci ip A Held.
 assert(Open:(QPge br,V293_cpu_lenv 120%Z bs,M,(fun _=>false),(false,nil,false::cs),
 RIabstract OwnershipWaiting,spec_done None)|=
 Amapsto(bs,0%Z)Tint32 true(Vint32 Int.zero) **
 ((IWcore br **CurTid OwnershipWaiting) **IWframe)).
 { unfold OPpre in Held.
   assert(Convert:forall st,st|=(SWINVt(OPinv br)OwnershipWaiting //\\ SWPRE_NDEAD V293_scheduler 106%Z OwnershipWaiting) ->
    st|=IWcore br **CurTid OwnershipWaiting).
   { intros st H;apply IWopen;exact(proj1 H). }
   eapply astar_mono;[intros st H;exact H| |exact Held].
   eapply astar_mono;[exact Convert|intros st H;exact H]. }
 assert(Packed:(QPge br,V293_cpu_lenv 120%Z bs,M,(fun _=>false),(false,nil,false::cs),
 RIabstract OwnershipWaiting,spec_done None)|=IWowned br bs **IWframe)by(unfold IWowned;sep auto).
 apply sat_split in Packed;destruct Packed as(Mt&Mf&Ot&Of&JM&JO&Owned&Frame).
 assert(Good:GoodInvAsrt(IWowned br bs)).
 { unfold IWowned;split;[exact I| ];split;[apply V293_ready_storage_core_good| ].
   unfold CurTid,Agvarmapsto,Aptrmapsto;cbn[GoodInvAsrt];intros;repeat split;exact I. }
 assert(Owned':(QPge br,V293_cpu_lenv 120%Z bs,Mt,(fun _=>false),(false,nil,top::ci),Ot,spec_done None)|=IWowned br bs).
 { eapply good_inv_prop;[exact Good|exact Owned]. }
 assert(Frame':(QPge br,V293_cpu_lenv 120%Z bs,Mf,(fun _=>false),(false,nil,top::ci),Of,spec_done None)|=IWframe).
 { eapply good_inv_prop;[unfold IWframe;split;[exact I|apply RCframe_good]|exact Frame]. }
 unfold IWpacket;exists Mt;exists Mf;exists Ot;exists Of.
 split;[exact JM| ];split;[exact JO| ];split;[exact Owned'| ];split;[exact Frame'| ].
 unfold RPpending,CPcall,OPinv,IWowned,IWcore in *.
 eapply V293_storage_pending_TaskSim;
 [exact RPbinding|right;right;reflexivity|reflexivity|exact Owned'].
Qed.

(* The cut is reachable; starting the old pending suffix is a callback
   witness, not a proof that this blocked task has globally resumed. *)
Theorem IWactual_old_cut : forall br bs cs ncs ip A,
 fresh(NPinitial 1)br ->fresh(QPmemory br 1 1)bs ->exists M,
 V293_global_steps(RCprogram,(CPpo,CGempty,ip))HPcst
 (FWtasks,FWos br cs ncs,OwnershipWaiting)
 (set FWtasks OwnershipWaiting(curs(sprim(switch 106%Z)),(kenil,FTpending)),
 (QPge br,FTenvs bs,M,(fun _=>false),FTaux cs ncs),OwnershipWaiting) /\
 (forall top ci,IWpacket br bs M top ci ip A) /\
 load Tint8 M(94%positive,0%Z)=Some(V293_byteval 4) /\
 ~(QPge br,V293_cpu_lenv 120%Z bs,M,(fun _=>false),(false,nil,false::cs),
 RIabstract OwnershipWaiting,spec_done None)|=V293_current_guard 94%positive OwnershipWaiting OwnershipTasks.
Proof.
 intros br bs cs ncs ip A FR FS.
 destruct(OPactual_entry br bs cs ncs ip FR FS)as(M&Trace&Owned&Saved&Cache&Gap).
 exists M;split;[exact Trace| ];split;[ |split;assumption].
 intros;eapply IWpartition;exact Owned.
Qed.

Theorem IWnonvacuous : exists br bs,
 fresh(NPinitial 1)br /\fresh(QPmemory br 1 1)bs /\
 forall (cs ncs:list bool) ip A,exists M,(forall top ci,IWpacket br bs M top ci ip A) /\
 load Tint8 M(94%positive,0%Z)=Some(V293_byteval 4).
Proof.
 destruct(memory_has_fresh_block(NPinitial 1))as[br FR].
 destruct(memory_has_fresh_block(QPmemory br 1 1))as[bs FS].
 exists br;exists bs;split;[exact FR| ];split;[exact FS| ].
 intros;destruct(IWactual_old_cut br bs cs ncs ip A FR FS)as(M&Trace&Packet&Cache&Gap).
 exists M;split;assumption.
Qed.

(* Compatibility with the earlier stronger invariant uses the SAME
   generic step proof, not a second implementation of the suffix. *)
Theorem IWcurrent_compatible : forall br bg bp target tp cells cache
 pc po pi ip A t ge M ir top ci O op f body caller tail tau d1 d2 saved b v,
 po f=Some(tau,d1,d2,body) ->V293_skip_client_state(SKIP,(kenil,tail)) ->
 (forall i,ir i=false) ->
 (ge,V293_cpu_lenv saved b,M,ir,(false,nil,top::ci),O,op)|=
 Amapsto(b,0%Z)Tint32 true v **
 (V293_ready_current_core br bg bp target tp cells cache **CurTid t) ->
 TaskSim(pc,(po,pi,ip))
 (SKIP,(kenil,kseq(sprim excrit)(kseq sret(kcall f body caller tail))))
 (ge,V293_cpu_lenv saved b,M,ir,(false,nil,top::ci))
 (pc,A)(SKIP,(kenil,tail))O V293_shared_li(V293_ready_current_inv br bg bp target tp cells cache)
 (fun st=>satp(fst st)(snd st)(RDYINV(V293_ready_current_inv br bg bp target tp cells cache)t **LINV V293_shared_li t nil))t.
Proof.
 intros br bg bp target tp cells cache pc po pi ip A t ge M ir top ci O op f body caller tail tau d1 d2 saved b v Bind Cases Clear Held.
 eapply V293_invariant_pending_TaskSim;[reflexivity|apply V293_current_core_good| | |exact Bind|exact Cases|exact Clear|exact Held].
 - intros;apply V293_return_disabled_SWINV;assumption.
 - intros;apply V293_return_enabled_INV;assumption.
Qed.

Lemma IWowned_saved_necessary : forall br bs ge le M ir aux O op,
 (ge,le,M,ir,aux,O,op)|=IWowned br bs ->
 load Tint32 M(bs,0%Z)=Some(Vint32 Int.zero).
Proof.
 intros br bs ge le M ir aux O op Held.
 apply(FTsaved_load bs ge le M ir aux O op);unfold IWowned in Held;sep auto.
Qed.

Lemma IWreject_missing_saved : forall br bs ge le M ir aux O op,
 load Tint32 M(bs,0%Z)=None ->
 ~(ge,le,M,ir,aux,O,op)|=IWowned br bs.
Proof.
 intros br bs ge le M ir aux O op Missing Held.
 pose proof(IWowned_saved_necessary br bs ge le M ir aux O op Held);congruence.
Qed.
