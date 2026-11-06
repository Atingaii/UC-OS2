(* Same frozen entry and caller, with task-owned pending saved storage. *)
Require Import CertiOS.certiucos.v293.proofs.V293CurrentReturnInvariant.
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
Require Import CertiOS.audit.probes.V293ReturnInvariantSplitProbe.
Require Import CertiOS.certiucos.v293.proofs.V293PendingReturnTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293CurrentHandoffPrefix.
Require Import CertiOS.certiucos.v293.proofs.V293ClientSkipTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293HandoffProgSim.
Require Import CertiOS.framework.proof.simulation.
Require Import CertiOS.framework.proof.rulesoundlib.
Require Import CertiOS.framework.proof.memory_prop.
Require Import CertiOS.framework.proof.lmachLib.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedSwitch.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickReturnTail.
Require Import Coq.Relations.Relation_Operators.
Local Ltac st_env := cbn[getgenv];unfold QPge;rewrite map_get_set' by discriminate;reflexivity.
Require Import CertiOS.audit.probes.V293PendingReturnTaskSimProbe.
Require Import CertiOS.certiucos.v293.proofs.V293EnabledPendingTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293SwitchReturnTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293CurrentHandoffPrefix.
Require Import CertiOS.audit.probes.V293CurrentHandoffPrefixProbe.
Require Import CertiOS.audit.probes.V293ReadyCurrentInvariantProbe.
Require Import CertiOS.audit.probes.V293InterruptBuilderCurrentCounterexample.

(* A snapshot partition, not the switch prefix of the blocked old task. *)
Definition SPpacket br bs M ci top : Prop :=
 exists Mt Mf Ot Of Ml Mc Ol Oc,
 join Mt Mf M /\join Ot Of(set(RIabstract OwnershipWaiting)curtid(oscurt OwnershipReady)) /\
 join Ml Mc Mt /\join Ol Oc Ot /\
 (QPge br,V293_cpu_lenv 120%Z 98%positive,Ml,(fun _=>false),(false,nil,top::ci),Ol,spec_done None)|=
 Amapsto(98%positive,0%Z)Tint32 true(Vint32 Int.zero) /\
 satp(QPge br,V293_cpu_lenv 120%Z 98%positive,Mc,(fun _=>false),(false,nil,top::ci))Oc
 (SWINVt(IPinv br)OwnershipReady) /\
 (QPge br,V293_cpu_lenv 120%Z 98%positive,Mf,(fun _=>false),(false,nil,top::ci),Of,spec_done None)|=STframe bs.

Lemma SPclose : forall br t ge le M ci top O op,
 (ge,le,M,(fun _=>false),(false,nil,top::ci),O,op)|=
 V293_ready_current_core 80%positive 81%positive 82%positive
 106%Z V293_tcb_type(STcells br)94%positive **CurTid t ->
 (ge,le,M,(fun _=>false),(false,nil,top::ci),O,op)|=SWINVt(IPinv br)t.
Proof.
 intros br t ge le M ci top O op Held;unfold SWINVt;fold(CurTid t).
 apply sat_split in Held;destruct Held as(Mc&Mt&Oc&Ot&JM&JO&Core&Current).
 apply sat_split';exists Mc;exists Mt;exists Oc;exists Ot;
 split;[exact JM| ];split;[exact JO| ];split;[ |exact Current].
 unfold IPinv;eapply V293_return_disabled_SWINV;[reflexivity|exact Core].
Qed.

Lemma SPpartition : forall br bs M ci ip A top,
 PTpacket br bs M ci ip A ->SPpacket br bs M ci top.
Proof.
 intros br bs M ci ip A top(Mt&Mf&Ot&Of&JM&JO&Owned&Frame&UnusedSim).
 assert(Snapshot:(QPge br,V293_cpu_lenv 120%Z 98%positive,Mt,(fun _=>false),(false,nil,top::ci),Ot,spec_done None)|=
 Amapsto(98%positive,0%Z)Tint32 true(Vint32 Int.zero) **
 (V293_ready_current_core 80%positive 81%positive 82%positive
 106%Z V293_tcb_type(STcells br)94%positive **CurTid OwnershipReady)).
 { eapply good_inv_prop;[split;[exact I|split;[apply V293_current_core_good|
 unfold CurTid,Agvarmapsto,Aptrmapsto;cbn[GoodInvAsrt];intros;repeat split;exact I]]|exact Owned]. }
 apply sat_split in Snapshot;destruct Snapshot as(Ml&Mc&Ol&Oc&JMt&JOt&Saved&Core).
 assert(Shared:(QPge br,V293_cpu_lenv 120%Z 98%positive,Mc,(fun _=>false),(false,nil,top::ci),Oc,spec_done None)|=
 SWINVt(IPinv br)OwnershipReady)by(apply SPclose;exact Core).
 unfold SPpacket;exists Mt;exists Mf;exists Ot;exists Of;exists Ml;exists Mc;exists Ol;exists Oc;
 split;[exact JM| ];split;[exact JO| ];split;[exact JMt| ];split;[exact JOt| ];split;[exact Saved| ];split.
 - intro ab;eapply swinv_aop_irev;exact Shared.
 - eapply good_inv_prop;[unfold STframe,RCframe;repeat split;exact I|exact Frame].
Qed.

(* The callback consumes no previously supplied simulation. *)
Theorem SPresume : forall br bs M ci top,
 SPpacket br bs M ci top ->
 exists Mt Mf Ot Of Ml Mc Ol Oc,
 join Mt Mf M /\join Ot Of(set(RIabstract OwnershipWaiting)curtid(oscurt OwnershipReady)) /\
 join Ml Mc Mt /\join Ol Oc Ot /\
 satp(QPge br,V293_cpu_lenv 120%Z 98%positive,Mc,(fun _=>false),(false,nil,top::ci))Oc
 (SWINVt(IPinv br)OwnershipReady) /\
 forall ip A Mc' Oc' o' O',
 satp(QPge br,V293_cpu_lenv 120%Z 98%positive,Mc',(fun _=>false),(false,nil,top::ci))Oc'
 (SWINVt(IPinv br)OwnershipReady) ->
 joinmem(QPge br,V293_cpu_lenv 120%Z 98%positive,Ml,(fun _=>false),(false,nil,top::ci))Mc' o' ->
 join Ol Oc' O' ->
 TaskSim(RCprogram,(CPpo,CGempty,ip))RPpending o'
 (RCprogram,A)(curs(hapi_code(spec_done None)),(kenil,kstop))O' V293_shared_li(IPinv br)
 (fun st=>satp(fst st)(snd st)(RDYINV(IPinv br)OwnershipReady **LINV V293_shared_li OwnershipReady nil))OwnershipReady.
Proof.
 intros br bs M ci top(Mt&Mf&Ot&Of&Ml&Mc&Ol&Oc&JM&JO&JMt&JOt&Saved&Shared&Frame).
 exists Mt;exists Mf;exists Ot;exists Of;exists Ml;exists Mc;exists Ol;exists Oc;
 split;[exact JM| ];split;[exact JO| ];split;[exact JMt| ];split;[exact JOt| ];split;[exact Shared| ].
 intros ip A Mc' Oc' o' O' Restored Mem Abs;unfold RPpending,IPinv in *.
 eapply V293_resume_callback;
 [exact RPbinding|right;right;reflexivity|exact Saved|exact Restored|exact Mem|exact Abs].
Qed.

Theorem SPnonvacuous : forall cs ci ip (A:osspec) top,
 exists br bs Mc Ms Mf,
 fresh(NPinitial 1)br /\fresh(QPmemory br 1 1)bs /\
 SPpacket br bs Ms ci top /\
 V293_global_steps(RCprogram,(CPpo,CGempty,ip))HPcst
 (FWtasks,FWos br cs ci,OwnershipWaiting)
 (set STswitch_tasks OwnershipWaiting(SKIP,(kenil,FTpending)),
 (QPge br,FTenvs bs,Ms,(fun _=>false),FTaux cs ci),OwnershipReady) /\
 store(Tptr V293_tcb_type)Mc(1%positive,0%Z)(Vptr OwnershipReady)=Some Ms /\
 free Tint32 98%positive Ms=Some Mf.
Proof.
 intros cs ci ip A top;destruct(PTnonvacuous cs ci ip A)
 as(br&bs&Mc&Ms&Mf&FR&FS&Packet&Trace&Store&Free).
 exists br;exists bs;exists Mc;exists Ms;exists Mf;
 split;[exact FR| ];split;[exact FS| ];split;[eapply SPpartition;exact Packet| ];
 split;[exact Trace| ];split;assumption.
Qed.

(* A copied cache value cannot justify the blocked current task's guard. *)
Theorem SPcopied_cache_gap : forall ge le M ir aux O op,
 load Tint8 M(94%positive,0%Z)=Some(V293_byteval 4) ->
 ~(ge,le,M,ir,aux,O,op)|=V293_current_guard 94%positive OwnershipWaiting OwnershipTasks.
Proof.
 intros ge le M ir aux O op Load Guard.
 eapply V293_current_handoff_guard_reject with(nc:=4%nat);
 [lia|exact Load|exact(proj1(proj2(proj2 NCcurrent_mismatch)))|exact SCwaiting_not_highest|exact Guard].
Qed.
