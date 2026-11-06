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
Require Import CertiOS.framework.proof.memory_prop.
Require Import CertiOS.framework.proof.lmachLib.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedSwitch.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickReturnTail.
Require Import Coq.Relations.Relation_Operators.
Local Ltac st_env := cbn[getgenv];unfold QPge;rewrite map_get_set' by discriminate;reflexivity.
Require Import CertiOS.audit.probes.V293PendingReturnTaskSimProbe.
Require Import CertiOS.certiucos.v293.proofs.V293EnabledPendingTaskSim.
Definition EPpacket br bs M ci ip A : Prop :=
 exists Mt Mf Ot Of,
 join Mt Mf M /\join Ot Of(set(RIabstract OwnershipWaiting)curtid(oscurt OwnershipReady)) /\
 (QPge br,V293_cpu_lenv 120%Z 98%positive,Mt,(fun _=>false),(false,nil,true::ci),Ot,spec_done None)|=
 Amapsto(98%positive,0%Z)Tint32 true(Vint32 Int.zero) **
 (V293_ready_current_core 80%positive 81%positive 82%positive
 106%Z V293_tcb_type(STcells br)94%positive **CurTid OwnershipReady) /\
 (QPge br,V293_cpu_lenv 120%Z 98%positive,Mf,(fun _=>false),(false,nil,true::ci),Of,spec_done None)|=STframe bs /\
 TaskSim(RCprogram,(CPpo,CGempty,ip))RPpending
 (QPge br,V293_cpu_lenv 120%Z 98%positive,Mt,(fun _=>false),(false,nil,true::ci))
 (RCprogram,A)(SKIP,(kenil,kstop))Ot V293_shared_li(IPinv br)
 (fun st=>satp(fst st)(snd st)(RDYINV(IPinv br)OwnershipReady **LINV V293_shared_li OwnershipReady nil))OwnershipReady.

Lemma EPclose : forall br bs M ci ip A,
 (QPge br,V293_cpu_lenv 120%Z 98%positive,M,(fun _=>false),(false,nil,true::ci),
 set(RIabstract OwnershipWaiting)curtid(oscurt OwnershipReady),spec_done None)|=
 Amapsto(98%positive,0%Z)Tint32 true(Vint32 Int.zero) **
 (V293_ready_current_core 80%positive 81%positive 82%positive
 106%Z V293_tcb_type(STcells br)94%positive **(CurTid OwnershipReady **STframe bs)) ->
 EPpacket br bs M ci ip A.
Proof.
 intros br bs M ci ip A Held.
 assert(Packed:(QPge br,V293_cpu_lenv 120%Z 98%positive,M,(fun _=>false),(false,nil,true::ci),
 set(RIabstract OwnershipWaiting)curtid(oscurt OwnershipReady),spec_done None)|=
 (Amapsto(98%positive,0%Z)Tint32 true(Vint32 Int.zero) **
 (V293_ready_current_core 80%positive 81%positive 82%positive
 106%Z V293_tcb_type(STcells br)94%positive **CurTid OwnershipReady)) **STframe bs)by(sep auto).
 apply sat_split in Packed;destruct Packed as(Mt&Mf&Ot&Of&JM&JO&Owned&Frame).
 unfold EPpacket;exists Mt;exists Mf;exists Ot;exists Of;
 split;[exact JM| ];split;[exact JO| ];split;[exact Owned| ];split;[exact Frame| ].
 unfold RPpending,IPinv.
 eapply V293_enabled_pending_TaskSim;
 [exact RPbinding|right;right;reflexivity|reflexivity|exact Owned].
Qed.

(* Physical/abstract ownership is unchanged by this snapshot control.
   Only the target saved stack top changes; no enabled entry trace is inferred. *)
Lemma EPtoggle : forall br bs M ci ip A,
 PTpacket br bs M ci ip A ->EPpacket br bs M ci ip A.
Proof.
 intros br bs M ci ip A(Mt&Mf&Ot&Of&JM&JO&Owned&Frame&OldSim).
 assert(Good:GoodInvAsrt(Amapsto(98%positive,0%Z)Tint32 true(Vint32 Int.zero) **
 (V293_ready_current_core 80%positive 81%positive 82%positive
 106%Z V293_tcb_type(STcells br)94%positive **CurTid OwnershipReady))).
 { split;[exact I|split;[apply V293_current_core_good|unfold CurTid,Agvarmapsto,Aptrmapsto;cbn[GoodInvAsrt];intros;repeat split;exact I]]. }
 assert(On:(QPge br,V293_cpu_lenv 120%Z 98%positive,Mt,(fun _=>false),(false,nil,true::ci),Ot,spec_done None)|=
 Amapsto(98%positive,0%Z)Tint32 true(Vint32 Int.zero) **
 (V293_ready_current_core 80%positive 81%positive 82%positive
 106%Z V293_tcb_type(STcells br)94%positive **CurTid OwnershipReady)).
 { eapply good_inv_prop;[exact Good|exact Owned]. }
 unfold EPpacket;exists Mt;exists Mf;exists Ot;exists Of;
 split;[exact JM| ];split;[exact JO| ];split;[exact On| ];split.
 - eapply good_inv_prop;[unfold STframe,RCframe;repeat split;exact I|exact Frame].
 - unfold RPpending,IPinv;eapply V293_enabled_pending_TaskSim;
   [exact RPbinding|right;right;reflexivity|reflexivity|exact On].
Qed.

Theorem EPnonvacuous : forall cs ci ip A,
 exists br bs Mc Ms Mf,
 fresh(NPinitial 1)br /\fresh(QPmemory br 1 1)bs /\
 PTpacket br bs Ms ci ip A /\EPpacket br bs Ms ci ip A /\
 V293_global_steps(RCprogram,(CPpo,CGempty,ip))HPcst
 (FWtasks,FWos br cs ci,OwnershipWaiting)
 (set STswitch_tasks OwnershipWaiting(SKIP,(kenil,FTpending)),
 (QPge br,FTenvs bs,Ms,(fun _=>false),FTaux cs ci),OwnershipReady) /\
 store(Tptr V293_tcb_type)Mc(1%positive,0%Z)(Vptr OwnershipReady)=Some Ms /\
 free Tint32 98%positive Ms=Some Mf.
Proof.
 intros cs ci ip A;destruct(PTnonvacuous cs ci ip A)
 as(br&bs&Mc&Ms&Mf&FR&FS&Packet&Trace&Store&Free).
 exists br;exists bs;exists Mc;exists Ms;exists Mf;
 split;[exact FR| ];split;[exact FS| ];split;[exact Packet| ];
 split;[apply EPtoggle;exact Packet| ];split;[exact Trace| ];split;assumption.
Qed.

Theorem EPtransfer : forall br bs M ci ip A,
 EPpacket br bs M ci ip A ->
 exists Mt Mf Ot Of Mt' Ms Ot' Os,
 join Mt Mf M /\join Ot Of(set(RIabstract OwnershipWaiting)curtid(oscurt OwnershipReady)) /\
 join Mt' Ms Mt /\join Ot' Os Ot /\
 satp(QPge br,V293_cpu_lenv 120%Z 98%positive,Ms,(fun _=>false),(true,nil,ci))Os(INV(IPinv br)) /\
 (QPge br,V293_cpu_lenv 120%Z 98%positive,Mt',(fun _=>false),(true,nil,ci),Ot',spec_done None)|=
 Amapsto(98%positive,0%Z)Tint32 true(Vint32 Int.zero) **CurTid OwnershipReady /\
 free Tint32 98%positive Mt'<>None /\
 TaskSim(RCprogram,(CPpo,CGempty,ip))(SKIP,(kenil,kseq sret(kcall 114%Z CPfullbody empenv kstop)))
 (QPge br,V293_cpu_lenv 120%Z 98%positive,Mt',(fun _=>false),(true,nil,ci))
 (RCprogram,A)(SKIP,(kenil,kstop))Ot' V293_shared_li(IPinv br)
 (fun st=>satp(fst st)(snd st)(RDYINV(IPinv br)OwnershipReady **LINV V293_shared_li OwnershipReady nil))OwnershipReady.
Proof.
 intros br bs M ci ip A(Mt&Mf&Ot&Of&JM&JO&Owned&Frame&Sim).
 assert(Packed:(QPge br,V293_cpu_lenv 120%Z 98%positive,Mt,(fun _=>false),(false,nil,true::ci),Ot,spec_done None)|=
 (Amapsto(98%positive,0%Z)Tint32 true(Vint32 Int.zero) **CurTid OwnershipReady) **
 V293_ready_current_core 80%positive 81%positive 82%positive 106%Z V293_tcb_type(STcells br)94%positive)by(sep auto).
 apply sat_split in Packed;destruct Packed as(Mt'&Ms&Ot'&Os&JMt&JOt&Task&Shared).
 assert(On:(QPge br,V293_cpu_lenv 120%Z 98%positive,Mt',(fun _=>false),(true,nil,ci),Ot',spec_done None)|=
 Amapsto(98%positive,0%Z)Tint32 true(Vint32 Int.zero) **CurTid OwnershipReady).
 { eapply good_inv_prop;[split;[exact I|unfold CurTid,Agvarmapsto,Aptrmapsto;cbn[GoodInvAsrt];intros;repeat split;exact I]|exact Task]. }
 exists Mt;exists Mf;exists Ot;exists Of;exists Mt';exists Ms;exists Ot';exists Os;
 split;[exact JM| ];split;[exact JO| ];split;[exact JMt| ];split;[exact JOt| ];split.
 - intro ab;unfold IPinv;apply V293_return_enabled_INV;[reflexivity| ];
   eapply good_inv_prop;[apply V293_current_core_good|exact Shared].
 - split;[exact On| ];split.
   + destruct(V293_tick_free_owned _ _ _ _ _ _ _ _ _ _ _ On)as(m&Free&Rest);rewrite Free;discriminate.
   + unfold IPinv;eapply V293_enabled_return_suffix;
     [exact RPbinding|right;right;reflexivity|reflexivity|exact On].
Qed.
Theorem EPowned_free_boundary : forall br bs M ci ip A,
 EPpacket br bs M ci ip A ->
 exists Mt Mf Ot Of Mret Mfullret,
 join Mt Mf M /\join Ot Of(set(RIabstract OwnershipWaiting)curtid(oscurt OwnershipReady)) /\
 free Tint32 98%positive Mt=Some Mret /\free Tint32 98%positive M=Some Mfullret /\
 join(emp:mem)M M /\free Tint32 98%positive(emp:mem)=None /\
 forall R:asrt,~(QPge br,V293_cpu_lenv 120%Z 98%positive,emp,(fun _=>false),
 (false,nil,true::ci),(emp:osabst),spec_done None)|=
 Amapsto(98%positive,0%Z)Tint32 true(Vint32 Int.zero) **R.
Proof.
 intros br bs M ci ip A(Mt&Mf&Ot&Of&JM&JO&Owned&Frame&Sim).
 destruct(V293_tick_free_owned _ _ _ _ _ _ _ _ _ _ _ Owned)as(Mret&Free&Rest).
 destruct(free_mono _ _ _ _ _ _ JM Free)as(Mfullret&WholeFree).
 exists Mt;exists Mf;exists Ot;exists Of;exists Mret;exists Mfullret;
 split;[exact JM| ];split;[exact JO| ];split;[exact Free| ];split;[exact WholeFree| ];
 split;[apply map_join_comm;apply map_join_emp| ];split;[reflexivity| ].
 intros R Bad;destruct(V293_tick_free_owned _ _ _ _ _ _ _ _ _ _ _ Bad)as(m&Impossible&EmptyRest).
 discriminate Impossible.
Qed.

Theorem EPsaved_stack_boundary : forall p ge le M ir ci ks,
 loststep p(curs(sprim excrit),(kenil,ks))(ge,le,M,ir,(false,nil,false::ci))
 (SKIP,(kenil,ks))(ge,le,M,ir,(false,nil,ci)) /\
 loststep p(curs(sprim excrit),(kenil,ks))(ge,le,M,ir,(false,nil,true::ci))
 (SKIP,(kenil,ks))(ge,le,M,ir,(true,nil,ci)) /\
 ~exists C' st',loststep p(curs(sprim excrit),(kenil,ks))(ge,le,M,ir,(false,nil,nil))C' st'.
Proof. apply PTsaved_stack_boundary. Qed.
