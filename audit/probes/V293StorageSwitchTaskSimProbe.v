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

Require Import CertiOS.certiucos.v293.proofs.V293StorageSwitchTaskSim.
Require Import CertiOS.audit.probes.V293InvariantPendingTaskSimProbe.
Require Import CertiOS.audit.probes.V293SwitchProgSimProbe.

Definition WSowned br bs :=Amapsto(bs,0%Z)Tint32 true(Vint32 Int.zero) **
 (SWINVt(OPinv br)OwnershipWaiting //\\ SWPRE_NDEAD V293_scheduler 106%Z OwnershipWaiting).
Definition WSpacket br bs M cs ip A : Prop :=exists Mt Mf Ot Of,
 join Mt Mf M /\join Ot Of(RIabstract OwnershipWaiting) /\
 (QPge br,V293_cpu_lenv 120%Z bs,Mt,(fun _=>false),(false,nil,false::cs),Ot,spec_done None)|=WSowned br bs /\
 (QPge br,V293_cpu_lenv 120%Z bs,Mf,(fun _=>false),(false,nil,false::cs),Of,spec_done None)|=IWframe /\
 TaskSim(RCprogram,(CPpo,CGempty,ip))
 (curs(sprim(switch 106%Z)),(kenil,FTpending))
 (QPge br,V293_cpu_lenv 120%Z bs,Mt,(fun _=>false),(false,nil,false::cs))
 (RCprogram,A)(curs(hapi_code(spec_seq sched(spec_done None))),(kenil,kstop))Ot V293_shared_li(OPinv br)
 (fun st=>satp(fst st)(snd st)(RDYINV(OPinv br)OwnershipWaiting **LINV V293_shared_li OwnershipWaiting nil))OwnershipWaiting.

Lemma WSpartition : forall br bs cs M ip A,
 getsched(RCprogram,A)=V293_scheduler ->
 (QPge br,V293_cpu_lenv 120%Z bs,M,(fun _=>false),(false,nil,false::cs),
 RIabstract OwnershipWaiting,spec_done None)|=OPpre br bs ->
 WSpacket br bs M cs ip A.
Proof.
 intros br bs cs M ip A Sched Held.
 assert(Packed:(QPge br,V293_cpu_lenv 120%Z bs,M,(fun _=>false),(false,nil,false::cs),
 RIabstract OwnershipWaiting,spec_done None)|=WSowned br bs **IWframe).
 { unfold OPpre,WSowned,IWframe in *;sep auto. }
 apply sat_split in Packed;destruct Packed as(Mt&Mf&Ot&Of&JM&JO&Owned&Frame).
 unfold WSpacket;exists Mt;exists Mf;exists Ot;exists Of;
 split;[exact JM| ];split;[exact JO| ];split;[exact Owned| ];split;[exact Frame| ].
 unfold FTpending,CPcall,WSowned,OPinv in *.
 eapply V293_storage_switch_TaskSim;
 [exact Sched|exact RPbinding|right;right;reflexivity|exact Owned].
Qed.

(* The SAME full-call execution reaches this old switch, not a target return. *)
Theorem WSactual_old_switch : forall br bs cs ncs ip A,
 getsched(RCprogram,A)=V293_scheduler ->
 fresh(NPinitial 1)br ->fresh(QPmemory br 1 1)bs ->exists M,
 V293_global_steps(RCprogram,(CPpo,CGempty,ip))HPcst
 (FWtasks,FWos br cs ncs,OwnershipWaiting)
 (set FWtasks OwnershipWaiting(curs(sprim(switch 106%Z)),(kenil,FTpending)),
 (QPge br,FTenvs bs,M,(fun _=>false),FTaux cs ncs),OwnershipWaiting) /\
 WSpacket br bs M cs ip A /\
 load Tint32 M(bs,0%Z)=Some(Vint32 Int.zero) /\
 load Tint8 M(94%positive,0%Z)=Some(V293_byteval 4) /\
 ~(QPge br,V293_cpu_lenv 120%Z bs,M,(fun _=>false),(false,nil,false::cs),
 RIabstract OwnershipWaiting,spec_done None)|=V293_current_guard 94%positive OwnershipWaiting OwnershipTasks.
Proof.
 intros br bs cs ncs ip A Sched FR FS.
 destruct(OPactual_entry br bs cs ncs ip FR FS)as(M&Trace&Owned&Saved&Cache&Gap).
 exists M;split;[exact Trace| ];split;[eapply WSpartition;eassumption| ];repeat split;assumption.
Qed.

Theorem WSnonvacuous : exists br bs,
 fresh(NPinitial 1)br /\fresh(QPmemory br 1 1)bs /\
 forall cs ncs ip,exists M,
 V293_global_steps(RCprogram,(CPpo,CGempty,ip))HPcst
 (FWtasks,FWos br cs ncs,OwnershipWaiting)
 (set FWtasks OwnershipWaiting(curs(sprim(switch 106%Z)),(kenil,FTpending)),
 (QPge br,FTenvs bs,M,(fun _=>false),FTaux cs ncs),OwnershipWaiting) /\
 WSpacket br bs M cs ip(snd V293SwitchProgSimProbe.SPph).
Proof.
 destruct(memory_has_fresh_block(NPinitial 1))as[br FR].
 destruct(memory_has_fresh_block(QPmemory br 1 1))as[bs FS].
 exists br;exists bs;split;[exact FR| ];split;[exact FS| ].
 intros;destruct(WSactual_old_switch br bs cs ncs ip(snd V293SwitchProgSimProbe.SPph)eq_refl FR FS)
 as(M&Trace&Packet&Saved&Cache&Gap);exists M;split;assumption.
Qed.

(* A distinct interface checks the full quantifier, without a simulation premise. *)
Theorem WSresume : forall br bs cs M,
 (QPge br,V293_cpu_lenv 120%Z bs,M,(fun _=>false),(false,nil,false::cs),
 RIabstract OwnershipWaiting,spec_done None)|=OPpre br bs ->
 exists Mt Mf Ot Of Ml Mc Ol Oc,
 join Mt Mf M /\join Ot Of(RIabstract OwnershipWaiting) /\
 join Ml Mc Mt /\join Ol Oc Ot /\
 satp(QPge br,V293_cpu_lenv 120%Z bs,Ml,(fun _=>false),(false,nil,false::cs))Ol
 (Amapsto(bs,0%Z)Tint32 true(Vint32 Int.zero)) /\
 satp(QPge br,V293_cpu_lenv 120%Z bs,Mc,(fun _=>false),(false,nil,false::cs))Oc
 (SWINVt(OPinv br)OwnershipWaiting) /\
 (QPge br,V293_cpu_lenv 120%Z bs,Mf,(fun _=>false),(false,nil,false::cs),Of,spec_done None)|=IWframe /\
 forall ip A Mc' Oc' o' O',
 satp(QPge br,V293_cpu_lenv 120%Z bs,Mc',(fun _=>false),(false,nil,false::cs))Oc'
 (SWINVt(OPinv br)OwnershipWaiting) ->
 joinmem(QPge br,V293_cpu_lenv 120%Z bs,Ml,(fun _=>false),(false,nil,false::cs))Mc' o' ->
 join Ol Oc' O' ->
 TaskSim(RCprogram,(CPpo,CGempty,ip))RPpending o'
 (RCprogram,A)(curs(hapi_code(spec_done None)),(kenil,kstop))O' V293_shared_li(OPinv br)
 (fun st=>satp(fst st)(snd st)(RDYINV(OPinv br)OwnershipWaiting **LINV V293_shared_li OwnershipWaiting nil))OwnershipWaiting.
Proof.
 intros br bs cs M Held.
 assert(Packed:(QPge br,V293_cpu_lenv 120%Z bs,M,(fun _=>false),(false,nil,false::cs),
 RIabstract OwnershipWaiting,spec_done None)|=WSowned br bs **IWframe).
 { unfold OPpre,WSowned,IWframe in *;sep auto. }
 apply sat_split in Packed;destruct Packed as(Mt&Mf&Ot&Of&JM&JO&Owned&Frame).
 unfold WSowned in Owned;apply sat_split in Owned;
 destruct Owned as(Ml&Mc&Ol&Oc&JMt&JOt&Saved&[Shared Pre]).
 assert(SavedAll:satp(QPge br,V293_cpu_lenv 120%Z bs,Ml,(fun _=>false),(false,nil,false::cs))Ol
 (Amapsto(bs,0%Z)Tint32 true(Vint32 Int.zero))).
 { intro ab;eapply good_inv_prop;[exact I|exact Saved]. }
 assert(SharedAll:satp(QPge br,V293_cpu_lenv 120%Z bs,Mc,(fun _=>false),(false,nil,false::cs))Oc
 (SWINVt(OPinv br)OwnershipWaiting)).
 { intro ab;eapply swinv_aop_irev;exact Shared. }
 exists Mt;exists Mf;exists Ot;exists Of;exists Ml;exists Mc;exists Ol;exists Oc;
 split;[exact JM| ];split;[exact JO| ];split;[exact JMt| ];split;[exact JOt| ];
 split;[exact SavedAll| ];split;[exact SharedAll| ];split;[exact Frame| ].
 intros ip A Mc' Oc' o' O' Restore JoinMem JoinAbs;unfold RPpending,CPcall,OPinv in *.
 eapply V293_storage_resume_callback;
 [exact RPbinding|right;right;reflexivity|exact Saved|exact Restore|exact JoinMem|exact JoinAbs].
Qed.

(* Returning the original shared heap is one compatible, nonempty callback
   instance. It does NOT mean that this blocked old task is schedulable. *)
Theorem WSresume_concrete : forall br bs cs M ip A,
 (QPge br,V293_cpu_lenv 120%Z bs,M,(fun _=>false),(false,nil,false::cs),
 RIabstract OwnershipWaiting,spec_done None)|=OPpre br bs ->
 exists Mt Mf Ot Of Ml Mc Ol Oc,
 join Mt Mf M /\join Ot Of(RIabstract OwnershipWaiting) /\
 join Ml Mc Mt /\join Ol Oc Ot /\
 satp(QPge br,V293_cpu_lenv 120%Z bs,Ml,(fun _=>false),(false,nil,false::cs))Ol
 (Amapsto(bs,0%Z)Tint32 true(Vint32 Int.zero)) /\
 satp(QPge br,V293_cpu_lenv 120%Z bs,Mc,(fun _=>false),(false,nil,false::cs))Oc
 (SWINVt(OPinv br)OwnershipWaiting) /\
 (QPge br,V293_cpu_lenv 120%Z bs,Mf,(fun _=>false),(false,nil,false::cs),Of,spec_done None)|=IWframe /\
 TaskSim(RCprogram,(CPpo,CGempty,ip))RPpending
 (QPge br,V293_cpu_lenv 120%Z bs,Mt,(fun _=>false),(false,nil,false::cs))
 (RCprogram,A)(curs(hapi_code(spec_done None)),(kenil,kstop))Ot V293_shared_li(OPinv br)
 (fun st=>satp(fst st)(snd st)(RDYINV(OPinv br)OwnershipWaiting **LINV V293_shared_li OwnershipWaiting nil))OwnershipWaiting.
Proof.
 intros br bs cs M ip A Held.
 destruct(WSresume br bs cs M Held)as(Mt&Mf&Ot&Of&Ml&Mc&Ol&Oc&JM&JO&JMt&JOt&Saved&Shared&Frame&Resume).
 exists Mt;exists Mf;exists Ot;exists Of;exists Ml;exists Mc;exists Ol;exists Oc;
 split;[exact JM| ];split;[exact JO| ];split;[exact JMt| ];split;[exact JOt| ];
 split;[exact Saved| ];split;[exact Shared| ];split;[exact Frame| ].
 eapply Resume;[exact Shared| |exact JOt].
 unfold joinmem;do 6 eexists;split;[reflexivity| ];split;[reflexivity|exact JMt].
Qed.

Lemma WSsaved_necessary : forall br bs ge le M ir aux O op,
 (ge,le,M,ir,aux,O,op)|=WSowned br bs ->load Tint32 M(bs,0%Z)=Some(Vint32 Int.zero).
Proof.
 intros br bs ge le M ir aux O op Held.
 apply(FTsaved_load bs ge le M ir aux O op);unfold WSowned in Held;sep auto.
Qed.
Lemma WSreject_missing_saved : forall br bs ge le M ir aux O op,
 load Tint32 M(bs,0%Z)=None ->~(ge,le,M,ir,aux,O,op)|=WSowned br bs.
Proof.
 intros br bs ge le M ir aux O op Missing Held.
 pose proof(WSsaved_necessary br bs ge le M ir aux O op Held);congruence.
Qed.
