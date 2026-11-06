(* The SAME allocated full call, seven C steps before its old switch. *)
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

Require Import CertiOS.certiucos.v293.proofs.V293LocalGlobalTrace.
Require Import CertiOS.certiucos.v293.proofs.V293HandoffTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitBoundarySwitch.
Require Import CertiOS.certiucos.v293.proofs.V293HandoffProgSim.
Import ListNotations.
Local Open Scope nat_scope.

Definition HCrest br : list(addr*type) :=
 ((96%positive,0%Z),Tint8)::((97%positive,0%Z),Tint8)::
  ((br,0%Z),Tint8)::((95%positive,0%Z),Tint32)::nil.
Definition HCcells br := ((94%positive,0%Z),Tint8)::((91%positive,0%Z),Tint8)::HCrest br.
Definition HCinv br :=V293_ready_storage_inv 80%positive 81%positive 82%positive
 106%Z V293_tcb_type(HCcells br).
Definition HCowned br bs :=Amapsto(bs,0%Z)Tint32 true(Vint32 Int.zero) **
 (SWINVt(V293_ready_inv 80%positive 81%positive 82%positive)OwnershipWaiting **
 (V293_owned_record_cell((94%positive,0%Z),Tint8,V293_byteval 6) **
 (V293_owned_record_cell((91%positive,0%Z),Tint8,V293_byteval 4) **
 (V293_owned_record_cell((93%positive,0%Z),Tptr V293_tcb_type,Vptr OwnershipReady) **V293_storage(HCrest br))))).
Definition HCpacket br bs M cs ip A : Prop :=exists Mt Mf Ot Of,
 join Mt Mf M /\join Ot Of(RIabstract OwnershipWaiting) /\
 (QPge br,V293_cpu_lenv 120%Z bs,Mt,(fun _=>false),(false,nil,false::cs),Ot,spec_done None)|=HCowned br bs /\
 (QPge br,V293_cpu_lenv 120%Z bs,Mf,(fun _=>false),(false,nil,false::cs),Of,spec_done None)|=IWframe /\
 TaskSim(RCprogram,(CPpo,CGempty,ip))
 (curs(V293_interrupt_handoff 103%Z 108%Z 106%Z),(kenil,FTpending))
 (QPge br,V293_cpu_lenv 120%Z bs,Mt,(fun _=>false),(false,nil,false::cs))
 (RCprogram,A)(curs(hapi_code(spec_seq sched(spec_done None))),(kenil,kstop))Ot V293_shared_li(HCinv br)
 (fun st=>satp(fst st)(snd st)(RDYINV(HCinv br)OwnershipWaiting **LINV V293_shared_li OwnershipWaiting nil))OwnershipWaiting.

Lemma HCpartition : forall br bs cs M ip A,
 getsched(RCprogram,A)=V293_scheduler ->
 (QPge br,V293_cpu_lenv 120%Z bs,M,(fun _=>false),(false,nil,false::cs),
 RIabstract OwnershipWaiting,spec_done None)|=FTpre_copy br bs ->
 HCpacket br bs M cs ip A.
Proof.
 intros br bs cs M ip A Sched Held.
 assert(Cells:V293_owned_record_cell((96%positive,0%Z),Tint8,V293_byteval 0) **
 (V293_owned_record_cell((97%positive,0%Z),Tint8,V293_byteval 0) **
 (V293_owned_record_cell((br,0%Z),Tint8,V293_byteval 1) **
 (V293_owned_record_cell((95%positive,0%Z),Tint32,Vint32 Int.zero) **Aemp))) ==>
 V293_storage(HCrest br)).
 { cbn[HCrest V293_storage];repeat apply astar_mono;
   try(intros st H;exact H);apply V293_exit_cell_to_storage. }
 assert(Parts:(QPge br,V293_cpu_lenv 120%Z bs,M,(fun _=>false),(false,nil,false::cs),
 RIabstract OwnershipWaiting,spec_done None)|=
 (V293_owned_record_cell((96%positive,0%Z),Tint8,V293_byteval 0) **
 (V293_owned_record_cell((97%positive,0%Z),Tint8,V293_byteval 0) **
 (V293_owned_record_cell((br,0%Z),Tint8,V293_byteval 1) **
 (V293_owned_record_cell((95%positive,0%Z),Tint32,Vint32 Int.zero) **Aemp)))) **
 (Amapsto(bs,0%Z)Tint32 true(Vint32 Int.zero) **
 (SWINVt(V293_ready_inv 80%positive 81%positive 82%positive)OwnershipWaiting **
 (V293_owned_record_cell((94%positive,0%Z),Tint8,V293_byteval 6) **
 (V293_owned_record_cell((91%positive,0%Z),Tint8,V293_byteval 4) **
 (V293_owned_record_cell((93%positive,0%Z),Tptr V293_tcb_type,Vptr OwnershipReady) **IWframe)))))).
 { unfold FTpre_copy,FTrest,IWframe in *;sep auto. }
 eapply astar_mono in Parts;[ |exact Cells|intros st H;exact H].
 assert(Packed:(QPge br,V293_cpu_lenv 120%Z bs,M,(fun _=>false),(false,nil,false::cs),
 RIabstract OwnershipWaiting,spec_done None)|=HCowned br bs **IWframe)
 by(unfold HCowned;clear Held;sep auto).
 apply sat_split in Packed;destruct Packed as(Mt&Mf&Ot&Of&JM&JO&Owned&Frame).
 assert(Fields:(QPge br,V293_cpu_lenv 120%Z bs,Mt,(fun _=>false),(false,nil,false::cs),Ot,spec_done None)|=
 V293_shared_core **Atrue).
 { unfold HCowned,SWINVt in Owned.
   assert(Open:(QPge br,V293_cpu_lenv 120%Z bs,Mt,(fun _=>false),(false,nil,false::cs),Ot,spec_done None)|=
   SWINV(V293_ready_inv 80%positive 81%positive 82%positive) **Atrue)by(sep auto).
   eapply astar_mono in Open;[ |apply V293_ready_switch_open|intros st H;exact H].
   unfold V293_ready_core,V293_shared_ready_records,V293_shared_core in *;
   sep normal in Open;sep destruct Open;clear Parts Held;sep normal;
   exists x;exists x0;exists x1;exists x2;sep auto. }
 assert(Empty:Of=emp)by(eapply V293_shared_no_abstract_frame;[exact Fields|exact JO]).
 subst Of;apply map_join_emp' in JO;subst Ot.
 unfold HCpacket;exists Mt;exists Mf;exists(RIabstract OwnershipWaiting);exists(emp:osabst).
 split;[exact JM| ];split;[apply map_join_emp| ];split;[exact Owned| ];split;[exact Frame| ].
 unfold HCowned,HCinv,HCcells,FTpending,CPcall in *.
 eapply V293_handoff_TaskSim with(nh:=4)(bc:=94%positive)(bh:=91%positive)(bo:=93%positive)
 (next:=OwnershipReady)(saved_value:=Vint32 Int.zero);
 [exact Sched|exact RPbinding|right;right;reflexivity|lia| | | | | |exact(RIfixed_tasks OwnershipWaiting)| |exact RIhighest|exact Owned].
 - unfold V293_cpu_lenv;rewrite map_get_set' by discriminate;apply map_emp_get.
 - unfold V293_cpu_lenv;rewrite map_get_set' by discriminate;apply map_emp_get.
 - st_env.
 - st_env.
 - st_env.
 - exists(Int.repr 6,wait(os_stat_sem(72%positive,Int.repr 5))Int.one,Vptr(120%positive,Int.repr 7));reflexivity.
Qed.

Theorem HCactual_handoff : forall br bs cs ncs ip A,
 getsched(RCprogram,A)=V293_scheduler ->
 fresh(NPinitial 1)br ->fresh(QPmemory br 1 1)bs ->exists M,
 V293_global_steps(RCprogram,(CPpo,CGempty,ip))HPcst
 (FWtasks,FWos br cs ncs,OwnershipWaiting)
 (set FWtasks OwnershipWaiting(curs(V293_interrupt_handoff 103%Z 108%Z 106%Z),(kenil,FTpending)),
 (QPge br,FTenvs bs,M,(fun _=>false),FTaux cs ncs),OwnershipWaiting) /\
 HCpacket br bs M cs ip A /\
 load Tint32 M(bs,0%Z)=Some(Vint32 Int.zero) /\
 load Tint8 M(94%positive,0%Z)=Some(V293_byteval 6).
Proof.
 intros br bs cs ncs ip A Sched FR FS.
 destruct(FTfixed_prefix br bs cs FR FS)as(M&Prefix&Held).
 pose proof(V293_local_steps_global RCprogram CPpo CGempty ip _ _ _ _ Prefix
 114%Z CPfullbody(emp:env)kstop Tvoid dnil(dcons 120%Z Tint32 dnil)
 FWtasks RPenvs(RPaux cs ncs)OwnershipWaiting HPcst RPbinding
 ltac:(change(goodks(RCprogram,(CPpo,CGempty,ip))CPcall);unfold CPcall;cbn[goodks];unfold pumerge;rewrite RPbinding;exact I))as Global.
 cbn[V293_enclose AddKsToTail]in Global.
 exists M;split.
 - eapply V293_global_trans;[apply FTenter;exact FS|exact Global].
 - split;[eapply HCpartition;[exact Sched|exact Held]| ];split.
   + apply(FTsaved_load bs (QPge br)(V293_cpu_lenv 120%Z bs)M(fun _=>false)
     (false,nil,false::cs)(RIabstract OwnershipWaiting)(spec_done None));
     unfold FTpre_copy,FTrest in Held;sep auto.
   + eapply V293_record_star_load_l with
     (s:=(QPge br,V293_cpu_lenv 120%Z bs,M,(fun _=>false),(false,nil,false::cs),RIabstract OwnershipWaiting,spec_done None))
     (P:=V293_owned_record_cell((94%positive,0%Z),Tint8,V293_byteval 6))(Q:=Atrue).
     * intros st H;apply V293_owned_record_cell_load;exact H.
     * unfold FTpre_copy in Held;sep auto.
Qed.

Theorem HCnonvacuous : exists br bs,
 fresh(NPinitial 1)br /\fresh(QPmemory br 1 1)bs /\
 forall cs (ncs:list bool) ip,exists M,
 HCpacket br bs M cs ip(snd V293SwitchProgSimProbe.SPph).
Proof.
 destruct(memory_has_fresh_block(NPinitial 1))as[br FR].
 destruct(memory_has_fresh_block(QPmemory br 1 1))as[bs FS].
 exists br;exists bs;split;[exact FR| ];split;[exact FS| ];intros.
 destruct(HCactual_handoff br bs cs ncs ip(snd V293SwitchProgSimProbe.SPph)eq_refl FR FS)
 as(M&Trace&Packet&Saved&Cache);exists M;exact Packet.
Qed.

(* The later cache=4 state still rejects the strong old-current guard. *)
Theorem HCactual_switch_gap : forall br bs cs ncs ip,
 fresh(NPinitial 1)br ->fresh(QPmemory br 1 1)bs ->exists M,
 V293_global_steps(RCprogram,(CPpo,CGempty,ip))HPcst
 (FWtasks,FWos br cs ncs,OwnershipWaiting)
 (set FWtasks OwnershipWaiting(curs(sprim(switch 106%Z)),(kenil,FTpending)),
 (QPge br,FTenvs bs,M,(fun _=>false),FTaux cs ncs),OwnershipWaiting) /\
 load Tint8 M(94%positive,0%Z)=Some(V293_byteval 4) /\
 ~(QPge br,V293_cpu_lenv 120%Z bs,M,(fun _=>false),(false,nil,false::cs),
 RIabstract OwnershipWaiting,spec_done None)|=V293_current_guard 94%positive OwnershipWaiting OwnershipTasks.
Proof.
 intros br bs cs ncs ip FR FS.
 destruct(OPactual_entry br bs cs ncs ip FR FS)as(M&Trace&Owned&Saved&Cache&Gap).
 exists M;split;[exact Trace| ];split;assumption.
Qed.

Lemma HCsaved_necessary : forall br bs ge le M ir aux O op,
 (ge,le,M,ir,aux,O,op)|=HCowned br bs ->
 load Tint32 M(bs,0%Z)=Some(Vint32 Int.zero).
Proof.
 intros br bs ge le M ir aux O op Held.
 apply(FTsaved_load bs ge le M ir aux O op);unfold HCowned in Held;sep auto.
Qed.
Lemma HCreject_missing_saved : forall br bs ge le M ir aux O op,
 load Tint32 M(bs,0%Z)=None ->~(ge,le,M,ir,aux,O,op)|=HCowned br bs.
Proof.
 intros br bs ge le M ir aux O op Missing Held.
 pose proof(HCsaved_necessary br bs ge le M ir aux O op Held);congruence.
Qed.
