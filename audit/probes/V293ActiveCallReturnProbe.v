Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.code.V293OSIntEnter.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickLifecycle.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewInternal.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTargetWitness.
Require Import CertiOS.certiucos.v293.code.V293ReadyTable.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.certiucos.v293.code.V293OSSchedNew.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import Lia.
Require Import CertiOS.certiucos.v293.proofs.V293SwitchProgSim.
Require Import CertiOS.audit.probes.V293CurrentHandoffPrefixProbe.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyStorageInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293ReadySwitchStep.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyCurrentInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293CurrentHandoffPrefix.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitBoundarySwitch.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitReadyHandoff.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.audit.probes.V293OSIntExitReadyHandoffProbe.
Require Import CertiOS.audit.probes.V293ReadyCriticalGlobalProbe.
Require Import CertiOS.audit.probes.V293ReadyFullCallProbe.
Require Import CertiOS.audit.probes.V293ReadyGlobalTraceProbe.
Require Import CertiOS.audit.probes.V293ReadySwitchStepProbe.
Require Import CertiOS.audit.probes.V293ReadySchedCallProbe.
Require Import CertiOS.audit.probes.V293TaskRecordInvariantProbe.
Require Import CertiOS.audit.probes.V293TaskRecordOwnershipProbe.
Require Import CertiOS.certiucos.v293.proofs.V293HandoffProgSim.
Require Import CertiOS.audit.probes.V293SwitchProgSimProbe.
Require Import CertiOS.certiucos.v293.proofs.V293ClientSkipTaskSim.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.simulation.
Require Import CertiOS.framework.proof.cstepLib.
Require Import CertiOS.framework.proof.step_prop.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import CertiOS.audit.probes.V293HandoffProgSimProbe.
Require Import CertiOS.audit.probes.V293ReadyTaskInvariantProbe.
Require Import CertiOS.audit.probes.V293ReadySourceTailProbe.
Require Import CertiOS.certiucos.v293.proofs.V293ExitDispatchProgSim.
Require Import CertiOS.certiucos.v293.proofs.V293ReadySchedCall.
Require Import CertiOS.certiucos.v293.proofs.V293ReadySourceTail.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewExec.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedChange.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedPointerCompare.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitDispatchCall.
Require Import CertiOS.certiucos.v293.code.V293OSSchedChange.
Require Import CertiOS.certiucos.v293.code.V293OSSchedDispatch.
Local Open Scope nat_scope.
Require Import CertiOS.audit.probes.V293ExitDispatchProgSimProbe.
Require Import CertiOS.audit.probes.V293SchedCallProgSimProbe.
Require Import CertiOS.audit.probes.V293SchedCallEntryProgSimProbe.
Require Import CertiOS.certiucos.v293.proofs.V293ExitCallDispatchProgSim.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyTaskInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTarget.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.framework.auxlibs.MapLib.
Require Import CertiOS.audit.probes.V293ExitCallDispatchProgSimProbe.
Require Import CertiOS.certiucos.v293.proofs.V293ExitNestingProgSim.
Require Import CertiOS.certiucos.v293.code.V293OSIntExit.
Require Import CertiOS.certiucos.v293.code.V293OSSchedGuards.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturnProgSim.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyFullCall.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyCallGlobal.
Require Import CertiOS.audit.probes.V293ExitNestingProgSimProbe.
Require Import CertiOS.audit.probes.V293ReadyFullCallProbe.
Require Import CertiOS.audit.probes.V293CriticalReturnProgSimProbe.
Require Import CertiOS.certiucos.v293.proofs.V293ResumedReturnProgSim.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitResumedReturn.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyGlobalTrace.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import Coq.Relations.Relation_Operators.

Require Import CertiOS.audit.probes.V293ResumedReturnProgSimProbe.

Local Open Scope nat_scope.
Require Import CertiOS.certiucos.v293.proofs.V293ExitActiveCallProgSim.
Require Import CertiOS.audit.probes.V293ExitQuietCallProgSimProbe.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickStorage.
Require Import CertiOS.framework.proof.join_prop.

Require Import CertiOS.audit.probes.V293ActiveCallWitnessProbe.

(* Explicit SOURCE-LEVEL interrupt-switch boundary, not a CPU-port body.
   Original call model and original framework semantics remain unchanged. *)
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitDispatchExecution.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitCallExecution.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyFullCall.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyCriticalGlobal.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCurrent.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedChange.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyTaskInvariant.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.certiucos.v293.code.V293OSSchedChange.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitExecution.
Require Import CertiOS.certiucos.v293.proofs.V293ReadySchedCall.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewExec.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.code.V293OSIntExit.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.code.V293ReadyTable.
Require Import CertiOS.certiucos.v293.code.V293OSSchedNew.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.certiucos.v293.code.V293OSIntEnter.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTargetWitness.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.cstepLib.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Require Import CertiOS.certiucos.v293.proofs.V293ReadySourceTail.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedPointerCompare.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickCountdown.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickLifecycle.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitInterruptGlobal.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyCacheContract.
Require Import Coq.Relations.Relation_Operators.
Require Import CertiOS.framework.proof.auxdef.
Require Import CertiOS.framework.proof.join_prop.
Require Import CertiOS.tactics.basetac.join_lib.
Require Import CertiOS.certiucos.v293.proofs.V293ReadySwitchStep.
Require Import CertiOS.certiucos.v293.proofs.V293LocalGlobalTrace.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyGlobalTrace.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyCallGlobal.
Require Import CertiOS.certiucos.v293.code.V293OSSchedDispatch.
Require Import CertiOS.certiucos.v293.code.V293OSSchedGuards.


Require Import CertiOS.audit.probes.V293ActiveCallTraceProbe.
Require Import CertiOS.audit.probes.V293ReadyResumptionProbe.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitSwitchReturn.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchState.

(* Ready runs an explicit environment fixture, NOT a scheduler choosing the
   blocked Waiting task. Its pending is absent at entry. *)
Definition ARtasks : tasks := set(sig OwnershipReady(curs RPcontext,(kenil,CPcall)))
 OwnershipWaiting(curs(sfexec 114%Z nil nil),(kenil,kstop)).
Definition ARenvs : cltenvs := set(sig OwnershipReady(emp:env))OwnershipWaiting(emp:env).
Definition ARos br cs ncs : osstate :=
 (QPge br,ARenvs,QPmemory br 1 1,(fun _=>false),RPaux cs ncs).
Definition ARsavedenvs bs : cltenvs := set ARenvs OwnershipWaiting(V293_cpu_lenv 120%Z bs).
Definition ARsuspended : tasks := set ARtasks OwnershipWaiting RPpending.
Definition ARback : tasks := set ARsuspended OwnershipReady(curs(sprim(switch 106%Z)),(kenil,CPcall)).
Definition ARdone : tasks := set(set ARback OwnershipReady(SKIP,(kenil,CPcall)))
 OwnershipWaiting(SKIP,(kenil,kstop)).
Local Ltac ar_env := unfold QPge;rewrite map_get_set' by discriminate;reflexivity.
Lemma ARenter : forall br bs cs ncs ip,
 fresh(QPmemory br 1 1)bs ->
 V293_global_steps(RCprogram,(CPpo,CGempty,ip))HPcst
 (ARtasks,ARos br cs ncs,OwnershipWaiting)
 (V293_local_global_at ARtasks ARenvs(RPaux cs ncs)OwnershipWaiting
 (curs CPfullbody,(kenil,CPcall))
 ((QPge br,V293_cpu_lenv 120%Z bs,allocb(QPmemory br 1 1)bs 0%Z 4),(fun _=>false),(false,nil,cs))).
Proof.
 intros br bs cs ncs ip Fresh.
 assert(Bind:=RPbinding).
 assert(Program:pumerge CPpo CGempty 114%Z=Some(Tvoid,dnil,dcons 120%Z Tint32 dnil,CPfullbody)).
 { unfold pumerge;rewrite Bind;reflexivity. }
 assert(Start:V293_local_global_at ARtasks ARenvs(RPaux cs ncs)OwnershipWaiting
 (curs(sfexec 114%Z nil nil),(kenil,kstop))
 ((QPge br,(emp:env),QPmemory br 1 1),(fun _=>false),(false,nil,cs))=
 (ARtasks,ARos br cs ncs,OwnershipWaiting)).
 { cbn[V293_local_global_at V293_global_at]. unfold ARos.
   assert(TC:set ARtasks OwnershipWaiting(curs(sfexec 114%Z nil nil),(kenil,kstop))=ARtasks).
   { apply get_set_same;unfold ARtasks;apply map_get_set. }
   assert(EC:set ARenvs OwnershipWaiting(emp:env)=ARenvs).
   { apply get_set_same;unfold ARenvs;apply map_get_set. }
   assert(AC:set(RPaux cs ncs)OwnershipWaiting(false,nil,cs)=RPaux cs ncs).
   { apply get_set_same;unfold RPaux;apply map_get_set. }
   change((set ARtasks OwnershipWaiting(curs(sfexec 114%Z nil nil),(kenil,kstop)),
   (QPge br,set ARenvs OwnershipWaiting(emp:env),QPmemory br 1 1,((fun _=>false):isr),
   set(RPaux cs ncs)OwnershipWaiting(false,nil,cs)),OwnershipWaiting)=
   (ARtasks,(QPge br,ARenvs,QPmemory br 1 1,((fun _=>false):isr),RPaux cs ncs),OwnershipWaiting)).
   rewrite TC,EC,AC;reflexivity. }
 rewrite <-Start.
 eapply V293_global_trans with(b:=V293_local_global_at ARtasks ARenvs(RPaux cs ncs)OwnershipWaiting
 (curs(salloc nil(dcons 120%Z Tint32 dnil)),(kenil,CPcall))
 ((QPge br,(emp:env),QPmemory br 1 1),(fun _=>false),(false,nil,cs))).
 - apply V293_loststep_global_single.
   + exists(curs(sfexec 114%Z nil nil));exists kenil;exists kstop;split;[reflexivity|left].
     exists 114%Z;exists(@nil val);exists(Tvoid,dnil,dcons 120%Z Tint32 dnil,CPfullbody).
     exists(@nil type);split;[reflexivity|exact Program].
   + apply ostc_step;eapply stmt_step;[reflexivity| ].
     eapply sfexec_step with(d1:=dnil)(d2:=dcons 120%Z Tint32 dnil);
     [reflexivity|reflexivity|exact Program|exact I|reflexivity].
 - eapply V293_global_trans with(b:=V293_local_global_at ARtasks ARenvs(RPaux cs ncs)OwnershipWaiting
   (curs(salloc nil dnil),(kenil,CPcall))
   ((QPge br,V293_cpu_lenv 120%Z bs,allocb(QPmemory br 1 1)bs 0%Z 4),(fun _=>false),(false,nil,cs))).
   + apply V293_loststep_global_single.
     * eapply V293_bound_call_inos;exact Bind.
     * apply ostc_step;eapply stmt_step;[reflexivity| ].
       eapply salloclv_step;[reflexivity|reflexivity| ];exists bs.
       split;[exact Fresh| ];split;[reflexivity| ];split.
       -- intros[v E];rewrite map_emp_get in E;discriminate.
       -- reflexivity.
   + apply V293_loststep_global_single.
     * eapply V293_bound_call_inos;exact Bind.
     * apply ostc_step;eapply stmt_step;[reflexivity|apply sallocend_step].
Qed.

Lemma ARto_switch : forall br bs cs ncs ip,
 fresh(NPinitial 1)br ->fresh(QPmemory br 1 1)bs ->
 exists Mc,
 V293_global_steps(RCprogram,(CPpo,CGempty,ip))HPcst
 (ARtasks,ARos br cs ncs,OwnershipWaiting)
 (set ARtasks OwnershipWaiting(curs(sprim(switch 106%Z)),(kenil,FTpending)),
 (QPge br,ARsavedenvs bs,Mc,(fun _=>false),FTaux cs ncs),OwnershipWaiting) /\
 (QPge br,V293_cpu_lenv 120%Z bs,Mc,(fun _=>false),(false,nil,false::cs),RIabstract OwnershipWaiting,spec_done None)|=
 FTafter_copy br bs OwnershipWaiting.
Proof.
 intros br bs cs ncs ip FR FS.
 destruct(FTfixed_prefix br bs cs FR FS)as(M&Prefix&Held).
 destruct(V293_handoff_copy_execution 80%positive 81%positive 82%positive
 (pumerge CPpo CGempty)(kseq(sprim excrit)(kseq sret kstop))
 (QPge br)(V293_cpu_lenv 120%Z bs)M(fun _=>false)(false,nil,false::cs)
 (RIabstract OwnershipWaiting)(spec_done None)OwnershipWaiting(FTrest br bs)
 103%Z 108%Z 106%Z 91%positive 94%positive 93%positive 4 6 OwnershipReady
 ltac:(lia)ltac:(unfold V293_cpu_lenv;rewrite map_get_set' by discriminate;apply map_emp_get)
 ltac:(unfold V293_cpu_lenv;rewrite map_get_set' by discriminate;apply map_emp_get)
 ltac:(ar_env)ltac:(ar_env)Held)as(Mc&Copy&Store&After&Frame).
 assert(Local:V293_local_steps(pumerge CPpo CGempty)
 (curs CPfullbody,(kenil,kstop))
 ((QPge br,V293_cpu_lenv 120%Z bs,allocb(QPmemory br 1 1)bs 0%Z 4),(fun _=>false),(false,nil,cs))
 (curs(sprim(switch 106%Z)),(kenil,kseq(sprim excrit)(kseq sret kstop)))
 ((QPge br,V293_cpu_lenv 120%Z bs,Mc),(fun _=>false),(false,nil,false::cs))).
 { eapply V293_local_trans;[exact Prefix|apply V293_csteps_local;exact Copy]. }
 pose proof(V293_local_steps_global RCprogram CPpo CGempty ip _ _ _ _ Local
 114%Z CPfullbody(emp:env)kstop Tvoid dnil(dcons 120%Z Tint32 dnil)
 ARtasks ARenvs(RPaux cs ncs)OwnershipWaiting HPcst RPbinding
 ltac:(change(goodks(RCprogram,(CPpo,CGempty,ip))CPcall);unfold CPcall;cbn[goodks];unfold pumerge;rewrite RPbinding;exact I))as Global.
 cbn[V293_enclose AddKsToTail]in Global.
 exists Mc;split;[ |exact After].
 eapply V293_global_trans;[apply ARenter;exact FS|exact Global].
Qed.

Definition ARswstate br bs M cs ncs : osstate :=
 (QPge br,ARsavedenvs bs,M,(fun _=>false),FTaux cs ncs).
Lemma ARfirst_switch : forall br bs cs ncs ip,
 fresh(NPinitial 1)br ->fresh(QPmemory br 1 1)bs ->
 exists M,
 V293_global_steps(RCprogram,(CPpo,CGempty,ip))HPcst
 (ARtasks,ARos br cs ncs,OwnershipWaiting)
 (ARsuspended,ARswstate br bs M cs ncs,OwnershipReady) /\
 (QPge br,V293_cpu_lenv 120%Z bs,M,(fun _=>false),(false,nil,false::cs),
 set(RIabstract OwnershipWaiting)curtid(oscurt OwnershipReady),spec_done None)|=
 FTafter_copy br bs OwnershipReady.
Proof.
 intros br bs cs ncs ip FR FS.
 destruct(ARto_switch br bs cs ncs ip FR FS)as(Mc&Prefix&Held).
 assert(Target:load(Tptr V293_tcb_type)Mc(93%positive,0%Z)=Some(Vptr OwnershipReady)).
 { eapply V293_record_star_load_l with
 (s:=(QPge br,V293_cpu_lenv 120%Z bs,Mc,(fun _=>false),(false,nil,false::cs),RIabstract OwnershipWaiting,spec_done None))
 (P:=V293_owned_record_cell((93%positive,0%Z),Tptr V293_tcb_type,Vptr OwnershipReady))(Q:=Atrue).
 - intros st H;apply V293_owned_record_cell_load;exact H.
 - unfold FTafter_copy in Held;sep auto. }
 destruct(V293_ready_switch_step 80%positive 81%positive 82%positive
 RCprogram CPpo CGempty ip
 (set ARtasks OwnershipWaiting(curs(sprim(switch 106%Z)),(kenil,FTpending)))HPcst FTpending
 OwnershipWaiting OwnershipReady 106%Z 93%positive 1%positive
 (QPge br)(V293_cpu_lenv 120%Z bs)(ARsavedenvs bs)Mc(fun _=>false)(false,nil,false::cs)
 (FTaux cs ncs)(RIabstract OwnershipWaiting)(spec_done None)
 (V293_owned_record_cell((94%positive,0%Z),Tint8,V293_byteval 4) **
 (V293_owned_record_cell((91%positive,0%Z),Tint8,V293_byteval 4) **
 (V293_owned_record_cell((93%positive,0%Z),Tptr V293_tcb_type,Vptr OwnershipReady) **FTrest br bs)))
 V293_tcb_type ltac:(unfold ARsavedenvs;apply map_get_set)ltac:(unfold FTaux;apply map_get_set)
 ltac:(apply map_get_set)ltac:(ar_env)Target ltac:(ar_env)Held)
 as(Msw&Switch&Store&Post&Current&OldCode&Others&Outside).
 assert(TMerge:set(set ARtasks OwnershipWaiting(curs(sprim(switch 106%Z)),(kenil,FTpending)))
 OwnershipWaiting(SKIP,(kenil,FTpending))=ARsuspended).
 { unfold ARsuspended,RPpending,FTpending;symmetry;apply set_set_eq. }
 rewrite TMerge in Switch.

 exists Msw;split;[ |exact Post].
 eapply V293_global_trans;[exact Prefix| ].
 unfold V293_global_steps;eapply rt1n_trans with(y:=(ARsuspended,ARswstate br bs Msw cs ncs,OwnershipReady));[exact Switch|apply rt1n_refl].
Qed.

Lemma ARtable : forall br bs cs M,
 (QPge br,V293_cpu_lenv 120%Z bs,M,(fun _=>false),(false,nil,false::cs),
 set(RIabstract OwnershipWaiting)curtid(oscurt OwnershipReady),spec_done None)|=
 FTafter_copy br bs OwnershipReady ->
 load(Tptr V293_tcb_type)M(82%positive,24%Z)=Some(Vptr OwnershipWaiting).
Proof.
 intros br bs cs M Held.
 unfold FTafter_copy in Held.
 destruct(V293_ready_switch_sound 80%positive 81%positive 82%positive _ _ _ Held)
 as(tasks&lo&hi&entries&Map&Records&Rel&Loads).
 change(get(set(RIabstract OwnershipWaiting)curtid(oscurt OwnershipReady))abstcblsid=
 Some(abstcblist tasks))in Map.
 rewrite map_get_set' in Map by discriminate.
 change(Some(abstcblist OwnershipTasks)=Some(abstcblist tasks))in Map.
 inversion Map;subst tasks.
 destruct Rel as(Lo&Hi&Nonempty&Bitmap&Len&Table).
 destruct(Table OwnershipWaiting(Int.repr 6)
 (wait(os_stat_sem(72%positive,Int.repr 5))Int.one)(Vptr(120%positive,Int.repr 7))eq_refl)
 as(p&Bound&Prio&Entry).
 assert(p=6)by(symmetry;apply V293_priority_repr_injective;[lia|exact Bound|exact Prio]);subst p.
 destruct Loads as(Low&High&Group&TableLoads).
 specialize(TableLoads 6 ltac:(lia));cbn[getmem]in TableLoads.
 rewrite Entry in TableLoads;exact TableLoads.
Qed.

Lemma ARcells : forall br bs cs M,
 (QPge br,V293_cpu_lenv 120%Z bs,M,(fun _=>false),(false,nil,false::cs),
 set(RIabstract OwnershipWaiting)curtid(oscurt OwnershipReady),spec_done None)|=
 FTafter_copy br bs OwnershipReady ->
 (QPge br,V293_cpu_lenv 120%Z bs,M,(fun _=>false),(false,nil,false::cs),
 set(RIabstract OwnershipWaiting)curtid(oscurt OwnershipReady),spec_done None)|=
 V293_owned_record_cell((93%positive,0%Z),Tptr V293_tcb_type,Vptr OwnershipReady) **
 (V293_owned_record_cell((1%positive,0%Z),Tptr V293_tcb_type,Vptr OwnershipReady) **
 (Amapsto(bs,0%Z)Tint32 true(Vint32 Int.zero) **Atrue)).
Proof.
 intros br bs cs M Held.
 unfold FTafter_copy in Held.
 assert(Open:(QPge br,V293_cpu_lenv 120%Z bs,M,(fun _=>false),(false,nil,false::cs),
 set(RIabstract OwnershipWaiting)curtid(oscurt OwnershipReady),spec_done None)|=
 (V293_shared_flags **V293_ready_full 80%positive 81%positive 82%positive OwnershipReady) **
 (V293_owned_record_cell((94%positive,0%Z),Tint8,V293_byteval 4) **
 (V293_owned_record_cell((91%positive,0%Z),Tint8,V293_byteval 4) **
 (V293_owned_record_cell((93%positive,0%Z),Tptr V293_tcb_type,Vptr OwnershipReady) **FTrest br bs)))).
 { eapply astar_mono;[apply V293_ready_switch_full|intros st H;exact H|exact Held]. }
 unfold V293_ready_full in Open;sep normal in Open;sep destruct Open.
 assert(Named:(QPge br,V293_cpu_lenv 120%Z bs,M,(fun _=>false),(false,nil,false::cs),
 set(RIabstract OwnershipWaiting)curtid(oscurt OwnershipReady),spec_done None)|=
 (GV OSTCBCur @ (Tptr x2) |-> (Vptr OwnershipReady)) **Atrue)by(sep auto).
 apply sat_split in Named;destruct Named as(ma&mb&oa&ob&JM&JO&Cell&Rest).
 destruct(V293_dispatch_named_cell_parts _ _ _ _ _ _ _ _ _ _ Cell)as(bc&GE&HC&HE).
 change(get(QPge br)OSTCBCur=Some(bc,Tptr x2))in GE.
 assert(GCur:get(QPge br)OSTCBCur=Some(1%positive,Tptr V293_tcb_type))by ar_env.
 change(Some(1%positive,Tptr V293_tcb_type)=Some(bc,Tptr x2))in GE.
 inversion GE;subst bc x2.
 unfold FTrest,Agvarmapsto in Open;sep normal in Open;sep destruct Open.
 unfold Agvarenv',Aptrmapsto in Open;cbn[addrval_to_addr]in Open.
 assert(Address:(QPge br,V293_cpu_lenv 120%Z bs,M,(fun _=>false),(false,nil,false::cs),
 set(RIabstract OwnershipWaiting)curtid(oscurt OwnershipReady),spec_done None)|=
 Agvarenv OSTCBCur(Tptr V293_tcb_type)(x2,0%Z) **Atrue)by(sep auto).
 apply sat_split in Address;destruct Address as(m1&m2&o1&o2&J1&J2&[b0[G[E0 Other]]]&Other2).
 change(get(QPge br)OSTCBCur=Some(b0,Tptr V293_tcb_type))in G.
 change(Some(1%positive,Tptr V293_tcb_type)=Some(b0,Tptr V293_tcb_type))in G.
 inversion G;subst b0;inversion E0;subst x2.
 unfold V293_owned_record_cell in *;sep auto.
Qed.

(* Environment code, not the kernel scheduler: Waiting remains blocked. *)
Lemma ARprepare : forall br bs cs ncs ip M,
 (QPge br,V293_cpu_lenv 120%Z bs,M,(fun _=>false),(false,nil,false::cs),
 set(RIabstract OwnershipWaiting)curtid(oscurt OwnershipReady),spec_done None)|=
 FTafter_copy br bs OwnershipReady ->
 exists Mb,
 V293_global_steps(RCprogram,(CPpo,CGempty,ip))HPcst
 (ARsuspended,ARswstate br bs M cs ncs,OwnershipReady)
 (ARback,ARswstate br bs Mb cs ncs,OwnershipReady) /\
 load(Tptr V293_tcb_type)Mb(93%positive,0%Z)=Some(Vptr OwnershipWaiting) /\
 (QPge br,V293_cpu_lenv 120%Z bs,Mb,(fun _=>false),(false,nil,false::cs),
 set(RIabstract OwnershipWaiting)curtid(oscurt OwnershipReady),spec_done None)|=
 V293_owned_record_cell((1%positive,0%Z),Tptr V293_tcb_type,Vptr OwnershipReady) **
 (Amapsto(bs,0%Z)Tint32 true(Vint32 Int.zero) **Atrue).
Proof.
 intros br bs cs ncs ip M Held.
 pose proof(ARtable _ _ _ _ Held)as Read.
 pose proof(ARcells _ _ _ _ Held)as Owned.
 destruct(V293_owned_record_cell_update _ (Tptr V293_tcb_type) _ (Vptr OwnershipWaiting)
 _ _ _ _ _ _ _ _ eq_refl Owned)as(Mb&Store&Stored).
 assert(EnvLocal:V293_local_steps(pumerge CPpo CGempty)(curs RPcontext,(kenil,kstop))
 ((QPge br,emp,M),(fun _=>false),(false,nil,false::ncs))
 (curs(sprim(switch 106%Z)),(kenil,kstop))
 ((QPge br,emp,Mb),(fun _=>false),(false,nil,false::ncs))).
 { eapply V293_local_cons.
   - apply ostc_step;eapply stmt_step;[reflexivity|apply sseq_step].
   - eapply V293_local_trans.
     + apply V293_csteps_local;unfold RPassign.
       eapply V293_assign_pointer_execution with(tp:=V293_tcb_type)(tr:=Tptr V293_tcb_type)
       (b:=93%positive)(off:=0%Z)(value:=Vptr OwnershipWaiting).
       * reflexivity.
       * reflexivity.
       * apply eq_vptr;eauto.
       * reflexivity.
       * change(load(Tptr V293_tcb_type)M(82%positive,24%Z)=Some(Vptr OwnershipWaiting));exact Read.
       * change(0<=0<=4294967295)%Z;lia.
       * exact Store.
     + eapply V293_local_cons.
       * apply ostc_step;eapply stmt_step;[reflexivity|apply sskip_step].
       * apply V293_local_refl. }
 assert(Good:goodks(RCprogram,(CPpo,CGempty,ip))CPcall).
 { unfold CPcall;cbn[goodks];unfold pumerge;rewrite RPbinding;exact I. }
 pose proof(V293_local_steps_global RCprogram CPpo CGempty ip _ _ _ _ EnvLocal
 114%Z CPfullbody emp kstop Tvoid dnil(dcons 120%Z Tint32 dnil)
 ARsuspended(ARsavedenvs bs)(FTaux cs ncs)OwnershipReady HPcst RPbinding Good)as Trace.
 assert(TC:set ARsuspended OwnershipReady(curs RPcontext,(kenil,CPcall))=ARsuspended).
 { apply TasksMod.get_set_same.
   change(get ARsuspended OwnershipReady=Some(curs RPcontext,(kenil,CPcall))).
   unfold ARsuspended,ARtasks;rewrite !map_get_set' by(vm_compute;discriminate);apply map_get_sig. }
 assert(LC:set(ARsavedenvs bs)OwnershipReady emp=ARsavedenvs bs).
 { apply CltEnvMod.get_set_same.
   change(get(ARsavedenvs bs)OwnershipReady=Some emp).
   unfold ARsavedenvs,ARenvs;rewrite !map_get_set' by(vm_compute;discriminate);apply map_get_sig. }
 assert(AC:set(FTaux cs ncs)OwnershipReady(false,nil,false::ncs)=FTaux cs ncs).
 { apply TaskLStMod.get_set_same.
   change(get(FTaux cs ncs)OwnershipReady=Some(false,nil,false::ncs)).
   unfold FTaux,RPaux;rewrite map_get_set' by(vm_compute;discriminate);reflexivity. }
 change(V293_global_steps(RCprogram,(CPpo,CGempty,ip))HPcst
 (set ARsuspended OwnershipReady(curs RPcontext,(kenil,CPcall)),
 (QPge br,set(ARsavedenvs bs)OwnershipReady emp,M,(fun _=>false),
 set(FTaux cs ncs)OwnershipReady(false,nil,false::ncs)),OwnershipReady)
 (set ARsuspended OwnershipReady(curs(sprim(switch 106%Z)),(kenil,CPcall)),
 (QPge br,set(ARsavedenvs bs)OwnershipReady emp,Mb,(fun _=>false),
 set(FTaux cs ncs)OwnershipReady(false,nil,false::ncs)),OwnershipReady))in Trace.
 rewrite TC,LC,AC in Trace.
 exists Mb;split;[exact Trace| ];split.
 - eapply V293_store_readback;[reflexivity|exact Store].
 - sep auto.
Qed.

Lemma ARresume : forall br bs enabled ci ncs ip Mb aus,
 get aus OwnershipReady=Some(false,nil,false::ncs) ->
 get aus OwnershipWaiting=Some(false,nil,enabled::ci) ->
 load(Tptr V293_tcb_type)Mb(93%positive,0%Z)=Some(Vptr OwnershipWaiting) ->
 (QPge br,V293_cpu_lenv 120%Z bs,Mb,(fun _=>false),(false,nil,enabled::ci),
 set(RIabstract OwnershipWaiting)curtid(oscurt OwnershipReady),spec_done None)|=
 V293_owned_record_cell((1%positive,0%Z),Tptr V293_tcb_type,Vptr OwnershipReady) **
 (Amapsto(bs,0%Z)Tint32 true(Vint32 Int.zero) **Atrue) ->
 exists Ms Mf,
 V293_global_steps(RCprogram,(CPpo,CGempty,ip))HPcst
 (ARback,(QPge br,ARsavedenvs bs,Mb,(fun _=>false),aus),OwnershipReady)
 (ARdone,(QPge br,set(ARsavedenvs bs)OwnershipWaiting emp,Mf,(fun _=>false),
 set aus OwnershipWaiting(enabled,nil,ci)),OwnershipWaiting) /\
 store(Tptr V293_tcb_type)Mb(1%positive,0%Z)(Vptr OwnershipWaiting)=Some Ms /\
 free Tint32 bs Ms=Some Mf /\
 (forall i,(0<=i<4)%Z ->get Mf(bs,i)=None) /\
 load(Tptr V293_tcb_type)Mf(1%positive,0%Z)=Some(Vptr OwnershipWaiting).
Proof.
 intros br bs enabled ci ncs ip Mb aus RunAux OldAux Target Held.
 assert(RunLocal:get(ARsavedenvs bs)OwnershipReady=Some emp).
 { unfold ARsavedenvs,ARenvs;rewrite !map_get_set' by(vm_compute;discriminate);apply map_get_sig. }
 assert(Suspended:get ARback OwnershipWaiting=Some RPpending).
 { unfold ARback,ARsuspended;rewrite map_get_set' by(vm_compute;discriminate);apply map_get_set. }
 destruct(V293_int_exit_switch_resume_return RCprogram CPpo CGempty ip ARback(ARsavedenvs bs)
 aus OwnershipReady OwnershipWaiting HPcst(QPge br)Mb(fun _=>false)
 emp(false,nil,false::ncs)CPcall 106%Z 93%positive 1%positive V293_tcb_type
 false enabled nil ci(set(RIabstract OwnershipWaiting)curtid(oscurt OwnershipReady))
 (spec_done None)Atrue 114%Z CPfullbody emp kstop Tvoid dnil(dcons 120%Z Tint32 dnil)
 120%Z bs(Vint32 Int.zero)ltac:(vm_compute;discriminate)RPbinding I
 (map_get_set _ _ _)RunLocal RunAux Suspended(map_get_set _ _ _)OldAux
 ltac:(ar_env)Target ltac:(ar_env)Held)
 as(Ms&Mf&Step&Resume&Store&Free&Rest&Removed&Frame).
 exists Ms;exists Mf;split;[exact Resume| ];split;[exact Store| ];split;[exact Free| ];
 split;[exact Removed| ].
 change(load(Tptr V293_tcb_type)
 (getmem(QPge br,emp,Mf,(fun _=>false),(enabled,nil,ci),
 set(RIabstract OwnershipWaiting)curtid(oscurt OwnershipReady),spec_done None))
 (1%positive,0%Z)=Some(Vptr OwnershipWaiting)).
 eapply V293_record_star_load_l;[apply V293_owned_record_cell_load|exact Rest].
Qed.

(* From an actual allocation, not a pre-existing pending continuation. *)
Theorem ARroundtrip : forall br bs cs ncs ip,
 fresh(NPinitial 1)br ->fresh(QPmemory br 1 1)bs ->
 exists Mfirst Mb Ms Mf,
 V293_global_steps(RCprogram,(CPpo,CGempty,ip))HPcst
 (ARtasks,ARos br cs ncs,OwnershipWaiting)
 (ARsuspended,ARswstate br bs Mfirst cs ncs,OwnershipReady) /\
 V293_global_steps(RCprogram,(CPpo,CGempty,ip))HPcst
 (ARsuspended,ARswstate br bs Mfirst cs ncs,OwnershipReady)
 (ARback,ARswstate br bs Mb cs ncs,OwnershipReady) /\
 V293_global_steps(RCprogram,(CPpo,CGempty,ip))HPcst
 (ARtasks,ARos br cs ncs,OwnershipWaiting)
 (ARdone,(QPge br,set(ARsavedenvs bs)OwnershipWaiting emp,Mf,(fun _=>false),
 set(FTaux cs ncs)OwnershipWaiting(false,nil,cs)),OwnershipWaiting) /\
 store(Tptr V293_tcb_type)Mb(1%positive,0%Z)(Vptr OwnershipWaiting)=Some Ms /\
 free Tint32 bs Ms=Some Mf /\
 (forall i,(0<=i<4)%Z ->get Mf(bs,i)=None) /\
 load(Tptr V293_tcb_type)Mf(1%positive,0%Z)=Some(Vptr OwnershipWaiting).
Proof.
 intros br bs cs ncs ip FR FS.
 destruct(ARfirst_switch br bs cs ncs ip FR FS)as(Mfirst&Prefix&After).
 destruct(ARprepare br bs cs ncs ip Mfirst After)as(Mb&Prepare&Target&Owned).
 assert(RunAux:get(FTaux cs ncs)OwnershipReady=Some(false,nil,false::ncs)).
 { unfold FTaux,RPaux;rewrite map_get_set' by(vm_compute;discriminate);reflexivity. }
 destruct(ARresume br bs false cs ncs ip Mb(FTaux cs ncs)RunAux(map_get_set _ _ _)Target Owned)
 as(Ms&Mf&Resume&Store&Free&Removed&Current).
 exists Mfirst;exists Mb;exists Ms;exists Mf;
 split;[exact Prefix| ];split;[exact Prepare| ];split.
 - eapply V293_global_trans;[exact Prefix| ];eapply V293_global_trans;[exact Prepare|exact Resume].
 - split;[exact Store| ];split;[exact Free| ];split;[exact Removed|exact Current].
Qed.

Theorem ARnonvacuous : forall cs ncs ip,exists br bs Mf,
 fresh(NPinitial 1)br /\fresh(QPmemory br 1 1)bs /\
 V293_global_steps(RCprogram,(CPpo,CGempty,ip))HPcst
 (ARtasks,ARos br cs ncs,OwnershipWaiting)
 (ARdone,(QPge br,set(ARsavedenvs bs)OwnershipWaiting emp,Mf,(fun _=>false),
 set(FTaux cs ncs)OwnershipWaiting(false,nil,cs)),OwnershipWaiting) /\
 (forall i,(0<=i<4)%Z ->get Mf(bs,i)=None).
Proof.
 intros cs ncs ip.
 destruct(memory_has_fresh_block(NPinitial 1))as(br&FR).
 destruct(memory_has_fresh_block(QPmemory br 1 1))as(bs&FS).
 destruct(ARroundtrip br bs cs ncs ip FR FS)as(Mfirst&Mb&Ms&Mf&Prefix&Prepare&Whole&Store&Free&Removed&Current).
 exists br;exists bs;exists Mf;split;[exact FR| ];split;[exact FS| ];split;assumption.
Qed.

(* One-factor control at the same reached heap: delete the saved false
   stack top, keep the nonempty outer stack true::ci. Both paths run. *)
Theorem ARstack_control : forall br bs ci ncs ip,
 fresh(NPinitial 1)br ->fresh(QPmemory br 1 1)bs ->
 exists Mb Ms Mf,
 V293_global_steps(RCprogram,(CPpo,CGempty,ip))HPcst
 (ARtasks,ARos br(true::ci)ncs,OwnershipWaiting)
 (ARback,ARswstate br bs Mb(true::ci)ncs,OwnershipReady) /\
 V293_global_steps(RCprogram,(CPpo,CGempty,ip))HPcst
 (ARback,ARswstate br bs Mb(true::ci)ncs,OwnershipReady)
 (ARdone,(QPge br,set(ARsavedenvs bs)OwnershipWaiting emp,Mf,(fun _=>false),
 set(FTaux(true::ci)ncs)OwnershipWaiting(false,nil,true::ci)),OwnershipWaiting) /\
 V293_global_steps(RCprogram,(CPpo,CGempty,ip))HPcst
 (ARback,(QPge br,ARsavedenvs bs,Mb,(fun _=>false),
 set(FTaux(true::ci)ncs)OwnershipWaiting(false,nil,true::ci)),OwnershipReady)
 (ARdone,(QPge br,set(ARsavedenvs bs)OwnershipWaiting emp,Mf,(fun _=>false),
 set(FTaux(true::ci)ncs)OwnershipWaiting(true,nil,ci)),OwnershipWaiting) /\
 store(Tptr V293_tcb_type)Mb(1%positive,0%Z)(Vptr OwnershipWaiting)=Some Ms /\
 free Tint32 bs Ms=Some Mf /\
 set(FTaux(true::ci)ncs)OwnershipWaiting(false,nil,true::ci)<>
 set(FTaux(true::ci)ncs)OwnershipWaiting(true,nil,ci).
Proof.
 intros br bs ci ncs ip FR FS.
 destruct(ARfirst_switch br bs(true::ci)ncs ip FR FS)as(Mfirst&Prefix&After).
 destruct(ARprepare br bs(true::ci)ncs ip Mfirst After)as(Mb&Prepare&Target&Owned).
 assert(RunAux:get(FTaux(true::ci)ncs)OwnershipReady=Some(false,nil,false::ncs)).
 { unfold FTaux,RPaux;rewrite map_get_set' by(vm_compute;discriminate);reflexivity. }
 destruct(ARresume br bs false(true::ci)ncs ip Mb(FTaux(true::ci)ncs)
 RunAux(map_get_set _ _ _)Target Owned)as(Ms&Mf&Positive&Store&Free&Removed&Current).
 assert(NegOwned:(QPge br,V293_cpu_lenv 120%Z bs,Mb,(fun _=>false),(false,nil,true::ci),
 set(RIabstract OwnershipWaiting)curtid(oscurt OwnershipReady),spec_done None)|=
 V293_owned_record_cell((1%positive,0%Z),Tptr V293_tcb_type,Vptr OwnershipReady) **
 (Amapsto(bs,0%Z)Tint32 true(Vint32 Int.zero) **Atrue)).
 { eapply good_inv_prop;[unfold V293_owned_record_cell;cbn;auto|exact Owned]. }
 assert(NegAux:get(set(FTaux(true::ci)ncs)OwnershipWaiting(false,nil,true::ci))
 OwnershipReady=Some(false,nil,false::ncs)).
 { rewrite map_get_set' by(vm_compute;discriminate);exact RunAux. }
 destruct(ARresume br bs true ci ncs ip Mb
 (set(FTaux(true::ci)ncs)OwnershipWaiting(false,nil,true::ci))
 NegAux(map_get_set _ _ _)Target NegOwned)as(Msn&Mfn&Negative&StoreN&FreeN&RemovedN&CurrentN).
 assert(Msn=Ms)by congruence;subst Msn.
 assert(Mfn=Mf)by congruence;subst Mfn.
 rewrite <- (set_set_eq _ _ _ _(FTaux(true::ci)ncs)OwnershipWaiting
 (true,nil,ci)(false,nil,true::ci))in Negative.
 exists Mb;exists Ms;exists Mf;split.
 - eapply V293_global_trans;[exact Prefix|exact Prepare].
 - split;[exact Positive| ];split;[exact Negative| ];split;[exact Store| ];split;[exact Free| ].
   intro Same;pose proof(f_equal(fun a:ltaskstset=>get a OwnershipWaiting)Same)as E.
   change(get(set(FTaux(true::ci)ncs)OwnershipWaiting(false,nil,true::ci))OwnershipWaiting=
   get(set(FTaux(true::ci)ncs)OwnershipWaiting(true,nil,ci))OwnershipWaiting)in E.
   rewrite !map_get_set in E;discriminate.
Qed.

Theorem ARendpoint_metadata : forall bs cs ncs,
 get ARtasks OwnershipWaiting=Some(curs(sfexec 114%Z nil nil),(kenil,kstop)) /\
 get ARsuspended OwnershipWaiting=Some RPpending /\
 get ARdone OwnershipWaiting=Some(SKIP,(kenil,kstop)) /\
 get ARdone OwnershipReady=Some(SKIP,(kenil,CPcall)) /\
 get(set(ARsavedenvs bs)OwnershipWaiting emp)OwnershipWaiting=Some emp /\
 get(set(FTaux cs ncs)OwnershipWaiting(false,nil,cs))OwnershipWaiting=Some(false,nil,cs) /\
 get(set(ARsavedenvs bs)OwnershipWaiting emp)OwnershipReady=Some emp /\
 get(set(FTaux cs ncs)OwnershipWaiting(false,nil,cs))OwnershipReady=Some(false,nil,false::ncs).
Proof. intros bs cs ncs;repeat split. Qed.
