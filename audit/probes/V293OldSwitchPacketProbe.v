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

Definition OPinv br := V293_ready_storage_inv 80%positive 81%positive 82%positive
 106%Z V293_tcb_type(STcells br).
Definition OPpre br bs :=
 Amapsto(bs,0%Z)Tint32 true(Vint32 Int.zero) **
 ((SWINVt(OPinv br)OwnershipWaiting //\\ SWPRE_NDEAD V293_scheduler 106%Z OwnershipWaiting) **
 (Amapsto(98%positive,0%Z)Tint32 true(Vint32 Int.zero) **RCframe)).

Lemma OPpartition : forall br bs cs M,
 (QPge br,V293_cpu_lenv 120%Z bs,M,(fun _=>false),(false,nil,false::cs),
 RIabstract OwnershipWaiting,spec_done None)|=FTafter_copy br bs OwnershipWaiting ->
 (QPge br,V293_cpu_lenv 120%Z bs,M,(fun _=>false),(false,nil,false::cs),
 RIabstract OwnershipWaiting,spec_done None)|=OPpre br bs.
Proof.
 intros br bs cs M Held.
 assert(Target:load(Tptr V293_tcb_type)M(93%positive,0%Z)=Some(Vptr OwnershipReady)).
 { eapply V293_record_star_load_l with
 (s:=(QPge br,V293_cpu_lenv 120%Z bs,M,(fun _=>false),(false,nil,false::cs),RIabstract OwnershipWaiting,spec_done None))
 (P:=V293_owned_record_cell((93%positive,0%Z),Tptr V293_tcb_type,Vptr OwnershipReady))(Q:=Atrue).
 - intros st H;apply V293_owned_record_cell_load;exact H.
 - unfold FTafter_copy in Held;sep auto. }
 pose proof(STrepack br bs cs OwnershipWaiting M Held)as Packed;clear Held.
 apply sat_split in Packed;destruct Packed as(Mc&Mf&Oc&Of&JM&JO&Shared&Frame).
 assert(Fields:(QPge br,V293_cpu_lenv 120%Z bs,Mc,(fun _=>false),(false,nil,false::cs),Oc,spec_done None)|=
 V293_shared_core **Atrue).
 { unfold SWINVt in Shared;eapply astar_mono in Shared;
 [ |apply V293_ready_storage_switch_open|intros st H;exact H].
 unfold V293_ready_storage_core,V293_ready_core,V293_shared_ready_records,V293_shared_core in *;
 sep normal in Shared;sep destruct Shared;sep auto. }
 assert(Empty:Of=emp)by(eapply V293_shared_no_abstract_frame;[exact Fields|exact JO]).
 subst Of;apply map_join_emp' in JO;subst Oc.
 assert(Open:(QPge br,V293_cpu_lenv 120%Z bs,Mc,(fun _=>false),(false,nil,false::cs),
 RIabstract OwnershipWaiting,spec_done None)|=V293_dispatch_cell 106%Z V293_tcb_type **Atrue).
 { apply V293_ready_storage_switch_resources in Shared;unfold V293_ready_storage_extra in Shared;clear Fields Frame;sep auto. }
 destruct(V293_dispatch_read_frame 106%Z V293_tcb_type 93%positive OwnershipReady Atrue
 (QPge br)(V293_cpu_lenv 120%Z bs)Mc Mf M(fun _=>false)(false,nil,false::cs)
 (RIabstract OwnershipWaiting)(spec_done None)ltac:(st_env)JM Target Open)as[Named SharedRead].
 assert(Member:indom OwnershipTasks OwnershipWaiting).
 { exists(Int.repr 6,wait(os_stat_sem(72%positive,Int.repr 5))Int.one,Vptr(120%positive,Int.repr 7));reflexivity. }
 pose proof(V293_storage_switch_pre 80%positive 81%positive 82%positive
 106%Z V293_tcb_type(STcells br)OwnershipWaiting OwnershipReady 93%positive OwnershipTasks
 (QPge br)(V293_cpu_lenv 120%Z bs)Mc(fun _=>false)(false,nil,false::cs)
 (RIabstract OwnershipWaiting)(spec_done None)ltac:(st_env)SharedRead
 (RIfixed_tasks OwnershipWaiting)Member RIhighest Shared)as Both.
 assert(Whole:(QPge br,V293_cpu_lenv 120%Z bs,M,(fun _=>false),(false,nil,false::cs),
 RIabstract OwnershipWaiting,spec_done None)|=
 (SWINVt(OPinv br)OwnershipWaiting //\\ SWPRE_NDEAD V293_scheduler 106%Z OwnershipWaiting) **
 (Amapsto(98%positive,0%Z)Tint32 true(Vint32 Int.zero) **STframe bs)).
 { apply sat_split';exists Mc;exists Mf;exists(RIabstract OwnershipWaiting);exists(emp:osabst);
 split;[exact JM| ];split;[apply map_join_emp| ];split;[exact Both|exact Frame]. }
 unfold OPpre,STframe in *;clear Shared Both Frame Open Fields Named;sep auto.
Qed.

(* Only the already frozen, complete allocation/call prefix is used. *)
Theorem OPactual_entry : forall br bs cs ncs ip,
 fresh(NPinitial 1)br ->fresh(QPmemory br 1 1)bs ->
 exists M,
 V293_global_steps(RCprogram,(CPpo,CGempty,ip))HPcst
 (FWtasks,FWos br cs ncs,OwnershipWaiting)
 (set FWtasks OwnershipWaiting(curs(sprim(switch 106%Z)),(kenil,FTpending)),
 (QPge br,FTenvs bs,M,(fun _=>false),FTaux cs ncs),OwnershipWaiting) /\
 (QPge br,V293_cpu_lenv 120%Z bs,M,(fun _=>false),(false,nil,false::cs),
 RIabstract OwnershipWaiting,spec_done None)|=OPpre br bs /\
 load Tint32 M(bs,0%Z)=Some(Vint32 Int.zero) /\
 load Tint8 M(94%positive,0%Z)=Some(V293_byteval 4) /\
 ~(QPge br,V293_cpu_lenv 120%Z bs,M,(fun _=>false),(false,nil,false::cs),
 RIabstract OwnershipWaiting,spec_done None)|=V293_current_guard 94%positive OwnershipWaiting OwnershipTasks.
Proof.
 intros br bs cs ncs ip FR FS.
 destruct(FTto_switch br bs cs ncs ip FR FS)as(M&Trace&Held).
 pose proof(OPpartition br bs cs M Held)as Packet.
 assert(Saved:load Tint32 M(bs,0%Z)=Some(Vint32 Int.zero)).
 { apply(FTsaved_load bs (QPge br)(V293_cpu_lenv 120%Z bs)M(fun _=>false)
 (false,nil,false::cs)(RIabstract OwnershipWaiting)(spec_done None));
 unfold OPpre in Packet;clear Held;sep auto. }
 assert(Cache:load Tint8 M(94%positive,0%Z)=Some(V293_byteval 4)).
 { eapply V293_record_star_load_l with
 (s:=(QPge br,V293_cpu_lenv 120%Z bs,M,(fun _=>false),(false,nil,false::cs),RIabstract OwnershipWaiting,spec_done None))
 (P:=V293_owned_record_cell((94%positive,0%Z),Tint8,V293_byteval 4))(Q:=Atrue).
 - intros st H;apply V293_owned_record_cell_load;exact H.
 - unfold FTafter_copy in Held;clear Packet;sep auto. }
 exists M;split;[exact Trace| ];split;[exact Packet| ];split;[exact Saved| ];split;[exact Cache| ].
 apply SPcopied_cache_gap;exact Cache.
Qed.

Theorem OPnonvacuous : exists br bs,
 fresh(NPinitial 1)br /\fresh(QPmemory br 1 1)bs /\
 forall cs ncs ip,exists M,
 V293_global_steps(RCprogram,(CPpo,CGempty,ip))HPcst
 (FWtasks,FWos br cs ncs,OwnershipWaiting)
 (set FWtasks OwnershipWaiting(curs(sprim(switch 106%Z)),(kenil,FTpending)),
 (QPge br,FTenvs bs,M,(fun _=>false),FTaux cs ncs),OwnershipWaiting) /\
 (QPge br,V293_cpu_lenv 120%Z bs,M,(fun _=>false),(false,nil,false::cs),
 RIabstract OwnershipWaiting,spec_done None)|=OPpre br bs.
Proof.
 destruct(memory_has_fresh_block(NPinitial 1))as[br FR].
 destruct(memory_has_fresh_block(QPmemory br 1 1))as[bs FS].
 exists br;exists bs;split;[exact FR| ];split;[exact FS| ].
 intros cs ncs ip;destruct(OPactual_entry br bs cs ncs ip FR FS)as(M&Trace&Packet&Rest).
 exists M;split;assumption.
Qed.

(* Logical boundary controls, not modified execution traces. *)
Lemma OPnecessary : forall target tp bt tasks current ge le M ir aux O op,
 get ge target=Some(bt,Tptr tp) ->
 get O abstcblsid=Some(abstcblist tasks) ->
 (ge,le,M,ir,aux,O,op)|=SWPRE_NDEAD V293_scheduler target current ->
 exists next,load(Tptr tp)M(bt,0%Z)=Some(Vptr next) /\
 V293_highest_ready tasks next /\indom tasks current.
Proof.
 intros target tp bt tasks current ge le M ir aux O op Env TaskMap [Switch Alive].
 destruct Switch as[next Switch].
 assert(Prio:(ge,le,M,ir,aux,O,op)|=AHprio V293_scheduler next **Atrue)by(clear Alive;sep auto).
 assert(Cell:(ge,le,M,ir,aux,O,op)|=(EX tq:type,GV target @ (Tptr tq) |->(Vptr next)) **Atrue).
 { clear Prio Alive;sep auto. }
 apply sat_split in Prio;destruct Prio as(m1&m2&o1&o2&JM&JO&[Sched Empty]&Rest).
 destruct Sched as[tasks' [Map Highest]].
 assert(FullMap:get O abstcblsid=Some(abstcblist tasks')).
 { eapply OSAbstMod.join_get_l;[exact JO|exact Map]. }
 assert(tasks'=tasks)by congruence;subst tasks'.
 apply sat_split in Cell;destruct Cell as(m3&m4&o3&o4&JC&JA&[tq Cell]&RestC).
 destruct(V293_dispatch_named_cell_parts _ _ _ _ _ _ _ _ _ _ Cell)as(b&GE&Owned&EO).
 change(get ge target=Some(b,Tptr tq))in GE.
 assert(b=bt /\tq=tp)by(split;congruence);destruct H as[B T];subst b tq.
 assert(Read:load(Tptr tp)m3(bt,0%Z)=Some(Vptr next)).
 { eapply symbolic_lemmas.mapstoval_load;[destruct next;reflexivity|exact Owned]. }
 assert(FullRead:load(Tptr tp)M(bt,0%Z)=Some(Vptr next)).
 { eapply load_mem_mono;[exact Read|exists m4;exact JC]. }
 destruct Alive as[tls Alive].
 assert(Member:indom tls current).
 { assert(Pure:(ge,le,M,ir,aux,O,op)|=[|indom tls current|] **
 (Aabsdata abstcblsid(abstcblist tls) **Atrue))by(clear Switch Rest RestC;sep auto).
 apply astar_l_apure_elim in Pure;exact(proj1 Pure). }
 assert(AliveMap:get O abstcblsid=Some(abstcblist tls)).
 { eapply V293_star_abst_get_l with(s:=(ge,le,M,ir,aux,O,op))
 (p:=Aabsdata abstcblsid(abstcblist tls))(q:=Atrue).
 - intros st H;rewrite <-(proj1 H);apply map_get_sig.
 - clear Switch Rest RestC;sep auto. }
 assert(tls=tasks)by congruence;subst tls.
 exists next;split;[exact FullRead| ];split;assumption.
Qed.

Theorem OPreject_wrong_selection : forall target tp bt tasks current next ge le M ir aux O op,
 get ge target=Some(bt,Tptr tp) ->get O abstcblsid=Some(abstcblist tasks) ->
 load(Tptr tp)M(bt,0%Z)=Some(Vptr next) ->~V293_highest_ready tasks next ->
 ~(ge,le,M,ir,aux,O,op)|=SWPRE_NDEAD V293_scheduler target current.
Proof.
 intros target tp bt tasks current next ge le M ir aux O op Env Map Read NotHighest Held.
 destruct(OPnecessary target tp bt tasks current ge le M ir aux O op Env Map Held)
 as(chosen&Load&Highest&Member).
 assert(chosen=next)by congruence;subst chosen;contradiction.
Qed.

Theorem OPreject_dead_current : forall target tp bt tasks current ge le M ir aux O op,
 get ge target=Some(bt,Tptr tp) ->get O abstcblsid=Some(abstcblist tasks) ->
 ~indom tasks current ->
 ~(ge,le,M,ir,aux,O,op)|=SWPRE_NDEAD V293_scheduler target current.
Proof.
 intros target tp bt tasks current ge le M ir aux O op Env Map Dead Held.
 destruct(OPnecessary target tp bt tasks current ge le M ir aux O op Env Map Held)
 as(chosen&Load&Highest&Member);contradiction.
Qed.

Theorem OPreject_waiting_target : forall br bs cs M,
 load(Tptr V293_tcb_type)M(93%positive,0%Z)=Some(Vptr OwnershipWaiting) ->
 ~(QPge br,V293_cpu_lenv 120%Z bs,M,(fun _=>false),(false,nil,false::cs),
 RIabstract OwnershipWaiting,spec_done None)|=SWPRE_NDEAD V293_scheduler 106%Z OwnershipWaiting.
Proof.
 intros br bs cs M Stale.
 eapply OPreject_wrong_selection with(bt:=93%positive)(tp:=V293_tcb_type)
 (tasks:=OwnershipTasks)(next:=OwnershipWaiting).
 - st_env.
 - apply RIfixed_tasks.
 - exact Stale.
 - exact V293ReadyCurrentInvariantProbe.SCwaiting_not_highest.
Qed.
