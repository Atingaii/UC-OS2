(* Same frozen entry and caller, with task-owned pending saved storage. *)
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
Definition PTpacket br bs M ci ip A : Prop :=
 exists Mt Mf Ot Of,
 join Mt Mf M /\join Ot Of(set(RIabstract OwnershipWaiting)curtid(oscurt OwnershipReady)) /\
 (QPge br,V293_cpu_lenv 120%Z 98%positive,Mt,(fun _=>false),(false,nil,false::ci),Ot,spec_done None)|=
 Amapsto(98%positive,0%Z)Tint32 true(Vint32 Int.zero) **
 (V293_ready_current_core 80%positive 81%positive 82%positive
 106%Z V293_tcb_type(STcells br)94%positive **CurTid OwnershipReady) /\
 (QPge br,V293_cpu_lenv 120%Z 98%positive,Mf,(fun _=>false),(false,nil,false::ci),Of,spec_done None)|=STframe bs /\
 TaskSim(RCprogram,(CPpo,CGempty,ip))RPpending
 (QPge br,V293_cpu_lenv 120%Z 98%positive,Mt,(fun _=>false),(false,nil,false::ci))
 (RCprogram,A)(SKIP,(kenil,kstop))Ot V293_shared_li(IPinv br)
 (fun st=>satp(fst st)(snd st)(RDYINV(IPinv br)OwnershipReady **LINV V293_shared_li OwnershipReady nil))OwnershipReady.

Lemma PTclose : forall br bs M ci ip A,
 (QPge br,V293_cpu_lenv 120%Z 98%positive,M,(fun _=>false),(false,nil,false::ci),
 set(RIabstract OwnershipWaiting)curtid(oscurt OwnershipReady),spec_done None)|=
 Amapsto(98%positive,0%Z)Tint32 true(Vint32 Int.zero) **
 (V293_ready_current_core 80%positive 81%positive 82%positive
 106%Z V293_tcb_type(STcells br)94%positive **(CurTid OwnershipReady **STframe bs)) ->
 PTpacket br bs M ci ip A.
Proof.
 intros br bs M ci ip A Held.
 assert(Packed:(QPge br,V293_cpu_lenv 120%Z 98%positive,M,(fun _=>false),(false,nil,false::ci),
 set(RIabstract OwnershipWaiting)curtid(oscurt OwnershipReady),spec_done None)|=
 (Amapsto(98%positive,0%Z)Tint32 true(Vint32 Int.zero) **
 (V293_ready_current_core 80%positive 81%positive 82%positive
 106%Z V293_tcb_type(STcells br)94%positive **CurTid OwnershipReady)) **STframe bs)by(sep auto).
 apply sat_split in Packed;destruct Packed as(Mt&Mf&Ot&Of&JM&JO&Owned&Frame).
 unfold PTpacket;exists Mt;exists Mf;exists Ot;exists Of;
 split;[exact JM| ];split;[exact JO| ];split;[exact Owned| ];split;[exact Frame| ].
 unfold RPpending,IPinv.
 eapply V293_pending_return_TaskSim;
 [exact RPbinding|right;right;reflexivity|reflexivity|exact Owned].
Qed.

Lemma PTselected : forall br bs cs ci ip A Mc,
 (QPge br,V293_cpu_lenv 120%Z bs,Mc,(fun _=>false),(false,nil,false::cs),
 RIabstract OwnershipWaiting,spec_done None)|=FTafter_copy br bs OwnershipWaiting ->
 exists Ms,
 lpstep(RCprogram,(CPpo,CGempty,ip))STswitch_tasks HPcst
 (QPge br,FTenvs bs,Mc,(fun _=>false),FTaux cs ci)OwnershipWaiting
 (set STswitch_tasks OwnershipWaiting(SKIP,(kenil,FTpending)))HPcst
 (QPge br,FTenvs bs,Ms,(fun _=>false),FTaux cs ci)OwnershipReady /\
 store(Tptr V293_tcb_type)Mc(1%positive,0%Z)(Vptr OwnershipReady)=Some Ms /\
 PTpacket br bs Ms ci ip A.
Proof.
 intros br bs cs ci ip A Mc Held.
 pose proof(STrepack br bs cs OwnershipWaiting Mc Held)as Packed.
 assert(Target:load(Tptr V293_tcb_type)Mc(93%positive,0%Z)=Some(Vptr OwnershipReady)).
 { eapply V293_record_star_load_l with
 (s:=(QPge br,V293_cpu_lenv 120%Z bs,Mc,(fun _=>false),(false,nil,false::cs),RIabstract OwnershipWaiting,spec_done None))
 (P:=V293_owned_record_cell((93%positive,0%Z),Tptr V293_tcb_type,Vptr OwnershipReady))(Q:=Atrue).
 - intros st H;apply V293_owned_record_cell_load;exact H.
 - clear Packed;unfold FTafter_copy in Held;sep auto. }
 assert(Highest:V293_scheduler(RIabstract OwnershipWaiting)OwnershipReady).
 { exists OwnershipTasks;split;[apply RIfixed_tasks|exact FXhighest]. }
 destruct(V293_ready_storage_switch_step 80%positive 81%positive 82%positive
 106%Z V293_tcb_type(STcells br)RCprogram CPpo CGempty ip STswitch_tasks HPcst FTpending
 OwnershipWaiting OwnershipReady 93%positive 1%positive(QPge br)(V293_cpu_lenv 120%Z bs)
 (FTenvs bs)Mc(fun _=>false)(false,nil,false::cs)(FTaux cs ci)
 (RIabstract OwnershipWaiting)(spec_done None)
 (Amapsto(98%positive,0%Z)Tint32 true(Vint32 Int.zero) **STframe bs)
 ltac:(unfold FTenvs;apply map_get_set)ltac:(unfold FTaux;apply map_get_set)
 (map_get_set _ _ _)ltac:(st_env)Target ltac:(st_env)Packed)
 as(Ms&Switch&Store&Shared&Pointer&Outside).
 assert(Self:sched_self V293_scheduler(set(RIabstract OwnershipWaiting)curtid(oscurt OwnershipReady))).
 { exists OwnershipReady;split;[apply map_get_set| ].
   destruct Highest as[ts[Map High]];exists ts;split;
   [rewrite map_get_set' by discriminate;exact Map|exact High]. }
 apply V293_current_handoff_switch_highest_frame with(bc:=94%positive)in Shared;[ |exact Self].
 eapply astar_mono in Shared;[ |apply V293_current_shared_open|intros st H;exact H].
 exists Ms;split;[exact Switch| ];split;[exact Store| ];apply PTclose.
 eapply good_inv_prop with(le:=V293_cpu_lenv 120%Z bs)(ie:=false)(cs:=false::cs)(op:=spec_done None).
 - split;[exact I| ];split;[apply V293_current_core_good| ];split;
   [unfold CurTid,Agvarmapsto,Aptrmapsto;cbn[GoodInvAsrt];intros;repeat split;exact I|
    split;[exact I|apply RCframe_good]].
 - clear Held Packed;sep auto.
Qed.

Theorem PTfull_call : forall br bs cs ci ip A,
 fresh(NPinitial 1)br ->fresh(QPmemory br 1 1)bs ->
 exists Mc Ms Mf,
 V293_global_steps(RCprogram,(CPpo,CGempty,ip))HPcst
 (FWtasks,FWos br cs ci,OwnershipWaiting)
 (set STswitch_tasks OwnershipWaiting(SKIP,(kenil,FTpending)),
 (QPge br,FTenvs bs,Ms,(fun _=>false),FTaux cs ci),OwnershipReady) /\
 PTpacket br bs Ms ci ip A /\
 V293_global_steps(RCprogram,(CPpo,CGempty,ip))HPcst
 (FWtasks,FWos br cs ci,OwnershipWaiting)
 (FTreturned,FTreturnstate br bs Mf cs ci,OwnershipReady) /\
 store(Tptr V293_tcb_type)Mc(1%positive,0%Z)(Vptr OwnershipReady)=Some Ms /\
 free Tint32 98%positive Ms=Some Mf /\
 load Tint32 Mf(bs,0%Z)=Some(Vint32 Int.zero) /\
 load Tint8 Mf(90%positive,0%Z)=Some(V293_byteval 99) /\
 (forall i,(0<=i<4)%Z ->get Mf(98%positive,i)=None).
Proof.
 intros br bs cs ci ip A FR FS.
 destruct(FTto_switch br bs cs ci ip FR FS)as(Mc&Prefix&Held).
 destruct(PTselected br bs cs ci ip A Mc Held)as(Ms&Switch&Store&Packet).
 destruct(STselected_return br bs cs false ci ip Mc(FTaux cs ci)
 ltac:(unfold FTaux;apply map_get_set)
 ltac:(unfold FTaux,RPaux;repeat rewrite map_get_set' by discriminate;apply map_get_sig)Held)
 as(Ms'&Mf&Return&Store'&Free&Post&Removed&Pointer).
 assert(Ms'=Ms)by congruence;subst Ms'.
 destruct(STsaved_retained br bs _ _ _ _ _ _ _ Post)as[Old Canary].
 exists Mc;exists Ms;exists Mf;split.
 - eapply V293_global_trans;[exact Prefix| ].
   unfold V293_global_steps;eapply rt1n_trans with
   (y:=(set STswitch_tasks OwnershipWaiting(SKIP,(kenil,FTpending)),
    (QPge br,FTenvs bs,Ms,(fun _=>false),FTaux cs ci),OwnershipReady));
   [exact Switch|constructor].
 - split;[exact Packet| ];split;[eapply V293_global_trans;[exact Prefix|exact Return]| ];
   split;[exact Store| ];split;[exact Free| ];split;[exact Old| ];split;assumption.
Qed.

Theorem PTnonvacuous : forall cs ci ip A,
 exists br bs Mc Ms Mf,
 fresh(NPinitial 1)br /\fresh(QPmemory br 1 1)bs /\PTpacket br bs Ms ci ip A /\
 V293_global_steps(RCprogram,(CPpo,CGempty,ip))HPcst
 (FWtasks,FWos br cs ci,OwnershipWaiting)
 (set STswitch_tasks OwnershipWaiting(SKIP,(kenil,FTpending)),
 (QPge br,FTenvs bs,Ms,(fun _=>false),FTaux cs ci),OwnershipReady) /\
 store(Tptr V293_tcb_type)Mc(1%positive,0%Z)(Vptr OwnershipReady)=Some Ms /\
 free Tint32 98%positive Ms=Some Mf.
Proof.
 intros cs ci ip A.
 destruct(memory_has_fresh_block(NPinitial 1))as[br FR].
 destruct(memory_has_fresh_block(QPmemory br 1 1))as[bs FS].
 destruct(PTfull_call br bs cs ci ip A FR FS)
 as(Mc&Ms&Mf&Prefix&Packet&Return&Store&Free&Rest).
 exists br;exists bs;exists Mc;exists Ms;exists Mf;
 split;[exact FR| ];split;[exact FS| ];split;[exact Packet| ];
 split;[exact Prefix| ];split;assumption.
Qed.

(* Moving every byte to the external frame leaves the same whole heap,
   but the empty task-owned heap cannot free the saved cell. *)
Theorem PTowned_free_boundary : forall br bs M ci ip A,
 PTpacket br bs M ci ip A ->
 exists Mt Mf Ot Of Mret Mfullret,
 join Mt Mf M /\join Ot Of(set(RIabstract OwnershipWaiting)curtid(oscurt OwnershipReady)) /\
 free Tint32 98%positive Mt=Some Mret /\free Tint32 98%positive M=Some Mfullret /\
 join(emp:mem)M M /\free Tint32 98%positive(emp:mem)=None /\
 forall R:asrt,~(QPge br,V293_cpu_lenv 120%Z 98%positive,emp,(fun _=>false),
 (false,nil,false::ci),(emp:osabst),spec_done None)|=
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

(* Change only the saved stack top; this checks excrit semantics, not
   the unproved IE=true TaskSim resource handover. *)
Theorem PTsaved_stack_boundary : forall p ge le M ir ci ks,
 loststep p(curs(sprim excrit),(kenil,ks))(ge,le,M,ir,(false,nil,false::ci))
 (SKIP,(kenil,ks))(ge,le,M,ir,(false,nil,ci)) /\
 loststep p(curs(sprim excrit),(kenil,ks))(ge,le,M,ir,(false,nil,true::ci))
 (SKIP,(kenil,ks))(ge,le,M,ir,(true,nil,ci)) /\
 ~exists C' st',loststep p(curs(sprim excrit),(kenil,ks))(ge,le,M,ir,(false,nil,nil))C' st'.
Proof.
 intros;split;[apply excrit_step;reflexivity| ];
 split;[apply excrit_step;reflexivity| ].
 intros(C'&st'&Bad);inversion Bad;subst;try discriminate.
 eapply V293_cstep_not_primitive;[eassumption|reflexivity].
Qed.
