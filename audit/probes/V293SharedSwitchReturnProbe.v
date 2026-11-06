(* Reuse the frozen full-call fixture; no new program or initial heap. *)
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

Definition STcells br := V293_exit_shared_cells 91%positive 96%positive 97%positive
 94%positive br 95%positive nil.
Definition STframe bs := Amapsto(bs,0%Z)Tint32 true(Vint32 Int.zero) **RCframe.
Definition STpost br bs := V293_ready_current_core 80%positive 81%positive 82%positive
 106%Z V293_tcb_type(STcells br)94%positive **(CurTid OwnershipReady **STframe bs).
Local Ltac st_env := cbn[getgenv];unfold QPge;rewrite map_get_set' by discriminate;reflexivity.

Lemma STrepack : forall br bs cs ct M,
 (QPge br,V293_cpu_lenv 120%Z bs,M,(fun _=>false),(false,nil,false::cs),
 RIabstract OwnershipWaiting,spec_done None)|=FTafter_copy br bs ct ->
 (QPge br,V293_cpu_lenv 120%Z bs,M,(fun _=>false),(false,nil,false::cs),
 RIabstract OwnershipWaiting,spec_done None)|=
 SWINVt(V293_ready_storage_inv 80%positive 81%positive 82%positive
 106%Z V293_tcb_type(STcells br))ct **
 (Amapsto(98%positive,0%Z)Tint32 true(Vint32 Int.zero) **STframe bs).
Proof.
 intros br bs cs ct M Held.
 assert(Cells:V293_owned_record_cell((91%positive,0%Z),Tint8,V293_byteval 4) **
 (V293_owned_record_cell((96%positive,0%Z),Tint8,V293_byteval 0) **
 (V293_owned_record_cell((97%positive,0%Z),Tint8,V293_byteval 0) **
 (V293_owned_record_cell((94%positive,0%Z),Tint8,V293_byteval 4) **
 (V293_owned_record_cell((br,0%Z),Tint8,V293_byteval 1) **
 (V293_owned_record_cell((95%positive,0%Z),Tint32,Vint32 Int.zero) **Aemp))))) ==>
 V293_storage(STcells br)).
 { unfold STcells,V293_exit_shared_cells;cbn[V293_storage].
   repeat apply astar_mono;try(intros st H;exact H);apply V293_exit_cell_to_storage. }
 assert(Global:forall m o,
 (QPge br,V293_cpu_lenv 120%Z bs,m,(fun _=>false),(false,nil,false::cs),o,spec_done None)|=
 V293_owned_record_cell((93%positive,0%Z),Tptr V293_tcb_type,Vptr OwnershipReady) ->
 (QPge br,V293_cpu_lenv 120%Z bs,m,(fun _=>false),(false,nil,false::cs),o,spec_done None)|=
 V293_dispatch_cell 106%Z V293_tcb_type).
 { intros m o H;unfold V293_dispatch_cell.
   apply astar_l_apure_elim in H;destruct H as[_ H].
   exists(Vptr OwnershipReady);apply astar_l_apure_intro;[ |reflexivity].
   exists 93%positive;unfold Agvarenv',Aptrmapsto;cbn[addrval_to_addr].
   apply astar_l_agvarenv_intro;[exact H|split;[reflexivity|change(get(QPge br)106%Z=Some(93%positive,Tptr V293_tcb_type));st_env]]. }
 assert(Parts:(QPge br,V293_cpu_lenv 120%Z bs,M,(fun _=>false),(false,nil,false::cs),
 RIabstract OwnershipWaiting,spec_done None)|=
 (V293_owned_record_cell((91%positive,0%Z),Tint8,V293_byteval 4) **
 (V293_owned_record_cell((96%positive,0%Z),Tint8,V293_byteval 0) **
 (V293_owned_record_cell((97%positive,0%Z),Tint8,V293_byteval 0) **
 (V293_owned_record_cell((94%positive,0%Z),Tint8,V293_byteval 4) **
 (V293_owned_record_cell((br,0%Z),Tint8,V293_byteval 1) **
 (V293_owned_record_cell((95%positive,0%Z),Tint32,Vint32 Int.zero) **Aemp)))))) **
 (V293_owned_record_cell((93%positive,0%Z),Tptr V293_tcb_type,Vptr OwnershipReady) **
 (SWINVt(V293_ready_inv 80%positive 81%positive 82%positive)ct **
 (Amapsto(98%positive,0%Z)Tint32 true(Vint32 Int.zero) **STframe bs)))).
 { unfold FTafter_copy,FTrest,STframe in *;sep auto. }
 eapply astar_mono in Parts;[ |exact Cells|intros st H;exact H].
 apply sat_split in Parts;destruct Parts as(ma&mb&oa&ob&JMa&JOa&Store&Parts).
 apply sat_split in Parts;destruct Parts as(mt&mr&ot&orr&JMb&JOb&Cell&Rest).
 apply Global in Cell.
 assert(Packed:(QPge br,V293_cpu_lenv 120%Z bs,M,(fun _=>false),(false,nil,false::cs),
 RIabstract OwnershipWaiting,spec_done None)|=
 V293_storage(STcells br) **(V293_dispatch_cell 106%Z V293_tcb_type **
 (SWINVt(V293_ready_inv 80%positive 81%positive 82%positive)ct **
 (Amapsto(98%positive,0%Z)Tint32 true(Vint32 Int.zero) **STframe bs)))).
 { apply sat_split';exists ma;exists mb;exists oa;exists ob.
   split;[exact JMa| ];split;[exact JOa| ];split;[exact Store| ].
   apply sat_split';exists mt;exists mr;exists ot;exists orr.
   split;[exact JMb| ];split;[exact JOb| ];split;assumption. }
 eapply astar_mono;[intros st H;apply V293_ready_storage_switch_resources;exact H|intros st H;exact H| ].
 unfold V293_ready_storage_extra;clear Held;sep auto.
Qed.

Definition STswitch_tasks := set FWtasks OwnershipWaiting(curs(sprim(switch 106%Z)),(kenil,FTpending)).
Definition STreturned_os br bs M aus enabled vci : osstate :=
 (QPge br,set(FTenvs bs)OwnershipReady(emp:env),M,(fun _=>false),
 set aus OwnershipReady(enabled,nil,vci)).

Lemma STselected_return : forall br bs cs enabled vci ip Mc aus,
 get aus OwnershipWaiting=Some(false,nil,false::cs) ->
 get aus OwnershipReady=Some(false,nil,enabled::vci) ->
 (QPge br,V293_cpu_lenv 120%Z bs,Mc,(fun _=>false),(false,nil,false::cs),
 RIabstract OwnershipWaiting,spec_done None)|=FTafter_copy br bs OwnershipWaiting ->
 exists Ms Mf,
 V293_global_steps(RCprogram,(CPpo,CGempty,ip))HPcst
 (STswitch_tasks,(QPge br,FTenvs bs,Mc,(fun _=>false),aus),OwnershipWaiting)
 (FTreturned,STreturned_os br bs Mf aus enabled vci,OwnershipReady) /\
 store(Tptr V293_tcb_type)Mc(1%positive,0%Z)(Vptr OwnershipReady)=Some Ms /\
 free Tint32 98%positive Ms=Some Mf /\
 (QPge br,emp,Mf,(fun _=>false),(enabled,nil,vci),
 set(RIabstract OwnershipWaiting)curtid(oscurt OwnershipReady),spec_done None)|=STpost br bs /\
 (forall i,(0<=i<4)%Z ->get Mf(98%positive,i)=None) /\
 load(Tptr V293_tcb_type)Mf(1%positive,0%Z)=Some(Vptr OwnershipReady).
Proof.
 intros br bs cs enabled vci ip Mc aus RunnerAux VictimAux Held.
 pose proof(STrepack br bs cs OwnershipWaiting Mc Held)as Packed.
 assert(Target:load(Tptr V293_tcb_type)Mc(93%positive,0%Z)=Some(Vptr OwnershipReady)).
 { eapply V293_record_star_load_l with
 (s:=(QPge br,V293_cpu_lenv 120%Z bs,Mc,(fun _=>false),(false,nil,false::cs),RIabstract OwnershipWaiting,spec_done None))
 (P:=V293_owned_record_cell((93%positive,0%Z),Tptr V293_tcb_type,Vptr OwnershipReady))(Q:=Atrue).
 - intros st H;apply V293_owned_record_cell_load;exact H.
 - clear Packed;unfold FTafter_copy in Held;sep auto. }
 assert(NextCode:get(set FWtasks OwnershipWaiting(curs(sprim(switch 106%Z)),(kenil,FTpending)))OwnershipReady=Some RPpending).
 { unfold FWtasks,RPtasks;repeat rewrite map_get_set' by discriminate;apply map_get_sig. }
 assert(NextEnv:get(FTenvs bs)OwnershipReady=Some(V293_cpu_lenv 120%Z 98%positive)).
 { unfold FTenvs,RPenvs;repeat rewrite map_get_set' by discriminate;apply map_get_sig. }
 assert(Highest:V293_scheduler(RIabstract OwnershipWaiting)OwnershipReady).
 { exists OwnershipTasks;split;[apply RIfixed_tasks|exact FXhighest]. }
 destruct(V293_int_exit_shared_switch_return 80%positive 81%positive 82%positive
 106%Z V293_tcb_type(STcells br)94%positive RCprogram CPpo CGempty ip
 (set FWtasks OwnershipWaiting(curs(sprim(switch 106%Z)),(kenil,FTpending)))
 (FTenvs bs)aus OwnershipWaiting OwnershipReady HPcst(QPge br)(V293_cpu_lenv 120%Z bs)
 Mc(fun _=>false)nil(false::cs)(RIabstract OwnershipWaiting)(spec_done None)(STframe bs)
 93%positive 1%positive FTpending enabled vci
 114%Z CPfullbody emp kstop Tvoid dnil(dcons 120%Z Tint32 dnil)120%Z 98%positive(Vint32 Int.zero)
 ltac:(vm_compute;discriminate)RPbinding ltac:(split;[exact I|apply RCframe_good])
 (map_get_set _ _ _)ltac:(unfold FTenvs;apply map_get_set)RunnerAux
 NextCode NextEnv VictimAux ltac:(st_env)Target ltac:(st_env)Highest Packed)
 as(Ms&Mf&Switch&Return&Store&Free&Post&Pointer&Removed&Frame).
 repeat rewrite <-set_set_eq in Return.
 exists Ms;exists Mf;split;[exact Return| ];
 split;[exact Store| ];split;[exact Free| ];split;[exact Post| ];split;assumption.
Qed.

Theorem STfull_call_shared_return : forall br bs cs ncs ip,
 fresh(NPinitial 1)br ->fresh(QPmemory br 1 1)bs ->
 exists Mc Ms Mf,
 V293_global_steps(RCprogram,(CPpo,CGempty,ip))HPcst
 (FWtasks,FWos br cs ncs,OwnershipWaiting)
 (set FWtasks OwnershipWaiting(curs(sprim(switch 106%Z)),(kenil,FTpending)),
 (QPge br,FTenvs bs,Mc,(fun _=>false),FTaux cs ncs),OwnershipWaiting) /\
 V293_global_steps(RCprogram,(CPpo,CGempty,ip))HPcst
 (FWtasks,FWos br cs ncs,OwnershipWaiting)
 (FTreturned,FTreturnstate br bs Mf cs ncs,OwnershipReady) /\
 store(Tptr V293_tcb_type)Mc(1%positive,0%Z)(Vptr OwnershipReady)=Some Ms /\
 free Tint32 98%positive Ms=Some Mf /\
 (QPge br,emp,Mf,(fun _=>false),(false,nil,ncs),
 set(RIabstract OwnershipWaiting)curtid(oscurt OwnershipReady),spec_done None)|=STpost br bs /\
 (forall i,(0<=i<4)%Z ->get Mf(98%positive,i)=None) /\
 load(Tptr V293_tcb_type)Mf(1%positive,0%Z)=Some(Vptr OwnershipReady).
Proof.
 intros br bs cs ncs ip FR FS.
 destruct(FTto_switch br bs cs ncs ip FR FS)as(Mc&Prefix&Held).
 destruct(STselected_return br bs cs false ncs ip Mc(FTaux cs ncs)
 ltac:(unfold FTaux;apply map_get_set)
 ltac:(unfold FTaux,RPaux;repeat rewrite map_get_set' by discriminate;apply map_get_sig)Held)
 as(Ms&Mf&Return&Store&Free&Post&Removed&Pointer).
 exists Mc;exists Ms;exists Mf;split;[exact Prefix| ];split.
 - eapply V293_global_trans;[exact Prefix|exact Return].
 - split;[exact Store| ];split;[exact Free| ];split;[exact Post| ];split;assumption.
Qed.

(* The switch heap and both task programs are fixed. Only the selected
   task's saved critical-stack top is removed in STaux_without_top. *)
Definition STaux_without_top cs vci :=
 set(FTaux cs(true::vci))OwnershipReady(false,nil,true::vci).

Theorem STsaved_top_actual_ablation : forall br bs cs vci ip,
 fresh(NPinitial 1)br ->fresh(QPmemory br 1 1)bs ->
 exists Mc Ms Mf,
 V293_global_steps(RCprogram,(CPpo,CGempty,ip))HPcst
 (FWtasks,FWos br cs(true::vci),OwnershipWaiting)
 (STswitch_tasks,(QPge br,FTenvs bs,Mc,(fun _=>false),FTaux cs(true::vci)),OwnershipWaiting) /\
 V293_global_steps(RCprogram,(CPpo,CGempty,ip))HPcst
 (STswitch_tasks,(QPge br,FTenvs bs,Mc,(fun _=>false),FTaux cs(true::vci)),OwnershipWaiting)
 (FTreturned,STreturned_os br bs Mf(FTaux cs(true::vci))false(true::vci),OwnershipReady) /\
 V293_global_steps(RCprogram,(CPpo,CGempty,ip))HPcst
 (STswitch_tasks,(QPge br,FTenvs bs,Mc,(fun _=>false),STaux_without_top cs vci),OwnershipWaiting)
 (FTreturned,STreturned_os br bs Mf(STaux_without_top cs vci)true vci,OwnershipReady) /\
 store(Tptr V293_tcb_type)Mc(1%positive,0%Z)(Vptr OwnershipReady)=Some Ms /\
 free Tint32 98%positive Ms=Some Mf /\
 (QPge br,emp,Mf,(fun _=>false),(false,nil,true::vci),
 set(RIabstract OwnershipWaiting)curtid(oscurt OwnershipReady),spec_done None)|=STpost br bs /\
 (QPge br,emp,Mf,(fun _=>false),(true,nil,vci),
 set(RIabstract OwnershipWaiting)curtid(oscurt OwnershipReady),spec_done None)|=STpost br bs /\
 get(set(FTaux cs(true::vci))OwnershipReady(false,nil,true::vci))OwnershipReady=Some(false,nil,true::vci) /\
 get(set(STaux_without_top cs vci)OwnershipReady(true,nil,vci))OwnershipReady=Some(true,nil,vci) /\
 (forall t,t<>OwnershipReady ->get(STaux_without_top cs vci)t=get(FTaux cs(true::vci))t).
Proof.
 intros br bs cs vci ip FR FS.
 destruct(FTto_switch br bs cs(true::vci)ip FR FS)as(Mc&Prefix&Held).
 destruct(STselected_return br bs cs false(true::vci)ip Mc(FTaux cs(true::vci))
 ltac:(unfold FTaux;apply map_get_set)
 ltac:(unfold FTaux,RPaux;repeat rewrite map_get_set' by discriminate;apply map_get_sig)Held)
 as(Ms&Mf&Positive&Store&Free&Post&Removed&Pointer).
 destruct(STselected_return br bs cs true vci ip Mc(STaux_without_top cs vci)
 ltac:(unfold STaux_without_top;rewrite map_get_set' by discriminate;unfold FTaux;apply map_get_set)
 ltac:(unfold STaux_without_top;apply map_get_set)Held)
 as(Ms2&Mf2&Negative&Store2&Free2&Post2&Removed2&Pointer2).
 assert(Ms2=Ms)by congruence;subst Ms2.
 assert(Mf2=Mf)by congruence;subst Mf2.
 exists Mc;exists Ms;exists Mf;split;[exact Prefix| ];split;[exact Positive| ];
 split;[exact Negative| ];split;[exact Store| ];split;[exact Free| ];
 split;[exact Post| ];split;[exact Post2| ];split;[apply map_get_set| ];
 split;[apply map_get_set| ].
 intros t Apart;unfold STaux_without_top;rewrite map_get_set' by congruence;reflexivity.
Qed.

Theorem STblocked_old_not_selected :
 ~V293_scheduler(RIabstract OwnershipReady)OwnershipWaiting.
Proof.
 intros[ts[Map Highest]].
 pose proof(RIfixed_tasks OwnershipReady)as Fixed.
 rewrite Map in Fixed;inversion Fixed;subst ts;exact(SXnot_highest Highest).
Qed.

Lemma STsaved_retained : forall br bs ge le M ir aux O op,
 (ge,le,M,ir,aux,O,op)|=STpost br bs ->
 load Tint32 M(bs,0%Z)=Some(Vint32 Int.zero) /\
 load Tint8 M(90%positive,0%Z)=Some(V293_byteval 99).
Proof.
 intros br bs ge le M ir aux O op Held.
 assert(Saved:(ge,le,M,ir,aux,O,op)|=
 Amapsto(bs,0%Z)Tint32 true(Vint32 Int.zero) **Atrue).
 { unfold STpost,STframe in Held;sep auto. }
 split.
 - eapply FTsaved_load;exact Saved.
 - eapply V293_record_star_load_l with(s:=(ge,le,M,ir,aux,O,op))
 (P:=V293_owned_record_cell((90%positive,0%Z),Tint8,V293_byteval 99))(Q:=Atrue).
   + intros st H;apply V293_owned_record_cell_load;exact H.
   + clear Saved;unfold STpost,STframe,RCframe in Held;sep auto.
Qed.

Theorem STnonvacuous : forall cs ncs ip,
 exists br bs Mf,
 fresh(NPinitial 1)br /\fresh(QPmemory br 1 1)bs /\
 V293_global_steps(RCprogram,(CPpo,CGempty,ip))HPcst
 (FWtasks,FWos br cs ncs,OwnershipWaiting)
 (FTreturned,FTreturnstate br bs Mf cs ncs,OwnershipReady) /\
 (QPge br,emp,Mf,(fun _=>false),(false,nil,ncs),
 set(RIabstract OwnershipWaiting)curtid(oscurt OwnershipReady),spec_done None)|=STpost br bs.
Proof.
 intros cs ncs ip.
 destruct(memory_has_fresh_block(NPinitial 1))as[br FR].
 destruct(memory_has_fresh_block(QPmemory br 1 1))as[bs FS].
 destruct(STfull_call_shared_return br bs cs ncs ip FR FS)
 as(Mc&Ms&Mf&Prefix&Run&Store&Free&Post&Rest).
 exists br;exists bs;exists Mf;split;[exact FR| ];split;[exact FS| ];split;assumption.
Qed.
