(* Same frozen boundary fixture; move writable cell 99 into shared storage.
   Both copy variants close the existing candidate, not a full kernel Inv. *)
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293SharedStateWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCurrent.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTarget.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTargetWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.audit.probes.V293TaskRecordOwnershipProbe.
Require Import CertiOS.certiucos.v293.code.V293ReadyTable.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.auxdef.
Require Import CertiOS.framework.proof.memory_prop.
Require Import CertiOS.framework.proof.lmachLib.
Require Import CertiOS.framework.proof.rulesoundlib.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import Coq.Lists.List Lia.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyTaskInvariant.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.audit.probes.V293TaskRecordInvariantProbe.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyTargetHandoff.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewExec.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchState.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.audit.probes.V293ReadyTaskInvariantProbe.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import CertiOS.certiucos.v293.code.V293OSSchedDispatch.
Require Import CertiOS.certiucos.v293.code.V293OSSchedNew.
Require Import CertiOS.audit.probes.V293ReadyTargetHandoffProbe.
Require Import CertiOS.certiucos.v293.proofs.V293ReadySchedCall.
Require Import CertiOS.audit.probes.V293ReadySchedCallProbe.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitDispatchExecution.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitExecution.
Require Import CertiOS.certiucos.v293.code.V293OSIntExit.
Require Import CertiOS.certiucos.v293.code.V293OSSchedChange.
Require Import CertiOS.certiucos.v293.code.V293OSSchedGuards.
Require Import CertiOS.framework.proof.cstepLib.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedChange.
Require Import CertiOS.audit.probes.V293OSIntExitDispatchExecutionProbe.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitDispatchCall.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitCallExecution.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyCriticalGlobal.
Require Import CertiOS.audit.probes.V293OSIntExitDispatchCallProbe.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitSwitchEntry.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickLifecycle.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyFullCall.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedPointerCompare.
Require Import CertiOS.audit.probes.V293OSIntExitSwitchEntryProbe.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitInterruptGlobal.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyGlobalTrace.
Require Import CertiOS.certiucos.v293.proofs.V293LocalGlobalTrace.
Require Import CertiOS.tactics.basetac.join_lib.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import CertiOS.audit.probes.V293OSIntExitInterruptGlobalProbe.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitBoundarySwitch.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyCacheContract.
Require Import CertiOS.audit.probes.V293OSIntExitBoundarySwitchProbe.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitSharedReclose.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyCurrentInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchStorage.
Import ListNotations.
Local Open Scope nat_scope.
Definition SRrest : list(addr*type) := [((99%positive,0%Z),Tint8)].
Definition SRprivate := RCframe ** V293_owned_record_cell((100%positive,0%Z),Tint8,V293_byteval 0).
Definition SRinv := V293_ready_current_inv 80%positive 81%positive 82%positive
 106%Z V293_tcb_type
 (V293_exit_shared_cells 91%positive 94%positive 95%positive 96%positive 98%positive 97%positive SRrest)96%positive.
Definition SRpost bs := SWINVt SRinv OwnershipReady **
 (Amapsto(bs,0%Z)Tint32 true(Vint32 Int.zero) **SRprivate).
Lemma SRprivate_good : GoodInvAsrt SRprivate.
Proof. unfold SRprivate;repeat split;try exact I;exact RCframe_good. Qed.
Lemma SRframe : SXframe ==> V293_storage SRrest **SRprivate.
Proof.
 intros st H.
 assert(Cell:st|=V293_owned_record_cell((99%positive,0%Z),Tint8,V293_byteval 23) **SRprivate).
 { unfold SXframe,SRprivate in *;sep auto. }
 eapply astar_mono in Cell;[ |apply V293_exit_cell_to_storage|intros s K;exact K].
 unfold SRrest;cbn[V293_storage];sep auto.
Qed.
Definition SRpre := SWINVt(V293_ready_inv 80%positive 81%positive 82%positive)SXct **
 (V293_owned_record_cell((91%positive,0%Z),Tint8,V293_byteval 88) **
 (V293_owned_record_cell((93%positive,0%Z),Tptr V293_tcb_type,Vptr OwnershipWaiting) **
 (V293_owned_record_cell((94%positive,0%Z),Tint8,V293_byteval 1) **
 (V293_owned_record_cell((95%positive,0%Z),Tint8,V293_byteval 0) **(V293_owned_record_cell((96%positive,0%Z),Tint8,V293_byteval 6) **
 (V293_owned_record_cell((98%positive,0%Z),Tint8,V293_byteval 1) **
 (V293_owned_record_cell((97%positive,0%Z),Tint32,Vint32(Int.repr 19)) **(V293_storage SRrest **SRprivate)))))))).
Lemma SRentry : forall ci,
 (BXge,SXcaller,SXmemory 1 6,(fun _=>false),(false,nil,ci),RIabstract SXct,spec_done None)|=SRpre.
Proof.
 intro ci;pose proof(BXindependent_entry ci)as Held.
 assert(Transport:SXpre ==>SRpre).
 { unfold SXpre,SXentry_frame,SRpre.
   repeat first[exact SRframe|intros st H;exact H|apply astar_mono]. }
 apply Transport;exact Held.
Qed.

Theorem SRcomplete_switch : forall sync enabled ci other otherle otheraux cst,
 exists bs Mf,fresh(SXmemory 1 6)bs /\
 V293_global_steps(BXglobal sync)cst
 (GXtasks other,(BXge,GXenvs otherle,SXmemory 1 6,(fun _=>false),GXaux enabled ci otheraux),SXct)
 (set(GXtasks other)SXct(BXend sync),
 (BXge,set(GXenvs otherle)SXct(V293_cpu_lenv 601%Z bs),Mf,(fun _=>false),
 set(GXaux enabled ci otheraux)SXct(false,nil,enabled::ci)),OwnershipReady) /\
 (BXge,V293_cpu_lenv 601%Z bs,Mf,(fun _=>false),(false,nil,enabled::ci),
 set(RIabstract SXct)curtid(oscurt OwnershipReady),spec_done None)|=SRpost bs /\
 load(Tptr V293_tcb_type)Mf(1%positive,0%Z)=Some(Vptr OwnershipReady) /\
 load Tint8 Mf(96%positive,0%Z)=Some(V293_byteval(if sync then 4 else 6)) /\
 load Tint32 Mf(97%positive,0%Z)=Some(Vint32(Int.repr 20)) /\
 (forall k,k<4 ->exists v,get Mf(bs,Z.of_nat k)=Some(true,v)) /\
 (V293_cache_current OwnershipTasks OwnershipReady Mf 96%positive <->sync=true).
Proof.
 intros sync enabled ci other otherle otheraux cst.
 destruct(V293_exit_boundary_shared_reclose sync 80%positive 81%positive 82%positive
 (BXprogram sync)kstop GXempty(BXprogram sync)GXempty((fun _=>None):intunit)
 (GXtasks other)(GXenvs otherle)(GXaux enabled ci otheraux)cst
 (curs(scall 501%Z nil))kenil SXcaller BXge SXcaller(SXmemory 1 6)(fun _=>false)
 enabled nil ci(RIabstract SXct)(spec_done None)SXct SRrest SRprivate OwnershipTasks 6
 300%Z 107%Z 100%Z 101%Z 102%Z 103%Z 104%Z 105%Z 106%Z
 108%Z 109%Z 113%Z 601%Z 110%Z 111%Z
 92%positive 91%positive 93%positive 94%positive 95%positive 98%positive 96%positive 97%positive
 (Int.repr 19)(V293_byteval 88)(Vptr OwnershipWaiting)1%positive
 (BXmerge sync)(GXcode other)(GXenv otherle)(GXaux_current enabled ci otheraux)I
 eq_refl eq_refl ltac:(vm_compute;intuition congruence)
 ltac:(discriminate)ltac:(discriminate)ltac:(discriminate)ltac:(discriminate)
 ltac:(discriminate)ltac:(discriminate)ltac:(discriminate)
 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
 (map_get_set _ _ _)(BXdomain other otherle otheraux enabled ci)
 (RIfixed_tasks SXct)SXcurrent SXnot_highest SRprivate_good(SXlookup 1 6)(SRentry ci))
 as(bs&next&nh&Me&Ms&Mf&Fresh&Different&PriorityDifferent&Highest&NextPriority&Exec&Post&Pointer&Cache&Counter&Alive&Coherent&CopyStore&PointerStore&NextBindings).
 assert(Next:next=OwnershipReady).
 { destruct RTliteral_rel as(Lo&Hi&Nonempty&Bitmap&Table).
   eapply V293_highest_unique;[exact Table|exact Highest|exact FXhighest]. }
 subst next.
 assert(Priority:nh=4).
 { destruct NextPriority as[Bound[st[m Task]]].
   assert(Ready:get OwnershipTasks OwnershipReady=Some(Int.repr 4,rdy,Vnull))by reflexivity.
   unfold get,TcbMap in Task,Ready;rewrite Ready in Task.
   apply V293_priority_repr_injective;[exact Bound|lia| ].
   symmetry;exact(f_equal(fun x=>match x with Some(p,_,_)=>p |None=>Int.zero end)Task). }
 subst nh;exists bs;exists Mf;repeat first[assumption|split].
Qed.

Theorem SRcopy_ablation : forall enabled ci other otherle otheraux cst,
 exists b0 M0 b1 M1,
 V293_global_steps(BXglobal true)cst
 (GXtasks other,(BXge,GXenvs otherle,SXmemory 1 6,(fun _=>false),GXaux enabled ci otheraux),SXct)
 (set(GXtasks other)SXct(BXend true),
 (BXge,set(GXenvs otherle)SXct(V293_cpu_lenv 601%Z b0),M0,(fun _=>false),
 set(GXaux enabled ci otheraux)SXct(false,nil,enabled::ci)),OwnershipReady) /\
 V293_global_steps(BXglobal false)cst
 (GXtasks other,(BXge,GXenvs otherle,SXmemory 1 6,(fun _=>false),GXaux enabled ci otheraux),SXct)
 (set(GXtasks other)SXct(BXend false),
 (BXge,set(GXenvs otherle)SXct(V293_cpu_lenv 601%Z b1),M1,(fun _=>false),
 set(GXaux enabled ci otheraux)SXct(false,nil,enabled::ci)),OwnershipReady) /\
 (BXge,V293_cpu_lenv 601%Z b0,M0,(fun _=>false),(false,nil,enabled::ci),
 set(RIabstract SXct)curtid(oscurt OwnershipReady),spec_done None)|=SRpost b0 /\
 (BXge,V293_cpu_lenv 601%Z b1,M1,(fun _=>false),(false,nil,enabled::ci),
 set(RIabstract SXct)curtid(oscurt OwnershipReady),spec_done None)|=SRpost b1 /\
 load(Tptr V293_tcb_type)M0(1%positive,0%Z)=Some(Vptr OwnershipReady) /\
 load(Tptr V293_tcb_type)M1(1%positive,0%Z)=Some(Vptr OwnershipReady) /\
 load Tint8 M0(96%positive,0%Z)=Some(V293_byteval 4) /\
 load Tint8 M1(96%positive,0%Z)=Some(V293_byteval 6) /\
 load Tint32 M0(97%positive,0%Z)=Some(Vint32(Int.repr 20)) /\
 load Tint32 M1(97%positive,0%Z)=Some(Vint32(Int.repr 20)) /\
 V293_cache_current OwnershipTasks OwnershipReady M0 96%positive /\
 ~V293_cache_current OwnershipTasks OwnershipReady M1 96%positive.
Proof.
 intros enabled ci other otherle otheraux cst.
 destruct(SRcomplete_switch true enabled ci other otherle otheraux cst)
 as(b0&M0&Fresh0&Exec0&Post0&Pointer0&Cache0&Counter0&Alive0&Coherent0).
 destruct(SRcomplete_switch false enabled ci other otherle otheraux cst)
 as(b1&M1&Fresh1&Exec1&Post1&Pointer1&Cache1&Counter1&Alive1&Coherent1).
 assert(C0:V293_cache_current OwnershipTasks OwnershipReady M0 96%positive)by(apply Coherent0;reflexivity).
 assert(C1:~V293_cache_current OwnershipTasks OwnershipReady M1 96%positive)by(rewrite Coherent1;discriminate).
 exists b0;exists M0;exists b1;exists M1;repeat first[assumption|split].
Qed.

Lemma SRprivate_canary : forall bs ge le Mf ir aux O op,
 (ge,le,Mf,ir,aux,O,op)|=SRpost bs ->
 load Tint8 Mf(100%positive,0%Z)=Some(V293_byteval 0).
Proof.
 intros bs ge le Mf ir aux O op Held.
 eapply V293_record_star_load_l with(s:=(ge,le,Mf,ir,aux,O,op))
 (P:=V293_owned_record_cell((100%positive,0%Z),Tint8,V293_byteval 0))(Q:=Atrue).
 - intros st H;apply V293_owned_record_cell_load;exact H.
 - unfold SRpost,SRprivate in Held;sep auto.
Qed.
