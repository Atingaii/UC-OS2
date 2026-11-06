(* Store closure after the original global switch; not a tick execution trace. *)
Require Import CertiOS.certiucos.v293.proofs.V293TimeDlyTaskBridge.
Require Import CertiOS.certiucos.v293.proofs.V293TimeDlyBlocking.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickLifecycle.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.code.V293ReadyTable.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.audit.probes.V293TimeDlyEntryProbe.
Require Import CertiOS.audit.probes.V293TimeDlyBlockingProbe.
Require Import CertiOS.audit.probes.V293TimeDlyTaskBridgeProbe.
Require Import CertiOS.audit.probes.V293TaskRecordOwnershipProbe.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List Lia.
Require Import CertiOS.certiucos.v293.proofs.V293TimeDlyAllocated.
Require Import CertiOS.certiucos.v293.proofs.V293TimeDlyCallEntry.
Require Import CertiOS.audit.probes.V293TimeDlyCallEntryProbe.
Require Import CertiOS.audit.probes.V293TimeDlySwitchProbe.
Require Import CertiOS.audit.probes.V293TimeDlyAllocatedProbe.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyGlobalTrace.
Require Import CertiOS.certiucos.v293.proofs.V293LocalGlobalTrace.
Require Import CertiOS.certiucos.v293.code.V293OSTimeDlyCall.
Require Import Coq.Relations.Relation_Operators.
Require Import CertiOS.audit.probes.V293TimeDlyCallGlobalProbe.
Require Import CertiOS.certiucos.v293.proofs.V293TimeDlyReadyClosure.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyTaskInvariant.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.audit.probes.V293TimeDlySchedCallProbe.
Require Import CertiOS.audit.probes.V293TimeDlyReadyClosureProbe.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyOwnedSchedCall.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyFullCall.
Require Import CertiOS.certiucos.v293.proofs.V293TimeDlyGlobalSwitch.
Require Import CertiOS.certiucos.v293.proofs.V293TimeDlyCallEntry.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewExec.
Require Import CertiOS.certiucos.v293.proofs.V293ReadySchedCall.
Require Import CertiOS.certiucos.v293.proofs.V293TimeDlySchedCall.
Require Import CertiOS.certiucos.v293.proofs.V293TimeDlyEntry.
Require Import CertiOS.certiucos.v293.code.V293OSSchedNew.
Require Import CertiOS.certiucos.v293.code.V293OSSchedDispatch.
Require Import CertiOS.certiucos.v293.code.V293OSSchedChange.
Require Import CertiOS.certiucos.v293.proofs.V293ReadySourceTail.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyCallGlobal.
Require Import CertiOS.audit.probes.V293ReadyOwnedSchedCallProbe.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyOwnedGlobalSwitch.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchState.
Require Import CertiOS.framework.proof.memory_prop.
Require Import CertiOS.framework.proof.lmachLib.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.framework.proof.rulesoundlib.

Require Import CertiOS.audit.probes.V293ReadyOwnedGlobalSwitchProbe.
Require Import CertiOS.certiucos.v293.proofs.V293SwitchedCountdownClosure.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickTaskBridge.
Import ListNotations.
Local Open Scope nat_scope.

Definition SCtasks2:=set(DEblocked(Int.repr 3))OwnershipReady
 (Int.repr 4,wait os_stat_time(Int.repr 2),Vnull).
Definition SCabs2:=set DGabs abstcblsid(abstcblist SCtasks2).
Definition SCtasks1:=set SCtasks2 OwnershipReady
 (Int.repr 4,wait os_stat_time(Int.repr 1),Vnull).
Definition SCabs1:=set SCabs2 abstcblsid(abstcblist SCtasks1).
Definition SCpost c bs O M:=
 (DWge,DCle,M,(fun _:hid=>false),(true,nil,nil),O,spec_done None)|=
 V293_ready_full 30%positive 31%positive 83%positive OwnershipWaiting **DGframe c bs.

(* No new scanner cell or linked-list resource is postulated here. *)
Theorem SCfirst:forall c bs M,DGpost c bs M ->exists M2,
 store Tint32 M(60%positive,44%Z)(Vint32(Int.repr 2))=Some M2 /\
 spec_step V293_scheduler(spec_prim nil(V293_tick_wait_step OwnershipReady))DGabs(END None)SCabs2 /\
 SCpost c bs SCabs2 M2 /\load Tint32 M2(60%positive,44%Z)=Some(Vint32(Int.repr 2)) /\
 (forall b i,b<>60%positive \/(i<44)%Z \/(48<=i)%Z ->get M2(b,i)=get M(b,i)).
Proof.
 intros c bs M Held.
 exact(V293_ready_countdown_store 30%positive 31%positive 83%positive OwnershipWaiting
 (DEblocked(Int.repr 3))OwnershipReady(Int.repr 4)3 Vnull(DGframe c bs)
 DWge DCle M(fun _:hid=>false)(true,nil,nil)DGabs(spec_done None)V293_scheduler
 (ltac:(change(2<=3<=4294967295)%Z;lia)) eq_refl eq_refl Held).
Qed.

Theorem SCsecond:forall c bs M2,SCpost c bs SCabs2 M2 ->exists M1,
 store Tint32 M2(60%positive,44%Z)(Vint32(Int.repr 1))=Some M1 /\
 spec_step V293_scheduler(spec_prim nil(V293_tick_wait_step OwnershipReady))SCabs2(END None)SCabs1 /\
 SCpost c bs SCabs1 M1 /\load Tint32 M1(60%positive,44%Z)=Some(Vint32(Int.repr 1)) /\
 (forall b i,b<>60%positive \/(i<44)%Z \/(48<=i)%Z ->get M1(b,i)=get M2(b,i)).
Proof.
 intros c bs M Held.
 exact(V293_ready_countdown_store 30%positive 31%positive 83%positive OwnershipWaiting
 SCtasks2 OwnershipReady(Int.repr 4)2 Vnull(DGframe c bs)
 DWge DCle M(fun _:hid=>false)(true,nil,nil)SCabs2(spec_done None)V293_scheduler
 (ltac:(change(2<=2<=4294967295)%Z;lia)) eq_refl eq_refl Held).
Qed.

Theorem SCtwo_countdowns:forall c enabled,exists bs M M2 M1,
 V293_global_steps DAprog DXclient(DXinitial c enabled)(DXfinal enabled bs M) /\
 DGpost c bs M /\
 store Tint32 M(60%positive,44%Z)(Vint32(Int.repr 2))=Some M2 /\
 spec_step V293_scheduler(spec_prim nil(V293_tick_wait_step OwnershipReady))DGabs(END None)SCabs2 /\
 SCpost c bs SCabs2 M2 /\
 store Tint32 M2(60%positive,44%Z)(Vint32(Int.repr 1))=Some M1 /\
 spec_step V293_scheduler(spec_prim nil(V293_tick_wait_step OwnershipReady))SCabs2(END None)SCabs1 /\
 SCpost c bs SCabs1 M1 /\load Tint32 M1(60%positive,44%Z)=Some(Vint32(Int.repr 1)) /\
 get SCtasks1 OwnershipReady=Some(Int.repr 4,wait os_stat_time(Int.repr 1),Vnull) /\
 get SCabs1 curtid=Some(oscurt OwnershipWaiting) /\
 (forall b i,b<>60%positive \/(i<44)%Z \/(48<=i)%Z ->get M1(b,i)=get M(b,i)).
Proof.
 intros c enabled;destruct(DGglobal_switch c enabled)
 as(bs&y&My&Mh&Mc&M&Run&Pre&Free&Dead&Trace&Switch&Store&After&Rest).
 destruct(SCfirst c bs M After)as(M2&S2&A2&H2&L2&F2).
 destruct(SCsecond c bs M2 H2)as(M1&S1&A1&H1&L1&F1).
 exists bs;exists M;exists M2;exists M1.
 split;[exact Trace| ];split;[exact After| ];split;[exact S2| ];split;[exact A2| ];
 split;[exact H2| ];split;[exact S1| ];split;[exact A1| ];split;[exact H1| ];
 split;[exact L1| ];split;[reflexivity| ];split;[reflexivity| ].
 intros b i Outside;rewrite F1 by exact Outside;apply F2;exact Outside.
Qed.

Lemma SCrecords:forall c bs M,SCpost c bs SCabs2 M ->V293_task_records M SCtasks2.
Proof.
 intros c bs M H;exact(V293_ready_full_records 30%positive 31%positive 83%positive
 OwnershipWaiting SCtasks2(DGframe c bs)DWge DCle M(fun _:hid=>false)
 (true,nil,nil)SCabs2(spec_done None)eq_refl H).
Qed.

(* Same updated heap, same physical store, only the abstract commit differs. *)
Theorem SCcommit_ablation:forall c enabled,exists bs M M2,
 V293_global_steps DAprog DXclient(DXinitial c enabled)(DXfinal enabled bs M) /\
 DGpost c bs M /\
 store Tint32 M(60%positive,44%Z)(Vint32(Int.repr 2))=Some M2 /\
 SCpost c bs SCabs2 M2 /\V293_task_records M2 SCtasks2 /\
 ~V293_task_records M2(DEblocked(Int.repr 3)).
Proof.
 intros c enabled;destruct(DGglobal_switch c enabled)
 as(bs&y&My&Mh&Mc&M&Run&Pre&Free&Dead&Trace&Switch&Store&After&Rest).
 destruct(SCfirst c bs M After)as(M2&S2&A2&H2&L2&F2).
 exists bs;exists M;exists M2.
 split;[exact Trace| ];split;[exact After| ];split;[exact S2| ];split;[exact H2| ];
 split;[eapply SCrecords;exact H2| ].
 intro Stale;specialize(Stale OwnershipReady(Int.repr 4)(wait os_stat_time(Int.repr 3))Vnull eq_refl).
 destruct Stale as(p&P&Priority&Fields&Status).
 destruct Status as(Stat&Delay&Message).
 change(load Tint32 M2(60%positive,44%Z)=Some(Vint32(Int.repr 3)))in Delay.
 rewrite L2 in Delay;discriminate.
Qed.

Lemma SCobserved:forall c bs M,SCpost c bs SCabs1 M ->
 (forall a tp v,In(a,tp,v)(DOcells c) ->load tp M a=Some v) /\
 load(Tptr V293_tcb_type)M(10%positive,0%Z)=Some(Vptr OwnershipWaiting) /\
 get SCabs1 curtid=Some(oscurt OwnershipWaiting).
Proof.
 intros c bs M H;split.
 - intros a tp v Member;eapply DScells_load with(ge:=DWge)(le:=DCle)
   (ir:=fun _:hid=>false)(aux:=(true,nil,nil))(O:=SCabs1)(op:=spec_done None);[exact Member| ].
   unfold SCpost,DGframe in H;clear -H;sep auto.
 - split;[exact(DGcurrent OwnershipWaiting(DGframe c bs)DCle M(fun _:hid=>false)(true,nil,nil)SCabs1 H)|reflexivity].
Qed.
