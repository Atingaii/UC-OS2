(* Typed counterexamples for a separate switch-compatible candidate; no boot claim. *)
Require Import CertiOS.audit.probes.V293ReadyStorageInvariantProbe.
Require Import CertiOS.audit.probes.V293InterruptBuilderCurrentCounterexample.
Require Import CertiOS.audit.probes.V293ReadyCriticalGlobalProbe.
Require Import CertiOS.audit.probes.V293TaskRecordInvariantProbe.
Require Import CertiOS.audit.probes.V293ReadyTaskInvariantProbe.
Require Import CertiOS.audit.probes.V293TaskRecordOwnershipProbe.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyStorageInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyTaskInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293ReadySwitchStep.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchStorage.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCurrent.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTarget.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.rulesoundlib.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.framework.proof.lmachLib.
Require Import CertiOS.framework.proof.memory_prop.
Require Import CertiOS.tactics.basetac.join_lib.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyCurrentInvariant.
Require Import CertiOS.audit.probes.V293CurrentSwitchObstruction.
Require Import CertiOS.audit.probes.V293InterruptChangedContinuousProbe.
Require Import CertiOS.audit.probes.V293OSIntExitLocalDispatchProbe.
Require Import CertiOS.audit.probes.V293InterruptBoundEntryProbe.

Require Import CertiOS.audit.probes.V293InterruptBoundDispatchContinuousProbe.
Require Import CertiOS.audit.probes.V293OSIntExitReadyBodyProbe.

Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.

Definition SCinv:=V293_ready_current_inv 80%positive 81%positive 82%positive
 106%Z V293_tcb_type PPcells 94%positive.
Definition SCguard:=V293_current_guard 94%positive.
Theorem SCgood : GoodI SCinv V293_scheduler V293_shared_li.
Proof. apply V293_ready_current_good. Qed.
Lemma SCwaiting_not_highest : ~V293_highest_ready OwnershipTasks OwnershipWaiting.
Proof. intros[p[m[Task _]]];vm_compute in Task;discriminate. Qed.
Lemma SCassociated : NCsnapshot 6 ==>SCguard OwnershipWaiting OwnershipTasks.
Proof.
 intros st H;apply NCsplit in H;unfold SCguard,V293_current_guard;left;exists 6.
 apply astar_l_apure_intro;[ |exact(proj1(proj2 NCcurrent_mismatch))].
 eapply astar_mono;[intros s K;exact K|intros s K;exact I|exact H].
Qed.
Lemma SCbad_rejected : forall M O,CCstate M O|=NCsnapshot 4 ->
 ~CCstate M O|=SCguard OwnershipWaiting OwnershipTasks.
Proof.
 intros M O H G;destruct(V293_current_guard_same 94%positive
 OwnershipWaiting OwnershipTasks 4 (CCstate M O) ltac:(lia)
 (NCload 4 M O ltac:(lia) H) G)as[C|Highest].
 - exact(proj1(proj2(proj2 NCcurrent_mismatch)) C).
 - exact(SCwaiting_not_highest Highest).
Qed.
Theorem SCleft_required_typed : exists M Mf O Of,
 CCstate M O|=BCpre /\ CCstate M O|=NCsnapshot 6 /\
 CCstate M O|=SCguard OwnershipWaiting OwnershipTasks /\
 ~V293_highest_ready OwnershipTasks OwnershipWaiting /\
 join M Mf(JBmemory 0 Int.zero Int.zero) /\join O Of(RIabstract OwnershipWaiting).
Proof.
 destruct BEchanged_same_state as(M&Mf&O&Of&JM&JO&H&B&W).
 change(CCstate M O|=NCsnapshot 6)in H.
 exists M;exists Mf;exists O;exists Of.
 split;[exact B| ];split;[exact H| ];split;[apply SCassociated;exact H| ].
 split;[exact SCwaiting_not_highest| ];split;assumption.
Qed.
Theorem SCall_required_typed : exists M Mf O Of M4 F4,
 join M Mf(JBmemory 0 Int.zero Int.zero) /\join O Of(RIabstract OwnershipWaiting) /\
 store Tint8 M(94%positive,0%Z)(V293_byteval 4)=Some M4 /\
 store Tint8(JBmemory 0 Int.zero Int.zero)(94%positive,0%Z)(V293_byteval 4)=Some F4 /\
 join M4 Mf F4 /\CCstate M O|=BCpre /\CCstate M4 O|=BCpre /\
 CCstate M4 O|=NCsnapshot 4 /\
 ~CCstate M4 O|=SCguard OwnershipWaiting OwnershipTasks /\
 V293_ready_select 16 0(V293_ready_group 16 0)=4 /\
 ~sched_self V293_scheduler(RIabstract OwnershipWaiting) /\
 load Tint8 M(94%positive,0%Z)=Some(V293_byteval 6) /\
 load Tint8 M4(94%positive,0%Z)=Some(V293_byteval 4) /\
 (forall a,a<>(94%positive,0%Z)->get M4 a=get M a) /\
 (forall a,a<>(94%positive,0%Z)->get F4 a=get(JBmemory 0 Int.zero Int.zero)a).
Proof.
 destruct NCtyped_single_byte as(M&Mf&O&Of&M4&F4&JM&JO&S&SF&JF&B&B4&H&Read&Read4&Out&OutF).
 exists M;exists Mf;exists O;exists Of;exists M4;exists F4.
 split;[exact JM| ];split;[exact JO| ];split;[exact S| ];split;[exact SF| ];split;[exact JF| ].
 split;[exact B| ];split;[exact B4| ];split;[exact H| ];split;[apply SCbad_rejected;exact H| ].
 split;[exact(proj1 NCcurrent_mismatch)| ];split;[exact(proj2(proj2(proj2 NCcurrent_mismatch)))| ].
 split;[exact Read| ];split;[exact Read4| ];split;assumption.
Qed.
Lemma SCafter_sched : forall O,
 get O abstcblsid=Some(abstcblist OwnershipTasks) ->
 sched_self V293_scheduler(set O curtid(oscurt OwnershipReady)).
Proof.
 intros O Tasks;exists OwnershipReady;split;[apply map_get_set| ].
 exists OwnershipTasks;split;[rewrite map_get_set' by discriminate;exact Tasks|exact RIhighest].
Qed.
Theorem SCright_required_typed : exists M O Mf,
 CSstate M O|=SWINVt PPinv OwnershipWaiting /\
 NCcurrent_relation(CSstate M O) /\
 store(Tptr V293_tcb_type)M(1%positive,0%Z)(Vptr OwnershipReady)=Some Mf /\
 CSstate Mf(set O curtid(oscurt OwnershipReady))|=SWINVt SCinv OwnershipReady /\
 ~NCcurrent_relation(CSstate Mf(set O curtid(oscurt OwnershipReady))) /\
 load Tint8 M(94%positive,0%Z)=Some(V293_byteval 6) /\
 load Tint8 Mf(94%positive,0%Z)=Some(V293_byteval 6) /\
 (forall b off,b<>1%positive ->get Mf(b,off)=get M(b,off)).
Proof.
 destruct CSswitch_witness as(M&O&Mf&H&Before&Highest&Tasks&S&After&NotAfter&ReadCS&ReadAfter&Outside).
 exists M;exists O;exists Mf;split;[exact H| ];split;[exact Before| ];split;[exact S| ];split.
 - unfold SCinv;apply(V293_current_switch_highest 80%positive 81%positive 82%positive
   106%Z V293_tcb_type PPcells 94%positive OwnershipReady CGge CGle Mf
   (fun _:hid=>false)(false,nil,[false])(set O curtid(oscurt OwnershipReady))(spec_done None)).
   + exact After.
   + apply SCafter_sched;exact Tasks.
 - split;[exact NotAfter| ];split;[exact ReadCS| ];split;[exact ReadAfter|exact Outside].
Qed.
Theorem SCsame_from_new_core : forall R ge le M ir aux O op t tasks lo hi entries nc,
 (ge,le,M,ir,aux,O,op)|=
 V293_ready_current_core 80%positive 81%positive 82%positive
 106%Z V293_tcb_type PPcells 94%positive **R ->
 get O curtid=Some(oscurt t) ->get O abstcblsid=Some(abstcblist tasks) ->
 V293_ready_rel lo hi entries tasks ->nc<256 ->
 load Tint8 M(94%positive,0%Z)=Some(V293_byteval nc) ->
 V293_ready_select lo hi(V293_ready_group lo hi)=nc ->sched_self V293_scheduler O.
Proof. intros;eapply V293_current_core_same_sched;eassumption. Qed.
