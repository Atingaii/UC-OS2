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

Require Import CertiOS.audit.probes.V293ReadyCurrentInvariantProbe.
Require Import CertiOS.audit.probes.V293OSIntExitReadyDynamicProbe.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptCurrentEntry.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptBindings.
Require Import CertiOS.certiucos.v293.code.V293OSIntEnter.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntEnterInternal.
Require Import CertiOS.framework.proof.toptheorem.

(* Actual candidate builder on the original typed heap; no reachability claim. *)
Definition CEinv:=V293_irq_current_inv 106%Z
 92%positive 81%positive 80%positive 91%positive 82%positive 94%positive 95%positive
 99%positive 96%positive 97%positive nil.
Definition CEpre:=ipreasrt' 0(fun _:hid=>false)nil(sched;;spec_done None)CEinv **
 p_local LDli OwnershipWaiting nil.
Definition CEspec:=V293_enter_bound_spec 112%Z 110%Z 111%Z
 99%positive 96%positive 97%positive Aemp Logic.I 300%Z.
Definition CEafter:=V293_irq_current_after 106%Z 112%Z 110%Z 111%Z
 92%positive 81%positive 80%positive 91%positive 82%positive 94%positive 95%positive
 99%positive 96%positive 97%positive nil 0(fun _:hid=>false)nil
 (sched;;spec_done None)OwnershipWaiting.
Theorem CEbuilder : Some CEpre=BuildintPre 0 BCintspec(fun _:hid=>false)nil CEinv LDli OwnershipWaiting nil.
Proof. reflexivity. Qed.
Lemma CEfrom_snapshot : forall M O,CCstate M O|=NCsnapshot 6 ->CCstate M O|=CEpre.
Proof.
 intros M O H;destruct(NCabstract 6 M O H)as[Current Tasks].
 unfold CEpre,CEinv.
 apply(V293_irq_current_builder_enrich 106%Z 112%Z 110%Z 111%Z
 92%positive 81%positive 80%positive 91%positive 82%positive 94%positive 95%positive
 99%positive 96%positive 97%positive nil 0(fun _:hid=>false)nil
 (sched;;spec_done None)OwnershipWaiting nil OwnershipWaiting OwnershipTasks(CCstate M O)).
 - change(CCstate M O|=BCpre);apply(NCbuilder 6);[lia|exact H].
 - exact Current.
 - exact Tasks.
 - apply SCassociated;exact H.
Qed.
Lemma CEbad_rejected : forall M O,CCstate M O|=NCsnapshot 4 ->~CCstate M O|=CEpre.
Proof.
 intros M O H New;destruct(NCabstract 4 M O H)as[C T].
 destruct(V293_irq_current_builder_guard 106%Z 112%Z 110%Z 111%Z
 92%positive 81%positive 80%positive 91%positive 82%positive 94%positive 95%positive
 99%positive 96%positive 97%positive nil 0(fun _:hid=>false)nil
 (sched;;spec_done None)OwnershipWaiting nil JBge emp M
 (isrupd(fun _:hid=>false)0 true)(false,[0],nil) O(sched;;spec_done None)New)
 as[ct[tasks[C0[T0 G]]]].
 assert(ct=OwnershipWaiting)by congruence;assert(tasks=OwnershipTasks)by congruence;subst ct tasks.
 exact(SCbad_rejected M O H G).
Qed.
Theorem CEtyped_entry_nonempty : exists M Mf O Of,
 join M Mf(JBmemory 0 Int.zero Int.zero) /\join O Of(RIabstract OwnershipWaiting) /\
 CCstate M O|=BCpre /\CCstate M O|=CEpre /\
 CCstate M O|=NCsnapshot 6 /\~V293_highest_ready OwnershipTasks OwnershipWaiting.
Proof.
 destruct BEchanged_same_state as(M&Mf&O&Of&JM&JO&H&B&W).
 change(CCstate M O|=NCsnapshot 6)in H.
 exists M;exists Mf;exists O;exists Of.
 split;[exact JM| ];split;[exact JO| ];split;[exact B| ];split;[apply CEfrom_snapshot;exact H| ].
 split;[exact H|exact SCwaiting_not_highest].
Qed.
Theorem CEtyped_single_byte : exists M Mf O Of M4 F4,
 join M Mf(JBmemory 0 Int.zero Int.zero) /\join O Of(RIabstract OwnershipWaiting) /\
 store Tint8 M(94%positive,0%Z)(V293_byteval 4)=Some M4 /\
 store Tint8(JBmemory 0 Int.zero Int.zero)(94%positive,0%Z)(V293_byteval 4)=Some F4 /\
 join M4 Mf F4 /\CCstate M O|=BCpre /\CCstate M4 O|=BCpre /\
 CCstate M O|=CEpre /\~CCstate M4 O|=CEpre /\
 CCstate M O|=NCsnapshot 6 /\CCstate M4 O|=NCsnapshot 4 /\
 load Tint8 M(94%positive,0%Z)=Some(V293_byteval 6) /\
 load Tint8 M4(94%positive,0%Z)=Some(V293_byteval 4) /\
 (forall a,a<>(94%positive,0%Z)->get M4 a=get M a) /\
 (forall a,a<>(94%positive,0%Z)->get F4 a=get(JBmemory 0 Int.zero Int.zero)a).
Proof.
 destruct BEchanged_same_state as(M&Mf&O&Of&JM&JO&H&B&W).
 change(CCstate M O|=NCsnapshot 6)in H.
 destruct(NCwrite M O H)as(M4&S&K).
 destruct(store_mono _ _ _ _ _ _ _ JM S)as(F4&SF).
 exists M;exists Mf;exists O;exists Of;exists M4;exists F4.
 split;[exact JM| ];split;[exact JO| ];split;[exact S| ];split;[exact SF| ];split.
 - apply map_join_comm;eapply join_store_join;[apply map_join_comm;exact JM|exact S|exact SF].
 - split;[exact B| ];split;[apply(NCbuilder 4);[lia|exact K]| ];split.
   + apply CEfrom_snapshot;exact H.
   + split;[apply CEbad_rejected;exact K| ];split;[exact H| ];split;[exact K| ];split.
     * apply(NCload 6 M O);[lia|exact H].
     * split;[apply(NCload 4 M4 O);[lia|exact K]| ];split.
       -- intros a D;rewrite(NCstore_only M M4 S);apply V293_put_byte_other;exact D.
       -- intros a D;rewrite(NCstore_only _ F4 SF);apply V293_put_byte_other;exact D.
Qed.
Theorem CEactual_entry : InfRules CEspec V293_scheduler LDli CEinv arfalse Afalse
 CEpre(sseq(sprim(eoi Int.zero))(scall 300%Z nil))CEafter OwnershipWaiting.
Proof.
 apply(V293_interrupt_current_entry 106%Z 112%Z 110%Z 111%Z
 92%positive 81%positive 80%positive 91%positive 82%positive 94%positive 95%positive
 99%positive 96%positive 97%positive nil CEspec V293_scheduler arfalse Afalse
 300%Z BCintspec 0(fun _:hid=>false)nil(sched;;spec_done None)OwnershipWaiting nil CEpre Int.zero).
 - reflexivity.
 - exact CEbuilder.
 - reflexivity.
 - change(0<=0<16)%Z;lia.
 - reflexivity.
Qed.
Theorem CEgood_and_enter_environment : GoodI CEinv V293_scheduler LDli /\
 WFFunEnv(V293_OSIntEnter_unit 300%Z 112%Z 110%Z)CEspec V293_scheduler LDli CEinv /\
 WFIFun(V293_OSIntEnter_unit 300%Z 112%Z 110%Z)CEspec V293_scheduler CEinv LDli.
Proof. split;[apply V293_irq_current_good|apply V293_irq_current_enter_environment]. Qed.
