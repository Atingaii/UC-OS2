(* Nonempty canonical storage/ready/TCB heap, actual unfiltered builder.
   The builder is a handler-entry resource, not an initialized predecessor. *)
Require Import CertiOS.certiucos.v293.proofs.V293InterruptBuilderEnterResources.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptBindings.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptQuietBuilder.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptControlRetention.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptFixedControlSpec.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntEnterInternal.
Require Import CertiOS.certiucos.v293.code.V293OSIntEnter.
Require Import CertiOS.audit.probes.V293InterruptQuietBuilderProbe.
Require Import CertiOS.audit.probes.V293InterruptBoundQuietContinuousProbe.
Require Import CertiOS.audit.probes.V293InterruptQuietContinuousProbe.
Require Import CertiOS.audit.probes.V293OSIntExitReadyDynamicProbe.
Require Import CertiOS.audit.probes.V293OSIntExitLocalDispatchProbe.
Require Import CertiOS.audit.probes.V293InterruptReadyEnvironmentProbe.
Require Import CertiOS.audit.probes.V293OSIntExitReadyBodyProbe.
Require Import CertiOS.audit.probes.V293TaskRecordInvariantProbe.
Require Import CertiOS.audit.probes.V293TaskRecordOwnershipProbe.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.framework.include_frm.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptSourceRoundtrip.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptQuietISRReturn.

Definition BRir := isrupd(isrupd(fun _:hid=>false)0 true)0 false.
Definition BRstate M O : RstateOP := (JBge,emp,M,BRir,(false,[0],nil),O,spec_done None).
Definition BRsnapshot n := V293_irq_bound_snapshot
 106%Z 112%Z 110%Z 111%Z 92%positive 81%positive 80%positive 91%positive 82%positive
 94%positive 95%positive 99%positive 96%positive 97%positive nil
 1 n 0(spec_done None)false BRir [0]nil OwnershipWaiting.
Definition BRrun n := exists M frame O Of Mf,
 join M frame(JBmemory n Int.zero Int.zero) /\
 join O Of(RIabstract OwnershipWaiting) /\QCstate M O|=BQpre /\
 V293_control_capture 99%positive 96%positive 97%positive(QCstate M O)=Some(O,V293_control 1 n 0) /\
 V293_local_steps RDprogram
 (curs(V293_irq_source_wrapper 301%Z 300%Z Int.zero),(kenil,kstop))(gettaskst(QCstate M O))
 (curs(scall 300%Z nil),(kenil,kseq(sprim exint)kstop))(gettaskst(BRstate Mf O)) /\
 BRstate Mf O|=BRsnapshot(V293_interrupt_nest_after 1 n) /\
 V293_control_capture 99%positive 96%positive 97%positive(BRstate Mf O)=
 Some(O,V293_control_enter(V293_control 1 n 0)) /\
 V293_control_step V293_scheduler V293_control_Enter(O,V293_control 1 n 0)
 (V293_control_Core(spec_done None))(O,V293_control_enter(V293_control 1 n 0)) /\
 (forall a,a<>(96%positive,0%Z) ->get Mf a=get M a).

Theorem BRactual_builder_prefix : forall n,n<256 ->BRrun n.
Proof.
 intros n Bound;destruct(QJentry_nonempty n Bound)as(M&frame&O&Of&JM&JO&Old).
 assert(Pre:QCstate M O|=BQpre).
 { apply BQpre_pack;apply QJsnapshot_to_builder with(nest:=n);assumption. }
 assert(Snapshot:QCstate M O|=V293_irq_bound_snapshot
 106%Z 112%Z 110%Z 111%Z 92%positive 81%positive 80%positive 91%positive 82%positive
 94%positive 95%positive 99%positive 96%positive 97%positive nil
 1 n 0(spec_done None)false(isrupd(fun _:hid=>false)0 true)[0]nil OwnershipWaiting).
 { apply V293_irq_bound_snapshot_pack;exact Old. }
 assert(Capture:V293_control_capture 99%positive 96%positive 97%positive(QCstate M O)=Some(O,V293_control 1 n 0)).
 { eapply V293_control_capture_owned;try lia.
   eapply V293_irq_bound_snapshot_controls;exact Snapshot. }
 destruct(V293_builder_enter_prefix 106%Z 112%Z 110%Z 111%Z
 92%positive 81%positive 80%positive 91%positive 82%positive 94%positive 95%positive
 99%positive 96%positive 97%positive nil QCintspec 0(fun _:hid=>false)nil
 OwnershipWaiting nil BQpre(spec_done None)(QCstate M O)RDprogram V293_scheduler 301%Z 300%Z Int.zero
 eq_refl eq_refl Pre eq_refl eq_refl ltac:(change(0<=0<2)%Z;lia))
 as[c[Mf[Valid[Captured[Trace[After[Read[Step Frame]]]]]]]].
 rewrite Capture in Captured;inversion Captured;subst c.
 unfold BRrun;exists M;exists frame;exists O;exists Of;exists Mf.
 split;[exact JM| ];split;[exact JO| ];split;[exact Pre| ];split;[exact Capture| ];
 split;[exact Trace| ];split;[exact After| ];split;[exact Read| ];split;[exact Step|exact Frame].
Qed.

Corollary BRnonempty_boundaries : BRrun 0 /\BRrun 254 /\BRrun 255.
Proof. repeat split;apply BRactual_builder_prefix;lia. Qed.

(* The completed resource witness, not just an arithmetic byte equation,
   is used before checking the exact post-EOI interrupt observation. *)
Theorem BRcompleted_prefix_eoi : exists M frame O Of Mf,
 join M frame(JBmemory 254 Int.zero Int.zero) /\
 join O Of(RIabstract OwnershipWaiting) /\
 V293_local_steps RDprogram
 (curs(V293_irq_source_wrapper 301%Z 300%Z Int.zero),(kenil,kstop))(gettaskst(QCstate M O))
 (curs(scall 300%Z nil),(kenil,kseq(sprim exint)kstop))(gettaskst(BRstate Mf O)) /\
 BRstate Mf O|=BRsnapshot 255 /\
 getisr(gettaskst(BRstate Mf O))0=false.
Proof.
 destruct(BRactual_builder_prefix 254 ltac:(lia))as(M&frame&O&Of&Mf&JM&JO&Pre&Capture&Trace&After&Read&Step&Frame).
 exists M;exists frame;exists O;exists Of;exists Mf.
 split;[exact JM| ];split;[exact JO| ];split;[exact Trace| ];split;[exact After| ].
 reflexivity.
Qed.
