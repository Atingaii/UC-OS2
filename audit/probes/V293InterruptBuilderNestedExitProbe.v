Require Import CertiOS.certiucos.v293.proofs.V293InterruptBuilderEnterCall.
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

Require Import CertiOS.certiucos.v293.proofs.V293InterruptBuilderNestedExit.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitCallExecution.
Require Import CertiOS.audit.probes.V293InterruptBuilderEnterResourcesProbe.

(* One program for both real calls, with the explicit normalized Exit body.
   This is not RDprogram's differently defined boundary Exit function. *)
Definition BNprogram (f:fid) : option function :=
 if Z.eq_dec f 300%Z then Some(V293_OSIntExit_abstract_function
 112%Z 110%Z 111%Z 120%Z 105%Z 103%Z 106%Z 108%Z 109%Z 200%Z 302%Z)
 else if Z.eq_dec f 301%Z then Some(V293_OSIntEnter_function 112%Z 110%Z) else None.
Definition BNrun n := exists M frame O Of Mf,
 join M frame(JBmemory n Int.zero Int.zero) /\
 join O Of(RIabstract OwnershipWaiting) /\QCstate M O|=BQpre /\
 V293_local_steps BNprogram
 (curs(V293_irq_source_wrapper 301%Z 300%Z Int.zero),(kenil,kstop))(gettaskst(QCstate M O))
 (curs(sprim exint),(kenil,kstop))(gettaskst(BRstate Mf O)) /\
 BRstate Mf O|=BRsnapshot n /\
 V293_control_capture 99%positive 96%positive 97%positive(BRstate Mf O)=Some(O,V293_control 1 n 0) /\
 (forall a,a<>(96%positive,0%Z)->get Mf a=get M a).

Theorem BNnonempty_nested : forall n,1<=n ->n<255 ->BNrun n.
Proof.
 intros n Lower Bound;destruct(QJentry_nonempty n ltac:(lia))as(M&frame&O&Of&JM&JO&Old).
 assert(Pre:QCstate M O|=BQpre).
 { apply BQpre_pack;apply QJsnapshot_to_builder with(nest:=n);try assumption;lia. }
 assert(Snapshot:QCstate M O|=V293_irq_bound_snapshot
 106%Z 112%Z 110%Z 111%Z 92%positive 81%positive 80%positive 91%positive 82%positive
 94%positive 95%positive 99%positive 96%positive 97%positive nil
 1 n 0(spec_done None)false(isrupd(fun _:hid=>false)0 true)[0]nil OwnershipWaiting).
 { apply V293_irq_bound_snapshot_pack;exact Old. }
 assert(Capture:V293_control_capture 99%positive 96%positive 97%positive(QCstate M O)=Some(O,V293_control 1 n 0)).
 { eapply V293_control_capture_owned;try lia.
   eapply V293_irq_bound_snapshot_controls;exact Snapshot. }
 destruct(V293_builder_nested_prefix 106%Z 112%Z 110%Z 111%Z
 92%positive 81%positive 80%positive 91%positive 82%positive 94%positive 95%positive
 99%positive 96%positive 97%positive nil QCintspec 0(fun _:hid=>false)nil
 OwnershipWaiting nil BQpre(spec_done None)(QCstate M O)BNprogram V293_scheduler 301%Z 300%Z Int.zero
 120%Z 105%Z 103%Z 108%Z 109%Z 200%Z 302%Z n 0
 eq_refl eq_refl Pre Capture Lower Bound eq_refl eq_refl ltac:(discriminate)ltac:(discriminate)
 eq_refl ltac:(change(0<=0<2)%Z;lia))as[Mf[Trace[After[Read Frame]]]].
 unfold BNrun;exists M;exists frame;exists O;exists Of;exists Mf.
 split;[exact JM| ];split;[exact JO| ];split;[exact Pre| ];
 split;[exact Trace| ];split;[exact After| ];split;[exact Read|exact Frame].
Qed.

Corollary BNboundaries : BNrun 1 /\BNrun 254.
Proof. split;apply BNnonempty_nested;lia. Qed.

(* A complete nonempty execution and its resource witness are obtained before
   asking the final byte observation. This does not remove any statement. *)
Theorem BNcompleted_observation : exists M frame O Of Mf,
 join M frame(JBmemory 254 Int.zero Int.zero) /\
 join O Of(RIabstract OwnershipWaiting) /\
 V293_local_steps BNprogram
 (curs(V293_irq_source_wrapper 301%Z 300%Z Int.zero),(kenil,kstop))(gettaskst(QCstate M O))
 (curs(sprim exint),(kenil,kstop))(gettaskst(BRstate Mf O)) /\
 BRstate Mf O|=BRsnapshot 254 /\
 load Tint8 Mf(96%positive,0%Z)=Some(V293_byteval 254).
Proof.
 destruct(BNnonempty_nested 254 ltac:(lia)ltac:(lia))as(M&frame&O&Of&Mf&JM&JO&Pre&Trace&After&Read&Frame).
 assert(Loads:load Tint8 Mf(96%positive,0%Z)=Some(V293_byteval 254)).
 { destruct(V293_builder_snapshot_memory 106%Z 112%Z 110%Z 111%Z
   92%positive 81%positive 80%positive 91%positive 82%positive 94%positive 95%positive
   99%positive 96%positive 97%positive nil 1 254 0(spec_done None)false BRir[0]nil OwnershipWaiting
   (BRstate Mf O)ltac:(lia)ltac:(lia)ltac:(lia)After)as[_[_[_[_[Load _]]]]];exact Load. }
 exists M;exists frame;exists O;exists Of;exists Mf.
 split;[exact JM| ];split;[exact JO| ];split;[exact Trace| ];split;[exact After|exact Loads].
Qed.
