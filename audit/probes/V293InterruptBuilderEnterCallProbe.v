(* Nonempty canonical storage/ready/TCB heap, actual unfiltered builder.
   The builder is a handler-entry resource, not an initialized predecessor. *)
Require Import CertiOS.certiucos.v293.proofs.V293InterruptBuilderEnterCall.
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

Definition BEcall n ks := exists M frame O Of Mf,
 join M frame(JBmemory n Int.zero Int.zero) /\
 join O Of(RIabstract OwnershipWaiting) /\QCstate M O|=BQpre /\
 V293_control_capture 99%positive 96%positive 97%positive(QCstate M O)=Some(O,V293_control 1 n 0) /\
 cstepstar RDprogram(curs(scall 301%Z nil),(kenil,ks))(JBge,emp,M)
 (curs(sskip None),(kenil,ks))(JBge,emp,Mf) /\
 V293_control_read 99%positive 96%positive 97%positive Mf=Some(V293_control_enter(V293_control 1 n 0)) /\
 V293_control_step V293_scheduler V293_control_Enter(O,V293_control 1 n 0)
 (V293_control_Core(spec_done None))(O,V293_control_enter(V293_control 1 n 0)) /\
 (forall a,a<>(96%positive,0%Z) ->get Mf a=get M a).

Theorem BEactual_builder_call : forall n ks,n<256 ->BEcall n ks.
Proof.
 intros n ks Bound;destruct(QJentry_nonempty n Bound)as(M&frame&O&Of&JM&JO&Old).
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
 destruct(V293_builder_enter_call 106%Z 112%Z 110%Z 111%Z
 92%positive 81%positive 80%positive 91%positive 82%positive 94%positive 95%positive
 99%positive 96%positive 97%positive nil QCintspec 0(fun _:hid=>false)nil
 OwnershipWaiting nil BQpre(spec_done None)(QCstate M O)RDprogram ks V293_scheduler 301%Z
 eq_refl eq_refl Pre eq_refl)as[c[Mf[Valid[Captured[Call[Read[Step Frame]]]]]]].
 rewrite Capture in Captured;inversion Captured;subst c.
 unfold BEcall;exists M;exists frame;exists O;exists Of;exists Mf.
 split;[exact JM| ];split;[exact JO| ];split;[exact Pre| ];split;[exact Capture| ];
 split;[exact Call| ];split;[exact Read| ];split;[exact Step|exact Frame].
Qed.

Corollary BEboundary_builder_calls : forall ks,
 BEcall 0 ks /\BEcall 254 ks /\BEcall 255 ks.
Proof. intro ks;repeat split;apply BEactual_builder_call;lia. Qed.

Lemma BEowned_byte_required : forall st,
 st|=Amapsto(96%positive,0%Z)Tint8 true(V293_byteval 0) ** Atrue ->
 exists byte,get(getmem st)(96%positive,0%Z)=Some(true,byte).
Proof. intros st Owned;eapply V293_builder_byte_writable;exact Owned. Qed.
