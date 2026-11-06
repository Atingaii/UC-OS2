Require Import CertiOS.tactics.basetac.join_lib.
Require Import CertiOS.tactics.basetac.join_general.
Require Import CertiOS.framework.proof.rulesoundlib.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.audit.probes.V293OSIntExitReadyDynamicProbe.
Require Import CertiOS.audit.probes.V293TaskRecordInvariantProbe.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptBoundQuietContinuous.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptBindings.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptQuietContinuous.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptReadyBoundary.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitBoundDynamic.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntEnterOpenExact.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntEnterInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitUnifiedInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitLocalDispatch.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitReadyDynamic.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedSwitch.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptSourceRoundtrip.
Require Import CertiOS.audit.probes.V293OSIntExitBoundDynamicProbe.
Require Import CertiOS.audit.probes.V293InterruptQuietContinuousProbe.
Require Import CertiOS.audit.probes.V293InterruptEntryControlProbe.
Require Import CertiOS.audit.probes.V293OSIntExitReadyBodyProbe.
Require Import CertiOS.audit.probes.V293InterruptReadyEnvironmentProbe.
Require Import CertiOS.audit.probes.V293OSIntExitLocalDispatchProbe.
Require Import CertiOS.audit.probes.V293TaskRecordOwnershipProbe.
Require Import CertiOS.audit.probes.V293OSIntExitExactInternalProbe.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitNondispatch.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.toptheorem.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import Coq.Lists.List Lia.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitAllExactDynamic.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptReadyLocal.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedExactLocal.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchState.
Require Import CertiOS.tactics.sepauto.sep_combine_lemmas.
Require Import CertiOS.certiucos.v293.code.V293ReadyTable.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickDelayHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitReadyBody.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitHandoffHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedChange.
Require Import CertiOS.certiucos.v293.proofs.V293TimeAccess.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptReadyEnvironment.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptReadyEnter.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitReadyDispatch.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyStorageInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyTaskInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedStoragePrefix.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchStorage.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.code.V293OSIntEnter.
Require Import CertiOS.audit.probes.V293ReadyTaskInvariantProbe.
Require Import CertiOS.audit.probes.V293OSIntExitReadyInternalProbe.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptChangedContinuous.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitReadyInternal.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitBuilders.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTargetWitness.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptSameContinuous.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitSameInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitResourceCodec.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedStoragePrefixWitness.
Require Import CertiOS.certiucos.v293.proofs.V293SharedStateWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedPrefix.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.audit.probes.V293InterruptBoundQuietContinuousProbe.
Require Import CertiOS.audit.probes.V293InterruptChangedContinuousProbe.
Require Import CertiOS.audit.probes.V293InterruptSameContinuousProbe.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptBoundDispatchContinuous.
Import ListNotations.
Local Open Scope nat_scope.
Definition BCintspec (i:hid):=if Nat.eq_dec i 0 then Some(sched;;spec_done None)else None.
Definition BCpre:=ipreasrt' 0(fun _:hid=>false)nil(sched;;spec_done None)RDinv **p_local LDli OwnershipWaiting nil.
Definition BCret:=iretasrt' 0(fun _:hid=>false)nil RDinv **p_local LDli OwnershipWaiting nil.
Definition BSpre:=ipreasrt' 0(fun _:hid=>false)nil(spec_done None)RDinv **p_local LDli OwnershipReady nil.
Definition BSret:=iretasrt' 0(fun _:hid=>false)nil RDinv **p_local LDli OwnershipReady nil.
Theorem BCbuilders :
 Some BCpre=BuildintPre 0 BCintspec(fun _:hid=>false)nil RDinv LDli OwnershipWaiting nil /\
 Some BCret=BuildintRet 0 BCintspec(fun _:hid=>false)nil RDinv LDli OwnershipWaiting nil.
Proof. split;reflexivity. Qed.
Theorem BSbuilders :
 Some BSpre=BuildintPre 0 QCintspec(fun _:hid=>false)nil RDinv LDli OwnershipReady nil /\
 Some BSret=BuildintRet 0 QCintspec(fun _:hid=>false)nil RDinv LDli OwnershipReady nil.
Proof. split;reflexivity. Qed.
Theorem BCtyped_entry_nonempty : exists M Mf O Of,
 join M Mf(JBmemory 0 Int.zero Int.zero) /\join O Of(RIabstract OwnershipWaiting) /\
 CCstate M O|=CCentry.
Proof. exact CCentry_nonempty. Qed.
Theorem BStyped_entry_nonempty : exists M Mf O Of,
 join M Mf(SCmemory 0 Int.zero Int.zero) /\join O Of(RIabstract OwnershipReady) /\
 SCirq_state M O|=SCentry.
Proof. exact SCentry_nonempty. Qed.
Theorem BCenvironment : GoodI RDinv V293_scheduler LDli /\
 WFFunEnv RDprogram BDspec V293_scheduler LDli RDinv /\
 WFIFun RDprogram BDspec V293_scheduler RDinv LDli.
Proof. exact BQenvironment. Qed.
Theorem BCactual_wrapper :
 InfRules BDspec V293_scheduler LDli RDinv arfalse BCret
 CCentry(V293_irq_source_wrapper 301%Z 300%Z Int.zero)Afalse OwnershipWaiting.
Proof.
 unfold CCentry;apply(V293_interrupt_bound_changed_continuous
 100%Z 101%Z 102%Z 103%Z 105%Z 106%Z 108%Z 109%Z 112%Z 110%Z 111%Z
 92%positive 81%positive 80%positive 91%positive 82%positive 93%positive 94%positive 95%positive
 99%positive 96%positive 97%positive nil 16 0 6 RTentries OwnershipTasks emp Int.zero
 (V293_byteval 88)(Vptr OwnershipWaiting)Int.zero BDspec 301%Z 300%Z BCintspec 0(fun _:hid=>false)nil
 OwnershipWaiting BCret Int.zero);try reflexivity.
 - apply RBvalid;lia.
 - unfold INUM;rewrite Int.unsigned_zero;cbn;lia.
Qed.
Theorem BSactual_wrapper :
 InfRules BDspec V293_scheduler LDli RDinv arfalse BSret
 SCentry(V293_irq_source_wrapper 301%Z 300%Z Int.zero)Afalse OwnershipReady.
Proof.
 unfold SCentry;apply(V293_interrupt_bound_same_continuous
 100%Z 101%Z 102%Z 103%Z 105%Z 106%Z 108%Z 109%Z 112%Z 110%Z 111%Z
 92%positive 81%positive 80%positive 91%positive 82%positive 93%positive 94%positive 95%positive
 99%positive 96%positive 97%positive nil 16 0 4 RTentries OwnershipTasks emp Int.zero
 (V293_byteval 88)(Vptr OwnershipReady)Int.zero BDspec 301%Z 300%Z QCintspec 0(fun _:hid=>false)nil
 OwnershipReady BSret Int.zero);try reflexivity.
 - exact SCvalid.
 - vm_compute;repeat constructor.
 - unfold INUM;rewrite Int.unsigned_zero;cbn;lia.
Qed.
Theorem BCnonempty_actual_wrapper : exists M Mf O Of,
 join M Mf(JBmemory 0 Int.zero Int.zero) /\join O Of(RIabstract OwnershipWaiting) /\
 CCstate M O|=CCentry /\
 InfRules BDspec V293_scheduler LDli RDinv arfalse BCret
 CCentry(V293_irq_source_wrapper 301%Z 300%Z Int.zero)Afalse OwnershipWaiting.
Proof.
 destruct BCtyped_entry_nonempty as(M&Mf&O&Of&JM&JO&H).
 exists M;exists Mf;exists O;exists Of;split;[exact JM| ];split;[exact JO| ];split;[exact H|apply BCactual_wrapper].
Qed.
Theorem BSnonempty_actual_wrapper : exists M Mf O Of,
 join M Mf(SCmemory 0 Int.zero Int.zero) /\join O Of(RIabstract OwnershipReady) /\
 SCirq_state M O|=SCentry /\
 InfRules BDspec V293_scheduler LDli RDinv arfalse BSret
 SCentry(V293_irq_source_wrapper 301%Z 300%Z Int.zero)Afalse OwnershipReady.
Proof.
 destruct BStyped_entry_nonempty as(M&Mf&O&Of&JM&JO&H).
 exists M;exists Mf;exists O;exists Of;split;[exact JM| ];split;[exact JO| ];split;[exact H|apply BSactual_wrapper].
Qed.
Theorem BCreturn_literal : BCret =
 (<||spec_done None||> ** Aisr(isrupd(fun _:hid=>false)0 false) ** Ais (0::nil) ** Acs nil **
 (IRINV RDinv ** A_dom_lenv nil)) **p_local LDli OwnershipWaiting nil.
Proof. reflexivity. Qed.
Theorem BSreturn_literal : BSret =
 (<||spec_done None||> ** Aisr(isrupd(fun _:hid=>false)0 false) ** Ais (0::nil) ** Acs nil **
 (IRINV RDinv ** A_dom_lenv nil)) **p_local LDli OwnershipReady nil.
Proof. reflexivity. Qed.
Theorem BCreturn_forget : BCret ==>
 iretasrt' 0(fun _:hid=>false)nil RDinv **p_local V293_shared_li OwnershipWaiting nil.
Proof.
 unfold BCret,LDli;apply astar_mono;[intros s H;exact H|apply V293_bound_dispatch_forget].
Qed.
Theorem BSreturn_forget : BSret ==>
 iretasrt' 0(fun _:hid=>false)nil RDinv **p_local V293_shared_li OwnershipReady nil.
Proof.
 unfold BSret,LDli;apply astar_mono;[intros s H;exact H|apply V293_bound_dispatch_forget].
Qed.
Theorem BCreturn_nonempty : exists M Mf O Of,
 join M Mf(JBmemory 1 Int.zero Int.zero) /\join O Of(RIabstract OwnershipWaiting) /\
 BQreturned_state M O|=BCret.
Proof.
 destruct BQreturned_nonempty as(M&Mf&O&Of&JM&JO&Snapshot&Return).
 exists M;exists Mf;exists O;exists Of;split;[exact JM| ];split;assumption.
Qed.
Theorem BCabstract_entry_differs :
 BCintspec 0=Some(sched;;spec_done None) /\QCintspec 0=Some(spec_done None) /\
 BCintspec 0<>QCintspec 0.
Proof. split;[reflexivity| ];split;[reflexivity|discriminate]. Qed.
Theorem BCruntime_unchanged :
 V293_irq_source_wrapper 301%Z 300%Z Int.zero=
 sseq(sprim(eoi Int.zero))(sseq(scall 301%Z nil)(sseq(scall 300%Z nil)(sprim exint))) /\
 RDprogram 300%Z=XIprogram 300%Z.
Proof. split;reflexivity. Qed.
