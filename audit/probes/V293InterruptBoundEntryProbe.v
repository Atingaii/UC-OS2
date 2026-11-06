Require Import CertiOS.certiucos.v293.proofs.V293InterruptSourceRoundtrip.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptReadyBoundary.
Require Import CertiOS.audit.probes.V293InterruptBoundDispatchContinuousProbe.
Require Import CertiOS.audit.probes.V293InterruptChangedContinuousProbe.
Require Import CertiOS.audit.probes.V293InterruptSameContinuousProbe.
Require Import CertiOS.audit.probes.V293InterruptQuietContinuousProbe.
Require Import CertiOS.audit.probes.V293OSIntExitReadyDynamicProbe.
Require Import CertiOS.audit.probes.V293OSIntExitReadyBodyProbe.
Require Import CertiOS.audit.probes.V293OSIntExitLocalDispatchProbe.
Require Import CertiOS.audit.probes.V293OSIntExitBoundDynamicProbe.
Require Import CertiOS.audit.probes.V293ReadyTaskInvariantProbe.
Require Import CertiOS.audit.probes.V293TaskRecordOwnershipProbe.
Require Import CertiOS.audit.probes.V293TaskRecordInvariantProbe.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptBoundEntry.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.
Lemma BEchanged_builder : forall M O,CCstate M O|=CCentry ->CCstate M O|=BCpre.
Proof.
 intros M O H;unfold CCentry in H.
 apply(V293_changed_entry_BuildintPre
 100%Z 101%Z 102%Z 103%Z 105%Z 106%Z 108%Z 109%Z 112%Z 110%Z 111%Z
 92%positive 81%positive 80%positive 91%positive 82%positive 93%positive 94%positive 95%positive
 99%positive 96%positive 97%positive nil 16 0 6 RTentries OwnershipTasks emp Int.zero
 (V293_byteval 88)(Vptr OwnershipWaiting)Int.zero 0(spec_done None)(fun _:hid=>false)nil
 OwnershipWaiting BCintspec BCpre);try reflexivity;try lia.
 - exact RTliteral_rel.
 - vm_compute;repeat constructor.
 - exact H.
Qed.
Theorem BEchanged_same_state : exists M Mf O Of,
 join M Mf(JBmemory 0 Int.zero Int.zero) /\join O Of(RIabstract OwnershipWaiting) /\
 CCstate M O|=CCentry /\CCstate M O|=BCpre /\
 InfRules BDspec V293_scheduler LDli RDinv arfalse BCret
 CCentry(V293_irq_source_wrapper 301%Z 300%Z Int.zero)Afalse OwnershipWaiting.
Proof.
 destruct BCtyped_entry_nonempty as(M&Mf&O&Of&JM&JO&H).
 exists M;exists Mf;exists O;exists Of;split;[exact JM| ];split;[exact JO| ];split;[exact H| ];split.
 - apply BEchanged_builder;exact H.
 - apply BCactual_wrapper.
Qed.
Lemma BEsame_builder : forall M O,SCirq_state M O|=SCentry ->SCirq_state M O|=BSpre.
Proof.
 intros M O H;unfold SCentry in H.
 apply(V293_same_entry_BuildintPre
 100%Z 101%Z 102%Z 103%Z 105%Z 106%Z 108%Z 109%Z 112%Z 110%Z 111%Z
 92%positive 81%positive 80%positive 91%positive 82%positive 93%positive 94%positive 95%positive
 99%positive 96%positive 97%positive nil 16 0 4 RTentries OwnershipTasks emp Int.zero
 (V293_byteval 88)(Vptr OwnershipReady)Int.zero 0(spec_done None)(fun _:hid=>false)nil
 OwnershipReady QCintspec BSpre);try reflexivity;try lia.
 - exact RTliteral_rel.
 - vm_compute;repeat constructor.
 - exact H.
Qed.
Theorem BEsame_same_state : exists M Mf O Of,
 join M Mf(SCmemory 0 Int.zero Int.zero) /\join O Of(RIabstract OwnershipReady) /\
 SCirq_state M O|=SCentry /\SCirq_state M O|=BSpre /\
 InfRules BDspec V293_scheduler LDli RDinv arfalse BSret
 SCentry(V293_irq_source_wrapper 301%Z 300%Z Int.zero)Afalse OwnershipReady.
Proof.
 destruct BStyped_entry_nonempty as(M&Mf&O&Of&JM&JO&H).
 exists M;exists Mf;exists O;exists Of;split;[exact JM| ];split;[exact JO| ];split;[exact H| ];split.
 - apply BEsame_builder;exact H.
 - apply BSactual_wrapper.
Qed.
Lemma BEbuilder_operation : forall i ir si aop Inv0 li t lg st,
 st|=ipreasrt' i ir si aop Inv0 **p_local li t lg ->getabsop st=aop.
Proof.
 intros i ir si aop Inv0 li t lg st H;unfold ipreasrt' in H.
 assert(K:st|=<||aop||> **Atrue)by(sep auto).
 apply astar_l_aop'_elim in K;exact(proj1 K).
Qed.
Definition BEchanged_wrong:=ipreasrt' 0(fun _:hid=>false)nil(spec_done None)RDinv **p_local LDli OwnershipWaiting nil.
Definition BEsame_wrong:=ipreasrt' 0(fun _:hid=>false)nil(sched;;spec_done None)RDinv **p_local LDli OwnershipReady nil.
Theorem BEchanged_operation_control :
 Some BEchanged_wrong=BuildintPre 0 QCintspec(fun _:hid=>false)nil RDinv LDli OwnershipWaiting nil /\
 exists M Mf O Of,join M Mf(JBmemory 0 Int.zero Int.zero) /\join O Of(RIabstract OwnershipWaiting) /\
 CCstate M O|=CCentry /\CCstate M O|=BCpre /\~CCstate M O|=BEchanged_wrong.
Proof.
 split;[reflexivity| ];destruct BEchanged_same_state as(M&Mf&O&Of&JM&JO&H&B&W).
 exists M;exists Mf;exists O;exists Of;split;[exact JM| ];split;[exact JO| ];split;[exact H| ];split;[exact B| ].
 intro Wrong;unfold BEchanged_wrong in Wrong;apply BEbuilder_operation in Wrong;discriminate.
Qed.
Theorem BEsame_operation_control :
 Some BEsame_wrong=BuildintPre 0 BCintspec(fun _:hid=>false)nil RDinv LDli OwnershipReady nil /\
 exists M Mf O Of,join M Mf(SCmemory 0 Int.zero Int.zero) /\join O Of(RIabstract OwnershipReady) /\
 SCirq_state M O|=SCentry /\SCirq_state M O|=BSpre /\~SCirq_state M O|=BEsame_wrong.
Proof.
 split;[reflexivity| ];destruct BEsame_same_state as(M&Mf&O&Of&JM&JO&H&B&W).
 exists M;exists Mf;exists O;exists Of;split;[exact JM| ];split;[exact JO| ];split;[exact H| ];split;[exact B| ].
 intro Wrong;unfold BEsame_wrong in Wrong;apply BEbuilder_operation in Wrong;discriminate.
Qed.
