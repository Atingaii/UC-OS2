(* Open the actual interrupt builder without guessing any control byte. *)
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptQuietContinuous.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptReadyBoundary.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptReadyEnvironment.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptReadyEnter.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptReadyLocal.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntEnterOpenExact.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitQuietExact.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitUnifiedInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntEnterInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedSwitch.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitReadyDynamic.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyStorageInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyTaskInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchStorage.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchState.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Require Import CertiOS.audit.probes.V293InterruptQuietContinuousProbe.
Require Import CertiOS.audit.probes.V293OSIntExitReadyBodyProbe.
Require Import CertiOS.audit.probes.V293OSIntExitReadyDynamicProbe.
Require Import CertiOS.audit.probes.V293ReadyTaskInvariantProbe.
Require Import CertiOS.audit.probes.V293TaskRecordOwnershipProbe.
Require Import CertiOS.audit.probes.V293TaskRecordInvariantProbe.
Require Import CertiOS.audit.probes.V293InterruptReadyEnvironmentProbe.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptEntryControl.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedStoragePrefix.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.framework.proof.toptheorem.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.framework.proof.rulesoundlib.
Require Import CertiOS.tactics.basetac.join_lib.
Require Import CertiOS.tactics.basetac.join_general.

Local Open Scope nat_scope.
Definition ECglobals:=V293_quiet_globals 112%Z 110%Z 111%Z 99%positive 96%positive 97%positive.
Definition ECpre:=ipreasrt' 0(fun _:hid=>false)nil(spec_done None)RDinv **
 p_local V293_shared_li OwnershipWaiting nil.
Definition ECentry:=ECpre ** ECglobals.
Definition ECpost:=V293_irq_entry_after_enter
 106%Z 112%Z 110%Z 111%Z 92%positive 81%positive 80%positive 91%positive 82%positive
 94%positive 95%positive 99%positive 96%positive 97%positive nil
 0 nil(spec_done None)OwnershipWaiting.

Lemma ECbuilder :
 Some ECpre=BuildintPre 0 QCintspec(fun _:hid=>false)nil RDinv V293_shared_li OwnershipWaiting nil.
Proof. reflexivity. Qed.

(* This is an actual builder precondition, not only a stronger snapshot. *)
Lemma ECsnapshot_to_builder : forall M O,QCstate M O|=QCentry ->QCstate M O|=ECentry.
Proof.
 intros M O H.
 unfold QCentry,V293_quiet_irq_snapshot,V293_enter_open_external,V293_quiet_irq_kept in H.
 assert(P:QCstate M O|=
 (Amapsto(99%positive,0%Z)Tint8 true(V293_byteval 1) **
 (Amapsto(96%positive,0%Z)Tint8 true(V293_byteval 1) **
 Amapsto(97%positive,0%Z)Tint8 true(V293_byteval 0))) **
 (<||spec_done None||> ** OS[isrupd(fun _:hid=>false)0 true,false,[0],nil] **
 (V293ReadyTaskInvariant.V293_ready_core 80%positive 81%positive 82%positive **
 (V293_dispatch_cell 106%Z V293_tcb_type **
 (V293_storage(V293_ready_irq_prefix 92%positive 91%positive 94%positive 95%positive) **
 (V293_storage nil ** A_dom_lenv nil ** p_local V293_shared_li OwnershipWaiting nil ** ECglobals))))))by(unfold ECglobals;sep auto).
 eapply astar_mono in P;[ |apply astar_mono;[apply V293_storage_byte_close;lia|apply astar_mono;apply V293_storage_byte_close;lia]|intros s K;exact K].
 assert(P2:QCstate M O|=
 (V293_storage(V293_ready_irq_prefix 92%positive 91%positive 94%positive 95%positive) **
 V293_storage([((99%positive,0%Z),Tint8);((96%positive,0%Z),Tint8);((97%positive,0%Z),Tint8)]++nil)) **
 (<||spec_done None||> ** OS[isrupd(fun _:hid=>false)0 true,false,[0],nil] **
 (V293ReadyTaskInvariant.V293_ready_core 80%positive 81%positive 82%positive **
 (V293_dispatch_cell 106%Z V293_tcb_type **
 (A_dom_lenv nil ** p_local V293_shared_li OwnershipWaiting nil ** ECglobals)))))by(cbn[app V293_storage];clear H;sep auto).
 eapply astar_mono in P2;[ |apply V293_storage_append|intros s K;exact K].
 assert(Core:QCstate M O|=getinv(RDinv 0) **
 (<||spec_done None||> ** OS[isrupd(fun _:hid=>false)0 true,false,[0],nil] **
 (A_dom_lenv nil ** p_local V293_shared_li OwnershipWaiting nil ** ECglobals))).
 { change(getinv(RDinv 0))with(V293_ready_storage_core 80%positive 81%positive 82%positive 106%Z V293_tcb_type JBcells).
   unfold V293_ready_storage_core,V293_ready_storage_extra,JBcells,V293_ready_irq_prefix in *.
   rewrite app_nil_r in P2;clear H P;sep auto. }
 assert(Z:(JBge,emp,empmem,isrupd(fun _:hid=>false)0 true,(false,[0],nil),empabst,spec_done None)|=isr_inv).
 { unfold isr_inv;exists(isrupd(fun _:hid=>false)0 true);split.
   - simpl;repeat split;reflexivity.
   - exists 0;split.
     + simpl;repeat split;reflexivity.
     + apply apure_intro;[split;reflexivity|intros;lia]. }
 assert(All:QCstate M O|=isr_inv ** (getinv(RDinv 0) **
 (<||spec_done None||> ** OS[isrupd(fun _:hid=>false)0 true,false,[0],nil] **
 (A_dom_lenv nil ** p_local V293_shared_li OwnershipWaiting nil ** ECglobals)))).
 { unfold QCstate;apply sat_split';exists empmem;exists M;exists empabst;exists O.
   split;[apply join_emp| ];split;[apply join_emp| ];split;assumption. }
 unfold ECentry,ECpre,ipreasrt',invlth_noisr;cbn[starinv_noisr Nat.sub].
 clear H P P2 Core Z;sep auto.
Qed.

Theorem ECentry_nonempty : exists M Mf O Of,
 join M Mf(JBmemory 1 Int.zero Int.zero) /\ join O Of(RIabstract OwnershipWaiting) /\
 QCstate M O|=ECentry.
Proof.
 destruct QCentry_nonempty as(M&Mf&O&Of&JM&JO&H).
 exists M;exists Mf;exists O;exists Of;split;[exact JM| ];split;[exact JO| ].
 apply ECsnapshot_to_builder;exact H.
Qed.

Theorem ECenvironment : GoodI RDinv V293_scheduler V293_shared_li /\
 WFFunEnv RDprogram QCspec V293_scheduler V293_shared_li RDinv /\
 WFIFun RDprogram QCspec V293_scheduler RDinv V293_shared_li.
Proof. exact QCenvironment. Qed.

Theorem ECactual_prefix : forall r ri,
 InfRules QCspec V293_scheduler V293_shared_li RDinv r ri ECentry
 (sseq(sprim(eoi Int.zero))(scall 301%Z nil))ECpost OwnershipWaiting.
Proof.
 intros r ri;unfold ECentry,ECpost.
 apply(V293_interrupt_entry_control
 106%Z 112%Z 110%Z 111%Z 92%positive 81%positive 80%positive 91%positive 82%positive
 94%positive 95%positive 99%positive 96%positive 97%positive nil
 QCspec V293_scheduler r ri 301%Z QCintspec 0(fun _:hid=>false)nil(spec_done None)
 OwnershipWaiting nil ECpre Int.zero);try reflexivity.
 unfold INUM;rewrite Int.unsigned_zero;cbn;lia.
Qed.

Lemma ECincrement : V293_interrupt_nest_after 1 254=255.
Proof. reflexivity. Qed.
Lemma ECsaturated : V293_interrupt_nest_after 1 255=255.
Proof. reflexivity. Qed.
Lemma ECnotrunning : V293_interrupt_nest_after 0 254=254.
Proof. reflexivity. Qed.
Lemma ECnot_zero_initial : V293_interrupt_nest_after 1 1=2.
Proof. reflexivity. Qed.
