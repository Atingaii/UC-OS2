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
Require Import CertiOS.audit.probes.V293InterruptEntryControlProbe.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptEntryGeneral.
Require Import Coq.Logic.FunctionalExtensionality.
Local Open Scope nat_scope.
(* Same byte heap and function environment; only ISR metadata changes. *)
Definition EGprior:isr:=isrupd(fun _:hid=>false)1 true.
Definition EGactive:isr:=isrupd EGprior 0 true.
Definition EGstate M O:RstateOP:=(JBge,emp,M,EGactive,
 (false,[0;1],nil),O,spec_done None).
Definition EGsnapshot:=V293_quiet_irq_snapshot
 106%Z 112%Z 110%Z 111%Z 92%positive 81%positive 80%positive 91%positive 82%positive
 94%positive 95%positive 99%positive 96%positive 97%positive nil
 1 1 0(spec_done None)false EGactive [0;1]nil OwnershipWaiting.
Definition EGpre:=ipreasrt' 0 EGprior [1](spec_done None)RDinv **
 p_local V293_shared_li OwnershipWaiting nil.
Definition EGentry:=EGpre ** ECglobals.
Definition EGpost:=V293_irq_entry_general_after
 106%Z 112%Z 110%Z 111%Z 92%positive 81%positive 80%positive 91%positive 82%positive
 94%positive 95%positive 99%positive 96%positive 97%positive nil
 0 EGprior [1](spec_done None)OwnershipWaiting.
Lemma EGbuilder : Some EGpre=BuildintPre 0 QCintspec EGprior [1]
 RDinv V293_shared_li OwnershipWaiting nil.
Proof. reflexivity. Qed.
Theorem EGsnapshot_nonempty : exists M Mf O Of,
 join M Mf(JBmemory 1 Int.zero Int.zero) /\ join O Of(RIabstract OwnershipWaiting) /\
 EGstate M O|=EGsnapshot.
Proof.
 pose proof QCraw_heap as H;unfold JBstate in H.
 assert(Moved:(JBge,emp,JBmemory 1 Int.zero Int.zero,(fun _:hid=>false),
 (false,nil,nil),RIabstract OwnershipWaiting,spec_done None)|=QCraw ** Atrue).
 { eapply good_inv_prop;[split;[exact(proj1 QCraw_good)|exact Logic.I]|exact H]. }
 assert(New:EGstate(JBmemory 1 Int.zero Int.zero)(RIabstract OwnershipWaiting)|=QCraw ** Atrue).
 { unfold EGstate;eapply goodfrm_prop;[split;[exact(proj2 QCraw_good)|exact Logic.I]|exact Moved]. }
 apply sat_split in New;destruct New as(M&Mf&O&Of&JM&JO&Owned&Extra).
 exists M;exists Mf;exists O;exists Of;split;[exact JM| ];split;[exact JO| ].
 assert(G:(JBge,emp,empmem,EGactive,(false,[0;1],nil),empabst,spec_done None)|=
 V293_quiet_globals 112%Z 110%Z 111%Z 99%positive 96%positive 97%positive).
 { unfold V293_quiet_globals;repeat split;apply agvarenv_intro;
 split;reflexivity. }
 assert(Pack:EGstate M O|=V293_quiet_globals 112%Z 110%Z 111%Z 99%positive 96%positive 97%positive ** QCraw).
 { unfold EGstate;apply sat_split';exists empmem;exists M;exists empabst;exists O.
 split;[apply join_emp| ];split;[apply join_emp| ];split;assumption. }
 apply astar_l_adomlenv_intro with(d:=nil)in Pack.
 2:{ intros x tau;split;[contradiction|intros[l E];discriminate]. }
 apply astar_l_aisr_intro with(i:=EGactive)in Pack;[ |reflexivity].
 apply astar_l_aie_intro with(i:=false)in Pack;[ |reflexivity].
 apply astar_l_ais_intro with(i:=[0;1])in Pack;[ |reflexivity].
 apply astar_l_acs_intro with(i:=nil)in Pack;[ |reflexivity].
 apply astar_l_aop'_intro with(aop:=spec_done None)in Pack;[ |reflexivity].
 unfold EGsnapshot,V293_quiet_irq_snapshot,V293_enter_open_external,QCraw,QCkept,
 p_local,LINV,V293_shared_li in *;clear H Moved Owned Extra;sep auto;apply V293_switch_li_good.
Qed.
Lemma EGsnapshot_to_builder : forall M O,EGstate M O|=EGsnapshot ->EGstate M O|=EGentry.
Proof.
 intros M O H.
 unfold EGsnapshot,V293_quiet_irq_snapshot,V293_enter_open_external,V293_quiet_irq_kept in H.
 assert(P:EGstate M O|=
 (Amapsto(99%positive,0%Z)Tint8 true(V293_byteval 1) **
 (Amapsto(96%positive,0%Z)Tint8 true(V293_byteval 1) **
 Amapsto(97%positive,0%Z)Tint8 true(V293_byteval 0))) **
 (<||spec_done None||> ** OS[EGactive,false,[0;1],nil] **
 (V293ReadyTaskInvariant.V293_ready_core 80%positive 81%positive 82%positive **
 (V293_dispatch_cell 106%Z V293_tcb_type **
 (V293_storage(V293_ready_irq_prefix 92%positive 91%positive 94%positive 95%positive) **
 (V293_storage nil ** A_dom_lenv nil ** p_local V293_shared_li OwnershipWaiting nil ** ECglobals))))))by(unfold ECglobals;sep auto).
 eapply astar_mono in P;[ |apply astar_mono;[apply V293_storage_byte_close;lia|apply astar_mono;apply V293_storage_byte_close;lia]|intros s K;exact K].
 assert(P2:EGstate M O|=
 (V293_storage(V293_ready_irq_prefix 92%positive 91%positive 94%positive 95%positive) **
 V293_storage([((99%positive,0%Z),Tint8);((96%positive,0%Z),Tint8);((97%positive,0%Z),Tint8)]++nil)) **
 (<||spec_done None||> ** OS[EGactive,false,[0;1],nil] **
 (V293ReadyTaskInvariant.V293_ready_core 80%positive 81%positive 82%positive **
 (V293_dispatch_cell 106%Z V293_tcb_type **
 (A_dom_lenv nil ** p_local V293_shared_li OwnershipWaiting nil ** ECglobals)))))by(cbn[app V293_storage];clear H;sep auto).
 eapply astar_mono in P2;[ |apply V293_storage_append|intros s K;exact K].
 assert(Core:EGstate M O|=getinv(RDinv 0) **
 (<||spec_done None||> ** OS[EGactive,false,[0;1],nil] **
 (A_dom_lenv nil ** p_local V293_shared_li OwnershipWaiting nil ** ECglobals))).
 { change(getinv(RDinv 0))with(V293_ready_storage_core 80%positive 81%positive 82%positive 106%Z V293_tcb_type JBcells).
   unfold V293_ready_storage_core,V293_ready_storage_extra,JBcells,V293_ready_irq_prefix in *.
   rewrite app_nil_r in P2;clear H P;sep auto. }
 assert(Z:(JBge,emp,empmem,EGactive,(false,[0;1],nil),empabst,spec_done None)|=isr_inv).
 { unfold isr_inv;exists(EGactive);split.
   - simpl;repeat split;reflexivity.
   - exists 0;split.
     + simpl;repeat split;reflexivity.
     + apply apure_intro;[split;reflexivity|intros;lia]. }
 assert(All:EGstate M O|=isr_inv ** (getinv(RDinv 0) **
 (<||spec_done None||> ** OS[EGactive,false,[0;1],nil] **
 (A_dom_lenv nil ** p_local V293_shared_li OwnershipWaiting nil ** ECglobals)))).
 { unfold EGstate;apply sat_split';exists empmem;exists M;exists empabst;exists O.
   split;[apply join_emp| ];split;[apply join_emp| ];split;assumption. }
 unfold EGentry,EGpre,ipreasrt',invlth_noisr;cbn[starinv_noisr Nat.sub].
 clear H P P2 Core Z;sep auto.
Qed.

Theorem EGentry_nonempty : exists M Mf O Of,
 join M Mf(JBmemory 1 Int.zero Int.zero) /\ join O Of(RIabstract OwnershipWaiting) /\
 EGstate M O|=EGentry.
Proof.
 destruct EGsnapshot_nonempty as(M&Mf&O&Of&JM&JO&H).
 exists M;exists Mf;exists O;exists Of;split;[exact JM| ];split;[exact JO| ].
 apply EGsnapshot_to_builder;exact H.
Qed.

Theorem EGenvironment : GoodI RDinv V293_scheduler V293_shared_li /\
 WFFunEnv RDprogram QCspec V293_scheduler V293_shared_li RDinv /\
 WFIFun RDprogram QCspec V293_scheduler RDinv V293_shared_li.
Proof. exact ECenvironment. Qed.

Theorem EGactual_prefix : forall r ri,
 InfRules QCspec V293_scheduler V293_shared_li RDinv r ri EGentry
 (sseq(sprim(eoi Int.zero))(scall 301%Z nil))EGpost OwnershipWaiting.
Proof.
 intros r ri;unfold EGentry,EGpost.
 apply(V293_interrupt_entry_general
 106%Z 112%Z 110%Z 111%Z 92%positive 81%positive 80%positive 91%positive 82%positive
 94%positive 95%positive 99%positive 96%positive 97%positive nil
 QCspec V293_scheduler r ri 301%Z QCintspec 0 EGprior [1](spec_done None)
 OwnershipWaiting nil EGpre Int.zero);try reflexivity.
 unfold INUM;rewrite Int.unsigned_zero;cbn;lia.
Qed.

Lemma EGnot_all_clear : ~(forall j,EGprior j=false).
Proof. intro H;specialize(H 1);discriminate. Qed.
Lemma EGother_active_survives : isrupd EGactive 0 false 1=true.
Proof. reflexivity. Qed.
Lemma EGEOI_exact : isrupd EGactive 0 false=EGprior.
Proof.
 apply functional_extensionality;intro j.
 unfold EGactive,EGprior,isrupd.
 destruct j as [ | j];reflexivity.
Qed.
Lemma EGmetadata_depth : forall M O,length(get_is_s(EGstate M O))=2.
Proof. reflexivity. Qed.

(* This heap-only bound is legal: the negative result is not a ban on all
   nesting constraints, nor a counterexample to framework soundness. *)
Lemma EGheap_only_bound_closure : forall n,assertion.inv_isr_prop ([|n<256|]).
Proof.
 intro n;unfold assertion.inv_isr_prop;split;[ |split;[ |split]];intros;
 destruct s as [[[[[[ge le] M] ir] [[ie si] cs]] O] op];exact H.
Qed.

Lemma EGsnapshot_load_nest : forall M O,EGstate M O|=EGsnapshot ->
 load Tint8 M(96%positive,0%Z)=Some(V293_byteval 1).
Proof.
 intros M O H.
 assert(P:EGstate M O|=Amapsto(96%positive,0%Z)Tint8 true(V293_byteval 1) ** Atrue).
 { unfold EGsnapshot,V293_quiet_irq_snapshot,V293_enter_open_external in H;sep auto. }
 change(load Tint8(getmem(EGstate M O))(96%positive,0%Z)=Some(V293_byteval 1)).
 eapply V293_star_load_l;[ |exact P].
 intros s K;eapply V293_mapsto_load;[lia|exact K].
Qed.

Theorem EGbuilder_allows_depth_mismatch : exists M Mf O Of,
 join M Mf(JBmemory 1 Int.zero Int.zero) /\ join O Of(RIabstract OwnershipWaiting) /\
 EGstate M O|=EGentry /\ load Tint8 M(96%positive,0%Z)=Some(V293_byteval 1) /\
 length(get_is_s(EGstate M O))<>1.
Proof.
 destruct EGsnapshot_nonempty as(M&Mf&O&Of&JM&JO&H).
 exists M;exists Mf;exists O;exists Of;split;[exact JM| ];split;[exact JO| ];split.
 - apply EGsnapshot_to_builder;exact H.
 - split;[apply EGsnapshot_load_nest with(O:=O);exact H| ].
   rewrite EGmetadata_depth;lia.
Qed.
