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
Require Import CertiOS.certiucos.v293.proofs.V293InterruptBindings.
Require Import CertiOS.audit.probes.V293InterruptEntryGeneralProbe.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordInvariant.
Local Open Scope nat_scope.
Definition EBli:=V293_irq_bound_li 112%Z 110%Z 111%Z 99%positive 96%positive 97%positive.
Definition EBspec:=V293_enter_bound_spec 112%Z 110%Z 111%Z 99%positive 96%positive 97%positive Aemp Logic.I 301%Z.
Definition EBprogram:=V293_OSIntEnter_unit 301%Z 112%Z 110%Z.
Definition EBpre:=ipreasrt' 0 EGprior [1](spec_done None)RDinv **p_local EBli OwnershipWaiting nil.
Definition EBpost:=V293_irq_bound_after
 106%Z 112%Z 110%Z 111%Z 92%positive 81%positive 80%positive 91%positive 82%positive
 94%positive 95%positive 99%positive 96%positive 97%positive nil
 0 EGprior [1](spec_done None)OwnershipWaiting.
Lemma EBbuilder : Some EBpre=BuildintPre 0 QCintspec EGprior [1]RDinv EBli OwnershipWaiting nil.
Proof. reflexivity. Qed.
Lemma EBentry_pack : EGentry ==>EBpre.
Proof.
 intros st H;unfold EGentry,EGpre in H;unfold EBpre,EBli.
 assert(B:st |=ipreasrt' 0 EGprior [1](spec_done None)RDinv **
 (p_local V293_shared_li OwnershipWaiting nil ** ECglobals))by(sep auto).
 eapply astar_mono in B;[ |intros s K;exact K|apply V293_irq_bound_local_close];exact B.
Qed.
Theorem EBentry_nonempty : exists M Mf O Of,
 join M Mf(JBmemory 1 Int.zero Int.zero) /\ join O Of(RIabstract OwnershipWaiting) /\
 EGstate M O|=EBpre.
Proof.
 destruct EGentry_nonempty as(M&Mf&O&Of&JM&JO&H).
 exists M;exists Mf;exists O;exists Of;split;[exact JM| ];split;[exact JO| ].
 apply EBentry_pack;exact H.
Qed.
Theorem EBenvironment : GoodI RDinv V293_scheduler EBli /\
 WFFunEnv EBprogram EBspec V293_scheduler EBli RDinv /\
 WFIFun EBprogram EBspec V293_scheduler RDinv EBli.
Proof.
 split.
 - apply V293_irq_bound_GoodI;exact(proj1 EGenvironment).
 - split;[apply V293_OSIntEnter_bound_WFFunEnv|apply V293_OSIntEnter_bound_WFIFun].
Qed.
Lemma EBsame_Enter_body : EBprogram 301%Z=RDprogram 301%Z.
Proof. reflexivity. Qed.
Theorem EBactual_prefix : forall r ri,
 InfRules EBspec V293_scheduler EBli RDinv r ri EBpre
 (sseq(sprim(eoi Int.zero))(scall 301%Z nil))EBpost OwnershipWaiting.
Proof.
 intros r ri;unfold EBpost.
 apply(V293_interrupt_bound_entry
 106%Z 112%Z 110%Z 111%Z 92%positive 81%positive 80%positive 91%positive 82%positive
 94%positive 95%positive 99%positive 96%positive 97%positive nil
 EBspec V293_scheduler r ri 301%Z QCintspec 0 EGprior [1](spec_done None)
 OwnershipWaiting nil EBpre Int.zero);try reflexivity.
 unfold INUM;rewrite Int.unsigned_zero;cbn;lia.
Qed.

(* Only one global binding changes. The entire heap, abstract map, and ISR
   metadata are fixed. This is assertion separation, not two executions. *)
Definition EBbadge:env:=set JBge 112%Z(100%positive,Tint8).
Definition EBbadstate M O:RstateOP:=(EBbadge,emp,M,EGactive,(false,[0;1],nil),O,spec_done None).
Definition EBstable(p:asrt):Prop:=forall le M ir aux O op,
 (JBge,le,M,ir,aux,O,op)|=p ->(EBbadge,le,M,ir,aux,O,op)|=p.
Lemma EBstar : forall p q,EBstable p ->EBstable q ->EBstable(p ** q).
Proof.
 intros p q P Q le M ir aux O op H;apply sat_split in H.
 destruct H as(m1&m2&o1&o2&JM&JO&Hp&Hq).
 apply sat_split';exists m1;exists m2;exists o1;exists o2.
 split;[exact JM| ];split;[exact JO| ];split;[apply P|apply Q];assumption.
Qed.
Lemma EBnamed : forall x tau permission v,x<>112%Z ->EBstable(Agvarmapsto x tau permission v).
Proof.
 intros x tau permission v Apart le M ir aux O op [b H];exists b.
 eapply EBstar;[ |intros l m r a o z K;exact K|exact H].
 intros l m r a o z K;apply agvarenv_elim in K.
 destruct K as[[Offset G] Empty];apply agvarenv_intro;[exact Empty| ].
 split;[exact Offset| ].
 change(get(set JBge 112%Z(100%positive,Tint8))x=Some(b,tau)).
 rewrite map_get_set';[exact G|congruence].
Qed.
Lemma EBcurrent : forall t,EBstable(CurTid t).
Proof.
 intros t le M ir aux O op [tau H];exists tau.
 eapply EBnamed;[unfold OSTCBCur;discriminate|exact H].
Qed.
Lemma EBstorage : forall cells,EBstable(V293_storage cells).
Proof.
 induction cells as [ |[a tau] cells IH];[intros le M ir aux O op H;exact H| ].
 cbn[V293_storage];apply EBstar;[ |exact IH].
 intros le M ir aux O op [v H];exists v;exact H.
Qed.
Lemma EBready : forall br bg bp,EBstable(V293ReadyTaskInvariant.V293_ready_core br bg bp).
Proof.
 intros br bg bp le M ir aux O op [t[ts[es[now H]]]].
 exists t;exists ts;exists es;exists now.
 unfold V293_shared_ready_records in *;eapply EBstar;[ | |exact H].
 - apply EBstar;[apply EBcurrent|intros l m r a o z K;exact K].
 - intros l m r a o z K;eapply V293_ready_payload_context;exact K.
Qed.
Lemma EBcore : EBstable(getinv(RDinv 0)).
Proof.
 change(EBstable(V293_ready_storage_core 80%positive 81%positive 82%positive 106%Z V293_tcb_type JBcells)).
 unfold V293_ready_storage_core,V293_ready_storage_extra;apply EBstar;[apply EBready| ].
 apply EBstar;[ |apply EBstorage].
 intros le M ir aux O op [v H];exists v.
 unfold V293_dispatch_cell in H;eapply EBstar;[intros l m r a o z K;exact K| |exact H].
 apply EBnamed;discriminate.
Qed.
Lemma EBweak_builder_stable : EBstable EGpre.
Proof.
 unfold EGpre;apply EBstar.
 - unfold ipreasrt',invlth_noisr;cbn[starinv_noisr Nat.sub].
   do 6(apply EBstar;[intros l m r a o z K;exact K| ]).
   apply EBstar;[apply EBcore|intros l m r a o z K;exact K].
 - unfold p_local,LINV;apply EBstar;[apply EBcurrent|intros l m r a o z K;exact K].
Qed.
Theorem EBbad_weak_builder_nonempty : exists M Mf O Of,
 join M Mf(JBmemory 1 Int.zero Int.zero) /\ join O Of(RIabstract OwnershipWaiting) /\
 EGstate M O|=EBpre /\ EBbadstate M O|=EGpre.
Proof.
 destruct EGentry_nonempty as(M&Mf&O&Of&JM&JO&H).
 exists M;exists Mf;exists O;exists Of;split;[exact JM| ];split;[exact JO| ];split.
 - apply EBentry_pack;exact H.
 - assert(Weak:EGstate M O|=EGpre).
   { unfold EGentry in H;assert(Z:ECglobals ==>Aemp).
     { intros s [G _];apply agvarenv_elim in G;exact(proj2 G). }
     eapply astar_mono in H;[ |intros s K;exact K|exact Z].
     apply astar_r_aemp_elim in H;exact H. }
   exact(EBweak_builder_stable emp M EGactive(false,[0;1],nil)O(spec_done None)Weak).
Qed.
Theorem EBbad_bound_builder_rejected : forall M O,~(EBbadstate M O|=EBpre).
Proof.
 intros M O H.
 assert(B:EBbadstate M O|=ECglobals ** Atrue).
 { unfold EBpre,p_local,LINV,EBli,V293_irq_bound_li in H;sep auto. }
 assert(G:EnvMod.get EBbadge 112%Z=Some(99%positive,Tint8)).
 { change(EnvMod.get(getgenv(EBbadstate M O))112%Z=Some(99%positive,Tint8)).
   eapply V293_star_env_l with(E:=fun ge le=>EnvMod.get ge 112%Z=Some(99%positive,Tint8));[ |exact B].
   intros s [R _];apply agvarenv_elim in R;exact(proj2(proj1 R)). }
 change(Some(100%positive,Tint8)=Some(99%positive,Tint8))in G;discriminate.
Qed.
Lemma EBsingle_changed_binding : forall x,x<>112%Z ->get EBbadge x=get JBge x.
Proof. intros x H;unfold EBbadge;apply map_get_set';congruence. Qed.
