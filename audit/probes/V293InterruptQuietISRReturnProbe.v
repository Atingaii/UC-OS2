(* Only an unrelated ISR bit changes; physical resources are identical. *)
Require Import CertiOS.audit.probes.V293InterruptQuietBuilderProbe.
Require Import CertiOS.audit.probes.V293InterruptBoundQuietContinuousProbe.
Require Import CertiOS.audit.probes.V293InterruptQuietContinuousProbe.
Require Import CertiOS.audit.probes.V293InterruptReadyEnvironmentProbe.
Require Import CertiOS.audit.probes.V293InterruptEntryControlProbe.
Require Import CertiOS.audit.probes.V293OSIntExitBoundDynamicProbe.
Require Import CertiOS.audit.probes.V293OSIntExitLocalDispatchProbe.
Require Import CertiOS.audit.probes.V293OSIntExitReadyBodyProbe.
Require Import CertiOS.audit.probes.V293OSIntExitReadyDynamicProbe.
Require Import CertiOS.audit.probes.V293TaskRecordInvariantProbe.
Require Import CertiOS.audit.probes.V293TaskRecordOwnershipProbe.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptQuietISRReturn.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptBoundEntry.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptQuietBuilder.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptBindings.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptQuietContinuous.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntEnterOpenExact.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntEnterInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitUnifiedInternal.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitNondispatch.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptSourceRoundtrip.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedSwitch.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptReadyBoundary.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.framework.proof.rulesoundlib.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.
Definition QKstate irq M O:RstateOP:=(JBge,emp,M,irq,(false,[0],nil),O,spec_done None).
Definition QKsnapshot nest irq:=BQsnapshot 1 nest 0(spec_done None)false irq[0]nil OwnershipWaiting.
Definition QKpre ir:=(ipreasrt' 0 ir nil(spec_done None)RDinv **p_local LDli OwnershipWaiting nil) //\\ QJfilter.
Definition QKret ir:=iretasrt' 0 ir nil RDinv **p_local LDli OwnershipWaiting nil.
Definition QKother:=isrupd(fun _:hid=>false)1 true.

Lemma QKsnapshot_change_isr : forall nest irq irq' M O,
 QKstate irq M O|=QKsnapshot nest irq ->
 QKstate irq' M O|=QKsnapshot nest irq'.
Proof.
 intros nest irq irq' M O H.
 assert(Empty:V293_quiet_globals 112%Z 110%Z 111%Z 99%positive 96%positive 97%positive ==>Aemp).
 { intros st [G _];apply agvarenv_elim in G;exact(proj2 G). }
 assert(RawPack:QKstate irq M O|=QJraw nest **V293_quiet_globals 112%Z 110%Z 111%Z 99%positive 96%positive 97%positive).
 { unfold QKsnapshot,BQsnapshot,V293_irq_bound_snapshot,V293_enter_bound_external,
 QJraw,QCkept,p_local,LINV,LDli,V293_irq_bound_li in *;sep auto. }
 eapply astar_mono in RawPack;[ |intros st H0;exact H0|exact Empty].
 assert(Raw:QKstate irq M O|=QJraw nest)by(sep auto).
 assert(Moved:QKstate irq' M O|=QJraw nest).
 { unfold QKstate in *;eapply goodfrm_prop;[exact(proj2(QJraw_good nest))|exact Raw]. }
 assert(G:(JBge,emp,empmem,irq',(false,[0],nil),empabst,spec_done None)|=
 V293_quiet_globals 112%Z 110%Z 111%Z 99%positive 96%positive 97%positive).
 { unfold V293_quiet_globals;repeat split;apply agvarenv_intro;split;reflexivity. }
 assert(Pack:QKstate irq' M O|=V293_quiet_globals 112%Z 110%Z 111%Z 99%positive 96%positive 97%positive **QJraw nest).
 { unfold QKstate;apply sat_split';exists empmem;exists M;exists empabst;exists O.
   split;[apply map_join_comm;apply map_join_emp| ];
   split;[apply map_join_comm;apply map_join_emp| ];split;assumption. }
 apply astar_l_adomlenv_intro with(d:=nil)in Pack.
 2:{ intros x tau;split;[contradiction|intros[l E];discriminate]. }
 apply astar_l_aisr_intro with(i:=irq')in Pack;[ |reflexivity].
 apply astar_l_aie_intro with(i:=false)in Pack;[ |reflexivity].
 apply astar_l_ais_intro with(i:=[0])in Pack;[ |reflexivity].
 apply astar_l_acs_intro with(i:=nil)in Pack;[ |reflexivity].
 apply astar_l_aop'_intro with(aop:=spec_done None)in Pack;[ |reflexivity].
 unfold QKsnapshot,BQsnapshot,V293_irq_bound_snapshot,V293_enter_bound_external,
 QJraw,QCkept,p_local,LINV,LDli,V293_irq_bound_li,V293_shared_li in *;
 clear H Raw RawPack Moved G Empty;sep auto;apply V293_irq_bound_good.
Qed.

Lemma QKsnapshot_builder : forall nest ir,nest<256 ->
 QKsnapshot nest(isrupd ir 0 true) ==>ipreasrt' 0 ir nil(spec_done None)RDinv **p_local LDli OwnershipWaiting nil.
Proof.
 intros nest ir Bound;unfold QKsnapshot,BQsnapshot,LDli.
 apply V293_bound_outer_snapshot_pre;lia.
Qed.
Lemma QKsnapshot_filter : forall nest irq,1<=nest ->nest<256 ->QKsnapshot nest irq ==>QJfilter.
Proof.
 intros nest irq Positive Bound st H;unfold QJfilter,V293_irq_quiet_filter.
 exists 1;exists nest;exists 0;apply astar_l_apure_intro;[ |repeat split;lia].
 unfold QKsnapshot,BQsnapshot in H;apply V293_irq_bound_snapshot_controls in H;exact H.
Qed.

Theorem QKsame_heap_active_input : forall nest,1<=nest ->nest<256 ->exists M Mf O Of,
 join M Mf(JBmemory nest Int.zero Int.zero) /\join O Of(RIabstract OwnershipWaiting) /\
 QCstate M O|=QJpre /\QKstate(isrupd QKother 0 true)M O|=QKpre QKother.
Proof.
 intros nest Positive Bound;destruct(QJfiltered_nonempty nest Positive Bound)as(M&Mf&O&Of&JM&JO&Entry&Pre).
 assert(New:QKstate(isrupd QKother 0 true)M O|=QKsnapshot nest(isrupd QKother 0 true)).
 { apply QKsnapshot_change_isr with(irq:=isrupd(fun _:hid=>false)0 true);exact Entry. }
 exists M;exists Mf;exists O;exists Of;split;[exact JM| ];split;[exact JO| ];split;[exact Pre| ].
 split;[apply QKsnapshot_builder with(nest:=nest);assumption|apply QKsnapshot_filter with(nest:=nest)(irq:=isrupd QKother 0 true);assumption].
Qed.

Theorem QKactual_wrapper : forall ir,
 InfRules BDspec V293_scheduler LDli RDinv arfalse(QKret ir)
 (QKpre ir)(V293_irq_source_wrapper 301%Z 300%Z Int.zero)Afalse OwnershipWaiting.
Proof.
 intro ir;unfold QKpre,QKret,QJfilter.
 apply(V293_interrupt_quiet_builder_general
 100%Z 101%Z 102%Z 103%Z 105%Z 106%Z 108%Z 109%Z 112%Z 110%Z 111%Z
 92%positive 81%positive 80%positive 91%positive 82%positive 93%positive 94%positive 95%positive
 99%positive 96%positive 97%positive nil BDspec 301%Z 300%Z QCintspec 0 ir nil
 OwnershipWaiting nil _ _ Int.zero);try reflexivity.
 all:unfold INUM;rewrite ?Int.unsigned_zero;cbn;lia.
Qed.

Theorem QKactive_return_resources : forall nest,nest<256 ->exists M Mf O Of,
 join M Mf(JBmemory nest Int.zero Int.zero) /\join O Of(RIabstract OwnershipWaiting) /\
 QKstate(isrupd QKother 0 false)M O|=QKsnapshot nest(isrupd QKother 0 false) /\
 QKstate(isrupd QKother 0 false)M O|=QKret QKother.
Proof.
 intros nest Bound;destruct(QJreturned_old_nonempty nest Bound)as(M&Mf&O&Of&JM&JO&Old).
 assert(Original:QKstate(fun _:hid=>false)M O|=QKsnapshot nest(fun _:hid=>false)).
 { unfold QJreturned_old in Old;unfold QKsnapshot,BQsnapshot.
   apply V293_irq_bound_snapshot_pack;exact Old. }
 assert(New:QKstate(isrupd QKother 0 false)M O|=QKsnapshot nest(isrupd QKother 0 false)).
 { apply QKsnapshot_change_isr with(irq:=fun _:hid=>false);exact Original. }
 exists M;exists Mf;exists O;exists Of;split;[exact JM| ];split;[exact JO| ];split;[exact New| ].
 unfold QKret;apply(V293_bound_quiet_partial_return
 106%Z 112%Z 110%Z 111%Z 92%positive 81%positive 80%positive 91%positive 82%positive
 94%positive 95%positive 99%positive 96%positive 97%positive nil 0 QKother nil
 OwnershipWaiting nil 1 nest 0);try lia;exact New.
Qed.

Theorem QKonly_other_ISR_bit : forall M O j,
 getmem(QCstate M O)=getmem(QKstate(isrupd QKother 0 true)M O) /\
 getabst(QCstate M O)=getabst(QKstate(isrupd QKother 0 true)M O) /\
 (j<>1 ->isrupd(fun _:hid=>false)0 true j=isrupd QKother 0 true j).
Proof.
 intros M O j;split;[reflexivity| ];split;[reflexivity| ].
 intro Other;unfold QKother,isrupd;destruct(Nat.eqb 0 j);[reflexivity| ].
 assert(E:Nat.eqb 1 j=false)by(apply Nat.eqb_neq;lia);rewrite E;reflexivity.
Qed.
Theorem QKother_bit_preserved_and_old_gate_rejected :
 isrupd QKother 0 true 1=true /\isrupd QKother 0 false 1=true /\
 ~(forall j,QKother j=false) /\
 V293_exit_quiet_depth 1(V293_interrupt_nest_after 1 255)=254.
Proof.
 split;[reflexivity| ];split;[reflexivity| ];split;[intro Clear;specialize(Clear 1);discriminate|reflexivity].
Qed.
Theorem QKlower_active_builder_rejected : forall I R st,
 ~st|=ipreasrt' 1(isrupd(fun _:hid=>false)0 true)nil(spec_done None)I **R.
Proof.
 intros I R st H;pose proof(V293_irq_builder_lower_clear 1 _ nil(spec_done None)I R st H 0 ltac:(lia))as Lower.
 discriminate.
Qed.

Theorem QKactive_entry_and_return_bit : forall st,
 (st|=QKpre QKother ->getisr(gettaskst st)1=true) /\
 (st|=QKret QKother ->getisr(gettaskst st)1=true).
Proof.
 intro st;split;intro H.
 - unfold QKpre in H;destruct H as[Builder Filter].
   assert(Meta:st|=Aisr(isrupd QKother 0 true) **Atrue)
   by(clear Filter;unfold inferules.ipreasrt' in Builder;sep auto).
   apply astar_l_aisr_elim in Meta;rewrite(proj1 Meta);reflexivity.
 - assert(Meta:st|=Aisr(isrupd QKother 0 false) **Atrue)
   by(unfold QKret,inferules.iretasrt' in H;sep auto).
   apply astar_l_aisr_elim in Meta;rewrite(proj1 Meta);reflexivity.
Qed.
