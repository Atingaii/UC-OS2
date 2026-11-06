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
Import ListNotations.
Local Open Scope nat_scope.
Definition BQsnapshot:=V293_irq_bound_snapshot
 106%Z 112%Z 110%Z 111%Z 92%positive 81%positive 80%positive 91%positive 82%positive
 94%positive 95%positive 99%positive 96%positive 97%positive nil.
Definition BQentry:=BQsnapshot 1 1 0(spec_done None)false(isrupd(fun _:hid=>false)0 true)[0]nil OwnershipWaiting.
Definition BQpre:=ipreasrt' 0(fun _:hid=>false)nil(spec_done None)RDinv **p_local LDli OwnershipWaiting nil.
Definition BQret:=iretasrt' 0(fun _:hid=>false)nil RDinv **p_local LDli OwnershipWaiting nil.
Lemma BQbuilders :
 Some BQpre=BuildintPre 0 QCintspec(fun _:hid=>false)nil RDinv LDli OwnershipWaiting nil /\
 Some BQret=BuildintRet 0 QCintspec(fun _:hid=>false)nil RDinv LDli OwnershipWaiting nil.
Proof. split;reflexivity. Qed.
Lemma BQentry_pack : QCentry ==>BQentry.
Proof. unfold QCentry,BQentry,BQsnapshot;apply V293_irq_bound_snapshot_pack. Qed.
Lemma BQpre_pack : ECentry ==>BQpre.
Proof.
 intros st H;unfold ECentry,ECpre in H;unfold BQpre,LDli.
 assert(P:st |=ipreasrt' 0(fun _:hid=>false)nil(spec_done None)RDinv **
 (p_local V293_shared_li OwnershipWaiting nil ** ECglobals))by(sep auto).
 eapply astar_mono in P;[ |intros s K;exact K|apply V293_irq_bound_local_close];exact P.
Qed.
Theorem BQentry_nonempty : exists M Mf O Of,
 join M Mf(JBmemory 1 Int.zero Int.zero) /\join O Of(RIabstract OwnershipWaiting) /\
 QCstate M O|=BQentry /\QCstate M O|=BQpre.
Proof.
 destruct QCentry_nonempty as(M&Mf&O&Of&JM&JO&H).
 exists M;exists Mf;exists O;exists Of;split;[exact JM| ];split;[exact JO| ];split.
 - apply BQentry_pack;exact H.
 - apply BQpre_pack;apply ECsnapshot_to_builder;exact H.
Qed.
Theorem BQenvironment : GoodI RDinv V293_scheduler LDli /\
 WFFunEnv RDprogram BDspec V293_scheduler LDli RDinv /\
 WFIFun RDprogram BDspec V293_scheduler RDinv LDli.
Proof.
 split;[apply V293_irq_bound_GoodI;exact(proj1 QCenvironment)|exact BDenvironment].
Qed.
Theorem BQactual_wrapper :
 InfRules BDspec V293_scheduler LDli RDinv arfalse BQret
 BQentry(V293_irq_source_wrapper 301%Z 300%Z Int.zero)Afalse OwnershipWaiting.
Proof.
 unfold BQentry,BQsnapshot;apply(V293_interrupt_bound_quiet_continuous
 100%Z 101%Z 102%Z 103%Z 105%Z 106%Z 108%Z 109%Z 112%Z 110%Z 111%Z
 92%positive 81%positive 80%positive 91%positive 82%positive 93%positive 94%positive 95%positive
 99%positive 96%positive 97%positive nil BDspec 301%Z 300%Z QCintspec 0(fun _:hid=>false)nil
 OwnershipWaiting nil BQret Int.zero 1 1 0);try reflexivity;try(cbn;lia).
 all: unfold gettopis,INUM;rewrite ?Int.unsigned_zero;cbn;lia.
Qed.
Theorem BQnonempty_actual_wrapper : exists M Mf O Of,
 join M Mf(JBmemory 1 Int.zero Int.zero) /\join O Of(RIabstract OwnershipWaiting) /\
 QCstate M O|=BQentry /\QCstate M O|=BQpre /\
 InfRules BDspec V293_scheduler LDli RDinv arfalse BQret
 BQentry(V293_irq_source_wrapper 301%Z 300%Z Int.zero)Afalse OwnershipWaiting.
Proof.
 destruct BQentry_nonempty as(M&Mf&O&Of&JM&JO&Entry&Pre).
 exists M;exists Mf;exists O;exists Of;split;[exact JM| ];split;[exact JO| ];split;[exact Entry| ];split;[exact Pre|apply BQactual_wrapper].
Qed.
Definition BQreturned:=BQsnapshot 1 1 0(spec_done None)false(fun _:hid=>false)[0]nil OwnershipWaiting.
Theorem BQreturn_literal : BQreturned ==>
 (<||spec_done None||> ** Aisr(isrupd(fun _:hid=>false)0 false) ** Ais (0::nil) ** Acs nil **
 (IRINV RDinv ** A_dom_lenv nil)) **p_local LDli OwnershipWaiting nil.
Proof.
 change(BQreturned ==>iretasrt' 0(fun _:hid=>false)nil RDinv **p_local LDli OwnershipWaiting nil).
 unfold BQreturned,BQsnapshot;apply V293_bound_quiet_return_resources;try reflexivity;lia.
Qed.
Lemma BQreturn_forget : BQret ==>
 iretasrt' 0(fun _:hid=>false)nil RDinv **p_local V293_shared_li OwnershipWaiting nil.
Proof.
 unfold BQret,LDli;apply astar_mono;[intros s H;exact H|apply V293_bound_dispatch_forget].
Qed.
Theorem BQroom_is_necessary : V293_interrupt_nest_after 1 255=255 /\
 V293_exit_quiet_depth 1(V293_interrupt_nest_after 1 255)=254 /\
 V293_exit_quiet_depth 1(V293_interrupt_nest_after 1 255)<>255.
Proof. exact V293_quiet_pair_saturation_counterexample. Qed.
Theorem BQquiet_is_not_all : ~V293_quiet_exit_valid 1(V293_interrupt_nest_after 1 0)0 [0].
Proof. exact QCdispatch_entry_not_quiet. Qed.
Theorem BQother_bit_survives : forall ir i j,i<>j ->ir j=true ->
 isrupd(isrupd ir i true)i false j=true.
Proof. exact V293_irq_other_bit_survives. Qed.
Theorem BQruntime_unchanged :
 V293_irq_source_wrapper 301%Z 300%Z Int.zero=
 sseq(sprim(eoi Int.zero))(sseq(scall 301%Z nil)(sseq(scall 300%Z nil)(sprim exint))) /\
 RDprogram 300%Z=XIprogram 300%Z /\
 BDspec=V293_bound_dynamic_spec
 100%Z 101%Z 102%Z 103%Z 105%Z 106%Z 108%Z 109%Z 112%Z 110%Z 111%Z
 92%positive 81%positive 80%positive 91%positive 82%positive 93%positive 94%positive 95%positive
 99%positive 96%positive 97%positive nil Aemp Logic.I 300%Z 301%Z 200%Z.
Proof. repeat split;reflexivity. Qed.

Definition BQreturned_state M O:RstateOP:=(JBge,emp,M,(fun _:hid=>false),(false,[0],nil),O,spec_done None).
Definition BQreturned_old:=V293_quiet_irq_snapshot
 106%Z 112%Z 110%Z 111%Z 92%positive 81%positive 80%positive 91%positive 82%positive
 94%positive 95%positive 99%positive 96%positive 97%positive nil
 1 1 0(spec_done None)false(fun _:hid=>false)[0]nil OwnershipWaiting.
Theorem BQreturned_old_nonempty : exists M Mf O Of,
 join M Mf(JBmemory 1 Int.zero Int.zero) /\ join O Of(RIabstract OwnershipWaiting) /\
 BQreturned_state M O|=BQreturned_old.
Proof.
 pose proof QCraw_heap as H;unfold JBstate in H.
 assert(Moved:(JBge,emp,JBmemory 1 Int.zero Int.zero,(fun _:hid=>false),
 (false,nil,nil),RIabstract OwnershipWaiting,spec_done None)|=QCraw ** Atrue).
 { eapply good_inv_prop;[split;[exact(proj1 QCraw_good)|exact Logic.I]|exact H]. }
 assert(New:BQreturned_state(JBmemory 1 Int.zero Int.zero)(RIabstract OwnershipWaiting)|=QCraw ** Atrue).
 { unfold BQreturned_state;eapply goodfrm_prop;[split;[exact(proj2 QCraw_good)|exact Logic.I]|exact Moved]. }
 apply sat_split in New;destruct New as(M&Mf&O&Of&JM&JO&Owned&Extra).
 exists M;exists Mf;exists O;exists Of;split;[exact JM| ];split;[exact JO| ].
 assert(G:(JBge,emp,empmem,(fun _:hid=>false),(false,[0],nil),empabst,spec_done None)|=
 V293_quiet_globals 112%Z 110%Z 111%Z 99%positive 96%positive 97%positive).
 { unfold V293_quiet_globals;repeat split;apply agvarenv_intro;
 split;reflexivity. }
 assert(Pack:BQreturned_state M O|=V293_quiet_globals 112%Z 110%Z 111%Z 99%positive 96%positive 97%positive ** QCraw).
 { unfold BQreturned_state;apply sat_split';exists empmem;exists M;exists empabst;exists O.
 split;[apply join_emp| ];split;[apply join_emp| ];split;assumption. }
 apply astar_l_adomlenv_intro with(d:=nil)in Pack.
 2:{ intros x tau;split;[contradiction|intros[l E];discriminate]. }
 apply astar_l_aisr_intro with(i:=(fun _:hid=>false))in Pack;[ |reflexivity].
 apply astar_l_aie_intro with(i:=false)in Pack;[ |reflexivity].
 apply astar_l_ais_intro with(i:=[0])in Pack;[ |reflexivity].
 apply astar_l_acs_intro with(i:=nil)in Pack;[ |reflexivity].
 apply astar_l_aop'_intro with(aop:=spec_done None)in Pack;[ |reflexivity].
 unfold BQreturned_old,V293_quiet_irq_snapshot,V293_enter_open_external,QCraw,QCkept,
 p_local,LINV,V293_shared_li in *;clear H Moved Owned Extra;sep auto;apply V293_switch_li_good.
Qed.
Theorem BQreturned_nonempty : exists M Mf O Of,
 join M Mf(JBmemory 1 Int.zero Int.zero) /\join O Of(RIabstract OwnershipWaiting) /\
 BQreturned_state M O|=BQreturned /\BQreturned_state M O|=BQret.
Proof.
 destruct BQreturned_old_nonempty as(M&Mf&O&Of&JM&JO&H).
 assert(New:BQreturned_state M O|=BQreturned).
 { unfold BQreturned_old in H;unfold BQreturned,BQsnapshot;apply V293_irq_bound_snapshot_pack;exact H. }
 exists M;exists Mf;exists O;exists Of;split;[exact JM| ];split;[exact JO| ];split;[exact New| ].
 apply BQreturn_literal;exact New.
Qed.
