(* Exact local footprint: mathematical subheap witness, not boot reachability. *)
Require Import CertiOS.audit.probes.V293InterruptReadyEnvironmentProbe.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptReadyLocal.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchState.
Require Import CertiOS.tactics.sepauto.sep_combine_lemmas.
Require Import CertiOS.certiucos.v293.code.V293ReadyTable.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickDelayHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitReadyBody.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitHandoffHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedChange.
Require Import CertiOS.certiucos.v293.proofs.V293TimeAccess.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptReadyEnvironment.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptReadyEnter.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitReadyDynamic.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitReadyDispatch.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyStorageInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyTaskInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedStoragePrefix.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedSwitch.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntEnterInternal.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchStorage.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.code.V293OSIntEnter.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.audit.probes.V293OSIntExitReadyDynamicProbe.
Require Import CertiOS.audit.probes.V293OSIntExitReadyBodyProbe.
Require Import CertiOS.audit.probes.V293ReadyTaskInvariantProbe.
Require Import CertiOS.audit.probes.V293TaskRecordOwnershipProbe.
Require Import CertiOS.audit.probes.V293TaskRecordInvariantProbe.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.framework.proof.rulesoundlib.
Require Import CertiOS.framework.proof.toptheorem.
Require Import CertiOS.tactics.basetac.join_lib.
Require Import CertiOS.tactics.basetac.join_general.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import Coq.Lists.List Lia.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptReadyBoundary.
Import ListNotations.
Local Open Scope nat_scope.
Definition RLspec:=V293_ready_local_spec
 100%Z 101%Z 102%Z 103%Z 105%Z 106%Z 108%Z 109%Z 112%Z 110%Z 111%Z
 92%positive 81%positive 80%positive 91%positive 82%positive 93%positive 94%positive 95%positive
 99%positive 96%positive 97%positive nil Aemp I 300%Z 301%Z 200%Z.
Definition RLboundary:=V293_enter_local_boundary 80%positive 81%positive 82%positive
 99%positive 96%positive 112%Z 110%Z 106%Z V293_tcb_type REprefix REsuffix
 (spec_done None)[0]nil OwnershipWaiting.
Definition RLfp:=V293_enter_local_fpre 80%positive 81%positive 82%positive
 99%positive 96%positive 112%Z 110%Z 106%Z V293_tcb_type REprefix REsuffix.
Definition RLfq:=V293_enter_local_fpost 80%positive 81%positive 82%positive
 99%positive 96%positive 112%Z 110%Z 106%Z V293_tcb_type REprefix REsuffix.
Definition RLstate(M:mem)(O:osabst):RstateOP:=
 (JBge,emp,M,(fun _:hid=>false),(false,[0],nil),O,spec_done None).
Theorem RLenvironment :
 GoodI RDinv V293_scheduler V293_shared_li /\
 WFFunEnv RDprogram RLspec V293_scheduler V293_shared_li RDinv /\
 WFIFun RDprogram RLspec V293_scheduler RDinv V293_shared_li.
Proof.
 split;[apply V293_ready_storage_good| ];split;
 change RDprogram with(V293_ready_irq_unit
 100%Z 101%Z 102%Z 103%Z 105%Z 106%Z 108%Z 109%Z 112%Z 110%Z 111%Z 120%Z
 300%Z 301%Z 200%Z 104%Z);unfold RLspec.
 - apply V293_ready_local_WFFunEnv;try discriminate;exact I.
 - apply V293_ready_local_WFIFun;try discriminate;exact I.
Qed.
Lemma RLbuilder :
 BuildPreI RDprogram 301%Z nil RElg RLfp OwnershipWaiting=
 Some(Aemp ** (RLboundary ** A_dom_lenv nil)) /\
 BuildRetI RDprogram 301%Z nil RElg RLfq OwnershipWaiting=
 Some(fun result=>Aemp ** (([|result=None|] ** RLboundary) ** A_dom_lenv nil)).
Proof. split;reflexivity. Qed.
Theorem RLentry_nonempty : exists M Mf O Of,
 join M Mf(JBmemory 0 Int.zero Int.zero) /\
 join O Of(RIabstract OwnershipWaiting) /\
 RLstate M O |=RLboundary ** A_dom_lenv nil.
Proof.
 pose proof REheap as Entry;apply sat_split in Entry.
 destruct Entry as(M&Mf&O&Of&JM&JO&Shared&Extra).
 exists M;exists Mf;exists O;exists Of;split;[exact JM| ];split;[exact JO| ].
 change(RLstate M O |=
 V293_ready_storage_core 80%positive 81%positive 82%positive 106%Z V293_tcb_type JBcells **
 CurTid OwnershipWaiting)in Shared.
 apply astar_l_aisr_intro with(i:=fun _:hid=>false)in Shared;[ |reflexivity].
 apply astar_l_aie_intro with(i:=false)in Shared;[ |reflexivity].
 apply astar_l_atopis_intro with(i:=0)in Shared;[ |reflexivity].
 assert(Flags:RLstate M O |= (V293_shared_flags **
 V293_ready_storage_core 80%positive 81%positive 82%positive 106%Z V293_tcb_type JBcells) **
 CurTid OwnershipWaiting).
 { assert(C:Aisr(fun _:hid=>false) ==>isrclr).
   { intros st K;unfold isrclr;exists(fun _:hid=>false);split;[exact K|split;[auto|exact(proj2 K)]]. }
 eapply astar_mono in Shared;[ |intros st K;exact K|apply astar_mono;
 [intros st K;exact K|apply astar_mono;[exact C|intros st K;exact K]]].
 unfold V293_shared_flags;clear -Shared;sep normal;exists 0;sep auto. }
 eapply astar_mono in Flags;[ |apply V293_ready_storage_switch_close|intros st K;exact K].
 apply astar_l_ais_intro with(i:=[0])in Flags;[ |reflexivity].
 apply astar_l_acs_intro with(i:=nil)in Flags;[ |reflexivity].
 apply astar_l_adomlenv_intro with(d:=nil)in Flags.
 2:{ intros x t;split;[contradiction|intros[l E];discriminate]. }
 apply astar_l_aop'_intro with(aop:=spec_done None)in Flags;[ |reflexivity].
 assert(G:(JBge,emp,empmem,(fun _:hid=>false),(false,[0],nil),empabst,spec_done None)|=
 V293_interrupt_globals 112%Z 110%Z 99%positive 96%positive).
 { unfold V293_interrupt_globals;split;apply agvarenv_intro;
 [split;reflexivity|split;reflexivity|split;reflexivity|split;reflexivity]. }
 assert(Pack:RLstate M O|=V293_interrupt_globals 112%Z 110%Z 99%positive 96%positive **
 (<||spec_done None||> ** (A_dom_lenv nil ** (Acs nil ** (Ais (0::nil) **
 (SWINV RDinv ** CurTid OwnershipWaiting)))))).
 { unfold RLstate;apply sat_split';exists empmem;exists M;exists empabst;exists O.
 split;[apply join_emp| ];split;[apply join_emp| ];split;[exact G|exact Flags]. }
 unfold RLboundary,V293_enter_local_boundary,REprefix,REsuffix,V293_ready_irq_prefix,V293_ready_irq_suffix.
 unfold p_local,LINV,V293_shared_li;clear -Pack;sep auto;apply V293_switch_li_good.
Qed.
Lemma RLlocal_empty_abstract : forall tid lg ge le M ir aux O op,
 (ge,le,M,ir,aux,O,op)|=p_local V293_shared_li tid lg ->O=emp.
Proof.
 intros tid lg ge le M ir aux O op H.
 unfold p_local,LINV,V293_shared_li in H.
 assert(C:(ge,le,M,ir,aux,O,op)|=CurTid tid)by(sep auto).
 destruct(V293_current_fragment_local _ _ _ _ _ _ _ _ C)as(b&tp&GE&Empty&Rest).
 exact Empty.
Qed.
(* One fixed state; neutralize only the exact local footprint to CurLINV. *)
Theorem RLlocal_exactness_control :
 REstate |=CurLINV V293_shared_li OwnershipWaiting /\
 ~REstate |=p_local V293_shared_li OwnershipWaiting nil.
Proof.
 split.
 - pose proof REentry_nonempty as H.
   eapply astar_mono in H;[ |apply V293_enter_ready_boundary_local|intros st K;exact K].
   apply V293_CurLINV_extend with(extra:=A_dom_lenv nil);exact H.
 - intro H;pose proof(RLlocal_empty_abstract _ _ _ _ _ _ _ _ _ H)as E.
   change(RIabstract OwnershipWaiting=emp)in E.
   pose proof(f_equal(fun O:osabst=>get O curtid)E)as K.
   vm_compute in K;discriminate.
Qed.
Theorem RLactual_call : forall r ri,
 InfRules RLspec V293_scheduler V293_shared_li RDinv r ri
 (RLboundary ** A_dom_lenv nil)(scall 301%Z nil)
 (RLboundary ** A_dom_lenv nil)OwnershipWaiting.
Proof.
 intros;unfold RLspec,RLboundary,REprefix,REsuffix;
 apply V293_ready_local_Enter_call;discriminate.
Qed.
Theorem RLclosed_call : forall r ri i si aop tid lg,
 InfRules RLspec V293_scheduler V293_shared_li RDinv r ri
 (V293_irq_ready_closed 80%positive 81%positive 82%positive 106%Z V293_tcb_type JBcells i si aop tid lg **
 V293_interrupt_globals 112%Z 110%Z 99%positive 96%positive)
 (scall 301%Z nil)
 (V293_irq_ready_closed 80%positive 81%positive 82%positive 106%Z V293_tcb_type JBcells i si aop tid lg **
 V293_interrupt_globals 112%Z 110%Z 99%positive 96%positive)tid.
Proof.
 intros;apply(V293_irq_local_enter_call
 80%positive 81%positive 82%positive 99%positive 96%positive
 112%Z 110%Z 106%Z V293_tcb_type REprefix REsuffix);reflexivity.
Qed.
Theorem RLreturn_resources : forall ir lg,
 (forall j,ir j=false) ->
 RLboundary ** A_dom_lenv nil ==>
 (iretasrt' 0 ir nil RDinv ** p_local V293_shared_li OwnershipWaiting lg) **
 V293_interrupt_globals 112%Z 110%Z 99%positive 96%positive.
Proof.
 intros;unfold RLboundary;apply(V293_irq_local_return_resources
 80%positive 81%positive 82%positive 99%positive 96%positive
 112%Z 110%Z 106%Z V293_tcb_type REprefix REsuffix);assumption.
Qed.
Theorem RLunchanged_entries : forall f,f<>301%Z ->RLspec f=REspec f.
Proof.
 intros;unfold RLspec,REspec,V293_ready_local_spec,V293_ready_irq_spec;
 repeat destruct Z.eq_dec;try congruence;reflexivity.
Qed.

Theorem RLeoi_enter : forall r ri intspec ir si tid lg pre,
 intspec 0<>None ->Some pre=BuildintPre 0 intspec ir si RDinv V293_shared_li tid lg ->
 (forall j,ir j=false) ->
 InfRules RLspec V293_scheduler V293_shared_li RDinv r ri
 (pre ** V293_interrupt_globals 112%Z 110%Z 99%positive 96%positive)
 (sseq(sprim(eoi Int.zero))(scall 301%Z nil))
 (V293_irq_ready_closed 80%positive 81%positive 82%positive 106%Z V293_tcb_type JBcells 0 si
 (match intspec 0 with Some a=>a|None=>spec_done None end)tid lg **
 V293_interrupt_globals 112%Z 110%Z 99%positive 96%positive)tid.
Proof.
 intros;eapply(V293_irq_local_eoi_enter
 80%positive 81%positive 82%positive 99%positive 96%positive
 112%Z 110%Z 106%Z V293_tcb_type REprefix REsuffix);try eassumption;try reflexivity.
 vm_compute;split;congruence.
Qed.
