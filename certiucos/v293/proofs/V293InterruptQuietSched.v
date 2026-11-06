(* A precise sched can be consumed on quiet entries only when current is highest. *)
Require Import CertiOS.certiucos.v293.proofs.V293InterruptQuietISRReturn.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptSourceRoundtrip.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptQuietBuilder.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptBindings.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptBoundQuietContinuous.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitBoundDynamic.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitReadyDynamic.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntEnterOpenExact.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntEnterInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitQuietExact.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptQuietContinuous.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedExactLocal.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTarget.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedDispatchFinish.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

(* This is an ordinary same-state guard, never additional abstract ownership. *)
Definition V293_irq_sched_self_guard := EX ct:tid,EX tasks:TcbMod.map,
 [|V293_highest_ready tasks ct|] **
 (Aabsdata curtid(oscurt ct) ** (Aabsdata abstcblsid(abstcblist tasks) ** Atrue)).
Lemma V293_irq_sched_self_guard_sound : forall st,
 st|=V293_irq_sched_self_guard ->sched_self V293_scheduler(getabst st).
Proof.
 intros st[ct[tasks H]];apply astar_l_apure_elim in H;destruct H as[Highest H].
 exists ct;split.
 - eapply V293_star_abst_get_l;[apply V293_shared_abs_get|exact H].
 - exists tasks;split;[ |exact Highest].
   eapply V293_star_abst_get_r;[ |exact H].
   eapply V293_star_abst_get_l;apply V293_shared_abs_get.
Qed.
Lemma V293_irq_sched_self_guard_complete : forall st,
 sched_self V293_scheduler(getabst st) ->st|=V293_irq_sched_self_guard.
Proof.
 intros st[ct[C[tasks[T Highest]]]].
 exists ct;exists tasks;apply astar_l_apure_intro;[ |exact Highest].
 destruct st as[[[[[[ge le] M]ir]aux]O]op];cbn in C,T.
 destruct(map_join_get_sig C)as[Orest Join].
 assert(TR:get Orest abstcblsid=Some(abstcblist tasks)).
 { assert(N:get(sig curtid(oscurt ct):osabst)abstcblsid=None)by(apply map_get_sig';discriminate).
   rewrite <-(map_join_get_none Join N);exact T. }
 destruct(map_join_get_sig TR)as[Ofinal JoinT].
 apply sat_split';exists(emp:mem);exists M;exists(sig curtid(oscurt ct));exists Orest.
 split;[apply map_join_comm;apply map_join_emp| ].
 split;[exact Join| ];split;[split;reflexivity| ].
 apply sat_split';exists(emp:mem);exists M;exists(sig abstcblsid(abstcblist tasks));exists Ofinal.
 split;[apply map_join_comm;apply map_join_emp| ].
 split;[exact JoinT| ];split;[split;reflexivity|exact I].
Qed.

Lemma V293_irq_guarded_sched_reduce : forall li P aop t,
 can_change_aop P ->
 absinferfull V293_scheduler li
 ((<||sched;;aop||> **P) //\\ V293_irq_sched_self_guard)
 (<||aop||> **P)t.
Proof.
 intros li P aop t Free.
 set(R:=P //\\ V293_irq_sched_self_guard).
 assert(RFree:can_change_aop R).
 { unfold R,V293_irq_sched_self_guard;cbn[can_change_aop];auto. }
 eapply absinfer_conseq' with(p:=<||sched;;aop||> **R)(q:=<||aop||> **R).
 - intros st H;apply astar_l_aop'_elim in H;destruct H as[Op[H Guard]].
   apply astar_l_aop'_intro;assumption.
 - eapply absinfer_trans' with(q:=<||spec_done None;;aop||> **R).
   + apply absinfer_seq';try exact RFree.
     eapply(absinfer_sched' _ (fun _=>True) _ _ _ _);try exact RFree.
     * intros st H;exact H.
     * intros st[H Guard];apply V293_irq_sched_self_guard_sound;exact Guard.
   + apply absinfer_seq_end';try exact RFree;intros st H;exact H.
 - intros st[H Guard];apply astar_l_aop'_elim in H;destruct H as[Op H].
   apply astar_l_aop'_intro;[split;assumption|exact Op].
Qed.

Section QuietSched.
Variables unmap group rows high table target current counter running nesting lock:var.
Variables bt bg br bh bp bo bc bk brun bn bl:block.
Variable rest:list(addr*type).
Let li:=V293_irq_bound_li running nesting lock brun bn bl.
Let Inv0:=V293_ready_dynamic_exit_inv target bt bg br bh bp bc bk brun bn bl rest.
Let efp:=V293_enter_bound_fpre running nesting lock brun bn bl Aemp Logic.I.
Let efq:=V293_enter_bound_fpost running nesting lock brun bn bl Aemp Logic.I.
Let xfp:=V293_bound_dynamic_fpre unmap group rows high table target current counter running nesting lock
 bt bg br bh bp bo bc bk brun bn bl rest Aemp Logic.I.
Let xfq:=V293_bound_dynamic_fpost unmap group rows high table target current counter running nesting lock
 bt bg br bh bp bo bc bk brun bn bl rest Aemp Logic.I.
Let snapshot:=V293_irq_bound_snapshot target running nesting lock bt bg br bh bp bc bk brun bn bl rest.
Let filter:=V293_irq_quiet_filter brun bn bl.
Lemma V293_quiet_snapshot_sched_reduce : forall run nest locked aop ir si t,
 absinferfull V293_scheduler li
 (snapshot run nest locked(sched;;aop)false ir si nil t //\\ V293_irq_sched_self_guard)
 (snapshot run nest locked aop false ir si nil t)t.
Proof.
 intros.
 set(R:=OS[ir,false,si,nil] **
 (Amapsto(brun,0%Z)Tint8 true(V293_byteval run) **
 (Amapsto(bn,0%Z)Tint8 true(V293_byteval nest) **
 (Amapsto(bl,0%Z)Tint8 true(V293_byteval locked) **
 (p_local li t nil **
 (V293_quiet_irq_kept target bt bg br bh bp bc bk rest ** A_dom_lenv nil)))))).
 unfold snapshot,V293_irq_bound_snapshot,V293_enter_bound_external.
 eapply absinfer_conseq' with(p:=(<||sched;;aop||> **R) //\\ V293_irq_sched_self_guard)
 (q:=<||aop||> **R).
 - intros st H;unfold R,li in *;sep auto.
 - apply V293_irq_guarded_sched_reduce.
   unfold R;split;[cbn[can_change_aop];tauto| ].
   apply V293_good_frame_action_free.
   split;[exact I| ];split;[exact I| ];split;[exact I| ];split.
   + apply V293_exact_local_frame;apply V293_irq_bound_good.
   + split;[apply V293_quiet_irq_kept_good|exact I].
 - intros st[H G];split;[clear G;unfold R,li in *;sep auto|exact G].
Qed.

Theorem V293_interrupt_quiet_sched_builder : forall Spec enter exit intspec i ir si t lg pre ret id,
 intspec i=Some(sched;;spec_done None) ->
 Some pre=BuildintPre i intspec ir si Inv0 li t lg ->
 Some ret=BuildintRet i intspec ir si Inv0 li t lg ->
 Spec enter=Some(efp,efq,(Tvoid,nil)) ->Spec exit=Some(xfp,xfq,(Tvoid,nil)) ->
 (0<=Int.unsigned id<Z.of_nat INUM)%Z ->i=Z.to_nat(Int.unsigned id) ->
 InfRules Spec V293_scheduler li Inv0 arfalse ret
 ((pre //\\ filter) //\\ V293_irq_sched_self_guard)
 (V293_irq_source_wrapper enter exit id)Afalse t.
Proof.
 intros Spec enter exit intspec i ir si t lg pre ret id Lookup Pre Ret Enter Exit Bound Index.
 unfold BuildintPre in Pre;rewrite Lookup in Pre;inversion Pre;subst pre.
 eapply conseq_rule with(p:=EX run,EX nest,EX locked,
 [|run<256 /\ nest<256 /\ locked<256 /\ (run=1 ->1<=nest \/ 0<locked) /\
 (forall j,j<i ->ir j=false)|] **
 (snapshot run nest locked(sched;;spec_done None)false(isrupd ir i true)(i::si)nil t //\\ V293_irq_sched_self_guard)).
 - intros st[[H F]G].
   pose proof(V293_irq_builder_lower_clear i ir si(sched;;spec_done None)Inv0(p_local li t lg)st H)as Lower.
   assert(Open:st|=(ipreasrt' i ir si(sched;;spec_done None)Inv0 **p_local li t lg) //\\ filter)by(split;assumption).
   apply V293_irq_quiet_builder_open in Open.
   destruct Open as[run[nest[locked Open]]];apply astar_l_apure_elim in Open.
   destruct Open as[[Run[Nest[Lock Quiet]]]Hld].
   exists run;exists nest;exists locked;apply astar_l_apure_intro;[split;assumption|tauto].
 - intros st H;exact H.
 - apply ex_intro_rule;intro run;apply ex_intro_rule;intro nest;apply ex_intro_rule;intro locked.
   eapply conseq_rule;[intros st H;apply astar_comm;exact H|intros st H;exact H| ].
   apply pure_split_rule;intros[Run[Nest[Lock[Quiet Lower]]]].
   eapply abscsq_rule_full with(p:=snapshot run nest locked(spec_done None)false(isrupd ir i true)(i::si)nil t)(q:=Afalse).
   + apply V293_quiet_snapshot_sched_reduce.
   + apply absinfer_eq'.
   + eapply V293_interrupt_quiet_partial_snapshot with(intspec:=intspec)(lg:=lg);eassumption.
Qed.
End QuietSched.
