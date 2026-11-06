(* A labelled scheduler extension of the fixed control machine. The original
   local rules are unchanged; task-map projection uses the existing hswi_step.
   This module does not replace the framework's program simulation. *)
Require Import CertiOS.certiucos.v293.proofs.V293InterruptFixedControlSpec.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptControlRetention.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCurrent.
Require Import CertiOS.framework.proof.step_prop.
Require Import CertiOS.framework.include_frm.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Definition V293_control_event := option(tid*tid).

Inductive V293_control_run_step (sd:ossched) :
 V293_control_code ->V293_control_state ->V293_control_event ->
 V293_control_code ->V293_control_state ->Prop :=
| V293_control_run_local : forall a s b s',
 V293_control_step sd a s b s' ->
 V293_control_run_step sd a s None b s'
| V293_control_run_switch : forall O c old next tail,
 get O curtid=Some(oscurt old) ->sd O next ->
 V293_control_run_step sd(V293_control_Core(sched;;tail))(O,c)(Some(old,next))
 (V293_control_Core tail)(set O curtid(oscurt next),c)
| V293_control_run_sequence : forall a s b s' old next tail,
 V293_control_run_step sd a s(Some(old,next))b s' ->
 V293_control_run_step sd(V293_control_Seq a tail)s(Some(old,next))
 (V293_control_Seq b tail)s'.

Definition V293_control_emit (event:V293_control_event)(rest:list(tid*tid)) :=
 match event with None=>rest|Some ev=>ev::rest end.

Inductive V293_control_run (sd:ossched) :
 V293_control_code ->V293_control_state ->list(tid*tid) ->
 V293_control_code ->V293_control_state ->Prop :=
| V293_control_run_refl : forall a s,V293_control_run sd a s [] a s
| V293_control_run_cons : forall a s event b s' events d s'',
 V293_control_run_step sd a s event b s' ->
 V293_control_run sd b s' events d s'' ->
 V293_control_run sd a s(V293_control_emit event events)d s''.

Theorem V293_control_run_local_exact : forall sd a s b s',
 V293_control_run_step sd a s None b s' <->V293_control_step sd a s b s'.
Proof. intros;split;[intro H;inversion H;subst;assumption|intro H;constructor;exact H]. Qed.

Theorem V293_control_run_switch_exact : forall sd a O c old next b s',
 V293_control_run_step sd(V293_control_Core a)(O,c)(Some(old,next))b s' <->
 exists tail,a=sched;;tail /\get O curtid=Some(oscurt old) /\sd O next /\
 b=V293_control_Core tail /\s'=(set O curtid(oscurt next),c).
Proof.
 intros;split.
 - intro H;inversion H;subst;exists tail;auto.
 - intros[tail[-> [Current[Selected[-> ->]]]]];constructor;assumption.
Qed.

Lemma V293_control_run_append : forall sd a s xs b s' ys d s'',
 V293_control_run sd a s xs b s' ->V293_control_run sd b s' ys d s'' ->
 V293_control_run sd a s(xs++ys)d s''.
Proof.
 intros sd a s xs b s' ys d s'' First;induction First;intro Last;cbn;[exact Last| ].
 replace(V293_control_emit event events++ys)with(V293_control_emit event(events++ys))
 by(destruct event;reflexivity).
 eapply V293_control_run_cons;eauto.
Qed.

Theorem V293_control_run_legacy_exact : forall sd a s b s',
 V293_control_run sd a s [] b s' <->V293_control_steps sd a s b s'.
Proof.
 intros sd a s b s';split.
 - intro H;remember([]:list(tid*tid))as events eqn:E in H.
   induction H;[constructor| ].
   destruct event as[pair| ];cbn in E;[discriminate| ].
   apply V293_control_run_local_exact in H.
   eapply V293_control_steps_cons;[exact H|apply IHV293_control_run;exact E].
 - intro H;induction H;[constructor| ].
   change(V293_control_run sd a s(V293_control_emit None [])d s'').
   eapply V293_control_run_cons;[constructor;exact H|exact IHV293_control_steps].
Qed.

(* Removing the new switch rule cannot change curtid, even through arbitrary
   original Core primitives and sequence contexts. *)
Lemma V293_control_local_current : forall sd a s b s',
 V293_control_step sd a s b s' ->get(fst s)curtid=get(fst s')curtid.
Proof.
 intros sd a s b s' H;induction H;cbn;try reflexivity;try assumption.
 exact(spec_step_tidsame _ _ _ _ _ H).
Qed.

Theorem V293_control_without_switch_current : forall sd a O c b O' c',
 V293_control_run sd a(O,c)[]b(O',c') ->get O curtid=get O' curtid.
Proof.
 intros sd a O c b O' c' H;apply V293_control_run_legacy_exact in H.
 change(get(fst(O,c))curtid=get(fst(O',c'))curtid).
 induction H;[reflexivity| ].
 etransitivity;[eapply V293_control_local_current;exact H|exact IHV293_control_steps].
Qed.

Theorem V293_control_switch_hpstep : forall pc api ints sd T cst ke ks
 a O c old next b O' c',
 V293_control_run_step sd(V293_control_Core a)(O,c)(Some(old,next))
 (V293_control_Core b)(O',c') ->
 get T old=Some(curs(hapi_code a),(ke,ks)) ->
 hpstep(pc,(api,ints,sd))T cst O
 (set T old(curs(hapi_code b),(ke,ks)))cst O' /\
 c'=c /\get O' curtid=Some(oscurt next) /\
 (forall key,key<>curtid ->get O' key=get O key) /\
 (forall other,other<>old ->get(set T old(curs(hapi_code b),(ke,ks)))other=get T other).
Proof.
 intros pc api ints sd T cst ke ks a O c old next b O' c' Step Code.
 apply V293_control_run_switch_exact in Step.
 destruct Step as[tail[-> [Current[Selected[Eq State]]]]].
 inversion Eq;subst b;inversion State;subst O' c'.
 split.
 - eapply hswi_step;[reflexivity|exact Selected|exact Current|exact Code|reflexivity|reflexivity].
 - split;[reflexivity| ];split;[apply map_get_set| ];split.
   + intros;apply map_get_set';congruence.
   + intros;apply map_get_set';congruence.
Qed.

Theorem V293_control_handler_quiet : forall sd O c,
 V293_control_valid c ->V293_control_dispatch(V293_control_enter c)=false ->
 V293_control_run sd V293_fixed_control_handler(O,c)[]
 (V293_control_Core(spec_done None))(O,V293_control_exit(V293_control_enter c)).
Proof.
 intros sd O c Valid Quiet;apply V293_control_run_legacy_exact.
 pose proof(V293_fixed_control_handler_prefix sd O c Valid)as H.
 rewrite(V293_control_quiet_code _ Quiet)in H;exact H.
Qed.

Theorem V293_control_handler_switch : forall sd O c old next,
 V293_control_valid c ->V293_control_dispatch(V293_control_enter c)=true ->
 get O curtid=Some(oscurt old) ->sd O next ->
 V293_control_run sd V293_fixed_control_handler(O,c)[(old,next)]
 (V293_control_Core(spec_done None))
 (set O curtid(oscurt next),V293_control_exit(V293_control_enter c)).
Proof.
 intros sd O c old next Valid Enabled Current Selected.
 pose proof(V293_fixed_control_handler_prefix sd O c Valid)as Prefix.
 rewrite(V293_control_enabled_code _ Enabled)in Prefix.
 apply V293_control_run_legacy_exact in Prefix.
 change(V293_control_run sd V293_fixed_control_handler(O,c)([]++[(old,next)])
 (V293_control_Core(spec_done None))(set O curtid(oscurt next),V293_control_exit(V293_control_enter c))).
 eapply V293_control_run_append;[exact Prefix| ].
 change(V293_control_run sd(V293_control_Core(sched;;spec_done None))
 (O,V293_control_exit(V293_control_enter c))(V293_control_emit(Some(old,next))[])
 (V293_control_Core(spec_done None))(set O curtid(oscurt next),V293_control_exit(V293_control_enter c))).
 eapply V293_control_run_cons;[constructor;assumption|constructor].
Qed.

Theorem V293_control_handler_self : forall sd O c current,
 V293_control_valid c ->V293_control_dispatch(V293_control_enter c)=true ->
 get O curtid=Some(oscurt current) ->sd O current ->
 V293_control_run sd V293_fixed_control_handler(O,c)[]
 (V293_control_Core(spec_done None))(O,V293_control_exit(V293_control_enter c)).
Proof.
 intros sd O c current Valid Enabled Current Selected.
 apply V293_control_run_legacy_exact.
 pose proof(V293_fixed_control_handler_prefix sd O c Valid)as Prefix.
 rewrite(V293_control_enabled_code _ Enabled)in Prefix.
 assert(Sched:spec_step sd sched O(spec_done None)O).
 { eapply spec_sched_step;[exact Current|exact Selected|apply map_join_emp]. }
 assert(Tail:V293_control_steps sd(V293_control_Core(sched;;spec_done None))
 (O,V293_control_exit(V293_control_enter c))
 (V293_control_Core(spec_done None))(O,V293_control_exit(V293_control_enter c))).
 { eapply V293_control_steps_cons.
   - apply V293_control_core_step;apply spec_seq_step2;exact Sched.
   - eapply V293_control_steps_cons;[apply V293_control_core_step;apply spec_seq_step1|constructor]. }
 clear Current Selected Sched;induction Prefix;[exact Tail| ].
 eapply V293_control_steps_cons;[exact H|apply IHPrefix;exact Tail].
Qed.

Theorem V293_control_switch_target_exact : forall O c old next tail b s' tasks,
 get O abstcblsid=Some(abstcblist tasks) ->
 (V293_control_run_step V293_scheduler(V293_control_Core(sched;;tail))(O,c)
 (Some(old,next))b s' <->
 get O curtid=Some(oscurt old) /\V293_highest_ready tasks next /\
 b=V293_control_Core tail /\s'=(set O curtid(oscurt next),c)).
Proof.
 intros O c old next tail b s' tasks Map;rewrite V293_control_run_switch_exact;split.
 - intros[rest[Eq[Current[[ts[Lookup Highest]][Code State]]]]].
   inversion Eq;subst rest;assert(ts=tasks)by congruence;subst ts;auto.
 - intros[Current[Highest[Code State]]];exists tail;repeat split;try assumption.
   exists tasks;auto.
Qed.

Theorem V293_control_switch_target_unique : forall O c old a b tail tasks entries,
 get O abstcblsid=Some(abstcblist tasks) ->V293_priority_table entries tasks ->
 V293_control_run_step V293_scheduler(V293_control_Core(sched;;tail))(O,c)
 (Some(old,a))(V293_control_Core tail)(set O curtid(oscurt a),c) ->
 V293_control_run_step V293_scheduler(V293_control_Core(sched;;tail))(O,c)
 (Some(old,b))(V293_control_Core tail)(set O curtid(oscurt b),c) ->a=b.
Proof.
 intros O c old a b tail tasks entries Map Table A B.
 apply(V293_control_switch_target_exact _ _ _ _ _ _ _ _ Map)in A,B.
 destruct A as[_[HA _]];destruct B as[_[HB _]].
 eapply V293_highest_unique;eassumption.
Qed.
