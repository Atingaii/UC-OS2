(* An explicit stateful front end, not an instance of the old osintspec. *)
Require Import CertiOS.certiucos.v293.proofs.V293InterruptControlRetention.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptQuietBuilder.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptBindings.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitReadyDynamic.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntEnterInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitHoare.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.code.V293OSIntEnter.
Require Import CertiOS.certiucos.v293.code.V293OSIntExit.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Inductive V293_control_code :=
| V293_control_Enter
| V293_control_Exit
| V293_control_Core (legacy:spec_code)
| V293_control_Seq (first second:V293_control_code).

(* The Exit decision uses the pre-decrement depth, then retains the update.
   Core scheduling is exactly the old rule, not an always-enabled shortcut. *)
Inductive V293_control_step (sd:ossched) :
 V293_control_code ->V293_control_state ->V293_control_code ->V293_control_state ->Prop :=
| V293_control_enter_step : forall O c,
 V293_control_valid c ->
 V293_control_step sd V293_control_Enter(O,c)
  (V293_control_Core(spec_done None))(O,V293_control_enter c)
| V293_control_exit_step : forall O c,
 V293_control_valid c ->
 V293_control_step sd V293_control_Exit(O,c)
  (V293_control_Core(V293_control_exit_code c))(O,V293_control_exit c)
| V293_control_core_step : forall a b O O' c,
 spec_step sd a O b O' ->
 V293_control_step sd(V293_control_Core a)(O,c)(V293_control_Core b)(O',c)
| V293_control_seq_done : forall v next s,
 V293_control_step sd(V293_control_Seq(V293_control_Core(spec_done v))next)s next s
| V293_control_seq_step : forall first next first' s s',
 V293_control_step sd first s first' s' ->
 V293_control_step sd(V293_control_Seq first next)s(V293_control_Seq first' next)s'.

Inductive V293_control_steps (sd:ossched) :
 V293_control_code ->V293_control_state ->V293_control_code ->V293_control_state ->Prop :=
| V293_control_steps_refl : forall a s,V293_control_steps sd a s a s
| V293_control_steps_cons : forall a s b s' d s'',
 V293_control_step sd a s b s' ->V293_control_steps sd b s' d s'' ->
 V293_control_steps sd a s d s''.

Definition V293_fixed_control_handler := V293_control_Seq V293_control_Enter V293_control_Exit.
Definition V293_fixed_control_intspec (i:hid) : option V293_control_code :=
 if Nat.ltb i INUM then Some V293_fixed_control_handler else None.

Theorem V293_fixed_control_lookup : forall i,i<INUM ->
 V293_fixed_control_intspec i=Some V293_fixed_control_handler.
Proof. intros i H;unfold V293_fixed_control_intspec;apply Nat.ltb_lt in H;rewrite H;reflexivity. Qed.

Theorem V293_control_exit_exact : forall sd O c next s',
 V293_control_step sd V293_control_Exit(O,c)next s' <->
 V293_control_valid c /\ next=V293_control_Core(V293_control_exit_code c) /\
 s'=(O,V293_control_exit c).
Proof. intros;split;[intro H;inversion H;subst;auto|intros[H[-> ->]];constructor;exact H]. Qed.

Lemma V293_control_step_valid : forall sd a s b s',
 V293_control_step sd a s b s' ->V293_control_valid(snd s) ->V293_control_valid(snd s').
Proof.
 intros sd a s b s' H;induction H;cbn;intros;
 eauto using V293_control_enter_valid,V293_control_exit_valid.
Qed.

(* One-step reflection rules out extra legacy behavior, not just a forward
   embedding that could silently add nondeterministic alternatives. *)
Theorem V293_control_core_exact : forall sd a O c next s',
 V293_control_step sd(V293_control_Core a)(O,c)next s' <->
 exists b,exists O',next=V293_control_Core b /\ s'=(O',c) /\ spec_step sd a O b O'.
Proof.
 intros;split.
 - intro H;inversion H;subst;eauto.
 - intros[b[O'[-> [-> H]]]];constructor;exact H.
Qed.

Theorem V293_control_core_trace_lift : forall sd a O b O' c,
 spec_stepstar sd a O b O' ->
 V293_control_steps sd(V293_control_Core a)(O,c)(V293_control_Core b)(O',c).
Proof.
 intros sd a O b O' c H;induction H.
 - constructor.
 - eapply V293_control_steps_cons;[apply V293_control_core_step;exact H|exact IHspec_stepstar].
Qed.

Theorem V293_control_core_trace_exact : forall sd a O c next s',
 V293_control_steps sd(V293_control_Core a)(O,c)next s' <->
 exists b,exists O',next=V293_control_Core b /\ s'=(O',c) /\ spec_stepstar sd a O b O'.
Proof.
 intros sd a O c next s';split.
 - intro Trace;remember(V293_control_Core a)as start eqn:Code in Trace;
   remember(O,c)as state eqn:State in Trace.
   revert a O c Code State.
   induction Trace as[x st|x st y st' z st'' Step Rest IH];intros a O c Code State;subst.
   + exists a;exists O;repeat split;constructor.
   + apply V293_control_core_exact in Step.
     destruct Step as[b[O'[-> [-> Legacy]]]].
     destruct(IH b O' c eq_refl eq_refl)as[d[O''[-> [-> Tail]]]].
     exists d;exists O'';repeat split;econstructor;eassumption.
 - intros[b[O'[-> [-> H]]]];apply V293_control_core_trace_lift;exact H.
Qed.

Theorem V293_fixed_control_handler_prefix : forall sd O c,
 V293_control_valid c ->
 V293_control_steps sd V293_fixed_control_handler(O,c)
  (V293_control_Core(V293_control_exit_code(V293_control_enter c)))
  (O,V293_control_exit(V293_control_enter c)).
Proof.
 intros sd O c Valid;unfold V293_fixed_control_handler.
 eapply V293_control_steps_cons.
 - apply V293_control_seq_step;constructor;exact Valid.
 - eapply V293_control_steps_cons;[apply V293_control_seq_done| ].
   eapply V293_control_steps_cons;[constructor;apply V293_control_enter_valid;exact Valid|constructor].
Qed.

Theorem V293_control_exit_post_guard : forall c,
 V293_control_dispatch c=
 (Nat.eqb(V293_control_running c)1 &&
  Nat.eqb(V293_control_nesting(V293_control_exit c))0 &&
  Nat.eqb(V293_control_lock c)0).
Proof.
 intros[r n l];unfold V293_control_dispatch,V293_control_exit,V293_exit_enabled,V293_exit_depth;cbn.
 destruct(Nat.eqb r 1);reflexivity.
Qed.

(* Applying the old pre-decrement selector a second time is observably wrong. *)
Lemma V293_control_double_decrement_counterexample :
 V293_control_exit_code(V293_control 1 2 0)=spec_done None /\
 V293_control_exit_code(V293_control_exit(V293_control 1 2 0))=sched;;spec_done None.
Proof. split;reflexivity. Qed.

Definition V293_control_cells br bn bl c R :=
 V293_rdy_raw_cells
 ((((br,0%Z),Tint8,V293_byteval(V293_control_running c)))::
  (((bn,0%Z),Tint8,V293_byteval(V293_control_nesting c)))::
  (((bl,0%Z),Tint8,V293_byteval(V293_control_lock c)))::nil) R.

Theorem V293_control_cells_capture : forall br bn bl c R st,
 V293_control_valid c ->st|=V293_control_cells br bn bl c R ->
 V293_control_capture br bn bl st=Some(getabst st,c).
Proof.
 intros br bn bl[r n l]R st[Rn[N L]]Held.
 apply(V293_control_capture_owned br bn bl r n l st Rn N L).
 unfold V293_control_cells in Held.
 cbn [V293_rdy_raw_cells V293_control_running V293_control_nesting V293_control_lock] in Held.
 unfold V293_irq_controls;sep auto.
Qed.

Theorem V293_control_enter_source : forall Spec sd li I r ri t aop
 running nesting br bn bl c R,
 V293_control_valid c ->
 (forall st,st|=R ->V293_interrupt_env running nesting br bn(getgenv st)(getlenv st)) ->
 (R ==>CurLINV li t) ->
 InfRules Spec sd li I r ri
 (<||aop||> **V293_control_cells br bn bl c R)
 (V293_OSIntEnter_updates running nesting)
 (<||aop||> **V293_control_cells br bn bl(V293_control_enter c)R)t.
Proof.
 intros Spec sd li I r ri t aop running nesting br bn bl[run nest locked]R
 [Run[Nest Lock]]Env Local.
 unfold V293_control_cells,V293_control_enter;cbn.
 change(InfRules Spec sd li I r ri
 (<||aop||> **V293_rdy_raw_cells(V293_interrupt_cells br bn run nest)
  (Amapsto(bl,0%Z)Tint8 true(V293_byteval locked) **R))
 (V293_OSIntEnter_updates running nesting)
 (<||aop||> **V293_rdy_raw_cells(V293_interrupt_cells br bn run(V293_interrupt_nest_after run nest))
  (Amapsto(bl,0%Z)Tint8 true(V293_byteval locked) **R))t).
 eapply V293_OSIntEnter_updates_hoare;try eassumption.
 - intros st Held;eapply V293_star_env_r;[exact Env|exact Held].
 - apply V293_star_CurLINV_r;exact Local.
Qed.

(* Only the running=1 decrement prefix: the dispatch continuation is not
   silently discharged, and the whole OSIntExit is not claimed here. *)
Theorem V293_control_exit_source : forall Spec sd li I r ri t aop
 nesting lock br bn bl n l R,
 n<256 ->l<256 ->
 (forall st,st|=R ->V293_interrupt_env nesting lock bn bl(getgenv st)(getlenv st)) ->
 (R ==>CurLINV li t) ->
 InfRules Spec sd li I r ri
 (<||aop||> **V293_control_cells br bn bl(V293_control 1 n l)R)
 (V293_OSIntExit_decrement nesting)
 (<||aop||> **V293_control_cells br bn bl(V293_control_exit(V293_control 1 n l))R)t.
Proof.
 intros Spec sd li I r ri t aop nesting lock br bn bl n l R N L Env Local.
 eapply conseq_rule with
 (p:=<||aop||> **V293_rdy_raw_cells(V293_exit_cells bn bl n l)
   (Amapsto(br,0%Z)Tint8 true(V293_byteval 1) **R))
 (q:=<||aop||> **V293_rdy_raw_cells(V293_exit_cells bn bl(V293_exit_depth n)l)
   (Amapsto(br,0%Z)Tint8 true(V293_byteval 1) **R)).
 - intros st Held;unfold V293_control_cells,V293_exit_cells,V293_interrupt_cells in *;
   cbn [V293_rdy_raw_cells V293_control_running V293_control_nesting V293_control_lock] in *;sep auto.
 - intros st Held;unfold V293_control_cells,V293_control_exit,V293_exit_cells,V293_interrupt_cells,V293_exit_depth in *;
   cbn [V293_rdy_raw_cells V293_control_running V293_control_nesting V293_control_lock Nat.eqb] in *;sep auto.
 - eapply V293_OSIntExit_decrement_hoare;try eassumption.
   + intros st Held;eapply V293_star_env_r;[exact Env|exact Held].
   + apply V293_star_CurLINV_r;exact Local.
Qed.

(* This still uses the old builder only as a source of admissible inputs;
   the new fixed table is not an osintspec argument of that builder. *)
Section FixedBuilder.
Variables target running nesting lock:var.
Variables bt bg br bh bp bc bk brun bn bl:block.
Variable rest:list(addr*type).
Let li:=V293_irq_bound_li running nesting lock brun bn bl.
Let Inv0:=V293_ready_dynamic_exit_inv target bt bg br bh bp bc bk brun bn bl rest.
Theorem V293_fixed_control_builder_prefix : forall sd intspec i ir si t lg pre aop st,
 i<INUM ->intspec i=Some aop ->
 Some pre=BuildintPre i intspec ir si Inv0 li t lg ->st|=pre ->
 exists c,V293_control_valid c /\
 V293_control_capture brun bn bl st=Some(getabst st,c) /\
 V293_fixed_control_intspec i=Some V293_fixed_control_handler /\
 V293_control_steps sd V293_fixed_control_handler(getabst st,c)
 (V293_control_Core(V293_control_exit_code(V293_control_enter c)))
 (getabst st,V293_control_exit(V293_control_enter c)).
Proof.
 intros sd intspec i ir si t lg pre aop st Bound Lookup Pre Held.
 destruct(V293_control_builder_capture target running nesting lock bt bg br bh bp bc bk
 brun bn bl rest intspec i ir si t lg pre aop st Lookup Pre Held)as[c[Valid Capture]].
 exists c;split;[exact Valid| ];split;[exact Capture| ];split.
 - apply V293_fixed_control_lookup;exact Bound.
 - apply V293_fixed_control_handler_prefix;exact Valid.
Qed.
End FixedBuilder.
