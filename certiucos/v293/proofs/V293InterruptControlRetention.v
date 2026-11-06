(* A migration interface, not a replacement for the framework's osabst. *)
Require Import CertiOS.certiucos.v293.proofs.V293InterruptQuietBuilder.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptBindings.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitReadyDynamic.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntEnterInternal.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptReadyEnter.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCall.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.code.V293OSIntExit.
Require Import CertiOS.framework.include_frm.
Require Import Coq.Lists.List Lia.
Local Open Scope nat_scope.

Record V293_irq_control := V293_control {
 V293_control_running:nat;
 V293_control_nesting:nat;
 V293_control_lock:nat
}.
Definition V293_control_valid c :=
 V293_control_running c<256 /\ V293_control_nesting c<256 /\ V293_control_lock c<256.
Definition V293_control_enter c :=
 V293_control (V293_control_running c)
 (V293_interrupt_nest_after(V293_control_running c)(V293_control_nesting c))
 (V293_control_lock c).
Definition V293_control_exit c :=
 V293_control (V293_control_running c)
 (if Nat.eqb(V293_control_running c)1 then Nat.pred(V293_control_nesting c)
  else V293_control_nesting c) (V293_control_lock c).
Definition V293_control_dispatch c :=
 Nat.eqb(V293_control_running c)1 &&
 V293_exit_enabled(V293_control_nesting c)(V293_control_lock c).
Definition V293_control_exit_code c :=
 if V293_control_dispatch c then sched;;spec_done None else spec_done None.

(* The old four-key state is preserved exactly, not overloaded with flags. *)
Definition V293_control_state := (osabst*V293_irq_control)%type.
Definition V293_control_erase (s:V293_control_state) := fst s.
Definition V293_control_state_code (s:V293_control_state) := V293_control_exit_code(snd s).

Definition V293_control_read (br bn bl:block)(M:mem) : option V293_irq_control :=
 match load Tint8 M(br,0%Z),load Tint8 M(bn,0%Z),load Tint8 M(bl,0%Z) with
 | Some(Vint32 r),Some(Vint32 n),Some(Vint32 l) =>
   Some(V293_control(Z.to_nat(Int.unsigned r))(Z.to_nat(Int.unsigned n))(Z.to_nat(Int.unsigned l)))
 | _,_,_=>None end.
Definition V293_control_capture br bn bl st : option V293_control_state :=
 match V293_control_read br bn bl(getmem st) with
 | Some c=>Some(getabst st,c) | None=>None end.

Lemma V293_control_read_exact : forall br bn bl M r n l,
 r<256 ->n<256 ->l<256 ->
 load Tint8 M(br,0%Z)=Some(V293_byteval r) ->
 load Tint8 M(bn,0%Z)=Some(V293_byteval n) ->
 load Tint8 M(bl,0%Z)=Some(V293_byteval l) ->
 V293_control_read br bn bl M=Some(V293_control r n l).
Proof.
 intros br bn bl M r n l R N L RR RN RL.
 unfold V293_control_read;rewrite RR,RN,RL;unfold V293_byteval.
 rewrite !V293_sched_snapshot_roundtrip by assumption;reflexivity.
Qed.

Theorem V293_control_capture_owned : forall br bn bl r n l st,
 r<256 ->n<256 ->l<256 ->st|=V293_irq_controls br bn bl r n l ->
 V293_control_capture br bn bl st=Some(getabst st,V293_control r n l).
Proof.
 intros br bn bl r n l st R N L Held.
 destruct(V293_irq_controls_load br bn bl r n l st R N L Held)as[RR[RN RL]].
 unfold V293_control_capture;rewrite(V293_control_read_exact br bn bl _ r n l R N L RR RN RL).
 reflexivity.
Qed.

Lemma V293_control_capture_unique : forall br bn bl st s s',
 V293_control_capture br bn bl st=Some s ->
 V293_control_capture br bn bl st=Some s' ->s=s'.
Proof. intros;congruence. Qed.

Lemma V293_control_dispatch_iff : forall r n l,
 V293_control_dispatch(V293_control r n l)=true <-> r=1 /\ n<=1 /\ l=0.
Proof.
 intros;unfold V293_control_dispatch;cbn.
 rewrite Bool.andb_true_iff,Nat.eqb_eq,V293_exit_enabled_iff;tauto.
Qed.

Lemma V293_control_quiet_code : forall c,
 V293_control_dispatch c=false ->V293_control_exit_code c=spec_done None.
Proof. intros c H;unfold V293_control_exit_code;rewrite H;reflexivity. Qed.
Lemma V293_control_enabled_code : forall c,
 V293_control_dispatch c=true ->V293_control_exit_code c=sched;;spec_done None.
Proof. intros c H;unfold V293_control_exit_code;rewrite H;reflexivity. Qed.

Lemma V293_control_enter_valid : forall c,
 V293_control_valid c ->V293_control_valid(V293_control_enter c).
Proof.
 intros[r n l][R[N L]];unfold V293_control_valid,V293_control_enter;cbn.
 repeat split;try assumption;apply V293_interrupt_nest_bound;exact N.
Qed.
Lemma V293_control_exit_valid : forall c,
 V293_control_valid c ->V293_control_valid(V293_control_exit c).
Proof.
 intros[r n l][R[N L]];unfold V293_control_valid,V293_control_exit;cbn.
 repeat split;try assumption;destruct(Nat.eqb r 1);destruct n;cbn in *;lia.
Qed.

(* Enter is saturated at 255: the pair is not unconditionally an identity. *)
Theorem V293_control_pair_dispatch_iff : forall r n l,
 V293_control_dispatch(V293_control_enter(V293_control r n l))=true <->
 r=1 /\ n=0 /\ l=0.
Proof.
 intros r n l;unfold V293_control_enter;cbn.
 rewrite V293_control_dispatch_iff.
 unfold V293_interrupt_nest_after;split.
 - intros[R[N L]];subst r.
   change((if Nat.ltb n 255 then S n else n)<=1)in N.
   destruct(Nat.ltb n 255)eqn:E;[ |apply Nat.ltb_ge in E];lia.
 - intros[-> [-> ->]];cbn;auto.
Qed.

Lemma V293_control_pair_saturated : forall l,
 V293_control_exit(V293_control_enter(V293_control 1 255 l))=V293_control 1 254 l /\
 V293_control_exit_code(V293_control_enter(V293_control 1 255 l))=spec_done None.
Proof. intros;split;reflexivity. Qed.

(* This excludes exact deterministic classification on erasure, not every
   possible nondeterministic specification or every reachable-state invariant. *)
Theorem V293_control_erasure_obstruction : forall (O:osabst),
 ~(@ex (osabst->bool)(fun classify =>
 classify(V293_control_erase(O,V293_control 1 1 0))=
 V293_control_dispatch(V293_control 1 1 0) /\
 classify(V293_control_erase(O,V293_control 1 1 1))=
 V293_control_dispatch(V293_control 1 1 1))).
Proof. intros O[classify[Yes No]];cbn in Yes,No;congruence. Qed.

Theorem V293_control_retained_selector : forall (O:osabst),
 V293_control_erase(O,V293_control 1 1 0)=V293_control_erase(O,V293_control 1 1 1) /\
 V293_control_state_code(O,V293_control 1 1 0)=sched;;spec_done None /\
 V293_control_state_code(O,V293_control 1 1 1)=spec_done None /\
 V293_control_state_code(O,V293_control 1 1 0)<>
 V293_control_state_code(O,V293_control 1 1 1).
Proof. intros;repeat split;try reflexivity;discriminate. Qed.

(* The existing source decrement and two guards, with no action-choice rule.
   Only the dispatch body remains a premise; this is not the whole ISR. *)
Theorem V293_control_source_guards : forall Spec sd li I r ri t aop
 nesting lock bn bl n l R dispatch q,
 n<256 ->l<256 ->
 (forall st,st|=R ->V293_interrupt_env nesting lock bn bl(getgenv st)(getlenv st)) ->
 (R ==>CurLINV li t) ->
 (V293_control_dispatch(V293_control 1 n l)=true ->
  InfRules Spec sd li I r ri
  (<||aop||> **V293_rdy_raw_cells(V293_exit_cells bn bl(Nat.pred n)l)R)dispatch q t) ->
 InfRules Spec sd li I r ri
 (<||aop||> **V293_rdy_raw_cells(V293_exit_cells bn bl n l)R)
 (V293_OSIntExit_nesting_dispatch nesting lock dispatch)
 (if V293_control_dispatch(V293_control 1 n l) then q else
  <||aop||> **V293_rdy_raw_cells(V293_exit_cells bn bl(Nat.pred n)l)R)t.
Proof.
 intros Spec sd li I r ri t aop nesting lock bn bl n l R dispatch q N L Env Local Body.
 change(InfRules Spec sd li I r ri
  (<||aop||> **V293_rdy_raw_cells(V293_exit_cells bn bl n l)R)
  (V293_OSIntExit_nesting_dispatch nesting lock dispatch)
  (if V293_exit_enabled n l then q else
   <||aop||> **V293_rdy_raw_cells(V293_exit_cells bn bl(V293_exit_depth n)l)R)t).
 eapply V293_OSIntExit_nesting_dispatch_hoare;try eassumption.
 intros Depth Lock;apply Body;change(V293_exit_enabled n l=true).
 unfold V293_exit_enabled;rewrite Depth,Lock;reflexivity.
Qed.

(* Capture from the unfiltered, existing interrupt builder. This does not
   install the product state in the old operational semantics. *)
Section BuilderCapture.
Variables target running nesting lock:var.
Variables bt bg br bh bp bc bk brun bn bl:block.
Variable rest:list(addr*type).
Let li:=V293_irq_bound_li running nesting lock brun bn bl.
Let Inv0:=V293_ready_dynamic_exit_inv target bt bg br bh bp bc bk brun bn bl rest.
Theorem V293_control_builder_capture : forall intspec i ir si t lg pre aop st,
 intspec i=Some aop ->
 Some pre=BuildintPre i intspec ir si Inv0 li t lg ->
 st|=pre ->
 exists c,V293_control_valid c /\
 V293_control_capture brun bn bl st=Some(getabst st,c).
Proof.
 intros intspec i ir si t lg pre aop st Lookup Pre Held.
 unfold BuildintPre in Pre;rewrite Lookup in Pre;inversion Pre;subst pre.
 apply V293_irq_bound_builder_open in Held.
 destruct Held as[run[nest[locked Held]]].
 apply astar_l_apure_elim in Held;destruct Held as[[Run[Nest Lock]]Snapshot].
 exists(V293_control run nest locked);split.
 - unfold V293_control_valid;cbn;auto.
 - eapply V293_control_capture_owned;try eassumption.
   eapply V293_irq_bound_snapshot_controls;exact Snapshot.
Qed.
End BuilderCapture.
