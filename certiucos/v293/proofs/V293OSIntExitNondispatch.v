(* Actual InfRules for the full accepted normalized body, restricted to
   non-dispatch paths. Acquired ISR ownership is preserved, not discarded. *)
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitBoundarySwitch.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitBody.
Require Import CertiOS.certiucos.v293.proofs.V293TimeAccess.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickDelayHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntEnterInternal.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.code.V293OSIntExit.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedGuards.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List Lia.
Local Open Scope nat_scope.

Definition V293_exit_quiet_data running brun run bn bl nest locked
    saved bs value R : asrt :=
 V293_time_cell true saved bs value **
 (V293_guard_cell running brun run **
  V293_rdy_raw_cells (V293_exit_cells bn bl nest locked) R).

Lemma V293_exit_quiet_good : forall running brun run bn bl nest locked
 saved bs value R,
 GoodFrm R -> GoodFrm (V293_exit_quiet_data running brun run bn bl
 nest locked saved bs value R).
Proof.
 intros. unfold V293_exit_quiet_data,V293_guard_cell,V293_time_cell,
 V293_time_binding,V293_exit_cells,V293_interrupt_cells.
 cbn [V293_rdy_raw_cells GoodFrm Aptrmapsto]. tauto.
Qed.

Lemma V293_exit_quiet_local : forall running brun run bn bl nest locked
 saved bs value R li tid,
 (R ==> CurLINV li tid) ->
 V293_exit_quiet_data running brun run bn bl nest locked saved bs value R
 ==> CurLINV li tid.
Proof.
 intros running brun run bn bl nest locked saved bs value R li tid Local.
 unfold V293_exit_quiet_data,V293_exit_cells,V293_interrupt_cells.
 cbn [V293_rdy_raw_cells]. repeat apply V293_star_CurLINV_r. exact Local.
Qed.

Theorem V293_OSIntExit_quiet_critical : forall Spec sd li I r ri tid aop
 enabled ir si ci running brun run nesting lock bn bl nest locked saved bs value R dispatch,
 (gettopis si <= INUM)%nat -> nest<256 -> locked<256 -> (2<=nest \/ 0<locked) ->
 GoodFrm R -> (R ==> CurLINV li tid) ->
 (forall st, st |= R -> V293_interrupt_env nesting lock bn bl (getgenv st)(getlenv st)) ->
 InfRules Spec sd li I r ri
 (<||aop||> ** OS[ir,enabled,si,ci] **
  V293_exit_quiet_data running brun run bn bl nest locked saved bs value R)
 (sseq (sprim encrit)
  (sseq (V293_OSIntExit_nesting_dispatch nesting lock dispatch) (sprim excrit)))
 (<||aop||> ** OS[ir,enabled,si,ci] **
  V293_exit_quiet_data running brun run bn bl (V293_exit_depth nest) locked saved bs value R) tid.
Proof.
 intros Spec sd li I r ri tid aop enabled ir si ci running brun run nesting lock
 bn bl nest locked saved bs value R dispatch Bound N L Off GF Local Env.
 apply V293_time_critical.
 - exact Bound.
 - apply V293_exit_quiet_good;exact GF.
 - apply V293_exit_quiet_good;exact GF.
 - apply V293_exit_quiet_local;exact Local.
 - intro extra.
   eapply conseq_rule with
   (p:=<||aop||> ** V293_rdy_raw_cells (V293_exit_cells bn bl nest locked)
    (R ** (V293_time_cell true saved bs value ** (V293_guard_cell running brun run ** extra))))
   (q:=<||aop||> ** V293_rdy_raw_cells (V293_exit_cells bn bl (V293_exit_depth nest) locked)
    (R ** (V293_time_cell true saved bs value ** (V293_guard_cell running brun run ** extra)))).
   + unfold V293_exit_quiet_data,V293_exit_cells,V293_interrupt_cells.
     cbn [V293_rdy_raw_cells]. intros s H;sep auto.
   + unfold V293_exit_quiet_data,V293_exit_cells,V293_interrupt_cells.
     cbn [V293_rdy_raw_cells]. intros s H;sep auto.
   + apply V293_OSIntExit_disabled_hoare;try assumption.
     * eapply V293_star_env_l;exact Env.
     * apply V293_star_CurLINV_l;exact Local.
Qed.

Definition V293_exit_quiet_depth run nest :=
 if Nat.eqb run 1 then V293_exit_depth nest else nest.

(* No premise asks for a proof or execution of the middle, dispatch, or ports.
   The global cells are caller-owned data; production invariant access is open. *)
Theorem V293_OSIntExit_nondispatch_body : forall Spec sd li I tid aop enabled ir si ci
 running brun run nesting lock bn bl nest locked saved bs old R
 table high target current counter sched handoff,
 (gettopis si <= INUM)%nat -> run<256 -> nest<256 -> locked<256 ->
 (run=1 -> 2<=nest \/ 0<locked) ->
 GoodFrm R -> (R ==> CurLINV li tid) ->
 (forall st, st |= R -> V293_interrupt_env nesting lock bn bl (getgenv st)(getlenv st)) ->
 InfRules Spec sd li I
 (fun result => [|result=None|] **
  (<||aop||> ** OS[ir,enabled,si,ci] **
   V293_exit_quiet_data running brun run bn bl
   (V293_exit_quiet_depth run nest) locked saved bs (Vint32 Int.zero) R))
 Afalse
 (<||aop||> ** OS[ir,enabled,si,ci] **
  V293_exit_quiet_data running brun run bn bl nest locked saved bs old R)
 (V293_exit_boundary_body running nesting lock saved table high target current counter sched handoff)
 Afalse tid.
Proof.
 intros Spec sd li I tid aop enabled ir si ci running brun run nesting lock bn bl
 nest locked saved bs old R table high target current counter sched handoff
 Bound Run N L Off GF Local Env.
 unfold V293_exit_boundary_body.
 eapply seq_rule with
 (p':=<||aop||> ** OS[ir,enabled,si,ci] **
 V293_exit_quiet_data running brun run bn bl nest locked saved bs (Vint32 Int.zero) R).
 - eapply conseq_rule;[ | | apply (V293_time_zero Spec sd li I _ _ tid aop
   (V293_guard_cell running brun run **
    (V293_rdy_raw_cells (V293_exit_cells bn bl nest locked) R ** OS[ir,enabled,si,ci])) saved bs old)].
   + unfold V293_exit_quiet_data. intros s H;sep auto.
   + unfold V293_exit_quiet_data. intros s H;sep auto.
   + apply V293_star_CurLINV_r. apply V293_star_CurLINV_l.
     unfold V293_exit_cells,V293_interrupt_cells;cbn [V293_rdy_raw_cells].
     repeat apply V293_star_CurLINV_r. exact Local.
 - eapply seq_rule with
   (p':=<||aop||> ** OS[ir,enabled,si,ci] **
    V293_exit_quiet_data running brun run bn bl
    (V293_exit_quiet_depth run nest) locked saved bs (Vint32 Int.zero) R).
   + eapply V293_tick_known_ift_hoare with(flag:=Nat.eqb run 1).
     * intros s H. assert (G:s |= V293_guard_cell running brun run ** Atrue).
       { unfold V293_exit_quiet_data in H;clear -H;sep auto. }
       destruct (V293_exit_running_eval running brun run Atrue s Run G) as [V T].
       split;[exact V|split;[exact T|discriminate]].
     * unfold V293_exit_quiet_depth. destruct (Nat.eqb run 1) eqn:E.
       -- apply V293_OSIntExit_quiet_critical;try assumption.
          apply Off;apply Nat.eqb_eq;exact E.
       -- intros s H;exact H.
   + apply ret_rule. intros s H. apply astar_l_apure_intro;[exact H|reflexivity].
Qed.
