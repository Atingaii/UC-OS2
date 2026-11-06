(* Construct the next owned tick entry from the ORIGINAL execution's raw
   resources. Do not invert existential canonical records or duplicate their
   permissions. The fixed CPU hook remains an open, separate checkpoint. *)
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickLosslessReturn.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickLosslessFields.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickWhileRecords.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickTaskBridge.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickLoop.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickExpiry.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickStorage.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickRawReadyReturn.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickPostHookReady.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickReadyChain.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List Coq.Sorting.Permutation Lia.
Import ListNotations.
Local Open Scope nat_scope.

Definition V293_tick_reentry_binding binding :=
  (V293_tick_task_after (fst binding),
    (V293_tick_binding_status true binding,snd (snd binding))).
Definition V293_tick_reentry_orphan binding : list V293_record_cell :=
  match V293_tick_binding_status true binding with
  | rdy => skipn 2 (V293_tick_binding_extra binding)
  | wait _ _ => []
  end.

Theorem V293_tick_reentry_binding_valid : forall binding,
  V293_tick_binding_valid binding ->
  V293_tick_binding_valid (V293_tick_reentry_binding binding).
Proof.
  intros [[b base d stat pend y x p] [status message]] [Valid [P Shape]].
  unfold V293_tick_task_valid in Valid; cbn in Valid.
  destruct Valid as ([Base Limit]&D&Stat&Pend&Y&X&Prio&Nonidle).
  change (p<13) in P.
  destruct status as [ | reason delay].
  - cbn in Shape. inversion Shape; subst d stat y x.
    unfold V293_tick_binding_valid,V293_tick_reentry_binding,V293_tick_binding_status,
      V293_tick_task_after,V293_tick_task_valid,V293_tick_wait_node,
      V293_tick_after_delay,V293_tick_after_stat,V293_tick_after_pend.
    cbn. repeat split;try assumption;try reflexivity;lia.
  - destruct Shape as [Shape Delay]. cbn in Shape,Delay.
    inversion Shape; subst stat y x. subst delay.
    assert (Dnext : (0<=V293_tick_after_delay d<=Int.max_unsigned)%Z).
    { change (0<=d<=4294967295)%Z in D.
      change (0<=V293_tick_after_delay d<=4294967295)%Z.
      unfold V293_tick_after_delay. destruct (Z.eqb d 0) eqn:E;
        [lia | apply Z.eqb_neq in E;lia]. }
    destruct (Z.eqb d 1) eqn:One.
    + apply Z.eqb_eq in One. subst d. destruct reason.
      * change (V293_tick_binding_valid (V293_tick_wait_node b base 0 os_stat_time 1 p,(rdy,message))).
        split.
        -- apply V293_tick_wait_node_valid;[split;assumption|change (0<=0<=4294967295)%Z;lia|lia|exact P|exact Nonidle].
        -- split;[exact P|reflexivity].
      * change (V293_tick_binding_valid (V293_tick_wait_node b base 0 os_stat_time 1 p,(rdy,message))).
        split.
        -- apply V293_tick_wait_node_valid;[split;assumption|change (0<=0<=4294967295)%Z;lia|lia|exact P|exact Nonidle].
        -- split;[exact P|reflexivity].
      * change (V293_tick_binding_valid (V293_tick_wait_node b base 0 os_stat_time 0 p,(rdy,message))).
        split.
        -- apply V293_tick_wait_node_valid;[split;assumption|change (0<=0<=4294967295)%Z;lia|lia|exact P|exact Nonidle].
        -- split;[exact P|reflexivity].
      * change (V293_tick_binding_valid (V293_tick_wait_node b base 0 os_stat_time 1 p,(rdy,message))).
        split.
        -- apply V293_tick_wait_node_valid;[split;assumption|change (0<=0<=4294967295)%Z;lia|lia|exact P|exact Nonidle].
        -- split;[exact P|reflexivity].
      * change (V293_tick_binding_valid (V293_tick_wait_node b base 0 os_stat_time 1 p,(rdy,message))).
        split.
        -- apply V293_tick_wait_node_valid;[split;assumption|change (0<=0<=4294967295)%Z;lia|lia|exact P|exact Nonidle].
        -- split;[exact P|reflexivity].
    + unfold V293_tick_binding_valid,V293_tick_reentry_binding,V293_tick_binding_status,
        V293_tick_task_after,V293_tick_wait_status,V293_tick_after_stat,V293_tick_after_pend.
      cbn [fst snd V293_tick_block V293_tick_base V293_tick_delay_value V293_tick_stat_value
        V293_tick_pend_value V293_tick_y V293_tick_x V293_tick_prio].
      rewrite One.
      split.
      * change (V293_tick_task_valid (V293_tick_wait_node b base (V293_tick_after_delay d) reason pend p)).
        apply V293_tick_wait_node_valid;try assumption. split;assumption.
      * split;[exact P|split;reflexivity].

Qed.

Lemma V293_tick_reentry_pointer : forall binding,
  V293_tick_task_pointer (fst (V293_tick_reentry_binding binding))=
  V293_tick_task_pointer (fst binding).
Proof. intros [t [status message]]. reflexivity. Qed.

Lemma V293_tick_reentry_value : forall binding,
  V293_tick_binding_value false (V293_tick_reentry_binding binding)=
  V293_tick_binding_value true binding.
Proof. intros [t [status message]]. reflexivity. Qed.

Theorem V293_tick_reentry_record_map : forall bindings idle message,
  V293_tick_record_map false (map V293_tick_reentry_binding bindings) idle message=
  V293_tick_record_map true bindings idle message.
Proof.
  induction bindings as [ | binding rest IH];intros idle message;[reflexivity| ].
  cbn [map V293_tick_record_map]. rewrite V293_tick_reentry_pointer,
    V293_tick_reentry_value,IH. reflexivity.
Qed.

Lemma V293_tick_reentry_keys : forall bindings idle,
  V293_tick_record_keys (map V293_tick_reentry_binding bindings) idle=
  V293_tick_record_keys bindings idle.
Proof.
  intros bindings idle. unfold V293_tick_record_keys. rewrite map_map.
  reflexivity.
Qed.

Lemma V293_tick_reentry_nodes : forall bindings,
  map fst (map V293_tick_reentry_binding bindings)=map V293_tick_task_after (map fst bindings).
Proof. intros bindings. rewrite !map_map. reflexivity. Qed.

Lemma V293_tick_reentry_head : forall bindings idle,
  V293_tick_head (map fst (map V293_tick_reentry_binding bindings)) idle=
  V293_tick_head (map fst bindings) idle.
Proof. intros [ | binding rest] idle;[reflexivity|apply V293_tick_reentry_pointer]. Qed.

(* Timeout event pointers remain owned frame cells, even though the new ready
   record and next iteration no longer read them. No Atrue disposal. *)
Lemma V293_tick_reentry_extra : forall binding,
  V293_tick_binding_extra binding=
  V293_tick_binding_extra (V293_tick_reentry_binding binding) ++ V293_tick_reentry_orphan binding.
Proof.
  intros [t [status message]]. destruct status as [ | reason delay].
  - reflexivity.
  - unfold V293_tick_binding_extra,V293_tick_reentry_binding,V293_tick_reentry_orphan,
      V293_tick_binding_status,V293_tick_wait_status.
    cbn [fst snd]. destruct (Z.eqb (V293_tick_delay_value t) 1);destruct reason;reflexivity.
Qed.

Theorem V293_tick_reentry_extras_permutation : forall bindings,
  Permutation (concat (map V293_tick_binding_extra bindings))
    (concat (map V293_tick_binding_extra (map V293_tick_reentry_binding bindings)) ++
      concat (map V293_tick_reentry_orphan bindings)).
Proof.
  induction bindings as [ | binding rest IH];[constructor| ].
  cbn [map concat]. rewrite (V293_tick_reentry_extra binding).
  eapply Permutation_trans.
  - apply Permutation_app_head. exact IH.
  - rewrite <- !app_assoc. apply Permutation_app_head. apply Permutation_app_swap_app.
Qed.

Theorem V293_tick_reentry_valid : forall bindings,
  Forall V293_tick_binding_valid bindings ->
  Forall V293_tick_binding_valid (map V293_tick_reentry_binding bindings).
Proof.
  intros bindings Valid. apply Forall_map. eapply Forall_impl;[ |exact Valid].
  intros binding Held. exact (V293_tick_reentry_binding_valid binding Held).
Qed.

Lemma V293_tick_reentry_extras_owned : forall bindings R s,
  s |= V293_owned_record_cells (concat (map V293_tick_binding_extra bindings)) ** R ->
  s |= V293_owned_record_cells
    (concat (map V293_tick_binding_extra (map V293_tick_reentry_binding bindings))) **
    (V293_owned_record_cells (concat (map V293_tick_reentry_orphan bindings)) ** R).
Proof.
  intros bindings R s Held.
  assert (Ordered : s |= V293_owned_record_cells
    (concat (map V293_tick_binding_extra (map V293_tick_reentry_binding bindings)) ++
      concat (map V293_tick_reentry_orphan bindings)) ** R).
  { eapply astar_mono;[ |intros st H;exact H|exact Held].
    intros st H. eapply V293_owned_cells_permutation;[apply V293_tick_reentry_extras_permutation|exact H]. }
  assert (Split : s |= (V293_owned_record_cells
    (concat (map V293_tick_binding_extra (map V293_tick_reentry_binding bindings))) **
      V293_owned_record_cells (concat (map V293_tick_reentry_orphan bindings))) ** R).
  { eapply astar_mono;[ |intros st H;exact H|exact Ordered].
    intros st H. apply V293_tick_cells_append. exact H. }
  clear -Split. sep auto.
Qed.

(* Only these two existing abstract slots change. Arbitrary disjoint frame
   resources are retained by the framework replacement lemma, not rebased. *)
Lemma V293_tick_reentry_shared : forall current oldtasks newtasks events oldnow newnow R
  ge le M ir aux O op,
  (ge,le,M,ir,aux,O,op) |= V293_shared_fields current oldtasks events oldnow ** R ->
  (ge,le,M,ir,aux,set (set O ostmid (ostm newnow)) abstcblsid (abstcblist newtasks),op) |=
    V293_shared_fields current newtasks events newnow ** R.
Proof.
  intros current oldtasks newtasks events oldnow newnow R ge le M ir aux O op Held.
  assert (Clock : (ge,le,M,ir,aux,O,op) |=
    Aabsdata ostmid (ostm oldnow) **
      (Aabsdata abstcblsid (abstcblist oldtasks) **
        ((Aabsdata curtid (oscurt current) ** Aabsdata absecblsid (absecblist events)) ** R))).
  { unfold V293_shared_fields in Held. clear -Held. sep auto. }
  apply V293_shared_replace_slot with (new:=ostm newnow) in Clock.
  assert (Tasks : (ge,le,M,ir,aux,set O ostmid (ostm newnow),op) |=
    Aabsdata abstcblsid (abstcblist oldtasks) **
      (Aabsdata ostmid (ostm newnow) **
        ((Aabsdata curtid (oscurt current) ** Aabsdata absecblsid (absecblist events)) ** R)))
    by (clear -Clock;sep auto).
  apply V293_shared_replace_slot with (new:=abstcblist newtasks) in Tasks.
  unfold V293_shared_fields. clear -Tasks. sep auto.
Qed.
