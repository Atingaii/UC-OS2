(* Exact resource rearrangement for tick. Canonical records alone omit Next,
   and omit delay/pend/event fields after timeout. Keep these cells explicit;
   no Atrue may absorb them and no load is used to manufacture ownership. *)
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickWhileRecords.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickTaskBridge.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickLoop.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickRecordReassembly.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.code.V293OSTimeTick.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickExpiry.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List Coq.Sorting.Permutation Lia.
Import ListNotations.
Local Open Scope nat_scope.

Definition V293_tick_after_layout binding :=
  let t := fst binding in
  V293_record_layout (V293_tick_task_pointer t) (V293_tick_prio t)
    (V293_tick_binding_status true binding) (snd (snd binding))
    (V293_tick_pend_value (V293_tick_task_after t)).

Definition V293_tick_residual_cells binding next : list V293_record_cell :=
  let t := V293_tick_task_after (fst binding) in
  let b := V293_tick_block t in let base := V293_tick_base t in
  ((b,(base+20)%Z),Tcom_ptr 410%Z,Vptr next) ::
  match V293_tick_binding_status true binding with
  | rdy =>
      [((b,(base+44)%Z),Tint32,Vint32 (Int.repr (V293_tick_delay_value t)));
       ((b,(base+49)%Z),Tint8,V293_byteval (V293_tick_pend_value t))] ++
      skipn 2 (V293_tick_binding_extra binding)
  | wait os_stat_time _ =>
      [((b,(base+49)%Z),Tint8,V293_byteval (V293_tick_pend_value t))]
  | wait _ _ => []
  end.

(* A cell permutation is an exact spatial equivalence, not a projection. *)
Lemma V293_owned_cells_permutation : forall before after,
  Permutation before after -> forall s,
  s |= V293_owned_record_cells before -> s |= V293_owned_record_cells after.
Proof.
  intros before after Order. induction Order; intros s Owned;
    cbn [V293_owned_record_cells] in *.
  - exact Owned.
  - eapply astar_mono; [intros st H;exact H | exact IHOrder | exact Owned].
  - clear -Owned. sep auto.
  - apply IHOrder2. apply IHOrder1. exact Owned.
Qed.

Local Ltac tick_permute :=
 lazymatch goal with
 | |- Permutation (@nil _) (@nil _) => constructor
 | |- Permutation ?xs (?x::?ys) =>
   let rec extract before rest :=
    lazymatch rest with
    | x::?tail =>
      eapply Permutation_trans with (l':=x::(before++tail));
      [apply Permutation_sym;apply Permutation_middle |
       apply perm_skip;cbn [app];tick_permute]
    | ?h::?tail => extract (before++[h]) tail
    end
   in extract (@nil V293_record_cell) xs
 end.

Lemma V293_tick_after_layout_permutation : forall binding next,
  V293_tick_binding_valid binding ->
  Permutation
    (V293_tick_task_cells (V293_tick_task_after (fst binding)) next ++
      V293_tick_binding_extra binding)
    (V293_tick_after_layout binding ++ V293_tick_residual_cells binding next).
Proof.
  intros [[b base d stat pend y x p] [status message]] next [Valid [P Shape]].
  unfold V293_tick_task_valid in Valid; cbn in Valid.
  destruct Valid as ([Base Limit] & D & Stat & Pend & Y & X & Prio & Nonidle).
  assert (U : Int.unsigned (Int.repr base)=base)
    by (apply Int.unsigned_repr;change (0<=base<=4294967295)%Z;lia).
  destruct status as [ | reason delay].
  - cbn in Shape. inversion Shape; subst d stat y x.
    unfold V293_tick_after_layout,V293_tick_residual_cells,V293_tick_binding_extra,
      V293_tick_binding_status,V293_tick_task_after,V293_tick_task_cells,
      V293_record_layout,V293_tick_task_pointer,V293_tick_record_extra.
    cbn; rewrite U. cbn. tick_permute.
  - destruct Shape as [Shape Delay]. cbn in Shape,Delay.
    inversion Shape; subst stat y x. subst delay.
    unfold V293_tick_after_layout,V293_tick_residual_cells,V293_tick_binding_extra,
      V293_tick_binding_status,V293_tick_task_after,V293_tick_task_cells,
      V293_record_layout,V293_tick_task_pointer,V293_tick_record_extra.
    cbn [fst snd V293_tick_block V293_tick_base V293_tick_delay_value
      V293_tick_stat_value V293_tick_pend_value V293_tick_y V293_tick_x V293_tick_prio].
    rewrite U. unfold V293_tick_wait_status,V293_tick_after_stat,V293_tick_after_pend.
    destruct (Z.eqb d 1); destruct reason; cbn; tick_permute.
Qed.

(* Bidirectional: the exact layout and the explicit residual are sufficient
   to reconstruct ALL raw per-node tick resources without a second copy. *)
Theorem V293_tick_node_fields_round_trip : forall binding next R s,
  V293_tick_binding_valid binding ->
  (s |= V293_owned_record_cells
      (V293_tick_task_cells (V293_tick_task_after (fst binding)) next) **
      (V293_owned_record_cells (V293_tick_binding_extra binding) ** R) <->
   s |= V293_owned_record_cells (V293_tick_after_layout binding) **
      (V293_owned_record_cells (V293_tick_residual_cells binding next) ** R)).
Proof.
  intros binding next R s Valid.
  pose proof (V293_tick_after_layout_permutation binding next Valid) as Order.
  split; intro Owned.
  - assert (Joined : s |= V293_owned_record_cells
        (V293_tick_task_cells (V293_tick_task_after (fst binding)) next ++
          V293_tick_binding_extra binding) ** R).
    { eapply astar_mono; [ | intros st H;exact H | ].
      - intros st H. apply V293_tick_cells_append. exact H.
      - clear -Owned. sep auto. }
    eapply astar_mono in Joined;
      [ | apply V293_owned_cells_permutation;exact Order | intros st H;exact H].
    assert (Split : s |=
      (V293_owned_record_cells (V293_tick_after_layout binding) **
       V293_owned_record_cells (V293_tick_residual_cells binding next)) ** R).
    { eapply astar_mono; [ | intros st H;exact H | exact Joined].
      intros st H. apply V293_tick_cells_append. exact H. }
    clear -Split. sep auto.
  - assert (Joined : s |= V293_owned_record_cells
        (V293_tick_after_layout binding ++ V293_tick_residual_cells binding next) ** R).
    { eapply astar_mono; [ | intros st H;exact H | ].
      - intros st H. apply V293_tick_cells_append. exact H.
      - clear -Owned. sep auto. }
    eapply astar_mono in Joined;
      [ | apply V293_owned_cells_permutation;apply Permutation_sym;exact Order | intros st H;exact H].
    assert (Split : s |=
      (V293_owned_record_cells
        (V293_tick_task_cells (V293_tick_task_after (fst binding)) next) **
       V293_owned_record_cells (V293_tick_binding_extra binding)) ** R).
    { eapply astar_mono; [ | intros st H;exact H | exact Joined].
      intros st H. apply V293_tick_cells_append. exact H. }
    clear -Split. sep auto.
Qed.

Definition V293_tick_chain_layouts bindings := concat (map V293_tick_after_layout bindings).
Fixpoint V293_tick_chain_residual bindings idle : list V293_record_cell :=
  match bindings with
  | [] => []
  | binding::rest => V293_tick_residual_cells binding
      (V293_tick_head (map V293_tick_task_after (map fst rest)) idle) ++
      V293_tick_chain_residual rest idle
  end.

Local Lemma tick_cells_interleave : forall (a b c d : list V293_record_cell),
  Permutation ((a++b)++(c++d)) ((a++c)++(b++d)).
Proof.
  intros a b c d. rewrite <- !app_assoc.
  apply Permutation_app_head. apply Permutation_app_swap_app.
Qed.

Lemma V293_tick_chain_fields_permutation : forall bindings idle,
  Forall V293_tick_binding_valid bindings ->
  Permutation
    (V293_tick_chain_cells (map V293_tick_task_after (map fst bindings)) idle ++
     concat (map V293_tick_binding_extra bindings))
    (V293_tick_chain_layouts bindings ++ V293_tick_chain_residual bindings idle).
Proof.
  induction bindings as [ | binding rest IH]; intros idle Valid; [constructor | ].
  inversion Valid as [ | head tail HeadValid TailValid]; subst head tail.
  cbn [V293_tick_chain_layouts map concat V293_tick_chain_cells V293_tick_chain_residual].
  eapply Permutation_trans; [apply tick_cells_interleave | ].
  eapply Permutation_trans.
  - apply Permutation_app.
    + apply V293_tick_after_layout_permutation. exact HeadValid.
    + apply IH. exact TailValid.
  - apply tick_cells_interleave.
Qed.

(* This exact finite-chain equivalence retains every raw byte permission.
   It does NOT claim that existential canonical records determine all old
   metadata, or that the original tick can yet be called a second time. *)
Theorem V293_tick_chain_fields_round_trip : forall bindings idle R s,
  Forall V293_tick_binding_valid bindings ->
  (s |= V293_owned_record_cells
      (V293_tick_chain_cells (map V293_tick_task_after (map fst bindings)) idle ++
       concat (map V293_tick_binding_extra bindings)) ** R <->
   s |= V293_owned_record_cells
      (V293_tick_chain_layouts bindings ++ V293_tick_chain_residual bindings idle) ** R).
Proof.
  intros bindings idle R s Valid.
  pose proof (V293_tick_chain_fields_permutation bindings idle Valid) as Order.
  split; intro Owned; eapply astar_mono; [ | | exact Owned | | | exact Owned];
    try (intros st H;exact H).
  - apply V293_owned_cells_permutation. exact Order.
  - apply V293_owned_cells_permutation. apply Permutation_sym. exact Order.
Qed.

Lemma V293_tick_after_layout_pack : forall binding s,
  V293_tick_binding_valid binding ->
  s |= V293_owned_record_cells (V293_tick_after_layout binding) ->
  s |= V293_owned_task_record (V293_tick_task_pointer (fst binding))
    (Int.repr (Z.of_nat (V293_tick_prio (fst binding))))
    (V293_tick_binding_status true binding) (snd (snd binding)).
Proof.
  intros [t [status message]] s [Valid [P Shape]] Held.
  assert (Pend : V293_tick_pend_value (V293_tick_task_after t)<256).
  { unfold V293_tick_task_valid in Valid.
    destruct Valid as (Base&D&Stat&Bound&Y&X&Prio&Nonidle).
    cbn [V293_tick_task_after V293_tick_pend_value].
    unfold V293_tick_after_pend,V293_tick_expired_pend.
    destruct (Z.eqb (V293_tick_delay_value t) 1);
      [destruct (V293_tick_waiting (V293_tick_stat_value t));lia | exact Bound]. }
  unfold V293_owned_task_record. exists (V293_tick_prio t).
  exists (V293_tick_pend_value (V293_tick_task_after t)).
  apply astar_l_apure_intro; [exact Held | repeat split;try reflexivity;assumption].
Qed.

Lemma V293_tick_chain_layouts_pack : forall bindings idle message R s,
  Forall V293_tick_binding_valid bindings -> NoDup (V293_tick_record_keys bindings idle) ->
  s |= V293_owned_record_cells (V293_tick_chain_layouts bindings) **
    (V293_owned_record_cell (V293_tick_idle_cell idle) **
      (V293_owned_record_cells (V293_tick_idle_extra idle message) ** R)) ->
  s |= V293_owned_task_records (V293_tick_record_map true bindings idle message) ** R.
Proof.
  induction bindings as [ | [t [status msg]] rest IH]; intros idle message R s Valid Unique Owned.
  - cbn [V293_tick_chain_layouts map concat V293_owned_record_cells V293_tick_record_map] in Owned |- *.
    assert (Idle : s |= V293_owned_task_record idle (Int.repr 12) rdy message ** R).
    { apply V293_tick_idle_record. clear -Owned. sep auto. }
    unfold V293_owned_task_records.
    change (s |= V293_owned_task_list ((idle,(Int.repr 12,rdy,message))::nil) ** R).
    cbn [V293_owned_task_list]. clear -Idle. sep auto.
  - inversion Valid as [ | head tail HeadValid TailValid]; subst head tail.
    change (NoDup (V293_tick_task_pointer t::V293_tick_record_keys rest idle)) in Unique.
    inversion Unique as [ | key keys Fresh TailUnique]; subst key keys.
    assert (Absent : get (V293_tick_record_map true rest idle message) (V293_tick_task_pointer t)=None).
    { apply V293_tick_record_map_absent. exact Fresh. }
    cbn [V293_tick_chain_layouts map concat] in Owned.
    assert (Split : s |=
      (V293_owned_record_cells (V293_tick_after_layout (t,(status,msg))) **
       V293_owned_record_cells (V293_tick_chain_layouts rest)) **
      (V293_owned_record_cell (V293_tick_idle_cell idle) **
        (V293_owned_record_cells (V293_tick_idle_extra idle message) ** R))).
    { eapply astar_mono; [ | intros st H;exact H | exact Owned].
      intros st H. apply V293_tick_cells_append. exact H. }
    assert (Head : s |=
      V293_owned_task_record (V293_tick_task_pointer t) (Int.repr (Z.of_nat (V293_tick_prio t)))
        (V293_tick_binding_status true (t,(status,msg))) msg **
      (V293_owned_record_cells (V293_tick_chain_layouts rest) **
        (V293_owned_record_cell (V293_tick_idle_cell idle) **
          (V293_owned_record_cells (V293_tick_idle_extra idle message) ** R)))).
    { eapply astar_mono; [ | intros st H;exact H | ].
      - intros st H. exact (V293_tick_after_layout_pack (t,(status,msg)) st HeadValid H).
      -
      clear -Split. sep auto. }
    assert (TailEntry : s |= V293_owned_record_cells (V293_tick_chain_layouts rest) **
      (V293_owned_record_cell (V293_tick_idle_cell idle) **
        (V293_owned_record_cells (V293_tick_idle_extra idle message) **
          (V293_owned_task_record (V293_tick_task_pointer t) (Int.repr (Z.of_nat (V293_tick_prio t)))
            (V293_tick_binding_status true (t,(status,msg))) msg ** R)))).
    { clear -Head. sep auto. }
    pose proof (IH _ _ _ _ TailValid TailUnique TailEntry) as TailRecords.
    cbn [V293_tick_record_map]. eapply V293_owned_task_records_reassemble.
    rewrite V293_tick_delete_absent by exact Absent.
    unfold V293_tick_binding_value. cbn [fst snd]. clear -TailRecords. sep auto.
Qed.

(* Stable lossless packing interface: the SAME joint heap owns canonical
   task records, all named residual cells, and the unchanged caller frame. *)
Theorem V293_tick_chain_records_lossless : forall bindings idle message R s,
  Forall V293_tick_binding_valid bindings -> NoDup (V293_tick_record_keys bindings idle) ->
  s |= V293_owned_record_cells
      (V293_tick_chain_cells (map V293_tick_task_after (map fst bindings)) idle) **
    (V293_owned_record_cells (concat (map V293_tick_binding_extra bindings)) **
      (V293_owned_record_cell (V293_tick_idle_cell idle) **
        (V293_owned_record_cells (V293_tick_idle_extra idle message) ** R))) ->
  s |= V293_owned_task_records (V293_tick_record_map true bindings idle message) **
    (V293_owned_record_cells (V293_tick_chain_residual bindings idle) ** R).
Proof.
  intros bindings idle message R s Valid Unique Owned.
  assert (Joined : s |= V293_owned_record_cells
      (V293_tick_chain_cells (map V293_tick_task_after (map fst bindings)) idle ++
        concat (map V293_tick_binding_extra bindings)) **
      (V293_owned_record_cell (V293_tick_idle_cell idle) **
        (V293_owned_record_cells (V293_tick_idle_extra idle message) ** R))).
  { eapply astar_mono; [ | intros st H;exact H | ].
    - intros st H. apply V293_tick_cells_append. exact H.
    - clear -Owned. sep auto. }
  apply V293_tick_chain_fields_round_trip in Joined; [ | exact Valid].
  assert (Split : s |=
    (V293_owned_record_cells (V293_tick_chain_layouts bindings) **
     V293_owned_record_cells (V293_tick_chain_residual bindings idle)) **
    (V293_owned_record_cell (V293_tick_idle_cell idle) **
      (V293_owned_record_cells (V293_tick_idle_extra idle message) ** R))).
  { eapply astar_mono; [ | intros st H;exact H | exact Joined].
    intros st H. apply V293_tick_cells_append. exact H. }
  apply V293_tick_chain_layouts_pack; [exact Valid | exact Unique | ].
  clear -Split. sep auto.
Qed.
