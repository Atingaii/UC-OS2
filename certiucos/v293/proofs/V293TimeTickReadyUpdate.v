(* Actual waiting-node tick rule, with one task-map witness and exact field
   permissions. Disabled entry owns the focused shared resources explicitly;
   this is not an enabled-entry borrow, full tick, or production ISR theorem. *)
Require Import CertiOS.certiucos.v293.proofs.V293TimeReadyShared.
Require Import CertiOS.certiucos.v293.proofs.V293TimeShared.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTarget.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickWhileHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickLosslessFields.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickReadyChain.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickRecordReassembly.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickWhileRecords.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickTaskBridge.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickLoop.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickExpiry.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickDelayHoare.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyTaskInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293TCBFieldsHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TCBSuccessHoare.
Require Import CertiOS.certiucos.v293.proofs.V293NullBytes.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.certiucos.v293.code.V293OSTimeTick.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.soundness.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List Coq.Sorting.Permutation Lia.
Import ListNotations.
Local Open Scope nat_scope.

Lemma V293_tick_wait_absinfer : forall sd tasks t priority reason d message R,
  get tasks t=Some (priority,wait reason (Int.repr d),message) ->
  (0<=d<=Int.max_unsigned)%Z -> can_change_aop R ->
  absinfer sd
    (<||spec_prim nil (V293_tick_wait_step t)||> **
      (Aabsdata abstcblsid (abstcblist tasks) ** R))
    (<||END None||> ** (Aabsdata abstcblsid (abstcblist
      (set tasks t (priority,V293_tick_wait_status reason d,message))) ** R)).
Proof.
  intros sd tasks t priority reason d message R Task D Free.
  apply absinfer_prim;[simpl;auto | simpl;auto | ].
  intros s O op H. destruct s as [[[[ge le] M] ir] aux].
  apply astar_l_aop'_elim in H. destruct H as [Action H].
  change (op=spec_prim nil (V293_tick_wait_step t)) in Action. subst op.
  assert (Slot : get O abstcblsid=Some (abstcblist tasks)).
  { change (get (getabst (ge,le,M,ir,aux,O,spec_prim nil (V293_tick_wait_step t)))
      abstcblsid=Some (abstcblist tasks)).
    eapply V293_star_abst_get_l;[apply V293_shared_abs_get | exact H]. }
  exists (set O abstcblsid (abstcblist
    (set tasks t (priority,V293_tick_wait_status reason d,message)))).
  exists (END None). split.
  - eapply spec_stepS;[eapply V293_tick_wait_transition;eassumption | apply spec_stepO].
  - apply astar_l_aop'_intro;[ | reflexivity].
    eapply change_aop_rule;[eapply V293_shared_replace_slot;exact H | simpl;auto].
Qed.

(* Erasing/reinstating only type facts never loses a byte permission. *)
Lemma V293_tick_owned_to_raw : forall cells R,
  V293_owned_record_cells cells ** R ==> V293_rdy_raw_cells cells R.
Proof.
  induction cells as [ | [[a tp] v] rest IH];intros R s H;
    cbn [V293_owned_record_cells V293_rdy_raw_cells] in *.
  - apply astar_l_aemp_elim;exact H.
  - unfold V293_owned_record_cell in H.
    assert (K:s |= Amapsto a tp true v ** (V293_owned_record_cells rest ** R))
      by (clear -H;sep auto).
    eapply astar_mono;[intros st Hs;exact Hs | apply IH | exact K].
Qed.
Lemma V293_tick_raw_to_owned : forall cells R,
  Forall (fun c=>let '(_,tp,v):=c in rule_type_val_match tp v=true) cells ->
  V293_rdy_raw_cells cells R ==> V293_owned_record_cells cells ** R.
Proof.
  induction cells as [ | [[a tp] v] rest IH];intros R Typed s H;
    cbn [V293_owned_record_cells V293_rdy_raw_cells] in *.
  - apply astar_l_aemp_intro;exact H.
  - inversion Typed as [ | head tail Head Tail];subst head tail.
    assert (K:s |= Amapsto a tp true v ** (V293_owned_record_cells rest ** R)).
    { eapply astar_mono;[intros st Hs;exact Hs | apply IH;exact Tail | exact H]. }
    unfold V293_owned_record_cell. clear -K Head. sep auto.
Qed.

(* Canonical waiting records do not own Next, and time-wait records do not
   own pend. These missing resources must be supplied by the caller. *)
Definition V293_tick_wait_missing t reason next : list V293_record_cell :=
  ((V293_tick_block t,(V293_tick_base t+20)%Z),Tcom_ptr 410%Z,Vptr next) ::
  match reason with
  | os_stat_time => [((V293_tick_block t,(V293_tick_base t+49)%Z),Tint8,
                      V293_byteval (V293_tick_pend_value t))]
  | _ => []
  end.
Definition V293_tick_wait_layout t reason message :=
  V293_record_layout (V293_tick_task_pointer t) (V293_tick_prio t)
    (wait reason (Int.repr (V293_tick_delay_value t))) message (V293_tick_pend_value t).

Local Ltac tick_update_permute :=
 lazymatch goal with
 | |- Permutation (@nil _) (@nil _) => constructor
 | |- Permutation ?xs (?x::?ys) =>
   let rec extract before rest :=
    lazymatch rest with
    | x::?tail => eapply Permutation_trans with (l':=x::(before++tail));
      [apply Permutation_sym;apply Permutation_middle |
       apply perm_skip;cbn [app];tick_update_permute]
    | ?h::?tail => extract (before++[h]) tail
    end
   in extract (@nil V293_record_cell) xs
 end.

Lemma V293_tick_wait_layout_permutation : forall t reason message next,
  V293_tick_binding_valid (t,(wait reason (Int.repr (V293_tick_delay_value t)),message)) ->
  Permutation
    (V293_tick_wait_layout t reason message ++ V293_tick_wait_missing t reason next)
    (V293_tick_task_cells t next ++
      V293_tick_binding_extra (t,(wait reason (Int.repr (V293_tick_delay_value t)),message))).
Proof.
  intros [b base d stat pend y x p] reason message next [Valid [P [Shape Delay]]].
  cbn in Shape. inversion Shape;subst stat y x.
  destruct Valid as ([Base Limit] & D & Stat & Pend & Y & X & Prio & Nonidle).
  cbn in Base,Limit.
  assert (U:Int.unsigned (Int.repr base)=base)
    by (apply Int.unsigned_repr;change (0<=base<=4294967295)%Z;lia).
  unfold V293_tick_wait_layout,V293_tick_wait_missing,V293_record_layout,
    V293_tick_task_pointer,V293_tick_task_cells,V293_tick_binding_extra,V293_tick_record_extra.
  cbn;rewrite U. destruct reason;cbn;tick_update_permute.
Qed.

Lemma V293_tick_wait_layout_open : forall t reason message next R,
  V293_tick_binding_valid (t,(wait reason (Int.repr (V293_tick_delay_value t)),message)) ->
  V293_owned_record_cells (V293_tick_wait_layout t reason message) **
    (V293_owned_record_cells (V293_tick_wait_missing t reason next) ** R) ==>
  V293_owned_record_cells (V293_tick_task_cells t next) **
    (V293_owned_record_cells
      (V293_tick_binding_extra (t,(wait reason (Int.repr (V293_tick_delay_value t)),message))) ** R).
Proof.
  intros t reason message next R Valid s Owned.
  assert (Joined:s |= V293_owned_record_cells
    (V293_tick_wait_layout t reason message ++ V293_tick_wait_missing t reason next) ** R).
  { eapply astar_mono;[ |intros st H;exact H | ];[intros st H;apply V293_tick_cells_append;exact H | ].
    clear -Owned;sep auto. }
  eapply astar_mono in Joined;
    [ |apply V293_owned_cells_permutation;apply V293_tick_wait_layout_permutation;exact Valid |
       intros st H;exact H].
  assert (Split:s |= (V293_owned_record_cells (V293_tick_task_cells t next) **
    V293_owned_record_cells
      (V293_tick_binding_extra (t,(wait reason (Int.repr (V293_tick_delay_value t)),message)))) ** R).
  { eapply astar_mono;[ |intros st H;exact H |exact Joined].
    intros st H;apply V293_tick_cells_append;exact H. }
  clear -Split;sep auto.
Qed.

Lemma V293_tick_cells_frame : forall cells, GoodFrm (V293_owned_record_cells cells).
Proof.
  induction cells as [ | [[a tp] v] rest IH];cbn [V293_owned_record_cells V293_owned_record_cell GoodFrm];auto.
Qed.
Lemma V293_tick_records_frame : forall tasks, GoodFrm (V293_owned_task_records tasks).
Proof.
  intro tasks. unfold V293_owned_task_records.
  induction (TcbMod.lst tasks) as [ | [t [[p status] message]] rest IH];
    cbn [V293_owned_task_list GoodFrm];[exact I | ].
  split;[ |exact IH]. unfold V293_owned_task_record. cbn [GoodFrm].
  intros q pend. split;[exact I |apply V293_tick_cells_frame].
Qed.
Lemma V293_tick_update_change : forall P, GoodInvAsrt P -> can_change_aop P.
Proof. induction P;simpl;intuition eauto. Qed.

Lemma V293_tick_after_task_typed : forall t next,
  V293_tick_task_valid t ->
  Forall (fun c=>let '(_,tp,v):=c in rule_type_val_match tp v=true)
    (V293_tick_task_cells (V293_tick_task_after t) next).
Proof.
  intros t next (Base&D&Stat&Pend&Y&X&Prio&Nonidle).
  assert (StatAfter:V293_tick_after_stat (V293_tick_delay_value t) (V293_tick_stat_value t)<256).
  { unfold V293_tick_after_stat,V293_tick_expired_stat.
    destruct (Z.eqb (V293_tick_delay_value t) 1);[destruct (V293_tick_waiting (V293_tick_stat_value t))| ];
      try exact Stat. destruct (V293_tick_status_arithmetic (V293_tick_stat_value t) Stat) as [_ [_ [_ ClearBound]]];exact ClearBound. }
  assert (PendAfter:V293_tick_after_pend (V293_tick_delay_value t)
    (V293_tick_pend_value t) (V293_tick_stat_value t)<256).
  { unfold V293_tick_after_pend,V293_tick_expired_pend.
    destruct (Z.eqb (V293_tick_delay_value t) 1);
      [destruct (V293_tick_waiting (V293_tick_stat_value t));lia | exact Pend]. }
  pose proof (V293_mask_byte_value (V293_tick_y t) ltac:(lia)) as [MaskY _].
  pose proof (V293_mask_byte_value (V293_tick_x t) X) as [MaskX _].
  cbn [V293_tick_task_cells V293_tick_task_after].
  apply Forall_forall. intros [[a tp] v] Member.
  repeat destruct Member as [Same|Member];try contradiction;
    inversion Same;subst a tp v;first [reflexivity |apply V293_byte_type;lia].
Qed.
Lemma V293_tick_bitmap_typed : forall bg br g lo hi,
  g<256 -> lo<256 -> hi<256 ->
  Forall (fun c=>let '(_,tp,v):=c in rule_type_val_match tp v=true)
    (V293_tick_bitmap_cells bg br g lo hi).
Proof. intros;repeat constructor;apply V293_byte_type;assumption. Qed.

Lemma V293_tick_wait_records_close : forall tasks t reason message next R,
  V293_tick_binding_valid (t,(wait reason (Int.repr (V293_tick_delay_value t)),message)) ->
  V293_owned_record_cells (V293_tick_task_cells (V293_tick_task_after t) next) **
    (V293_owned_record_cells
      (V293_tick_binding_extra (t,(wait reason (Int.repr (V293_tick_delay_value t)),message))) **
      (V293_owned_task_records (del tasks (V293_tick_task_pointer t)) ** R)) ==>
  V293_owned_task_records (set tasks (V293_tick_task_pointer t)
    (Int.repr (Z.of_nat (V293_tick_prio t)),
      V293_tick_wait_status reason (V293_tick_delay_value t),message)) **
    (V293_owned_record_cells
      (V293_tick_residual_cells (t,(wait reason (Int.repr (V293_tick_delay_value t)),message)) next) ** R).
Proof.
  intros tasks t reason message next R Valid s Owned.
  apply (proj1 (V293_tick_node_fields_round_trip _ next _ s Valid)) in Owned.
  assert (Packed:s |= V293_owned_task_record (V293_tick_task_pointer t)
    (Int.repr (Z.of_nat (V293_tick_prio t)))
    (V293_tick_wait_status reason (V293_tick_delay_value t)) message **
    (V293_owned_task_records (del tasks (V293_tick_task_pointer t)) **
      (V293_owned_record_cells
        (V293_tick_residual_cells (t,(wait reason (Int.repr (V293_tick_delay_value t)),message)) next) ** R))).
  { eapply astar_mono;[intros st H;exact (V293_tick_after_layout_pack
      (t,(wait reason (Int.repr (V293_tick_delay_value t)),message)) st Valid H) |intros st H;exact H | ].
    clear -Owned;sep auto. }
  apply V293_owned_task_records_reassemble;exact Packed.
Qed.

Section ReadyUpdate.
Variables br bg bp bn : block.

(* This focused assertion is exactly the shared core's task/ready/clock
   resources, plus explicit missing cells and the scanner pointer. No second
   copy of raw TCB/ready/clock resources is supplied. *)
Definition V293_tick_ready_wait_pre ct tasks es n t reason message pend lo hi entries bc next frame :=
  (CurTid ct ** V293_shared_fields ct tasks es n) **
  (V293_owned_record_cells (V293_record_layout (V293_tick_task_pointer t) (V293_tick_prio t)
    (wait reason (Int.repr (V293_tick_delay_value t))) message pend) **
  (V293_owned_task_records (del tasks (V293_tick_task_pointer t)) **
  (V293_owned_record_cells (V293_ready_cells br bg bp lo hi entries) **
  (PV (bn,Int.zero) @ Tint32 |-> Vint32 n **
  (V293_owned_record_cell (V293_tick_pointer_cell bc (V293_tick_task_pointer t)) **
  (V293_owned_record_cells (V293_tick_wait_missing t reason next) ** frame)))))).

Definition V293_tick_ready_wait_post t reason message bc next frame :=
  V293_time_ready_core br bg bp bn **
  (V293_owned_record_cell (V293_tick_pointer_cell bc next) **
  (V293_owned_record_cells
    (V293_tick_residual_cells (t,(wait reason (Int.repr (V293_tick_delay_value t)),message)) next) ** frame)).

(* Exact preservation of all bytes in the pending task, not a load-only or
   Atrue reconstruction. Other tasks, table entries, and clock are framed. *)
Lemma V293_tick_ready_wait_after_close : forall ct tasks es n t reason message lo hi entries bc next frame,
  V293_tick_binding_valid (t,(wait reason (Int.repr (V293_tick_delay_value t)),message)) ->
  get tasks (V293_tick_task_pointer t)=Some
    (Int.repr (Z.of_nat (V293_tick_prio t)),wait reason (Int.repr (V293_tick_delay_value t)),message) ->
  V293_ready_rel lo hi entries tasks ->
  let updated:=set tasks (V293_tick_task_pointer t)
    (Int.repr (Z.of_nat (V293_tick_prio t)),V293_tick_wait_status reason (V293_tick_delay_value t),message) in
  V293_owned_record_cell (V293_tick_pointer_cell bc next) **
  (V293_owned_record_cells (V293_tick_task_cells (V293_tick_task_after t) next) **
  (V293_owned_record_cells (V293_tick_bitmap_cells bg br
    (V293_tick_next_group t (V293_ready_group lo hi)) (V293_tick_next_lo t lo) (V293_tick_next_hi t hi)) **
  (V293_owned_record_cells
    (V293_tick_binding_extra (t,(wait reason (Int.repr (V293_tick_delay_value t)),message))) **
  (V293_owned_task_records (del tasks (V293_tick_task_pointer t)) **
  (V293_owned_record_cells (V293_priority_cells bp 0%Z entries) **
  ((CurTid ct ** V293_shared_fields ct updated es n) **
  (PV (bn,Int.zero) @ Tint32 |-> Vint32 n ** frame))))))) ==>
  V293_tick_ready_wait_post t reason message bc next frame.
Proof.
  intros ct tasks es n t reason message lo hi entries bc next frame Valid Task Rel.
  cbn zeta. intros s Owned.
  pose proof (V293_tick_binding_ready_rel
    (t,(wait reason (Int.repr (V293_tick_delay_value t)),message)) tasks lo hi entries Valid Task Rel)
    as [Group NewRel].
  assert (Records:s |= V293_owned_task_records (set tasks (V293_tick_task_pointer t)
    (Int.repr (Z.of_nat (V293_tick_prio t)),V293_tick_wait_status reason (V293_tick_delay_value t),message)) **
    (V293_owned_record_cells
      (V293_tick_residual_cells (t,(wait reason (Int.repr (V293_tick_delay_value t)),message)) next) **
     (V293_owned_record_cell (V293_tick_pointer_cell bc next) **
      (V293_owned_record_cells (V293_tick_bitmap_cells bg br
        (V293_tick_next_group t (V293_ready_group lo hi)) (V293_tick_next_lo t lo) (V293_tick_next_hi t hi)) **
       (V293_owned_record_cells (V293_priority_cells bp 0%Z entries) **
        ((CurTid ct ** V293_shared_fields ct
          (set tasks (V293_tick_task_pointer t)
            (Int.repr (Z.of_nat (V293_tick_prio t)),V293_tick_wait_status reason (V293_tick_delay_value t),message)) es n) **
         (PV (bn,Int.zero) @ Tint32 |-> Vint32 n ** frame))))))).
  { apply V293_tick_wait_records_close;[exact Valid | ]. clear -Owned;sep auto. }
  unfold V293_tick_ready_wait_post,V293_time_ready_core,V293_time_ready_fields,V293_ready_payload,V293_ready_owned.
  cbn [V293_tick_binding_value V293_tick_binding_status fst snd] in Group,NewRel.
  unfold V293_ready_cells. cbn [V293_tick_bitmap_cells V293_owned_record_cells] in Records.
  rewrite Group in Records.
  cbn [V293_owned_record_cells app].
  clear -Records NewRel. sep auto.
Qed.

Section NodeRule.
Variables (ct : tid) (tasks : TcbMod.map) (es : EcbMod.map) (n : int32)
  (t : V293_tick_task) (reason : tcbstats) (message : val)
  (lo hi : nat) (entries : list val) (bc : block) (next : addrval) (frame : asrt).
Let binding := (t,(wait reason (Int.repr (V293_tick_delay_value t)),message)).
Let updated := set tasks (V293_tick_task_pointer t)
  (Int.repr (Z.of_nat (V293_tick_prio t)),V293_tick_wait_status reason (V293_tick_delay_value t),message).
Let action := spec_prim nil (V293_tick_wait_step (V293_tick_task_pointer t)).
Let before := V293_tick_pointer_cell bc (V293_tick_task_pointer t)::
  (V293_tick_task_cells t next ++ V293_tick_bitmap_cells bg br (V293_ready_group lo hi) lo hi).
Let after := V293_tick_pointer_cell bc next::
  (V293_tick_task_cells (V293_tick_task_after t) next ++
   V293_tick_bitmap_cells bg br (V293_tick_next_group t (V293_ready_group lo hi))
     (V293_tick_next_lo t lo) (V293_tick_next_hi t hi)).
Let remainder slot := V293_owned_record_cells (V293_tick_binding_extra binding) **
  (V293_owned_task_records (del tasks (V293_tick_task_pointer t)) **
  (V293_owned_record_cells (V293_priority_cells bp 0%Z entries) **
  ((CurTid ct ** V293_shared_fields ct slot es n) **
  (PV (bn,Int.zero) @ Tint32 |-> Vint32 n ** frame)))).

Lemma V293_tick_ready_wait_before_open :
  V293_tick_binding_valid binding ->
  V293_tick_ready_wait_pre ct tasks es n t reason message (V293_tick_pend_value t)
    lo hi entries bc next frame ==> V293_rdy_raw_cells before (remainder tasks).
Proof.
  intros Valid s H. unfold V293_tick_ready_wait_pre in H.
  assert (Opened:s |= V293_owned_record_cells (V293_tick_task_cells t next) **
    (V293_owned_record_cells (V293_tick_binding_extra binding) **
    (V293_owned_task_records (del tasks (V293_tick_task_pointer t)) **
    (V293_owned_record_cells (V293_ready_cells br bg bp lo hi entries) **
    ((CurTid ct ** V293_shared_fields ct tasks es n) **
    (PV (bn,Int.zero) @ Tint32 |-> Vint32 n **
    (V293_owned_record_cell (V293_tick_pointer_cell bc (V293_tick_task_pointer t)) ** frame))))))).
  { apply V293_tick_wait_layout_open;[exact Valid | ].
    unfold V293_tick_wait_layout. clear -H;sep auto. }
  apply V293_tick_owned_to_raw.
  unfold before,remainder. unfold V293_ready_cells in Opened.
  cbn [V293_owned_record_cells app V293_tick_pointer_cell V293_tick_bitmap_cells] in Opened |- *.
  (* The task cell list is also finite even when its values are symbolic. *)
  cbn [V293_tick_task_cells V293_owned_record_cells app] in Opened |- *.
  cbn [V293_tick_bitmap_cells V293_owned_record_cells app].
  clear -Opened;sep auto.
Qed.

Lemma V293_tick_ready_wait_raw_close :
  V293_tick_binding_valid binding ->
  get tasks (V293_tick_task_pointer t)=Some (V293_tick_binding_value false binding) ->
  V293_ready_rel lo hi entries tasks ->
  V293_rdy_raw_cells after (remainder updated) ==>
    V293_tick_ready_wait_post t reason message bc next frame.
Proof.
  intros Valid Task Rel s H.
  assert (G:V293_ready_group lo hi<256)
    by (unfold V293_ready_group;destruct (lo=?0);destruct (hi=?0);lia).
  pose proof Rel as RelFull. destruct Rel as [Lo [Hi Rest]].
  pose proof (V293_tick_next_bitmap_bounds t (V293_ready_group lo hi) lo hi (proj1 Valid) G Lo Hi)
    as [GN [LN HN]].
  assert (Typed:Forall (fun c=>let '(_,tp,v):=c in rule_type_val_match tp v=true) after).
  { unfold after. constructor;[reflexivity | ]. apply Forall_app. split.
    - apply V293_tick_after_task_typed;exact (proj1 Valid).
    - apply V293_tick_bitmap_typed;assumption. }
  pose proof (V293_tick_raw_to_owned after (remainder updated) Typed s H) as Owned.
  eapply V293_tick_ready_wait_after_close with (ct:=ct) (tasks:=tasks) (es:=es) (n:=n)
    (lo:=lo) (hi:=hi) (entries:=entries);[exact Valid |exact Task |exact RelFull | ].
  unfold after,remainder in Owned. cbn [V293_tick_task_cells V293_tick_bitmap_cells
    V293_tick_pointer_cell V293_owned_record_cells app] in Owned |- *.
  clear -Owned;sep auto.
Qed.

Lemma V293_tick_ready_wait_finish : forall sd ir si ci,
  V293_tick_binding_valid binding ->
  get tasks (V293_tick_task_pointer t)=Some (V293_tick_binding_value false binding) ->
  V293_ready_rel lo hi entries tasks -> can_change_aop frame ->
  absinfer sd (<||action||> ** OS[ir,false,si,ci] ** V293_rdy_raw_cells after (remainder tasks))
    (<||END None||> ** OS[ir,false,si,ci] ** V293_tick_ready_wait_post t reason message bc next frame).
Proof.
  intros sd ir si ci Valid Task Rel Free.
  set (other:=V293_owned_record_cells (V293_tick_binding_extra binding) **
    (V293_owned_task_records (del tasks (V293_tick_task_pointer t)) **
    (V293_owned_record_cells (V293_priority_cells bp 0%Z entries) **
    ((CurTid ct ** (Aabsdata curtid (oscurt ct) **
       (Aabsdata absecblsid (absecblist es) ** Aabsdata ostmid (ostm n)))) **
    (PV (bn,Int.zero) @ Tint32 |-> Vint32 n ** frame))))).
  eapply absinfer_conseq with
    (p:=<||action||> ** (Aabsdata abstcblsid (abstcblist tasks) **
      (OS[ir,false,si,ci] ** V293_rdy_raw_cells after other)))
    (q:=<||END None||> ** (Aabsdata abstcblsid (abstcblist updated) **
      (OS[ir,false,si,ci] ** V293_rdy_raw_cells after other))).
  - intros s H.
    assert (K:s |= <||END None||> ** OS[ir,false,si,ci] ** V293_rdy_raw_cells after (remainder updated)).
    { unfold other,remainder,V293_shared_fields,after in *.
      cbn [V293_rdy_raw_cells V293_tick_task_cells V293_tick_bitmap_cells V293_tick_pointer_cell app] in *.
      clear -H;sep auto. }
    eapply astar_mono;[intros st Hs;exact Hs | |exact K].
    apply astar_mono;[intros st Hs;exact Hs |apply V293_tick_ready_wait_raw_close;assumption].
  - unfold action,updated. apply V293_tick_wait_absinfer.
    + exact Task.
    + exact (proj1 (proj2 (proj1 Valid))).
    + cbn [can_change_aop]. split;[repeat split;exact Logic.I | ].
      unfold after,other.
      cbn [V293_rdy_raw_cells V293_tick_task_cells V293_tick_bitmap_cells app can_change_aop].
      repeat split;try exact Logic.I;try exact Free;
        apply V293_tick_update_change;first [apply V293_owned_cells_good |apply V293_task_list_good].
  - unfold other,remainder,V293_shared_fields,after.
    cbn [V293_rdy_raw_cells V293_tick_task_cells V293_tick_bitmap_cells V293_tick_pointer_cell app].
    intros s H;sep auto.
Qed.

(* The real four-part original iteration, initially DISABLED. Its physical
   stores are proved by InfRules, then the existing task primitive is reduced
   and the same shared clock/task/ready core is closed without Atrue. *)
Theorem V293_tick_ready_wait_iteration_hoare : forall Spec sd li I r ri tid
  ptcb rows group ir si ci,
  NoAbs li -> V293_tick_binding_valid binding ->
  get tasks (V293_tick_task_pointer t)=Some (V293_tick_binding_value false binding) ->
  V293_ready_rel lo hi entries tasks ->
  (forall st, st |= frame -> V293_tick_delay_env ptcb rows group bc br bg (getgenv st) (getlenv st)) ->
  ((CurTid ct ** frame) ==> CurLINV li tid) -> GoodFrm frame -> can_change_aop frame ->
  (gettopis si<=INUM)%nat ->
  InfRules Spec sd li I r ri
    (<||action||> ** OS[ir,false,si,ci] **
      V293_tick_ready_wait_pre ct tasks es n t reason message (V293_tick_pend_value t)
        lo hi entries bc next frame)
    (V293_tick_iteration ptcb rows group)
    (<||END None||> ** OS[ir,false,si,ci] ** V293_tick_ready_wait_post t reason message bc next frame) tid.
Proof.
  intros Spec sd li I r ri tid ptcb rows group ir si ci NA Valid Task Rel Env Inv GF Free Bound.
  eapply abscsq_rule with
    (p:=<||action||> ** OS[ir,false,si,ci] ** V293_rdy_raw_cells before (remainder tasks))
    (q:=<||action||> ** OS[ir,false,si,ci] ** V293_rdy_raw_cells after (remainder tasks)).
  - exact NA.
  - apply absinfer_conseq with
      (p:=<||action||> ** OS[ir,false,si,ci] ** V293_rdy_raw_cells before (remainder tasks))
      (q:=<||action||> ** OS[ir,false,si,ci] ** V293_rdy_raw_cells before (remainder tasks)).
    + intros st H;exact H.
    + apply absinfer_eq.
    + apply astar_mono;[intros st H;exact H | ].
      apply astar_mono;[intros st H;exact H |apply V293_tick_ready_wait_before_open;exact Valid].
  - apply V293_tick_ready_wait_finish;assumption.
  - unfold before,after. apply V293_tick_node_iteration_hoare.
    + exact (proj1 Valid).
    + unfold V293_ready_group;destruct (lo=?0);destruct (hi=?0);lia.
    + exact (proj1 Rel).
    + exact (proj1 (proj2 Rel)).
    + unfold remainder. repeat apply V293_star_env_r. exact Env.
    + unfold remainder. intros st H.
      apply V293_CurLINV_extend with (extra:=Atrue).
      eapply astar_mono;[exact Inv|intros s Hs;exact Hs| ]. clear -H;sep auto.
    + unfold remainder. cbn [GoodFrm]. repeat split;try exact Logic.I;try exact GF;
        first [apply V293_tick_cells_frame |apply V293_tick_records_frame].
    + exact Bound.
Qed.

Theorem V293_tick_ready_wait_iteration_semantics : forall Spec sd li I r ri tid
  ptcb rows group ir si ci,
  NoAbs li -> V293_tick_binding_valid binding ->
  get tasks (V293_tick_task_pointer t)=Some (V293_tick_binding_value false binding) ->
  V293_ready_rel lo hi entries tasks ->
  (forall st, st |= frame -> V293_tick_delay_env ptcb rows group bc br bg (getgenv st) (getlenv st)) ->
  ((CurTid ct ** frame) ==> CurLINV li tid) -> GoodFrm frame -> can_change_aop frame ->
  (gettopis si<=INUM)%nat ->
  simulation.RuleSem Spec sd li I r ri
    (<||action||> ** OS[ir,false,si,ci] **
      V293_tick_ready_wait_pre ct tasks es n t reason message (V293_tick_pend_value t)
        lo hi entries bc next frame)
    (V293_tick_iteration ptcb rows group)
    (<||END None||> ** OS[ir,false,si,ci] ** V293_tick_ready_wait_post t reason message bc next frame) tid.
Proof. intros. apply RuleSound. apply V293_tick_ready_wait_iteration_hoare;assumption. Qed.

End NodeRule.
End ReadyUpdate.
