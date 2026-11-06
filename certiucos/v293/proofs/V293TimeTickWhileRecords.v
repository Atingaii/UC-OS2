(* The ORIGINAL complete while, with jointly owned canonical task records.
   Ready tasks and the actual idle guard are included. Suspension/flags and
   the production ISR invariant are not represented by this interface. *)
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickRecordReassembly.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickTaskBridge.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickLoop.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.code.V293OSTimeTick.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Definition V293_tick_binding_valid (binding : V293_tick_task * (taskstatus * val)) :=
  let '(t,(status,message)) := binding in
  V293_tick_task_valid t /\ V293_tick_prio t<13 /\
  match status with
  | rdy => t=V293_tick_wait_node (V293_tick_block t) (V293_tick_base t) 0
      os_stat_time (V293_tick_pend_value t) (V293_tick_prio t)
  | wait reason delay =>
      t=V293_tick_wait_node (V293_tick_block t) (V293_tick_base t)
        (V293_tick_delay_value t) reason (V293_tick_pend_value t) (V293_tick_prio t) /\
      delay=Int.repr (V293_tick_delay_value t)
  end.
Definition V293_tick_binding_extra (binding : V293_tick_task * (taskstatus * val)) :=
  let '(t,(status,message)) := binding in
  V293_tick_record_extra (V293_tick_block t) (V293_tick_base t) (V293_tick_prio t)
    (match status with rdy => os_stat_time | wait reason _ => reason end) message.
Definition V293_tick_binding_status (after : bool) (binding : V293_tick_task * (taskstatus * val)) :=
  let '(t,(status,message)) := binding in
  if after then
    match status with rdy => rdy | wait reason _ => V293_tick_wait_status reason (V293_tick_delay_value t) end
  else status.
Definition V293_tick_binding_value (after : bool) (binding : V293_tick_task * (taskstatus * val)) : abstcb.B :=
  (Int.repr (Z.of_nat (V293_tick_prio (fst binding))),
   V293_tick_binding_status after binding,snd (snd binding)).
Fixpoint V293_tick_record_map (after : bool) (bindings : list (V293_tick_task * (taskstatus * val))) idle message : TcbMod.map :=
  match bindings with
  | [] => sig idle (Int.repr 12,rdy,message)
  | binding::rest => set (V293_tick_record_map after rest idle message)
      (V293_tick_task_pointer (fst binding)) (V293_tick_binding_value after binding)
  end.
Definition V293_tick_record_keys (bindings : list (V293_tick_task * (taskstatus * val))) idle :=
  map (fun binding => V293_tick_task_pointer (fst binding)) bindings ++ [idle].
Definition V293_tick_idle_extra idle message := tl (V293_record_layout idle 12 rdy message 0).

Lemma V293_tick_record_map_absent : forall bindings idle message after t,
  ~ In t (V293_tick_record_keys bindings idle) ->
  get (V293_tick_record_map after bindings idle message) t=None.
Proof.
  induction bindings as [ | binding rest IH]; intros idle message after t Apart.
  - cbn [V293_tick_record_map]. apply map_get_sig'.
    intro Same. apply Apart. change (In t [idle]). left. congruence.
  - cbn [V293_tick_record_map]. rewrite map_get_set'.
    + apply IH. intro Member. apply Apart. right. exact Member.
    + intro Same. apply Apart. left. congruence.
Qed.

Lemma V293_tick_delete_absent : forall (tasks : TcbMod.map) t,
  get tasks t=None -> del tasks t=tasks.
Proof.
  intros tasks t Missing. apply TcbMod.extensionality. intro u.
  change (get (del tasks t) u=get tasks u). rewrite map_del_sem.
  match goal with |- context [if ?decision then _ else _] => destruct decision as [Same|Apart] end;
    [subst u;symmetry;exact Missing | reflexivity].
Qed.

Lemma V293_tick_binding_record_after : forall binding next R s,
  V293_tick_binding_valid binding ->
  s |= V293_owned_record_cells (V293_tick_task_cells (V293_tick_task_after (fst binding)) next) **
    (V293_owned_record_cells (V293_tick_binding_extra binding) ** R) ->
  s |= V293_owned_task_record (V293_tick_task_pointer (fst binding))
    (Int.repr (Z.of_nat (V293_tick_prio (fst binding))))
    (V293_tick_binding_status true binding) (snd (snd binding)) ** (R ** Atrue).
Proof.
  intros [t [status message]] next R s [Valid [P Shape]] Owned.
  destruct t as [b base d stat pend y x p].
  destruct status as [ | reason delay].
  - cbn in Shape. inversion Shape; subst d stat y x.
    destruct s as [[[[[[ge le] M] ir] aux] O] op].
    cbn [V293_tick_binding_status V293_tick_binding_extra fst snd] in *.
    unfold V293_tick_task_valid in Valid; cbn in Valid.
    destruct Valid as ([Base Limit] & D & Stat & Pend & Y & X & Prio & Nonidle).
    assert (U:Int.unsigned (Int.repr base)=base) by (apply Int.unsigned_repr;change (0<=base<=4294967295)%Z;lia).
    assert (Cells : (ge,le,M,ir,aux,O,op) |=
      V293_owned_record_cells (V293_record_layout (b,Int.repr base) p rdy message 0) ** (R ** Atrue)).
    { unfold V293_record_layout. cbn [fst snd]; rewrite U.
      cbn [V293_tick_task_after V293_tick_task_cells V293_tick_task_pointer
        V293_tick_block V293_tick_base V293_tick_delay_value V293_tick_stat_value
        V293_tick_pend_value V293_tick_y V293_tick_x V293_tick_prio
        V293_tick_after_delay V293_tick_after_stat V293_tick_after_pend
        V293_tick_record_extra app V293_owned_record_cells] in Owned |- *.
      clear -Owned. sep auto. }
    eapply astar_mono; [ | | exact Cells]; [ | intros;assumption].
    intros st Held. unfold V293_owned_task_record.
    change (p<13) in P. exists p. exists 0. apply astar_l_apure_intro; [exact Held | repeat split;try reflexivity;lia].
  - destruct Shape as [Shape Delay]. cbn in Shape,Delay.
    inversion Shape; subst stat y x. subst delay.
    unfold V293_tick_task_valid in Valid; cbn in Valid.
    destruct Valid as (Base & D & Stat & Pend & Y & X & Prio & Nonidle).
    destruct s as [[[[[[ge le] M] ir] aux] O] op].
    change ((ge,le,M,ir,aux,O,op) |=
      V293_owned_task_record (b,Int.repr base) (Int.repr (Z.of_nat p))
        (V293_tick_wait_status reason d) message ** (R ** Atrue)).
    eapply V293_tick_wait_record_after_frame; [exact Base | exact P | exact Pend | exact Owned].
Qed.

Lemma V293_tick_idle_record : forall idle message R s,
  s |= V293_owned_record_cell (V293_tick_idle_cell idle) **
    (V293_owned_record_cells (V293_tick_idle_extra idle message) ** R) ->
  s |= V293_owned_task_record idle (Int.repr 12) rdy message ** R.
Proof.
  intros idle message R s Owned.
  assert (Cells : s |= V293_owned_record_cells (V293_record_layout idle 12 rdy message 0) ** R).
  { unfold V293_tick_idle_extra,V293_record_layout,V293_tick_idle_cell in *.
    cbn [tl app V293_owned_record_cells] in *. clear -Owned. sep auto. }
  eapply astar_mono; [ | | exact Cells]; [ | intros;assumption].
  intros st Held. unfold V293_owned_task_record.
  exists 12. exists 0. apply astar_l_apure_intro; [exact Held | repeat split;reflexivity || lia].
Qed.

(* Raw chain and extra cells are jointly separated BEFORE they are converted.
   No second copy of either a future task or the idle priority is assumed. *)
Theorem V293_tick_chain_records_after : forall bindings idle message R s,
  Forall V293_tick_binding_valid bindings -> NoDup (V293_tick_record_keys bindings idle) ->
  s |= V293_owned_record_cells
      (V293_tick_chain_cells (map V293_tick_task_after (map fst bindings)) idle) **
    (V293_owned_record_cells (concat (map V293_tick_binding_extra bindings)) **
    (V293_owned_record_cell (V293_tick_idle_cell idle) **
    (V293_owned_record_cells (V293_tick_idle_extra idle message) ** R))) ->
  s |= V293_owned_task_records (V293_tick_record_map true bindings idle message) ** (R ** Atrue).
Proof.
  induction bindings as [ | [t [status msg]] rest IH]; intros idle message R s Valid Unique Owned.
  - cbn [map concat V293_tick_chain_cells V293_owned_record_cells V293_tick_record_map] in Owned |- *.
    assert (Idle : s |= V293_owned_task_record idle (Int.repr 12) rdy message ** R).
    { apply V293_tick_idle_record. clear -Owned. sep auto. }
    unfold V293_owned_task_records. change (s |= V293_owned_task_list ((idle,(Int.repr 12,rdy,message))::nil) ** (R ** Atrue)).
    cbn [V293_owned_task_list]. clear -Idle. sep auto.
  - inversion Valid as [ | head tail HeadValid TailValid]; subst head tail.
    change (NoDup (V293_tick_task_pointer t::V293_tick_record_keys rest idle)) in Unique.
    inversion Unique as [ | key keys Fresh TailUnique]; subst key keys.
    assert (Absent : get (V293_tick_record_map true rest idle message) (V293_tick_task_pointer t)=None).
    { apply V293_tick_record_map_absent. exact Fresh. }
    assert (Opened : s |=
      V293_owned_record_cells (V293_tick_task_cells (V293_tick_task_after t)
        (V293_tick_head (map V293_tick_task_after (map fst rest)) idle)) **
      (V293_owned_record_cells (V293_tick_binding_extra (t,(status,msg))) **
      (V293_owned_record_cells (V293_tick_chain_cells (map V293_tick_task_after (map fst rest)) idle) **
      (V293_owned_record_cells (concat (map V293_tick_binding_extra rest)) **
      (V293_owned_record_cell (V293_tick_idle_cell idle) **
      (V293_owned_record_cells (V293_tick_idle_extra idle message) ** R)))))).
    { cbn [map concat V293_tick_chain_cells] in Owned.
      assert (Split : s |=
        (V293_owned_record_cells (V293_tick_task_cells (V293_tick_task_after t)
          (V293_tick_head (map V293_tick_task_after (map fst rest)) idle)) **
         V293_owned_record_cells (V293_tick_chain_cells (map V293_tick_task_after (map fst rest)) idle)) **
        ((V293_owned_record_cells (V293_tick_binding_extra (t,(status,msg))) **
          V293_owned_record_cells (concat (map V293_tick_binding_extra rest))) **
         (V293_owned_record_cell (V293_tick_idle_cell idle) **
          (V293_owned_record_cells (V293_tick_idle_extra idle message) ** R)))).
      { eapply astar_mono; [ | | exact Owned].
        - intros st H. apply V293_tick_cells_append. exact H.
        - intros st H. eapply astar_mono; [ | | exact H].
          + intros st0 H0. apply V293_tick_cells_append. exact H0.
          + intros st0 H0. exact H0. }
      clear -Split. sep auto. }
    pose proof (V293_tick_binding_record_after (t,(status,msg)) _ _ _ HeadValid Opened) as HeadRecord.
    assert (TailEntry : s |=
      V293_owned_record_cells (V293_tick_chain_cells (map V293_tick_task_after (map fst rest)) idle) **
      (V293_owned_record_cells (concat (map V293_tick_binding_extra rest)) **
      (V293_owned_record_cell (V293_tick_idle_cell idle) **
      (V293_owned_record_cells (V293_tick_idle_extra idle message) **
      (V293_owned_task_record (V293_tick_task_pointer t) (Int.repr (Z.of_nat (V293_tick_prio t)))
        (V293_tick_binding_status true (t,(status,msg))) msg ** (R ** Atrue)))))).
    { cbn [fst snd] in HeadRecord. clear -HeadRecord. sep auto. }
    pose proof (IH _ _ _ _ TailValid TailUnique TailEntry) as TailRecords.
    cbn [V293_tick_record_map].
    eapply V293_owned_task_records_reassemble.
    rewrite V293_tick_delete_absent by exact Absent.
    unfold V293_tick_binding_value. cbn [fst snd]. clear -TailRecords. sep auto.
Qed.

(* One vertical interface: the original complete while produces ONE Mf,
   then that very heap supplies every canonical record and the framed state. *)
Theorem V293_tick_while_owned_records :
  forall bindings idle message P ks ge le M ir enabled si ci O op
    ptcb rows group bc bg br g lo hi R,
  get le ptcb=Some (bc,Tptr V293_tcb_type) ->
  get le rows=None -> get ge rows=Some (br,Tarray Tint8 2) ->
  get le group=None -> get ge group=Some (bg,Tint8) ->
  (Int.unsigned (snd idle)+50<=Int.max_unsigned)%Z ->
  Forall V293_tick_binding_valid bindings -> NoDup (V293_tick_record_keys bindings idle) ->
  g<256 -> lo<256 -> hi<256 ->
  (ge,le,M,ir,(enabled,si,ci),O,op) |=
    V293_tick_loop_owned bc (V293_tick_head (map fst bindings) idle) (map fst bindings)
      idle bg br g lo hi
      (V293_owned_record_cells (concat (map V293_tick_binding_extra bindings)) **
        (V293_owned_record_cells (V293_tick_idle_extra idle message) ** R)) ->
  let '(gf,(lof,hif)) := V293_tick_chain_bitmap (map fst bindings) g lo hi in
  exists Mf,
  V293_local_steps P
    (curs (swhile (V293_tick_guard ptcb) (V293_tick_iteration ptcb rows group)),(kenil,ks))
    ((ge,le,M),ir,(enabled,si,ci))
    (curs (sskip None),(kenil,ks)) ((ge,le,Mf),ir,(enabled,si,ci)) /\
  load (Tptr V293_tcb_type) Mf (bc,0%Z)=Some (Vptr idle) /\
  V293_task_records Mf (V293_tick_record_map true bindings idle message) /\
  (ge,le,Mf,ir,(enabled,si,ci),O,op) |=
    V293_owned_task_records (V293_tick_record_map true bindings idle message) **
    ((V293_owned_record_cell (V293_tick_pointer_cell bc idle) **
      (V293_owned_record_cells (V293_tick_bitmap_cells bg br gf lof hif) ** R)) ** Atrue).
Proof.
  intros bindings idle message P ks ge le M ir enabled si ci O op
    ptcb rows group bc bg br g lo hi R Bind Nr Gr Ng Gg IdleLimit Valid Unique G Lo Hi Owned.
  assert (RawValid : Forall V293_tick_task_valid (map fst bindings)).
  { apply Forall_forall. intros t Member. apply in_map_iff in Member.
    destruct Member as (binding & Same & Member). subst t.
    rewrite Forall_forall in Valid. specialize (Valid binding Member).
    destruct binding as [t [status msg]]. exact (proj1 Valid). }
  destruct (V293_tick_chain_bitmap (map fst bindings) g lo hi) as [gf [lof hif]] eqn:Bitmap.
  pose proof (V293_tick_while_owned_execution (map fst bindings) P ks ge le M ir enabled si ci O op
    ptcb rows group bc idle bg br g lo hi _ Bind Nr Gr Ng Gg IdleLimit RawValid G Lo Hi Owned) as Run.
  rewrite Bitmap in Run. destruct Run as (Mf & Exec & Pointer & Returned).
  assert (Joint : (ge,le,Mf,ir,(enabled,si,ci),O,op) |=
    V293_owned_task_records (V293_tick_record_map true bindings idle message) **
    ((V293_owned_record_cell (V293_tick_pointer_cell bc idle) **
      (V293_owned_record_cells (V293_tick_bitmap_cells bg br gf lof hif) ** R)) ** Atrue)).
  { apply V293_tick_chain_records_after; [exact Valid | exact Unique | ].
    unfold V293_tick_loop_owned in Returned. clear -Returned. sep auto. }
  exists Mf. split; [exact Exec | ]. split; [exact Pointer | ]. split; [ | exact Joint].
  apply sat_split in Joint.
  destruct Joint as (m1 & m2 & o1 & o2 & JM & JO & Records & Frame).
  pose proof (V293_owned_task_records_sound _ _ Records) as All.
  intros t p st msg Lookup. eapply V293_task_record_sub; [exists m2;exact JM | ].
  apply All. exact Lookup.
Qed.
