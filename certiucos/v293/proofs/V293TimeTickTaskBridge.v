(* A represented, unsuspended waiting node in the ORIGINAL tick iteration.
   The same final memory supplies the new task records and ready bitmap.
   This is not a full tick/ISR invariant: suspension and flags are not
   expressible by the framework taskstatus used by these selected records. *)
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickLoop.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickExpiry.
Require Import CertiOS.certiucos.v293.code.V293OSTimeTick.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.code.V293ReadyTable.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewExec.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTarget.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.step_prop.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Definition V293_tick_reason_stat reason :=
  match reason with
  | os_stat_time => 0 | os_stat_sem _ => 1 | os_stat_mbox _ => 2
  | os_stat_q _ => 4 | os_stat_mutexsem _ => 16
  end.

Definition V293_tick_wait_status reason d :=
  if Z.eqb d 1 then rdy else wait reason (Int.repr (V293_tick_after_delay d)).

Definition V293_tick_wait_node b base d reason pend p :=
  Build_V293_tick_task b base d (V293_tick_reason_stat reason) pend
    (V293_prio_row p) (V293_prio_bit p) p.

(* The old loop owns Y, bitY, bitX and priority, but not X or message.
   Event pointers remain owned even when timeout clears the pending status. *)
Definition V293_tick_record_extra b base p reason message : list V293_record_cell :=
  [((b,(base+51)%Z),Tint8,V293_byteval (V293_prio_bit p));
   ((b,(base+32)%Z),Tptr Tvoid,message)] ++
  match reason with
  | os_stat_sem eid | os_stat_q eid | os_stat_mbox eid | os_stat_mutexsem eid =>
      [((b,(base+28)%Z),Tcom_ptr 411%Z,Vptr eid)]
  | os_stat_time => []
  end.

Definition V293_tick_wait_rows lo hi d p :=
  if Z.eqb d 1 then V293_ready_set_rows lo hi p else (lo,hi).

Lemma V293_tick_wait_node_valid : forall b base d reason pend p,
  (0<=base /\ base+54<=Int.max_unsigned)%Z ->
  (0<=d<=Int.max_unsigned)%Z -> pend<256 -> p<13 -> p<>12 ->
  V293_tick_task_valid (V293_tick_wait_node b base d reason pend p).
Proof.
  intros b base d reason pend p Base D Pend P Nonidle.
  destruct (V293_prio_coordinates p P) as [Y X].
  unfold V293_tick_task_valid,V293_tick_wait_node; cbn.
  destruct reason; cbn; repeat split; try tauto; lia.
Qed.

Definition V293_tick_wait_step (t : tid) : osabstep := fun vl O result =>
  vl = nil /\ exists tasks priority reason d message,
    get O abstcblsid = Some (abstcblist tasks) /\
    get tasks t = Some (priority,wait reason (Int.repr d),message) /\
    (0<=d<=Int.max_unsigned)%Z /\
    result = (None,set O abstcblsid (abstcblist
      (set tasks t (priority,V293_tick_wait_status reason d,message)))).

Theorem V293_tick_wait_transition : forall sd O tasks t priority reason d message,
  get O abstcblsid = Some (abstcblist tasks) ->
  get tasks t = Some (priority,wait reason (Int.repr d),message) ->
  (0<=d<=Int.max_unsigned)%Z ->
  spec_step sd (spec_prim nil (V293_tick_wait_step t)) O (END None)
    (set O abstcblsid (abstcblist
      (set tasks t (priority,V293_tick_wait_status reason d,message)))).
Proof.
  intros sd O tasks t priority reason d message Slot Task D.
  eapply spec_prim_step with (O:=O) (Of:=emp).
  - split; [reflexivity | ]. exists tasks. exists priority. exists reason.
    exists d. exists message. auto.
  - split.
    + intro id. unfold indom.
      destruct (OSAbstMod.eq_dec id abstcblsid) as [Same|Apart].
      * subst id. rewrite map_get_set. split; intros; eauto.
      * split; intros [v Lookup]; exists v.
        -- rewrite map_get_set' by congruence; exact Lookup.
        -- rewrite map_get_set' in Lookup by congruence; exact Lookup.
    + intros ts Lookup. rewrite Slot in Lookup. inversion Lookup; subst ts.
      exists (set tasks t (priority,V293_tick_wait_status reason d,message)).
      split; [apply map_get_set | ]. unfold eqdomtls. intro u. unfold indom.
      change ((exists v, get tasks u = Some v) <->
        (exists v, get (set tasks t (priority,V293_tick_wait_status reason d,message)) u = Some v)).
      destruct (TcbMod.eq_dec u t) as [Same|Apart].
      * subst u. split; intros; [eexists; apply map_get_set | eexists; exact Task].
      * split; intros [v Lookup']; exists v.
        -- rewrite map_get_set' by congruence; exact Lookup'.
        -- rewrite map_get_set' in Lookup' by congruence; exact Lookup'.
  - unfold tidsame. rewrite map_get_set'; [reflexivity | discriminate].
  - apply map_join_emp.
  - apply map_join_emp.
Qed.

Lemma V293_tick_wait_bitmap_values : forall b base d reason pend p lo hi,
  let t := V293_tick_wait_node b base d reason pend p in
  V293_tick_next_lo t lo = fst (V293_tick_wait_rows lo hi d p) /\
  V293_tick_next_hi t hi = snd (V293_tick_wait_rows lo hi d p) /\
  V293_tick_next_group t (V293_ready_group lo hi) =
    V293_ready_group (fst (V293_tick_wait_rows lo hi d p))
      (snd (V293_tick_wait_rows lo hi d p)).
Proof.
  intros b base d reason pend p lo hi.
  cbn zeta. unfold V293_tick_next_lo,V293_tick_next_hi,V293_tick_next_group,
    V293_tick_wait_node,V293_tick_wait_rows,V293_tick_after_row,V293_tick_after_group.
  cbn. destruct (Z.eqb d 1).
  2: { unfold V293_prio_row. destruct (p <? 8); repeat split; reflexivity. }
  assert (W : V293_tick_wakes (V293_tick_reason_stat reason)=true)
    by (destruct reason; reflexivity).
  unfold V293_tick_expired_row,V293_tick_expired_group. rewrite W.
  split.
  - unfold V293_ready_set_rows,V293_prio_row,V293_prio_bit.
    destruct (p <? 8); reflexivity.
  - split.
    + unfold V293_ready_set_rows,V293_prio_row,V293_prio_bit.
      destruct (p <? 8); reflexivity.
    + unfold V293_prio_row. apply V293_ready_set_group_correct.
Qed.

(* A status-only task update preserves the actual priority-table relation. *)
Lemma V293_tick_priority_table : forall entries tasks t p old new message,
  V293_priority_table entries tasks ->
  get tasks t = Some (p,old,message) ->
  V293_priority_table entries (set tasks t (p,new,message)).
Proof.
  intros entries tasks t p old new message [Len Table] Task.
  split; [exact Len | ]. intros u q status msg Lookup.
  destruct (TcbMod.eq_dec u t) as [Same|Apart].
  - subst u. rewrite map_get_set in Lookup. inversion Lookup; subst.
    eapply Table; exact Task.
  - rewrite map_get_set' in Lookup by congruence. eapply Table; exact Lookup.
Qed.

Theorem V293_tick_wait_bitmap_tasks : forall lo hi tasks t p reason d message,
  p<13 -> V293_bitmap_tasks lo hi tasks ->
  get tasks t = Some (Int.repr (Z.of_nat p),wait reason (Int.repr d),message) ->
  V293_bitmap_tasks (fst (V293_tick_wait_rows lo hi d p))
    (snd (V293_tick_wait_rows lo hi d p))
    (set tasks t (Int.repr (Z.of_nat p),V293_tick_wait_status reason d,message)).
Proof.
  intros lo hi tasks t p reason d message P Bitmap Task q Q.
  unfold V293_tick_wait_rows,V293_tick_wait_status. destruct (Z.eqb d 1).
  - rewrite V293_ready_set_membership by assumption. split.
    + intros [Same|Ready].
      * subst q. exists t. exists message. apply map_get_set.
      * destruct (proj1 (Bitmap q Q) Ready) as [u [msg Lookup]].
        assert (Apart:u<>t) by (intro Same; subst u; rewrite Task in Lookup; discriminate).
        exists u. exists msg. rewrite map_get_set' by congruence. exact Lookup.
    + intros [u [msg Lookup]]. destruct (TcbMod.eq_dec u t) as [Same|Apart].
      * subst u. rewrite map_get_set in Lookup. left.
        eapply V293_priority_repr_injective; [exact Q | exact P | congruence].
      * rewrite map_get_set' in Lookup by congruence.
        right. apply (proj2 (Bitmap q Q)). exists u; exists msg; exact Lookup.
  - cbn [fst snd]. rewrite (Bitmap q Q). split.
    + intros [u [msg Lookup]].
      assert (Apart:u<>t) by (intro Same; subst u; rewrite Task in Lookup; discriminate).
      exists u. exists msg. rewrite map_get_set' by congruence. exact Lookup.
    + intros [u [msg Lookup]]. destruct (TcbMod.eq_dec u t) as [Same|Apart].
      * subst u. rewrite map_get_set in Lookup. discriminate.
      * rewrite map_get_set' in Lookup by congruence. exists u; exists msg; exact Lookup.
Qed.

Lemma V293_tick_wait_record_after : forall b base d reason pend p message next R
    ge le M ir aux O op,
  (0<=base /\ base+54<=Int.max_unsigned)%Z -> p<13 -> pend<256 ->
  (ge,le,M,ir,aux,O,op) |=
    V293_owned_record_cells (V293_tick_task_cells
      (V293_tick_task_after (V293_tick_wait_node b base d reason pend p)) next) **
    (V293_owned_record_cells (V293_tick_record_extra b base p reason message) ** R) ->
  (ge,le,M,ir,aux,O,op) |=
    V293_owned_task_record (b,Int.repr base) (Int.repr (Z.of_nat p))
      (V293_tick_wait_status reason d) message ** Atrue.
Proof.
  intros b base d reason pend p message next R ge le M ir aux O op [Base Limit] P Pend Owned.
  assert (U : Int.unsigned (Int.repr base)=base).
  { apply Int.unsigned_repr. lia. }
  unfold V293_tick_wait_status.
  unfold V293_tick_task_after,V293_tick_wait_node,V293_tick_task_cells,
    V293_tick_record_extra in Owned.
  cbn [V293_tick_block V293_tick_base V293_tick_delay_value V293_tick_stat_value
    V293_tick_pend_value V293_tick_y V293_tick_x V293_tick_prio] in Owned.
  unfold V293_tick_after_stat,V293_tick_after_pend in Owned.
  destruct (Z.eqb d 1) eqn:Expiry.
  - assert (Stat:V293_tick_expired_stat (V293_tick_reason_stat reason)=0)
      by (destruct reason; reflexivity).
    rewrite Stat in Owned.
    assert (Held : (ge,le,M,ir,aux,O,op) |=
      V293_owned_record_cells (V293_record_layout (b,Int.repr base) p rdy message 0) ** Atrue).
    { unfold V293_record_layout; cbn [fst snd]; rewrite U.
      cbn [app V293_owned_record_cells] in Owned |- *.
      clear -Owned. sep auto. }
    eapply astar_mono; [ | | exact Held]; [ | intros;exact I].
    intros st Cells. unfold V293_owned_task_record.
    exists p. exists 0. apply astar_l_apure_intro; [exact Cells | repeat split; try reflexivity; lia].
  - assert (Held : (ge,le,M,ir,aux,O,op) |=
      V293_owned_record_cells (V293_record_layout (b,Int.repr base) p
        (wait reason (Int.repr (V293_tick_after_delay d))) message pend) ** Atrue).
    { destruct reason; unfold V293_record_layout; cbn [fst snd]; rewrite U;
        cbn [app V293_tick_reason_stat V293_owned_record_cells] in Owned |- *;
        clear -Owned; sep auto. }
    eapply astar_mono; [ | | exact Held]; [ | intros;exact I].
    intros st Cells. unfold V293_owned_task_record.
    exists p. exists pend. apply astar_l_apure_intro; [exact Cells | repeat split; try reflexivity; lia].
Qed.

Lemma V293_tick_records_replace : forall tasks t priority status message
    ge le M ir aux O op,
  (ge,le,M,ir,aux,O,op) |= V293_owned_task_record t priority status message ** Atrue ->
  (ge,le,M,ir,aux,O,op) |= V293_owned_task_records (del tasks t) ** Atrue ->
  V293_task_records M (set tasks t (priority,status,message)).
Proof.
  intros tasks t priority status message ge le M ir aux O op Selected Others u p st msg Lookup.
  destruct (TcbMod.eq_dec u t) as [Same|Apart].
  - subst u. rewrite map_get_set in Lookup. inversion Lookup; subst p st msg.
    apply sat_split in Selected.
    destruct Selected as (m1 & m2 & o1 & o2 & JM & JO & Record & Rest).
    eapply V293_task_record_sub; [exists m2; exact JM | ].
    exact (V293_owned_task_record_sound _ _ _ _ _ Record).
  - rewrite map_get_set' in Lookup by congruence.
    apply sat_split in Others.
    destruct Others as (m1 & m2 & o1 & o2 & JM & JO & Records & Rest).
    eapply V293_task_record_sub; [exists m2; exact JM | ].
    apply (V293_owned_task_records_sound _ _ Records).
    rewrite map_del_sem. destruct (map_dec_a t u); [congruence | exact Lookup].
Qed.

(* A vertical bridge, not a detached model run. Full permissions construct
   every original store; the resulting Mf witnesses BOTH physical records
   and the task-map/bitmap relation. Extra cells and other tasks are framed. *)
Theorem V293_tick_wait_iteration_refines :
  forall P ks ge le M ir enabled si ci O op sd ptcb rows group bc b base next d
    reason pend p bg br lo hi message current tasks events now entries R,
  get le ptcb = Some (bc,Tptr V293_tcb_type) ->
  get le rows = None -> get ge rows = Some (br,Tarray Tint8 2) ->
  get le group = None -> get ge group = Some (bg,Tint8) ->
  (0<=base /\ base+54<=Int.max_unsigned)%Z ->
  (0<=d<=Int.max_unsigned)%Z -> pend<256 -> p<13 -> p<>12 -> lo<256 -> hi<256 ->
  V293_priority_table entries tasks -> V293_bitmap_tasks lo hi tasks ->
  get tasks (b,Int.repr base) =
    Some (Int.repr (Z.of_nat p),wait reason (Int.repr d),message) ->
  (ge,le,M,ir,(enabled,si,ci),O,op) |=
    V293_owned_record_cell (V293_tick_pointer_cell bc (b,Int.repr base)) **
    (V293_owned_record_cells (V293_tick_task_cells
      (V293_tick_wait_node b base d reason pend p) next) **
    (V293_owned_record_cells (V293_tick_bitmap_cells bg br (V293_ready_group lo hi) lo hi) **
    (V293_owned_record_cells (V293_tick_record_extra b base p reason message) **
    (V293_owned_task_records (del tasks (b,Int.repr base)) **
    (V293_shared_fields current tasks events now ** R))))) ->
  exists Mf,
  let tasks' := set tasks (b,Int.repr base)
    (Int.repr (Z.of_nat p),V293_tick_wait_status reason d,message) in
  let O' := set O abstcblsid (abstcblist tasks') in
  let rr := V293_tick_wait_rows lo hi d p in
  spec_step sd (spec_prim nil (V293_tick_wait_step (b,Int.repr base))) O (END None) O' /\
  V293_local_steps P (curs (V293_tick_iteration ptcb rows group),(kenil,ks))
    ((ge,le,M),ir,(enabled,si,ci))
    (curs (sskip None),(kenil,ks)) ((ge,le,Mf),ir,(enabled,si,ci)) /\
  V293_task_records Mf tasks' /\
  V293_priority_table entries tasks' /\ V293_bitmap_tasks (fst rr) (snd rr) tasks' /\
  (ge,le,Mf,ir,(enabled,si,ci),O',op) |=
    V293_owned_record_cell (V293_tick_pointer_cell bc next) **
    (V293_owned_record_cells (V293_tick_task_cells
      (V293_tick_task_after (V293_tick_wait_node b base d reason pend p)) next) **
    (V293_owned_record_cells (V293_tick_bitmap_cells bg br
      (V293_ready_group (fst rr) (snd rr)) (fst rr) (snd rr)) **
    (V293_owned_record_cells (V293_tick_record_extra b base p reason message) **
    (V293_owned_task_records (del tasks (b,Int.repr base)) **
    (V293_shared_fields current tasks' events now ** R))))).
Proof.
  intros P ks ge le M ir enabled si ci O op sd ptcb rows group bc b base next d
    reason pend p bg br lo hi message current tasks events now entries R
    Bind Nr Gr Ng Gg Base D Pend Pr Nonidle Lo Hi Table Bitmap Task Owned.
  assert (Group:V293_ready_group lo hi<256).
  { unfold V293_ready_group. destruct (lo=?0); destruct (hi=?0); lia. }
  pose proof (V293_tick_wait_node_valid b base d reason pend p Base D Pend Pr Nonidle) as Valid.
  destruct (V293_tick_node_iteration_owned_execution P ks ge le M ir enabled si ci O op
    ptcb rows group bc (V293_tick_wait_node b base d reason pend p) next bg br
    (V293_ready_group lo hi) lo hi _ Bind Nr Gr Ng Gg Valid Group Lo Hi Owned)
    as (Mf & Exec & Returned).
  destruct (V293_tick_wait_bitmap_values b base d reason pend p lo hi) as [Low [High Grp]].
  cbn zeta in Low,High,Grp. rewrite Low,High,Grp in Returned.
  assert (Selected : (ge,le,Mf,ir,(enabled,si,ci),O,op) |=
    V293_owned_task_record (b,Int.repr base) (Int.repr (Z.of_nat p))
      (V293_tick_wait_status reason d) message ** Atrue).
  { eapply V293_tick_wait_record_after; [exact Base | exact Pr | exact Pend | ].
    clear -Returned. sep auto. }
  assert (Others : (ge,le,Mf,ir,(enabled,si,ci),O,op) |=
    V293_owned_task_records (del tasks (b,Int.repr base)) ** Atrue) by (clear -Returned;sep auto).
  pose proof (V293_tick_records_replace tasks _ _ _ _ _ _ _ _ _ _ _ Selected Others) as Records.
  assert (Slot:get O abstcblsid=Some (abstcblist tasks)).
  { change (get (getabst (ge,le,Mf,ir,(enabled,si,ci),O,op)) abstcblsid = Some (abstcblist tasks)).
    eapply V293_star_abst_get_l with (p:=V293_shared_fields current tasks events now) (q:=Atrue).
    - intros st H. exact (proj1 (proj2 (V293_shared_fields_get _ _ _ _ st H))).
    - clear -Returned. sep auto. }
  assert (Final : (ge,le,Mf,ir,(enabled,si,ci),O,op) |=
    Aabsdata abstcblsid (abstcblist tasks) **
    (V293_owned_record_cell (V293_tick_pointer_cell bc next) **
    (V293_owned_record_cells (V293_tick_task_cells
      (V293_tick_task_after (V293_tick_wait_node b base d reason pend p)) next) **
    (V293_owned_record_cells (V293_tick_bitmap_cells bg br
      (V293_ready_group (fst (V293_tick_wait_rows lo hi d p)) (snd (V293_tick_wait_rows lo hi d p)))
      (fst (V293_tick_wait_rows lo hi d p)) (snd (V293_tick_wait_rows lo hi d p))) **
    (V293_owned_record_cells (V293_tick_record_extra b base p reason message) **
    (V293_owned_task_records (del tasks (b,Int.repr base)) **
    ((Aabsdata curtid (oscurt current) **
      (Aabsdata absecblsid (absecblist events) ** Aabsdata ostmid (ostm now))) ** R))))))).
  { unfold V293_shared_fields in Returned. clear -Returned. sep auto. }
  apply V293_shared_replace_slot with (new:=abstcblist (set tasks (b,Int.repr base)
    (Int.repr (Z.of_nat p),V293_tick_wait_status reason d,message))) in Final.
  exists Mf. cbn zeta. split; [eapply V293_tick_wait_transition; eassumption | ].
  split; [exact Exec | ]. split; [exact Records | ].
  split; [eapply V293_tick_priority_table; eassumption | ].
  split; [eapply V293_tick_wait_bitmap_tasks; eassumption | ].
  unfold V293_shared_fields. clear -Final. sep auto.
Qed.
