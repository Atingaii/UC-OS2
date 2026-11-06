(* Four same-block records plus an ACTUAL 13-entry priority table. Entry
   ownership is constructed before the original complete while executes. *)
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickReadyChain.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickWhileShared.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickWhileRecords.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickTaskBridge.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickLoop.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyTaskInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293SharedStateWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTargetWitness.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.certiucos.v293.code.V293OSTimeTick.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.audit.probes.V293TimeTickWhileRecordsProbe.
Require Import CertiOS.audit.probes.V293TimeTickWhileSharedProbe.
Require Import CertiOS.audit.probes.V293TimeTickTraversalProbe.
Require Import CertiOS.audit.probes.V293TaskRecordOwnershipProbe.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Definition RCentries : list val :=
  [Vnull;Vnull;Vptr WhileSecond;Vnull;Vptr WhileReady;Vnull;Vnull;
   Vnull;Vnull;Vnull;Vptr WhileHead;Vnull;Vptr WhileIdle].
Definition RCcells :=
  V293_tick_pointer_cell 70%positive WhileHead ::
  (V293_tick_chain_cells (map fst WhileBindings) WhileIdle ++
  (V293_tick_bitmap_cells 92%positive 93%positive 3 16 16 ++
  (V293_tick_idle_cell WhileIdle ::
  (concat (map V293_tick_binding_extra WhileBindings) ++
  (V293_tick_idle_extra WhileIdle Vnull ++
  (V293_priority_cells 94%positive 0%Z RCentries ++ WhileFrameCells)))))).
Definition RCmemory := OwnershipCellsMemory RCcells.
Definition RCstate M O : RstateOP := ChainState M O.

Lemma RCold_lookup : forall t pr st m,
  get WhileOldTasks t=Some (pr,st,m) ->
  (t=WhileHead /\ (pr,st,m)=(Int.repr 10,wait WhileReason (Int.repr 1),Vnull)) \/
  (t=WhileSecond /\ (pr,st,m)=(Int.repr 2,wait os_stat_time (Int.repr 3),Vnull)) \/
  (t=WhileReady /\ (pr,st,m)=(Int.repr 4,rdy,Vnull)) \/
  (t=WhileIdle /\ (pr,st,m)=(Int.repr 12,rdy,Vnull)).
Proof.
  intros t pr st m H. unfold WhileOldTasks in H. cbn [V293_tick_record_map WhileBindings] in H.
  destruct (TcbMod.eq_dec WhileHead t) as [E|N];[subst t| ].
  - rewrite map_get_set in H. left. inversion H;auto.
  - rewrite map_get_set' in H by exact N.
    destruct (TcbMod.eq_dec WhileSecond t) as [E|N2];[subst t| ].
    + rewrite map_get_set in H. right;left. inversion H;auto.
    + rewrite map_get_set' in H by exact N2.
      destruct (TcbMod.eq_dec WhileReady t) as [E|N4];[subst t| ].
      * rewrite map_get_set in H. right;right;left. inversion H;auto.
      * rewrite map_get_set' in H by exact N4.
        destruct (TcbMod.eq_dec WhileIdle t) as [E|N12];[subst t| ].
        -- rewrite map_get_sig in H. right;right;right. inversion H;auto.
        -- rewrite map_get_sig' in H by exact N12. discriminate.
Qed.

Lemma RCold_rel : V293_ready_rel 16 16 RCentries WhileOldTasks.
Proof.
  split;[lia| ]. split;[lia| ]. split.
  - exists 4. left. split;[lia|vm_compute;reflexivity].
  - split.
    + intros p Bound. assert (Bits : V293_bitmap_ready 16 16 p <-> p=4 \/ p=12).
      { do 13 (destruct p as [ |p];[vm_compute;intuition lia| ]). lia. }
      rewrite Bits. split.
      * intros [E|E];subst p.
        -- exists WhileReady. exists Vnull. vm_compute;reflexivity.
        -- exists WhileIdle. exists Vnull. vm_compute;reflexivity.
      * intros (t&m&Lookup). apply RCold_lookup in Lookup.
        destruct Lookup as [[T E]|[[T E]|[[T E]|[T E]]]].
        -- discriminate E.
        -- discriminate E.
        -- left. apply V293_priority_repr_injective;try lia.
           exact (f_equal (fun value => fst (fst value)) E).
        -- right. apply V293_priority_repr_injective;try lia.
           exact (f_equal (fun value => fst (fst value)) E).
    + split;[reflexivity| ]. intros t pr st m Lookup. apply RCold_lookup in Lookup.
      destruct Lookup as [[T E]|[[T E]|[[T E]|[T E]]]];subst t;inversion E;subst.
      * exists 10. repeat split;reflexivity || lia.
      * exists 2. repeat split;reflexivity || lia.
      * exists 4. repeat split;reflexivity || lia.
      * exists 12. repeat split;reflexivity || lia.
Qed.

Lemma RCraw_entry : WhileState RCmemory |=
  V293_tick_loop_owned 70%positive WhileHead (map fst WhileBindings) WhileIdle
    92%positive 93%positive 3 16 16
    (V293_owned_record_cells (concat (map V293_tick_binding_extra WhileBindings)) **
      (V293_owned_record_cells (V293_tick_idle_extra WhileIdle Vnull) **
      (V293_owned_record_cells (V293_priority_cells 94%positive 0%Z RCentries) **
        V293_owned_record_cells WhileFrameCells))).
Proof.
  assert (Apart : OwnershipCellsSeparated RCcells).
  { vm_compute. repeat split;intros;intuition congruence. }
  assert (Valid : Forall (fun cell => let '(_,tp,v) := cell in
    rule_type_val_match tp v=true) RCcells).
  { repeat constructor;reflexivity. }
  pose proof (OwnershipCellsSpatial _ Apart Valid WhileGlobal TickLocal) as Encoded.
  assert (Rebased : WhileState RCmemory |= V293_owned_record_cells RCcells).
  { unfold WhileState,RCmemory. eapply TickCellsRebase. exact Encoded. }
  unfold V293_tick_loop_owned.
  change (WhileState RCmemory |=
    V293_owned_record_cell (V293_tick_pointer_cell 70%positive WhileHead) **
    V293_owned_record_cells
      (V293_tick_chain_cells (map fst WhileBindings) WhileIdle ++
      (V293_tick_bitmap_cells 92%positive 93%positive 3 16 16 ++
      (V293_tick_idle_cell WhileIdle ::
      (concat (map V293_tick_binding_extra WhileBindings) ++
      (V293_tick_idle_extra WhileIdle Vnull ++
      (V293_priority_cells 94%positive 0%Z RCentries ++ WhileFrameCells))))))) in Rebased.
  eapply astar_mono;[intros st H;exact H| |exact Rebased].
  intros st H. apply V293_tick_cells_append in H.
  eapply astar_mono;[intros st0 H0;exact H0| |exact H].
  intros st0 H0. apply V293_tick_cells_append in H0.
  eapply astar_mono;[intros st1 H1;exact H1| |exact H0].
  intros st1 H1. cbn [V293_owned_record_cells] in H1 |- *.
  eapply astar_mono;[intros st2 H2;exact H2| |exact H1].
  intros st2 H2. apply V293_tick_cells_append in H2.
  eapply astar_mono;[intros st3 H3;exact H3| |exact H2].
  intros st3 H3. apply V293_tick_cells_append in H3.
  eapply astar_mono;[intros st4 H4;exact H4| |exact H3].
  intros st4 H4. apply V293_tick_cells_append in H4. exact H4.
Qed.

Theorem RCentry : RCstate RCmemory ChainOld |=
  V293_tick_loop_owned 70%positive WhileHead (map fst WhileBindings) WhileIdle
    92%positive 93%positive 3 16 16
    (V293_owned_record_cells (concat (map V293_tick_binding_extra WhileBindings)) **
      (V293_owned_record_cells (V293_tick_idle_extra WhileIdle Vnull) **
      (V293_shared_fields WhileReady WhileOldTasks ChainEvents (Int.repr 37) **
      (V293_owned_record_cells (V293_priority_cells 94%positive 0%Z RCentries) **
        V293_owned_record_cells WhileFrameCells)))).
Proof.
  assert (Joint : RCstate RCmemory ChainOld |=
    V293_tick_loop_owned 70%positive WhileHead (map fst WhileBindings) WhileIdle
      92%positive 93%positive 3 16 16
      (V293_owned_record_cells (concat (map V293_tick_binding_extra WhileBindings)) **
        (V293_owned_record_cells (V293_tick_idle_extra WhileIdle Vnull) **
        (V293_owned_record_cells (V293_priority_cells 94%positive 0%Z RCentries) **
          V293_owned_record_cells WhileFrameCells))) **
    V293_shared_fields WhileReady WhileOldTasks ChainEvents (Int.repr 37)).
  { eapply V293_target_wstate_star with (m1:=RCmemory) (m2:=emp) (o1:=emp) (o2:=ChainOld).
    - apply map_join_emp.
    - apply map_join_comm;apply map_join_emp.
    - exact RCraw_entry.
    - exact ChainFields. }
  unfold V293_tick_loop_owned in *. clear -Joint. sep auto.
Qed.

Definition RCexecution P ks Mf := V293_local_steps P
  (curs (swhile (V293_tick_guard 901%Z) (V293_tick_iteration 901%Z 902%Z 903%Z)),(kenil,ks))
  ((WhileGlobal,TickLocal,RCmemory),(fun _ => false),(false,nil,nil))
  (curs (sskip None),(kenil,ks)) ((WhileGlobal,TickLocal,Mf),(fun _ => false),(false,nil,nil)).
Definition RCresult Mf := RCstate Mf ChainNew |=
  V293_ready_payload 93%positive 92%positive 94%positive WhileNewTasks **
  ((V293_owned_record_cell (V293_tick_pointer_cell 70%positive WhileIdle) **
    (V293_shared_fields WhileReady WhileNewTasks ChainEvents (Int.repr 37) **
      V293_owned_record_cells WhileFrameCells)) ** Atrue).

Theorem RCliteral : forall sd P ks,
  V293_task_records RCmemory WhileOldTasks /\
  spec_stepstar sd (V293_tick_chain_code WhileBindings) ChainOld (END None) ChainNew /\
  (forall id, id<>abstcblsid -> get ChainNew id=get ChainOld id) /\
  exists Mf, RCexecution P ks Mf /\
    load (Tptr V293_tcb_type) Mf (70%positive,0%Z)=Some (Vptr WhileIdle) /\
    V293_task_records Mf WhileNewTasks /\
    3=V293_ready_group 16 20 /\ V293_ready_rel 16 20 RCentries WhileNewTasks /\
    V293_ready_loads Mf 93%positive 92%positive 94%positive 16 20 RCentries /\ RCresult Mf.
Proof.
  intros sd P ks.
  exact (V293_tick_while_ready_payload WhileBindings WhileIdle Vnull WhileReady ChainEvents (Int.repr 37)
    RCentries sd P ks WhileGlobal TickLocal RCmemory (fun _ => false) false nil nil ChainOld (spec_done None)
    901%Z 902%Z 903%Z 70%positive 92%positive 93%positive 94%positive 16 16
    (V293_owned_record_cells WhileFrameCells)
    ltac:(apply map_get_sig) ltac:(vm_compute;reflexivity) ltac:(vm_compute;reflexivity)
    ltac:(vm_compute;reflexivity) ltac:(vm_compute;reflexivity)
    ltac:(change (368+50<=4294967295)%Z;lia) WhileBindingsValid WhileKeysUnique RCold_rel RCentry).
Qed.

(* Correct Mf remains untouched. Interpreting its ready rows as the old
   rows must fail by an ACTUAL high-row read, independently of entry checks. *)
Theorem RCold_bitmap_control : forall (sd : ossched) P ks, exists Mf,
  RCexecution P ks Mf /\ RCresult Mf /\
  load Tint8 Mf (93%positive,1%Z)=Some (V293_byteval 20) /\
  ~ (RCstate Mf ChainNew |=
    V293_owned_record_cells (V293_tick_bitmap_cells 92%positive 93%positive 3 16 16) ** Atrue).
Proof.
  intros sd P ks. destruct (RCliteral sd P ks) as (Old & Abstract & Slots & Mf & Exec & Pointer & Records & G & Rel & Loads & Result).
  exists Mf. split;[exact Exec| ]. split;[exact Result| ].
  destruct Loads as [Low [High Rest]]. split;[exact High| ]. intro Stale.
  assert (Bad : load Tint8 Mf (93%positive,1%Z)=Some (V293_byteval 16)).
  { change (load Tint8 (getmem (RCstate Mf ChainNew)) (93%positive,1%Z)=Some (V293_byteval 16)).
    eapply V293_record_star_load_l;[ |exact Stale].
    apply V293_owned_record_cells_load. vm_compute;auto. }
  pose proof (eq_trans (eq_sym High) Bad) as Clash. discriminate Clash.
Qed.

Lemma RCsingle_omitted_bit : forall p, p<13 ->
  (V293_bitmap_ready 16 20 p <-> p=10 \/ V293_bitmap_ready 16 16 p).
Proof.
  intros p Bound. do 13 (destruct p as [ |p];[vm_compute;intuition lia| ]). lia.
Qed.

(* Only the expired head's ready bit is omitted; tasks and every other bit
   are unchanged. No claim that mutant C ran, and no heap byte is removed. *)
Theorem RComitted_ready_control : forall (sd : ossched) P ks, exists Mf,
  RCexecution P ks Mf /\ RCresult Mf /\
  V293_task_records Mf WhileNewTasks /\
  V293_ready_rel 16 20 RCentries WhileNewTasks /\
  (forall p, p<13 -> p<>10 ->
    (V293_bitmap_ready 16 20 p <-> V293_bitmap_ready 16 16 p)) /\
  ~ V293_bitmap_tasks 16 16 WhileNewTasks.
Proof.
  intros sd P ks. destruct (RCliteral sd P ks) as (Old & Abstract & Slots & Mf & Exec & Pointer & Records & G & Rel & Loads & Result).
  exists Mf. split;[exact Exec| ]. split;[exact Result| ]. split;[exact Records| ].
  split;[exact Rel| ]. split.
  - intros p Bound Apart. rewrite RCsingle_omitted_bit by exact Bound. intuition congruence.
  - intro Bad. assert (Head : exists t m,get WhileNewTasks t=Some (Int.repr (Z.of_nat 10),rdy,m)).
    { exists WhileHead. exists Vnull. unfold WhileNewTasks. apply map_get_set. }
    apply (proj2 (Bad 10 ltac:(lia))) in Head. vm_compute in Head. intuition lia.
Qed.

Theorem RCslots_ready_idle_frame : forall (sd : ossched) P ks, exists Mf,
  RCexecution P ks Mf /\ RCresult Mf /\
  get ChainNew curtid=Some (oscurt WhileReady) /\
  get ChainNew absecblsid=Some (absecblist ChainEvents) /\
  get ChainNew ostmid=Some (ostm (Int.repr 37)) /\
  V293_task_record Mf WhileReady (Int.repr 4) rdy Vnull /\
  V293_task_record Mf WhileIdle (Int.repr 12) rdy Vnull /\
  V293_table_loads V293_tcb_type Mf 94%positive RCentries /\
  load Tint32 Mf (90%positive,0%Z)=Some (Vint32 (Int.repr 99)).
Proof.
  intros sd P ks. destruct (RCliteral sd P ks) as (Old & Abstract & Slots & Mf & Exec & Pointer & Records & G & Rel & Loads & Result).
  pose proof (V293_shared_fields_get _ _ _ _ _ ChainFields) as [Current [Tasks [Events Time]]].
  exists Mf. split;[exact Exec| ]. split;[exact Result| ].
  split;[rewrite Slots by discriminate;exact Current| ].
  split;[rewrite Slots by discriminate;exact Events| ].
  split;[rewrite Slots by discriminate;exact Time| ]. split.
  - apply Records. unfold WhileNewTasks. cbn [WhileBindings V293_tick_record_map].
    rewrite !map_get_set' by (vm_compute;congruence). apply map_get_set.
  - split.
    + apply Records. unfold WhileNewTasks. cbn [WhileBindings V293_tick_record_map].
      rewrite !map_get_set' by (vm_compute;congruence). apply map_get_sig.
    + split;[exact (proj2 (proj2 (proj2 Loads)))| ].
      assert (Frame : RCstate Mf ChainNew |= V293_owned_record_cells WhileFrameCells ** Atrue)
        by (unfold RCresult in Result;clear -Result;sep auto).
      change (load Tint32 (getmem (RCstate Mf ChainNew)) (90%positive,0%Z)=Some (Vint32 (Int.repr 99))).
      eapply V293_record_star_load_l;[ |exact Frame].
      apply V293_owned_record_cells_load. left;reflexivity.
Qed.
