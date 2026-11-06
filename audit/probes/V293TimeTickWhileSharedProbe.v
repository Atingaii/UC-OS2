(* A nonempty shared entry on the existing four-record physical fixture.
   Event data is nonempty but no event/TCB consistency invariant is asserted. *)
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickWhileShared.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickWhileRecords.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickTaskBridge.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickLoop.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293SharedStateWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTargetWitness.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.code.V293OSTimeTick.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.audit.probes.V293TimeTickWhileRecordsProbe.
Require Import CertiOS.audit.probes.V293TimeTickTraversalProbe.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Definition ChainEvents : EcbMod.map :=
  sig (84%positive,Int.repr 4) (abssem (Int.repr 0),[WhileHead]).
Definition ChainOld : osabst := V293_shared_fixture_abs WhileReady WhileOldTasks ChainEvents (Int.repr 37).
Definition ChainNew := set ChainOld abstcblsid (abstcblist WhileNewTasks).
Definition ChainState M O : RstateOP :=
  (WhileGlobal,TickLocal,M,(fun _ => false),(false,nil,nil),O,spec_done None).

Lemma ChainFields : V293_target_wstate WhileGlobal TickLocal emp ChainOld |=
  V293_shared_fields WhileReady WhileOldTasks ChainEvents (Int.repr 37).
Proof.
  unfold V293_shared_fields,ChainOld,V293_shared_fixture_abs.
  repeat (eapply V293_target_wstate_star;
    [apply map_join_emp | apply map_join_merge;apply map_disjoint;intros key;destruct key;simpl;auto |
     split;reflexivity | ]).
  split;reflexivity.
Qed.

Theorem ChainEntry : ChainState WhileMemory ChainOld |=
  V293_tick_loop_owned 70%positive WhileHead (map fst WhileBindings) WhileIdle
    92%positive 93%positive 3 16 16
    (V293_owned_record_cells (concat (map V293_tick_binding_extra WhileBindings)) **
      (V293_owned_record_cells (V293_tick_idle_extra WhileIdle Vnull) **
      (V293_shared_fields WhileReady WhileOldTasks ChainEvents (Int.repr 37) **
        V293_owned_record_cells WhileFrameCells))).
Proof.
  assert (Joint : ChainState WhileMemory ChainOld |=
    V293_tick_loop_owned 70%positive WhileHead (map fst WhileBindings) WhileIdle
      92%positive 93%positive 3 16 16
      (V293_owned_record_cells (concat (map V293_tick_binding_extra WhileBindings)) **
        (V293_owned_record_cells (V293_tick_idle_extra WhileIdle Vnull) **
          V293_owned_record_cells WhileFrameCells)) **
    V293_shared_fields WhileReady WhileOldTasks ChainEvents (Int.repr 37)).
  { eapply V293_target_wstate_star with (m1:=WhileMemory) (m2:=emp) (o1:=emp) (o2:=ChainOld).
    - apply map_join_emp.
    - apply map_join_comm. apply map_join_emp.
    - exact WhileEntry.
    - exact ChainFields. }
  unfold V293_tick_loop_owned in *. clear -Joint. sep auto.
Qed.

Definition ChainResult Mf := ChainState Mf ChainNew |=
  V293_owned_task_records WhileNewTasks **
  ((V293_owned_record_cell (V293_tick_pointer_cell 70%positive WhileIdle) **
    (V293_owned_record_cells (V293_tick_bitmap_cells 92%positive 93%positive 3 16 20) **
    (V293_shared_fields WhileReady WhileNewTasks ChainEvents (Int.repr 37) **
      V293_owned_record_cells WhileFrameCells))) ** Atrue).

Theorem ChainLiteral : forall sd P ks,
  V293_task_records WhileMemory WhileOldTasks /\
  spec_stepstar sd (V293_tick_chain_code WhileBindings) ChainOld (END None) ChainNew /\
  (forall id, id<>abstcblsid -> get ChainNew id=get ChainOld id) /\
  exists Mf, WhileExecution P ks Mf /\
    load (Tptr V293_tcb_type) Mf (70%positive,0%Z)=Some (Vptr WhileIdle) /\
    V293_task_records Mf WhileNewTasks /\ ChainResult Mf.
Proof.
  intros sd P ks.
  exact (V293_tick_while_shared_records WhileBindings WhileIdle Vnull WhileReady ChainEvents (Int.repr 37)
    sd P ks WhileGlobal TickLocal WhileMemory (fun _ => false) false nil nil ChainOld (spec_done None)
    901%Z 902%Z 903%Z 70%positive 92%positive 93%positive 3 16 16
    (V293_owned_record_cells WhileFrameCells)
    ltac:(apply map_get_sig) ltac:(vm_compute;reflexivity) ltac:(vm_compute;reflexivity)
    ltac:(vm_compute;reflexivity) ltac:(vm_compute;reflexivity)
    ltac:(change (368+50<=4294967295)%Z;lia) WhileBindingsValid WhileKeysUnique
    ltac:(lia) ltac:(lia) ltac:(lia) ChainEntry).
Qed.

Definition ChainFirstTasks := set WhileOldTasks WhileHead (Int.repr 10,rdy,Vnull).
Definition ChainFirst := set ChainOld abstcblsid (abstcblist ChainFirstTasks).

(* The original code is ordered even though disjoint table sets commute.
   Inspect its first actual intermediate state, not just the final map. *)
Theorem ChainFirstStep : forall sd,
  V293_tick_chain_code WhileBindings=
    spec_seq (spec_prim nil (V293_tick_wait_step WhileHead))
      (spec_seq (spec_prim nil (V293_tick_wait_step WhileSecond)) (END None)) /\
  spec_stepstar sd (spec_prim nil (V293_tick_wait_step WhileHead)) ChainOld (END None) ChainFirst /\
  get ChainFirstTasks WhileHead=Some (Int.repr 10,rdy,Vnull) /\
  get ChainFirstTasks WhileSecond=Some (Int.repr 2,wait os_stat_time (Int.repr 3),Vnull).
Proof.
  intro sd. split; [reflexivity | ]. split.
  - eapply spec_stepS; [ | apply spec_stepO].
    unfold ChainFirst,ChainFirstTasks.
    apply V293_tick_wait_transition with (reason:=WhileReason) (d:=1%Z).
    + pose proof (V293_shared_fields_get _ _ _ _ _ ChainFields) as [_ [Slot _]]. exact Slot.
    + unfold WhileOldTasks. apply map_get_set.
    + change (0<=1<=4294967295)%Z;lia.
  - split; [apply map_get_set | ].
    unfold ChainFirstTasks,WhileOldTasks. cbn [WhileBindings V293_tick_record_map].
    rewrite !map_get_set' by (vm_compute;congruence). apply map_get_set.
Qed.

Lemma ChainFirstIsSingleOmission : ChainFirstTasks=WhileOmitSecond.
Proof.
  apply TcbMod.extensionality. intro t.
  change (get ChainFirstTasks t=get WhileOmitSecond t).
  change (get
    (set (set (set (set (sig WhileIdle (Int.repr 12,rdy,Vnull))
      WhileReady (Int.repr 4,rdy,Vnull))
      WhileSecond (Int.repr 2,wait os_stat_time (Int.repr 3),Vnull))
      WhileHead (Int.repr 10,wait WhileReason (Int.repr 1),Vnull))
      WhileHead (Int.repr 10,rdy,Vnull)) t =
    get (set (set (set (set (sig WhileIdle (Int.repr 12,rdy,Vnull))
      WhileReady (Int.repr 4,rdy,Vnull))
      WhileSecond (Int.repr 2,wait os_stat_time (Int.repr 2),Vnull))
      WhileHead (Int.repr 10,rdy,Vnull))
      WhileSecond (Int.repr 2,wait os_stat_time (Int.repr 3),Vnull)) t).
  destruct (TcbMod.eq_dec t WhileHead) as [Same|Nh]; [subst t | ].
  - rewrite map_get_set. rewrite map_get_set' by (vm_compute;congruence). symmetry;apply map_get_set.
  - destruct (TcbMod.eq_dec t WhileSecond) as [Same|Ns]; [subst t | ].
    + rewrite map_get_set' by (vm_compute;congruence).
      rewrite map_get_set' by (vm_compute;congruence). rewrite !map_get_set. reflexivity.
    + rewrite !map_get_set' by congruence. symmetry. rewrite !map_get_set' by congruence. reflexivity.
Qed.

(* Both the complete physical while and the omitted abstract path execute.
   Only the second waiting update is absent; the very same Mf rejects it. *)
Theorem ChainOmitSecondControl : forall sd P ks, exists Mf,
  WhileExecution P ks Mf /\ ChainResult Mf /\
  spec_stepstar sd (V293_tick_chain_code WhileBindings) ChainOld (END None) ChainNew /\
  spec_stepstar sd (spec_prim nil (V293_tick_wait_step WhileHead)) ChainOld (END None) ChainFirst /\
  ChainFirstTasks=WhileOmitSecond /\
  (forall id, id<>abstcblsid -> get ChainFirst id=get ChainNew id) /\
  load Tint32 Mf (81%positive,172%Z)=Some (Vint32 (Int.repr 2)) /\
  ~ V293_task_records Mf ChainFirstTasks.
Proof.
  intros sd P ks. destruct (ChainLiteral sd P ks) as (Old & Abstract & Slots & Mf & Exec & Pointer & Records & Result).
  pose proof (ChainFirstStep sd) as (_ & First & _).
  exists Mf. split; [exact Exec | ]. split; [exact Result | ]. split; [exact Abstract | ].
  split; [exact First | ]. split; [exact ChainFirstIsSingleOmission | ]. split.
  - intros id Apart. unfold ChainFirst,ChainNew. rewrite !map_get_set' by congruence. reflexivity.
  - pose proof (WhileSecondDelay _ Records) as Delay. split; [exact Delay | ].
    rewrite ChainFirstIsSingleOmission. intro Stale.
    pose proof (Stale WhileSecond (Int.repr 2) (wait os_stat_time (Int.repr 3)) Vnull
      ltac:(apply map_get_set)) as (p & Range & Priority & Fields & Stat & Bad & Msg).
    change (load Tint32 Mf (81%positive,172%Z)=Some (Vint32 (Int.repr 3))) in Bad.
    rewrite Delay in Bad. discriminate.
Qed.

Theorem ChainSlotsReadyIdleFrame : forall (sd : ossched) P ks, exists Mf,
  WhileExecution P ks Mf /\ ChainResult Mf /\
  get ChainNew curtid=Some (oscurt WhileReady) /\
  get ChainNew absecblsid=Some (absecblist ChainEvents) /\
  get ChainNew ostmid=Some (ostm (Int.repr 37)) /\
  V293_task_record Mf WhileReady (Int.repr 4) rdy Vnull /\
  V293_task_record Mf WhileIdle (Int.repr 12) rdy Vnull /\
  load Tint32 Mf (90%positive,0%Z)=Some (Vint32 (Int.repr 99)).
Proof.
  intros sd P ks. destruct (ChainLiteral sd P ks) as (Old & Abstract & Slots & Mf & Exec & Pointer & Records & Result).
  pose proof (V293_shared_fields_get _ _ _ _ _ ChainFields) as [Current [Tasks [Events Time]]].
  exists Mf. split; [exact Exec | ]. split; [exact Result | ].
  split; [rewrite Slots by discriminate;exact Current | ].
  split; [rewrite Slots by discriminate;exact Events | ].
  split; [rewrite Slots by discriminate;exact Time | ].
  split.
  - apply Records. unfold WhileNewTasks. cbn [WhileBindings V293_tick_record_map].
    rewrite !map_get_set' by (vm_compute;congruence). apply map_get_set.
  - split.
    + apply Records. unfold WhileNewTasks. cbn [WhileBindings V293_tick_record_map].
      rewrite !map_get_set' by (vm_compute;congruence). apply map_get_sig.
    + assert (Frame : ChainState Mf ChainNew |= V293_owned_record_cells WhileFrameCells ** Atrue)
        by (unfold ChainResult in Result;clear -Result;sep auto).
      change (load Tint32 (getmem (ChainState Mf ChainNew)) (90%positive,0%Z)=Some (Vint32 (Int.repr 99))).
      eapply V293_record_star_load_l; [ | exact Frame].
      apply V293_owned_record_cells_load. left;reflexivity.
Qed.
