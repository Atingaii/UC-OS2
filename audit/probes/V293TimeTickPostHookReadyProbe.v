(* Nonempty encoded entry. Initial scan is IDLE, not HEAD. The original
   post-hook path must load HEAD before walking the three real task nodes. *)
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickPostHookReady.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickReadyChain.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickWhileShared.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickWhileRecords.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickShared.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickSuffix.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickLoop.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyTaskInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTarget.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293SharedStateWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTargetWitness.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.certiucos.v293.code.V293OSTimeTick.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.audit.probes.V293TimeTickReadyChainProbe.
Require Import CertiOS.audit.probes.V293TimeTickWhileSharedProbe.
Require Import CertiOS.audit.probes.V293TimeTickWhileRecordsProbe.
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

Definition PHglobal : env :=
  set (set (set WhileGlobal 1001%Z (101%positive,Tint32))
    1002%Z (102%positive,Tint8)) 1003%Z (103%positive,Tptr V293_tcb_type).
Definition PHcells :=
  ((101%positive,0%Z),Tint32,Vint32 (Int.repr 37)) ::
  ((102%positive,0%Z),Tint8,V293_byteval 1) ::
  ((103%positive,0%Z),Tptr V293_tcb_type,Vptr WhileHead) ::
  V293_tick_pointer_cell 70%positive WhileIdle :: tl RCcells.
Definition PHmemory := OwnershipCellsMemory PHcells.
Definition PHstate M O : RstateOP :=
  (PHglobal,TickLocal,M,(fun _ => false),(false,[3%nat],[false]),O,spec_done None).
Definition PHnew := set (set ChainOld ostmid (ostm (Int.repr 38))) abstcblsid (abstcblist WhileNewTasks).

Lemma PHraw_entry : PHstate PHmemory emp |=
  V293_tick_suffix_owned 101%positive (Int.repr 37) 102%positive 1 103%positive WhileHead
    70%positive WhileIdle (map fst WhileBindings) WhileIdle 92%positive 93%positive 3 16 16
    (V293_owned_record_cells (concat (map V293_tick_binding_extra WhileBindings)) **
      (V293_owned_record_cells (V293_tick_idle_extra WhileIdle Vnull) **
        (V293_owned_record_cells (V293_priority_cells 94%positive 0%Z RCentries) **
          V293_owned_record_cells WhileFrameCells))).
Proof.
  assert (Apart : OwnershipCellsSeparated PHcells).
  { vm_compute. repeat split;intros a Member Rest;
      repeat destruct Member as [Member|Member];try contradiction;subst a;intuition discriminate. }
  assert (Valid : Forall (fun cell => let '(_,tp,v) := cell in
    rule_type_val_match tp v=true) PHcells).
  { repeat constructor;reflexivity. }
  pose proof (OwnershipCellsSpatial _ Apart Valid PHglobal TickLocal) as Encoded.
  assert (Rebased : PHstate PHmemory emp |= V293_owned_record_cells PHcells).
  { unfold PHstate,PHmemory. eapply TickCellsRebase. exact Encoded. }
  unfold V293_tick_suffix_owned,V293_tick_loop_owned.
  change (PHstate PHmemory emp |=
    V293_owned_record_cell ((101%positive,0%Z),Tint32,Vint32 (Int.repr 37)) **
    (V293_owned_record_cell ((102%positive,0%Z),Tint8,V293_byteval 1) **
    (V293_owned_record_cell ((103%positive,0%Z),Tptr V293_tcb_type,Vptr WhileHead) **
    (V293_owned_record_cell (V293_tick_pointer_cell 70%positive WhileIdle) **
      V293_owned_record_cells
      (V293_tick_chain_cells (map fst WhileBindings) WhileIdle ++
      (V293_tick_bitmap_cells 92%positive 93%positive 3 16 16 ++
      (V293_tick_idle_cell WhileIdle ::
      (concat (map V293_tick_binding_extra WhileBindings) ++
      (V293_tick_idle_extra WhileIdle Vnull ++
      (V293_priority_cells 94%positive 0%Z RCentries ++ WhileFrameCells)))))))))) in Rebased.
  eapply astar_mono;[intros st H;exact H| |exact Rebased].
  eapply astar_mono;[intros st H;exact H| ].
  eapply astar_mono;[intros st H;exact H| ].
  eapply astar_mono;[intros st H;exact H| ].
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

Lemma PHfields : V293_target_wstate PHglobal TickLocal emp ChainOld |=
  V293_shared_fields WhileReady WhileOldTasks ChainEvents (Int.repr 37).
Proof.
  unfold V293_shared_fields,ChainOld,V293_shared_fixture_abs.
  repeat (eapply V293_target_wstate_star;
    [apply map_join_emp|apply map_join_merge;apply map_disjoint;intros key;destruct key;simpl;auto|
      split;reflexivity| ]).
  split;reflexivity.
Qed.

Theorem PHentry : PHstate PHmemory ChainOld |=
  V293_tick_suffix_owned 101%positive (Int.repr 37) 102%positive 1 103%positive WhileHead
    70%positive WhileIdle (map fst WhileBindings) WhileIdle 92%positive 93%positive 3 16 16
    (V293_owned_record_cells (concat (map V293_tick_binding_extra WhileBindings)) **
      (V293_owned_record_cells (V293_tick_idle_extra WhileIdle Vnull) **
        (V293_shared_fields WhileReady WhileOldTasks ChainEvents (Int.repr 37) **
          (V293_owned_record_cells (V293_priority_cells 94%positive 0%Z RCentries) **
            V293_owned_record_cells WhileFrameCells)))).
Proof.
  assert (Joint : PHstate PHmemory ChainOld |=
    V293_tick_suffix_owned 101%positive (Int.repr 37) 102%positive 1 103%positive WhileHead
      70%positive WhileIdle (map fst WhileBindings) WhileIdle 92%positive 93%positive 3 16 16
      (V293_owned_record_cells (concat (map V293_tick_binding_extra WhileBindings)) **
        (V293_owned_record_cells (V293_tick_idle_extra WhileIdle Vnull) **
          (V293_owned_record_cells (V293_priority_cells 94%positive 0%Z RCentries) **
            V293_owned_record_cells WhileFrameCells))) **
    V293_shared_fields WhileReady WhileOldTasks ChainEvents (Int.repr 37)).
  { apply sat_split'. exists PHmemory. exists (emp:mem). exists (emp:osabst). exists ChainOld.
    split;[apply map_join_emp| ]. split;[apply map_join_comm;apply map_join_emp| ].
    split;[exact PHraw_entry| ]. eapply V293_shared_fields_rebase. exact PHfields. }
  unfold V293_tick_suffix_owned,V293_tick_loop_owned in *. clear -Joint. sep auto.
Qed.

Definition PHexecution P ks Mf := V293_local_steps P
  (curs (V293_tick_post_hook 901%Z 902%Z 903%Z 1001%Z 1002%Z 1003%Z),(kenil,ks))
  ((PHglobal,TickLocal,PHmemory),(fun _ => false),(false,[3%nat],[false]))
  (curs (sskip None),(kenil,ks)) ((PHglobal,TickLocal,Mf),(fun _ => false),(false,[3%nat],[false])).
Definition PHresult Mf := PHstate Mf PHnew |=
  V293_ready_payload 93%positive 92%positive 94%positive WhileNewTasks **
  ((V293_owned_record_cell ((101%positive,0%Z),Tint32,Vint32 (Int.repr 38)) **
    (V293_owned_record_cell ((102%positive,0%Z),Tint8,V293_byteval 1) **
      (V293_owned_record_cell ((103%positive,0%Z),Tptr V293_tcb_type,Vptr WhileHead) **
        (V293_owned_record_cell (V293_tick_pointer_cell 70%positive WhileIdle) **
          (V293_shared_fields WhileReady WhileNewTasks ChainEvents (Int.repr 38) **
            V293_owned_record_cells WhileFrameCells))))) ** Atrue).

Theorem PHliteral : forall sd P ks,
  V293_task_records PHmemory WhileOldTasks /\
  spec_stepstar sd (spec_seq V293_tick_clock_action (V293_tick_chain_code WhileBindings))
    ChainOld (END None) PHnew /\
  (forall id, id<>ostmid -> id<>abstcblsid -> get PHnew id=get ChainOld id) /\
  exists Mf, PHexecution P ks Mf /\
    load Tint32 Mf (101%positive,0%Z)=Some (Vint32 (Int.repr 38)) /\
    load (Tptr V293_tcb_type) Mf (70%positive,0%Z)=Some (Vptr WhileIdle) /\
    V293_task_records Mf WhileNewTasks /\
    3=V293_ready_group 16 20 /\ V293_ready_rel 16 20 RCentries WhileNewTasks /\
    V293_ready_loads Mf 93%positive 92%positive 94%positive 16 20 RCentries /\ PHresult Mf.
Proof.
  intros sd P ks.
  exact (V293_tick_post_hook_ready_payload WhileBindings WhileIdle Vnull WhileReady ChainEvents (Int.repr 37)
    RCentries sd P ks PHglobal TickLocal PHmemory (fun _ => false) false [3%nat] [false] ChainOld (spec_done None)
    901%Z 902%Z 903%Z 1001%Z 1002%Z 1003%Z 70%positive 101%positive 102%positive 103%positive WhileIdle
    92%positive 93%positive 94%positive 16 16 (V293_owned_record_cells WhileFrameCells)
    ltac:(apply map_get_sig) ltac:(vm_compute;reflexivity) ltac:(vm_compute;reflexivity)
    ltac:(vm_compute;reflexivity) ltac:(vm_compute;reflexivity)
    ltac:(vm_compute;reflexivity) ltac:(vm_compute;reflexivity)
    ltac:(vm_compute;reflexivity) ltac:(vm_compute;reflexivity)
    ltac:(vm_compute;reflexivity) ltac:(vm_compute;reflexivity)
    ltac:(change (368+50<=4294967295)%Z;lia) WhileBindingsValid WhileKeysUnique RCold_rel PHentry).
Qed.

(* Same actual Mf and all task updates retained. ONLY abstract clock update
   is omitted (ChainNew rather than PHnew); no modified C execution claimed. *)
Theorem PHomitted_clock_control : forall (sd : ossched) P ks, exists Mf,
  PHexecution P ks Mf /\ PHresult Mf /\
  load Tint32 Mf (101%positive,0%Z)=Some (Vint32 (Int.repr 38)) /\
  get ChainNew ostmid=Some (ostm (Int.repr 37)) /\
  (forall id, id<>ostmid -> get PHnew id=get ChainNew id) /\
  ~ (PHstate Mf ChainNew |= V293_shared_fields WhileReady WhileNewTasks ChainEvents (Int.repr 38) ** Atrue).
Proof.
  intros sd P ks. destruct (PHliteral sd P ks)
    as (Old&Abstract&Slots&Mf&Exec&Time&Pointer&Records&Group&Rel&Loads&Result).
  pose proof (V293_shared_fields_get _ _ _ _ _ PHfields) as [Current [Tasks [Events Clock]]].
  assert (Stale : get ChainNew ostmid=Some (ostm (Int.repr 37))).
  { unfold ChainNew. rewrite map_get_set' by discriminate. exact Clock. }
  exists Mf. split;[exact Exec| ]. split;[exact Result| ]. split;[exact Time| ]. split;[exact Stale| ]. split.
  - intros id NotClock. unfold PHnew,ChainNew.
    destruct (OSAbstMod.eq_dec id abstcblsid) as [Same|NotTasks].
    + subst id. rewrite !map_get_set. reflexivity.
    + rewrite !map_get_set' by congruence. reflexivity.
  - intro Bad. pose proof (V293_star_abst_get_l _ _ _ _
      (fun st H => proj2 (proj2 (proj2 (V293_shared_fields_get _ _ _ _ st H)))) _ Bad) as Wrong.
    change (get ChainNew ostmid=Some (ostm (Int.repr 38))) in Wrong.
    rewrite Stale in Wrong. discriminate Wrong.
Qed.

Theorem PHold_physical_clock_control : forall (sd : ossched) P ks, exists Mf,
  PHexecution P ks Mf /\ PHresult Mf /\
  load Tint32 Mf (101%positive,0%Z)=Some (Vint32 (Int.repr 38)) /\
  ~ (PHstate Mf PHnew |= V293_owned_record_cell
    ((101%positive,0%Z),Tint32,Vint32 (Int.repr 37)) ** Atrue).
Proof.
  intros sd P ks. destruct (PHliteral sd P ks)
    as (Old&Abstract&Slots&Mf&Exec&Time&Pointer&Records&Group&Rel&Loads&Result).
  exists Mf. split;[exact Exec| ]. split;[exact Result| ]. split;[exact Time| ]. intro Bad.
  assert (Wrong : load Tint32 Mf (101%positive,0%Z)=Some (Vint32 (Int.repr 37))).
  { change (load Tint32 (getmem (PHstate Mf PHnew)) (101%positive,0%Z)=Some (Vint32 (Int.repr 37))).
    eapply V293_record_star_load_l;[apply V293_owned_record_cell_load|exact Bad]. }
  pose proof (eq_trans (eq_sym Time) Wrong) as Clash. discriminate Clash.
Qed.

Theorem PHinitialization_and_frame : forall (sd : ossched) P ks, exists Mf,
  load (Tptr V293_tcb_type) PHmemory (70%positive,0%Z)=Some (Vptr WhileIdle) /\
  WhileHead<>WhileIdle /\ PHexecution P ks Mf /\ PHresult Mf /\
  V293_task_record Mf WhileHead (Int.repr 10) rdy Vnull /\
  V293_task_record Mf WhileSecond (Int.repr 2) (wait os_stat_time (Int.repr 2)) Vnull /\
  V293_task_record Mf WhileIdle (Int.repr 12) rdy Vnull /\
  get PHnew curtid=Some (oscurt WhileReady) /\
  get PHnew absecblsid=Some (absecblist ChainEvents) /\
  V293_table_loads V293_tcb_type Mf 94%positive RCentries /\
  load Tint32 Mf (90%positive,0%Z)=Some (Vint32 (Int.repr 99)).
Proof.
  intros sd P ks. destruct (PHliteral sd P ks)
    as (Old&Abstract&Slots&Mf&Exec&Time&Pointer&Records&Group&Rel&Loads&Result).
  pose proof (V293_shared_fields_get _ _ _ _ _ PHfields) as [Current [Tasks [Events Clock]]].
  exists Mf. split.
  - change (load (Tptr V293_tcb_type) (getmem (PHstate PHmemory emp)) (70%positive,0%Z)=Some (Vptr WhileIdle)).
    eapply V293_record_star_load_r;[ |exact PHraw_entry].
    eapply V293_record_star_load_r. eapply V293_record_star_load_r.
    eapply V293_record_star_load_l. apply V293_owned_record_cell_load.
  - split;[vm_compute;congruence| ]. split;[exact Exec| ]. split;[exact Result| ]. split.
    + apply Records. unfold WhileNewTasks. apply map_get_set.
    + split.
      * apply Records. unfold WhileNewTasks. cbn [WhileBindings V293_tick_record_map].
        rewrite map_get_set' by (vm_compute;congruence). apply map_get_set.
      * split.
        -- apply Records. unfold WhileNewTasks. cbn [WhileBindings V293_tick_record_map].
           rewrite !map_get_set' by (vm_compute;congruence). apply map_get_sig.
        -- split;[rewrite Slots by discriminate;exact Current| ].
           split;[rewrite Slots by discriminate;exact Events| ].
           split;[exact (proj2 (proj2 (proj2 Loads)))| ].
           assert (Frame : PHstate Mf PHnew |= V293_owned_record_cells WhileFrameCells ** Atrue)
             by (unfold PHresult in Result;clear -Result;sep auto).
           change (load Tint32 (getmem (PHstate Mf PHnew)) (90%positive,0%Z)=Some (Vint32 (Int.repr 99))).
           eapply V293_record_star_load_l;[ |exact Frame].
           apply V293_owned_record_cells_load. left;reflexivity.
Qed.
