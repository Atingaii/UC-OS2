Require Import CertiOS.certiucos.v293.proofs.V293TimeTickStorage.
(* Real allocation/initialization and a separate post-hook return checkpoint.
   These traces are NOT joined across the still-open CPU hook. *)
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickRawReadyReturn.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickLifecycle.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordInvariant.
Require Import CertiOS.audit.probes.V293TimeTickPostHookReadyProbe.
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

Definition RRlocal := V293_tick_locals 901%Z 904%Z 70%positive 71%positive.
Definition RRcaller : env := set emp 9999%Z (999%positive,Tint32).
Definition RRcells :=
  ((101%positive,0%Z),Tint32,Vint32 (Int.repr 37)) ::
  ((102%positive,0%Z),Tint8,V293_byteval 1) ::
  ((103%positive,0%Z),Tptr V293_tcb_type,Vptr WhileHead) :: tl RCcells.
Definition RRbase := OwnershipCellsMemory RRcells.
Definition RRstate le M O : RstateOP :=
  (PHglobal,le,M,(fun _ => false),(false,[3%nat],[false]),O,spec_done None).
Definition RRframe :=
  V293_owned_record_cell ((101%positive,0%Z),Tint32,Vint32 (Int.repr 37)) **
  (V293_owned_record_cell ((102%positive,0%Z),Tint8,V293_byteval 1) **
    (V293_owned_record_cell ((103%positive,0%Z),Tptr V293_tcb_type,Vptr WhileHead) **
      (V293_owned_record_cells (V293_tick_chain_cells (map fst WhileBindings) WhileIdle) **
        (V293_owned_record_cells (V293_tick_bitmap_cells 92%positive 93%positive 3 16 16) **
          (V293_owned_record_cell (V293_tick_idle_cell WhileIdle) **
            (V293_owned_record_cells (concat (map V293_tick_binding_extra WhileBindings)) **
              (V293_owned_record_cells (V293_tick_idle_extra WhileIdle Vnull) **
                (V293_shared_fields WhileReady WhileOldTasks ChainEvents (Int.repr 37) **
                  (V293_owned_record_cells (V293_priority_cells 94%positive 0%Z RCentries) **
                    V293_owned_record_cells WhileFrameCells))))))))).

Lemma RRbase_raw : RRstate RRlocal RRbase emp |=
  V293_owned_record_cell ((101%positive,0%Z),Tint32,Vint32 (Int.repr 37)) **
  (V293_owned_record_cell ((102%positive,0%Z),Tint8,V293_byteval 1) **
  (V293_owned_record_cell ((103%positive,0%Z),Tptr V293_tcb_type,Vptr WhileHead) **
  (V293_owned_record_cells (V293_tick_chain_cells (map fst WhileBindings) WhileIdle) **
  (V293_owned_record_cells (V293_tick_bitmap_cells 92%positive 93%positive 3 16 16) **
  (V293_owned_record_cell (V293_tick_idle_cell WhileIdle) **
    (V293_owned_record_cells (concat (map V293_tick_binding_extra WhileBindings)) **
      (V293_owned_record_cells (V293_tick_idle_extra WhileIdle Vnull) **
        (V293_owned_record_cells (V293_priority_cells 94%positive 0%Z RCentries) **
          V293_owned_record_cells WhileFrameCells)))))))).
Proof.
  assert (Apart : OwnershipCellsSeparated RRcells).
  { vm_compute. repeat split;intros a Member Rest;
      repeat destruct Member as [Member|Member];try contradiction;subst a;intuition discriminate. }
  assert (Valid : Forall (fun cell => let '(_,tp,v) := cell in
    rule_type_val_match tp v=true) RRcells).
  { repeat constructor;reflexivity. }
  pose proof (OwnershipCellsSpatial _ Apart Valid PHglobal RRlocal) as Encoded.
  assert (Rebased : RRstate RRlocal RRbase emp |= V293_owned_record_cells RRcells).
  { unfold RRstate,RRbase. eapply TickCellsRebase. exact Encoded. }
  change (RRstate RRlocal RRbase emp |=
    V293_owned_record_cell ((101%positive,0%Z),Tint32,Vint32 (Int.repr 37)) **
    (V293_owned_record_cell ((102%positive,0%Z),Tint8,V293_byteval 1) **
    (V293_owned_record_cell ((103%positive,0%Z),Tptr V293_tcb_type,Vptr WhileHead) **
      V293_owned_record_cells
      (V293_tick_chain_cells (map fst WhileBindings) WhileIdle ++
      (V293_tick_bitmap_cells 92%positive 93%positive 3 16 16 ++
      (V293_tick_idle_cell WhileIdle ::
      (concat (map V293_tick_binding_extra WhileBindings) ++
      (V293_tick_idle_extra WhileIdle Vnull ++
      (V293_priority_cells 94%positive 0%Z RCentries ++ WhileFrameCells))))))))) in Rebased.
  eapply astar_mono;[intros st H;exact H| |exact Rebased].
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

Lemma RRbase_entry : RRstate RRlocal RRbase ChainOld |= RRframe.
Proof.
  assert (Joint : RRstate RRlocal RRbase ChainOld |=
    (V293_owned_record_cell ((101%positive,0%Z),Tint32,Vint32 (Int.repr 37)) **
      (V293_owned_record_cell ((102%positive,0%Z),Tint8,V293_byteval 1) **
      (V293_owned_record_cell ((103%positive,0%Z),Tptr V293_tcb_type,Vptr WhileHead) **
      (V293_owned_record_cells (V293_tick_chain_cells (map fst WhileBindings) WhileIdle) **
      (V293_owned_record_cells (V293_tick_bitmap_cells 92%positive 93%positive 3 16 16) **
      (V293_owned_record_cell (V293_tick_idle_cell WhileIdle) **
        (V293_owned_record_cells (concat (map V293_tick_binding_extra WhileBindings)) **
        (V293_owned_record_cells (V293_tick_idle_extra WhileIdle Vnull) **
        (V293_owned_record_cells (V293_priority_cells 94%positive 0%Z RCentries) **
          V293_owned_record_cells WhileFrameCells))))))))) **
    V293_shared_fields WhileReady WhileOldTasks ChainEvents (Int.repr 37)).
  { apply sat_split'. exists RRbase. exists (emp:mem). exists (emp:osabst). exists ChainOld.
    split;[apply map_join_emp| ]. split;[apply map_join_comm;apply map_join_emp| ].
    split;[exact RRbase_raw| ]. eapply V293_shared_fields_rebase. exact PHfields. }
  unfold RRframe. clear -Joint. sep auto.
Qed.

Lemma RRfresh : fresh RRbase 70%positive /\
  fresh (allocb RRbase 70%positive 0%Z 4) 71%positive.
Proof.
  assert (Outside : forall b i, b=70%positive \/ b=71%positive -> get RRbase (b,i)=None).
  { intros b i Which. unfold RRbase. apply OwnershipCellsOutside.
    destruct Which as [E|E];subst b;vm_compute;intro Member;
      repeat destruct Member as [Member|Member];try contradiction;discriminate. }
  split.
  - intros l i E [v Bound]. subst l. change (get RRbase (70%positive,i)=Some v) in Bound.
    rewrite Outside in Bound by auto. discriminate.
  - intros l i E [v Bound]. subst l.
    change (get (allocb RRbase 70%positive 0%Z 4) (71%positive,i)=Some v) in Bound.
    rewrite V293_success_allocb_outside in Bound by (left;discriminate).
    change (get RRbase (71%positive,i)=Some v) in Bound.
    rewrite Outside in Bound by auto. discriminate.
Qed.

Definition RRfunction := V293_tick_function 901%Z 902%Z 903%Z 904%Z 1001%Z 1002%Z 1003%Z 1101%Z.
Definition RRprefix P ks M := V293_local_steps P
  (curs (scall 1100%Z nil),(kenil,ks))
  ((PHglobal,RRcaller,RRbase),(fun _ => false),(false,[3%nat],[false]))
  (curs (scall 1101%Z nil),(kenil,kseq (V293_tick_post_hook 901%Z 902%Z 903%Z 1001%Z 1002%Z 1003%Z)
    (kseq sret (kcall 1100%Z
      (sseq (V293_tick_body 901%Z 902%Z 903%Z 904%Z 1001%Z 1002%Z 1003%Z 1101%Z) sret) RRcaller ks))))
  ((PHglobal,RRlocal,M),(fun _ => false),(false,[3%nat],[false])).
Definition RRentry M := RRstate RRlocal M ChainOld |=
  V293_tick_storage_owned 101%positive (Int.repr 37) 102%positive 1 103%positive WhileHead
    70%positive Vundef (map fst WhileBindings) WhileIdle 92%positive 93%positive 3 16 16
    (V293_owned_record_cells (concat (map V293_tick_binding_extra WhileBindings)) **
      (V293_owned_record_cells (V293_tick_idle_extra WhileIdle Vnull) **
        (V293_shared_fields WhileReady WhileOldTasks ChainEvents (Int.repr 37) **
          (V293_owned_record_cells (V293_priority_cells 94%positive 0%Z RCentries) **
            (V293_owned_record_cell ((71%positive,0%Z),Tint32,Vint32 Int.zero) **
              V293_owned_record_cells WhileFrameCells))))).

Theorem RRallocated_entry : forall P ks, P 1100%Z=Some RRfunction -> exists M,
  RRprefix P ks M /\ load (Tptr V293_tcb_type) M (70%positive,0%Z)=Some Vundef /\
  load Tint32 M (71%positive,0%Z)=Some (Vint32 Int.zero) /\ RRentry M.
Proof.
  intros P ks Program. destruct RRfresh as [FreshScan FreshSaved].
  destruct (V293_tick_call_to_hook P ks PHglobal RRcaller RRbase (fun _ => false)
    false [3%nat] [false] ChainOld (spec_done None) 1100%Z 901%Z 902%Z 903%Z 904%Z
    1001%Z 1002%Z 1003%Z 1101%Z 70%positive 71%positive RRframe Program ltac:(discriminate)
    FreshScan FreshSaved RRbase_entry) as (M&Prefix&Scan&Saved&Owned).
  exists M. split;[exact Prefix| ]. split;[exact Scan| ]. split;[exact Saved| ].
  unfold RRentry,RRframe,V293_tick_storage_owned in *. clear -Owned. sep auto.
Qed.

Definition RRexecution P ks M Mf := V293_local_steps P
  (curs (sskip None),(kenil,kseq (V293_tick_post_hook 901%Z 902%Z 903%Z 1001%Z 1002%Z 1003%Z)
    (kseq sret (kcall 1100%Z
      (sseq (V293_tick_body 901%Z 902%Z 903%Z 904%Z 1001%Z 1002%Z 1003%Z 1101%Z) sret) RRcaller ks))))
  ((PHglobal,RRlocal,M),(fun _ => false),(false,[3%nat],[false]))
  (curs (sskip None),(kenil,ks))
  ((PHglobal,RRcaller,Mf),(fun _ => false),(false,[3%nat],[false])).
Definition RRresult Mf := RRstate RRcaller Mf PHnew |=
  V293_tick_return_payload 93%positive 92%positive 94%positive WhileNewTasks
    101%positive (Int.repr 38) 102%positive 103%positive WhileHead WhileReady ChainEvents WhileFrameCells.

Theorem RRliteral : forall (sd : ossched) P ks, P 1100%Z=Some RRfunction -> exists M Ms Mf,
  RRprefix P ks M /\ load (Tptr V293_tcb_type) M (70%positive,0%Z)=Some Vundef /\
  load Tint32 M (71%positive,0%Z)=Some (Vint32 Int.zero) /\
  spec_stepstar sd (spec_seq V293_tick_clock_action (V293_tick_chain_code WhileBindings))
    ChainOld (END None) PHnew /\
  (forall id, id<>ostmid -> id<>abstcblsid -> get PHnew id=get ChainOld id) /\
  RRexecution P ks M Mf /\
  load Tint32 Ms (101%positive,0%Z)=Some (Vint32 (Int.repr 38)) /\
  load (Tptr V293_tcb_type) Ms (70%positive,0%Z)=Some (Vptr WhileIdle) /\
  V293_task_records Ms WhileNewTasks /\
  3=V293_ready_group 16 20 /\ V293_ready_rel 16 20 RCentries WhileNewTasks /\
  V293_ready_loads Ms 93%positive 92%positive 94%positive 16 20 RCentries /\ RRresult Mf /\
  (forall b i, b<>70%positive -> b<>71%positive -> get Mf (b,i)=get Ms (b,i)) /\
  (forall k, k<4 -> get Mf (70%positive,Z.of_nat k)=None /\ get Mf (71%positive,Z.of_nat k)=None).
Proof.
  intros sd P ks Program. destruct (RRallocated_entry P ks Program) as (M&Prefix&Scan&Saved&Entry).
  pose proof (V293_tick_raw_ready_return WhileBindings WhileIdle Vnull WhileReady ChainEvents (Int.repr 37)
    RCentries sd P ks PHglobal RRcaller M (fun _ => false) false [3%nat] [false] ChainOld (spec_done None)
    901%Z 904%Z 902%Z 903%Z 1001%Z 1002%Z 1003%Z 70%positive 71%positive 101%positive 102%positive 103%positive
    92%positive 93%positive 94%positive 16 16 1100%Z
    (sseq (V293_tick_body 901%Z 902%Z 903%Z 904%Z 1001%Z 1002%Z 1003%Z 1101%Z) sret) WhileFrameCells
    ltac:(discriminate) ltac:(discriminate)
    ltac:(vm_compute;reflexivity) ltac:(vm_compute;reflexivity) ltac:(vm_compute;reflexivity)
    ltac:(vm_compute;reflexivity) ltac:(vm_compute;reflexivity)
    ltac:(vm_compute;reflexivity) ltac:(vm_compute;reflexivity)
    ltac:(vm_compute;reflexivity) ltac:(vm_compute;reflexivity)
    ltac:(vm_compute;reflexivity) ltac:(vm_compute;reflexivity)
    ltac:(change (368+50<=4294967295)%Z;lia) WhileBindingsValid WhileKeysUnique RCold_rel Entry) as Run.
  destruct Run as (Old&Abstract&Slots&Ms&Mf&Exec&Time&Pointer&Records&Group&Rel&Loads&Result&Frame&Gone).
  exists M. exists Ms. exists Mf. split;[exact Prefix| ]. split;[exact Scan| ]. split;[exact Saved| ].
  split;[exact Abstract| ]. split;[exact Slots| ]. split;[exact Exec| ]. split;[exact Time| ].
  split;[exact Pointer| ]. split;[exact Records| ]. split;[exact Group| ]. split;[exact Rel| ].
  split;[exact Loads| ]. split;[exact Result| ]. split;assumption.
Qed.

(* Both checkpoints are satisfiable in a concrete program; no hook body is
   installed, so this is deliberately NOT one continuous full call. *)
Definition RRprogram : progunit := fun f => if Z.eq_dec f 1100%Z then Some RRfunction else None.
Theorem RRnonvacuous : forall (sd : ossched),
  RRcaller<>RRlocal /\ RRprogram 1100%Z=Some RRfunction /\
  exists M Mf, RRprefix RRprogram kstop M /\ RRexecution RRprogram kstop M Mf /\ RRresult Mf.
Proof.
  intro sd. split.
  - intro Same. assert (Read := f_equal (fun e => get e 9999%Z) Same). vm_compute in Read. discriminate.
  - split;[reflexivity| ]. destruct (RRliteral sd RRprogram kstop eq_refl)
      as (M&Ms&Mf&Prefix&Scan&Saved&Abstract&Slots&Exec&Time&Pointer&Records&Group&Rel&Loads&Result&Frame&Gone).
    exists M. exists Mf. split;[exact Prefix| ]. split;assumption.
Qed.

Theorem RRobservations : forall (sd : ossched) P ks, P 1100%Z=Some RRfunction -> exists M Mf,
  RRprefix P ks M /\ RRexecution P ks M Mf /\ RRresult Mf /\
  load Tint32 Mf (101%positive,0%Z)=Some (Vint32 (Int.repr 38)) /\
  V293_task_record Mf WhileHead (Int.repr 10) rdy Vnull /\
  V293_task_record Mf WhileSecond (Int.repr 2) (wait os_stat_time (Int.repr 2)) Vnull /\
  V293_task_record Mf WhileIdle (Int.repr 12) rdy Vnull /\
  V293_table_loads V293_tcb_type Mf 94%positive RCentries /\
  load Tint32 Mf (90%positive,0%Z)=Some (Vint32 (Int.repr 99)) /\
  get PHnew curtid=Some (oscurt WhileReady) /\ get PHnew absecblsid=Some (absecblist ChainEvents) /\
  (forall k, k<4 -> get Mf (70%positive,Z.of_nat k)=None /\ get Mf (71%positive,Z.of_nat k)=None).
Proof.
  intros sd P ks Program. destruct (RRliteral sd P ks Program)
    as (M&Ms&Mf&Prefix&Scan&Saved&Abstract&Slots&Exec&Time&Pointer&Records&Group&Rel&Loads&Result&Frame&Gone).
  pose proof (V293_shared_fields_get _ _ _ _ _ PHfields) as [Current [Tasks [Events Clock]]].
  exists M. exists Mf. split;[exact Prefix| ]. split;[exact Exec| ]. split;[exact Result| ]. split.
  - exact (eq_trans (V293_load_block_frame Tint32 Ms Mf 101%positive 0%Z
      ltac:(intro i;apply Frame;discriminate)) Time).
  - split.
    + eapply V293_task_record_frame;[intro i;apply Frame;discriminate| ].
      apply Records. unfold WhileNewTasks. apply map_get_set.
    + split.
      * eapply V293_task_record_frame;[intro i;apply Frame;discriminate| ].
        apply Records. unfold WhileNewTasks. cbn [WhileBindings V293_tick_record_map].
        rewrite map_get_set' by (vm_compute;congruence). apply map_get_set.
      * split.
        -- eapply V293_task_record_frame;[intro i;apply Frame;discriminate| ].
           apply Records. unfold WhileNewTasks. cbn [WhileBindings V293_tick_record_map].
           rewrite !map_get_set' by (vm_compute;congruence). apply map_get_sig.
        -- split.
           ++ intros p Bound. exact (eq_trans (V293_load_block_frame (Tptr V293_tcb_type) Ms Mf
                94%positive (4*Z.of_nat p)%Z ltac:(intro i;apply Frame;discriminate))
                (proj2 (proj2 (proj2 Loads)) p Bound)).
           ++ split.
              ** assert (Canary : RRstate RRcaller Mf PHnew |= V293_owned_record_cells WhileFrameCells ** Atrue).
                 { unfold RRresult,V293_tick_return_payload in Result.
                   cbn [app V293_owned_record_cells] in Result. clear -Result. sep auto. }
                 change (load Tint32 (getmem (RRstate RRcaller Mf PHnew)) (90%positive,0%Z)=Some (Vint32 (Int.repr 99))).
                 eapply V293_record_star_load_l;[ |exact Canary].
                 apply V293_owned_record_cells_load. left;reflexivity.
              ** split;[rewrite Slots by discriminate;exact Current| ].
                 split;[rewrite Slots by discriminate;exact Events|exact Gone].
Qed.

(* Only the abstract clock slot is changed; execution, new task/ready payload
   and every actual returned byte remain the same. *)
Theorem RRomitted_clock_control : forall (sd : ossched) P ks, P 1100%Z=Some RRfunction -> exists M Mf,
  RRexecution P ks M Mf /\ RRresult Mf /\
  load Tint32 Mf (101%positive,0%Z)=Some (Vint32 (Int.repr 38)) /\
  get ChainNew ostmid=Some (ostm (Int.repr 37)) /\
  (forall id, id<>ostmid -> get PHnew id=get ChainNew id) /\
  ~ (RRstate RRcaller Mf ChainNew |= V293_shared_fields WhileReady WhileNewTasks ChainEvents (Int.repr 38) ** Atrue).
Proof.
  intros sd P ks Program. destruct (RRobservations sd P ks Program)
    as (M&Mf&Prefix&Exec&Result&Time&Rest).
  pose proof (V293_shared_fields_get _ _ _ _ _ PHfields) as [Current [Tasks [Events Clock]]].
  assert (Stale : get ChainNew ostmid=Some (ostm (Int.repr 37))).
  { unfold ChainNew. rewrite map_get_set' by discriminate. exact Clock. }
  exists M. exists Mf. split;[exact Exec| ]. split;[exact Result| ]. split;[exact Time| ]. split;[exact Stale| ]. split.
  - intros id NotClock. unfold PHnew,ChainNew.
    destruct (OSAbstMod.eq_dec id abstcblsid) as [Same|NotTasks].
    + subst id. rewrite !map_get_set. reflexivity.
    + rewrite !map_get_set' by congruence. reflexivity.
  - intro Bad. pose proof (V293_star_abst_get_l _ _ _ _
      (fun st H => proj2 (proj2 (proj2 (V293_shared_fields_get _ _ _ _ st H)))) _ Bad) as Wrong.
    change (get ChainNew ostmid=Some (ostm (Int.repr 38))) in Wrong.
    rewrite Stale in Wrong. discriminate Wrong.
Qed.

(* A post-relation rejection, NOT a claim of executing an omitted-free C mutant. *)
Theorem RRfreed_pointer_control : forall (sd : ossched) P ks, P 1100%Z=Some RRfunction -> exists M Mf,
  RRexecution P ks M Mf /\ RRresult Mf /\
  (forall k, k<4 -> get Mf (70%positive,Z.of_nat k)=None /\ get Mf (71%positive,Z.of_nat k)=None) /\
  ~ (RRstate RRcaller Mf PHnew |=
    V293_owned_record_cell (V293_tick_pointer_cell 70%positive WhileIdle) ** Atrue).
Proof.
  intros sd P ks Program. destruct (RRliteral sd P ks Program)
    as (M&Ms&Mf&Prefix&Scan&Saved&Abstract&Slots&Exec&Time&Pointer&Records&Group&Rel&Loads&Result&Frame&Gone).
  exists M. exists Mf. split;[exact Exec| ]. split;[exact Result| ]. split;[exact Gone| ]. intro Bad.
  assert (Wrong : load (Tptr V293_tcb_type) Mf (70%positive,0%Z)=Some (Vptr WhileIdle)).
  { change (load (Tptr V293_tcb_type) (getmem (RRstate RRcaller Mf PHnew)) (70%positive,0%Z)=Some (Vptr WhileIdle)).
    eapply V293_record_star_load_l;[apply V293_owned_record_cell_load|exact Bad]. }
  assert (Missing : load (Tptr V293_tcb_type) Mf (70%positive,0%Z)=None).
  { pose proof (proj1 (Gone 0 ltac:(lia))) as Missing0.
    (* The get type index must be addr, not its definitionally equal pair. *)
    change (get Mf ((70%positive,0%Z):addr)=None) in Missing0.
    unfold load,loadm. cbn [typelen loadbytes]. rewrite Missing0. reflexivity. }
  rewrite Missing in Wrong. discriminate.
Qed.
