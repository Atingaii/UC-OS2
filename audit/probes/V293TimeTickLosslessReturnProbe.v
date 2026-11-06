Require Import CertiOS.certiucos.v293.proofs.V293TimeTickTaskBridge.
Require Import CertiOS.audit.probes.V293TimeTickRawReadyReturnProbe.
Require Import CertiOS.tactics.basetac.perm_map_lemmas_part4.
Require Import CertiOS.tactics.basetac.perm_map_lemmas_part1.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewWitness.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickLosslessFields.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickLosslessReturn.
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

Definition LRlocal := V293_tick_locals 901%Z 904%Z 70%positive 71%positive.
Definition LRcaller : env := set emp 9999%Z (90%positive,Tint32).
Definition LRglobal : env := set PHglobal OSTCBCur (105%positive,Tptr Tvoid).
Definition LRpointer := V293_encoded_memory 105%positive 0%Z false
  (encode_val (Tptr Tvoid) (Vptr WhileReady)).
Definition LRcells :=
  ((101%positive,0%Z),Tint32,Vint32 (Int.repr 37)) ::
  ((102%positive,0%Z),Tint8,V293_byteval 1) ::
  ((103%positive,0%Z),Tptr V293_tcb_type,Vptr WhileHead) :: tl RCcells.
Definition LRrawmemory := OwnershipCellsMemory LRcells.
Definition LRbase := merge LRpointer LRrawmemory.
Definition LRstate le M O : RstateOP :=
  (LRglobal,le,M,(fun _ => false),(false,[3%nat],[false]),O,spec_done None).
Definition LRframe :=
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
                    (CurTid WhileReady ** V293_owned_record_cells WhileFrameCells)))))))))).

Lemma LRrawmemory_raw : LRstate LRlocal LRrawmemory emp |=
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
  (* Reuse RRbase_raw's OwnershipCellsSpatial construction; all raw cells are
     the same and their satisfaction is independent of ge/le. *)
  exact RRbase_raw.
Qed.

Lemma LRbase_join : join LRpointer LRrawmemory LRbase.
Proof.
  apply map_join_merge. apply map_disjoint. intros [b i].
  destruct (Pos.eq_dec b 105%positive) as [E|E].
  - subst b. right;left. unfold LRrawmemory. apply OwnershipCellsOutside.
    vm_compute;intro Member;repeat destruct Member as [Member|Member];try contradiction;discriminate.
  - left. unfold LRpointer. apply V293_encoded_memory_outside. left;exact E.
Qed.

Lemma LRpointer_spatial : LRstate LRlocal LRpointer emp |= CurTid WhileReady.
Proof.
  exists Tvoid. exists 105%positive.
  apply sat_split'. exists (emp:mem). exists LRpointer.
  exists (emp:osabst). exists (emp:osabst).
  split;[apply map_join_comm;apply map_join_emp| ]. split;[apply map_join_emp| ]. split.
  - exists 105%positive. split;[apply map_get_set| ]. repeat split;reflexivity.
  - split;[apply V293_encoded_memory_mapsto|reflexivity].
Qed.

Lemma LRbase_entry : LRstate LRlocal LRbase ChainOld |= LRframe.
Proof.
  assert (Joint : LRstate LRlocal LRbase ChainOld |=
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
    (CurTid WhileReady ** V293_shared_fields WhileReady WhileOldTasks ChainEvents (Int.repr 37))).
  { apply sat_split'. exists LRrawmemory. exists LRpointer.
    exists (emp:osabst). exists ChainOld.
    split;[apply map_join_comm;exact LRbase_join| ].
    split;[apply map_join_comm;apply map_join_emp| ].
    split;[exact LRrawmemory_raw| ].
    apply sat_split'. exists LRpointer. exists (emp:mem).
    exists (emp:osabst). exists ChainOld.
    split;[apply map_join_emp| ]. split;[apply map_join_comm;apply map_join_emp| ].
    split;[exact LRpointer_spatial| ]. eapply V293_shared_fields_rebase. exact PHfields. }
  unfold LRframe. clear -Joint. sep auto.
Qed.

Lemma LRfresh : fresh LRbase 70%positive /\
  fresh (allocb LRbase 70%positive 0%Z 4) 71%positive.
Proof.
  assert (Outside : forall b i, b=70%positive \/ b=71%positive -> get LRbase (b,i)=None).
  { intros b i Which. eapply mem_join_get_none with (m1:=LRpointer) (m2:=LRrawmemory).
    - unfold LRpointer. apply V293_encoded_memory_outside. left;destruct Which;congruence.
    - unfold LRrawmemory. apply OwnershipCellsOutside.
      destruct Which as [E|E];subst b;vm_compute;intro Member;
        repeat destruct Member as [Member|Member];try contradiction;discriminate.
    - exact LRbase_join. }
  split.
  - intros l i E [v Bound]. subst l. change (get LRbase (70%positive,i)=Some v) in Bound.
    rewrite Outside in Bound by auto. discriminate.
  - intros l i E [v Bound]. subst l.
    change (get (allocb LRbase 70%positive 0%Z 4) (71%positive,i)=Some v) in Bound.
    rewrite V293_success_allocb_outside in Bound by (left;discriminate).
    change (get LRbase (71%positive,i)=Some v) in Bound.
    rewrite Outside in Bound by auto. discriminate.
Qed.

Definition LRfunction := V293_tick_function 901%Z 902%Z 903%Z 904%Z 1001%Z 1002%Z 1003%Z 1101%Z.
Definition LRprefix P ks M := V293_local_steps P
  (curs (scall 1100%Z nil),(kenil,ks))
  ((LRglobal,LRcaller,LRbase),(fun _ => false),(false,[3%nat],[false]))
  (curs (scall 1101%Z nil),(kenil,kseq (V293_tick_post_hook 901%Z 902%Z 903%Z 1001%Z 1002%Z 1003%Z)
    (kseq sret (kcall 1100%Z
      (sseq (V293_tick_body 901%Z 902%Z 903%Z 904%Z 1001%Z 1002%Z 1003%Z 1101%Z) sret) LRcaller ks))))
  ((LRglobal,LRlocal,M),(fun _ => false),(false,[3%nat],[false])).
Definition LRentry M := LRstate LRlocal M ChainOld |=
  V293_tick_storage_owned 101%positive (Int.repr 37) 102%positive 1 103%positive WhileHead
    70%positive Vundef (map fst WhileBindings) WhileIdle 92%positive 93%positive 3 16 16
    (V293_owned_record_cells (concat (map V293_tick_binding_extra WhileBindings)) **
      (V293_owned_record_cells (V293_tick_idle_extra WhileIdle Vnull) **
        (V293_shared_fields WhileReady WhileOldTasks ChainEvents (Int.repr 37) **
          (V293_owned_record_cells (V293_priority_cells 94%positive 0%Z RCentries) **
            (V293_owned_record_cell ((71%positive,0%Z),Tint32,Vint32 Int.zero) **
              (CurTid WhileReady ** V293_owned_record_cells WhileFrameCells)))))).

Theorem LRallocated_entry : forall P ks, P 1100%Z=Some LRfunction -> exists M,
  LRprefix P ks M /\ load (Tptr V293_tcb_type) M (70%positive,0%Z)=Some Vundef /\
  load Tint32 M (71%positive,0%Z)=Some (Vint32 Int.zero) /\ LRentry M.
Proof.
  intros P ks Program. destruct LRfresh as [FreshScan FreshSaved].
  destruct (V293_tick_call_to_hook P ks LRglobal LRcaller LRbase (fun _ => false)
    false [3%nat] [false] ChainOld (spec_done None) 1100%Z 901%Z 902%Z 903%Z 904%Z
    1001%Z 1002%Z 1003%Z 1101%Z 70%positive 71%positive LRframe Program ltac:(discriminate)
    FreshScan FreshSaved LRbase_entry) as (M&Prefix&Scan&Saved&Owned).
  exists M. split;[exact Prefix| ]. split;[exact Scan| ]. split;[exact Saved| ].
  unfold LRentry,LRframe,V293_tick_storage_owned in *. clear -Owned. sep auto.
Qed.

Definition LRexecution P ks M Mf := V293_local_steps P
  (curs (sskip None),(kenil,kseq (V293_tick_post_hook 901%Z 902%Z 903%Z 1001%Z 1002%Z 1003%Z)
    (kseq sret (kcall 1100%Z
      (sseq (V293_tick_body 901%Z 902%Z 903%Z 904%Z 1001%Z 1002%Z 1003%Z 1101%Z) sret) LRcaller ks))))
  ((LRglobal,LRlocal,M),(fun _ => false),(false,[3%nat],[false]))
  (curs (sskip None),(kenil,ks))
  ((LRglobal,LRcaller,Mf),(fun _ => false),(false,[3%nat],[false])).
Definition LRresult Mf := LRstate LRcaller Mf PHnew |=
  V293_tick_lossless_return_payload 93%positive 92%positive 94%positive WhileNewTasks
    101%positive (Int.repr 38) 102%positive 103%positive WhileHead WhileReady ChainEvents WhileFrameCells
    (V293_tick_chain_residual WhileBindings WhileIdle).

Theorem LRliteral : forall (sd : ossched) P ks, P 1100%Z=Some LRfunction -> exists M Ms Mf,
  LRprefix P ks M /\ load (Tptr V293_tcb_type) M (70%positive,0%Z)=Some Vundef /\
  load Tint32 M (71%positive,0%Z)=Some (Vint32 Int.zero) /\
  spec_stepstar sd (spec_seq V293_tick_clock_action (V293_tick_chain_code WhileBindings))
    ChainOld (END None) PHnew /\
  (forall id, id<>ostmid -> id<>abstcblsid -> get PHnew id=get ChainOld id) /\
  LRexecution P ks M Mf /\
  load Tint32 Ms (101%positive,0%Z)=Some (Vint32 (Int.repr 38)) /\
  load (Tptr V293_tcb_type) Ms (70%positive,0%Z)=Some (Vptr WhileIdle) /\
  V293_task_records Ms WhileNewTasks /\
  3=V293_ready_group 16 20 /\ V293_ready_rel 16 20 RCentries WhileNewTasks /\
  V293_ready_loads Ms 93%positive 92%positive 94%positive 16 20 RCentries /\ LRresult Mf /\
  (forall b i, b<>70%positive -> b<>71%positive -> get Mf (b,i)=get Ms (b,i)) /\
  (forall k, k<4 -> get Mf (70%positive,Z.of_nat k)=None /\ get Mf (71%positive,Z.of_nat k)=None).
Proof.
  intros sd P ks Program. destruct (LRallocated_entry P ks Program) as (M&Prefix&Scan&Saved&Entry).
  pose proof (V293_tick_raw_lossless_return WhileBindings WhileIdle Vnull WhileReady ChainEvents (Int.repr 37)
    RCentries sd P ks LRglobal LRcaller M (fun _ => false) false [3%nat] [false] ChainOld (spec_done None)
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
Definition LRprogram : progunit := fun f => if Z.eq_dec f 1100%Z then Some LRfunction else None.
Theorem LRnonvacuous : forall (sd : ossched),
  LRcaller<>LRlocal /\ LRprogram 1100%Z=Some LRfunction /\
  exists M Mf, LRprefix LRprogram kstop M /\ LRexecution LRprogram kstop M Mf /\ LRresult Mf.
Proof.
  intro sd. split.
  - intro Same. assert (Read := f_equal (fun e => get e 9999%Z) Same). vm_compute in Read. discriminate.
  - split;[reflexivity| ]. destruct (LRliteral sd LRprogram kstop eq_refl)
      as (M&Ms&Mf&Prefix&Scan&Saved&Abstract&Slots&Exec&Time&Pointer&Records&Group&Rel&Loads&Result&Frame&Gone).
    exists M. exists Mf. split;[exact Prefix| ]. split;assumption.
Qed.

Theorem LRobservations : forall (sd : ossched) P ks, P 1100%Z=Some LRfunction -> exists M Mf,
  LRprefix P ks M /\ LRexecution P ks M Mf /\ LRresult Mf /\
  load Tint32 Mf (101%positive,0%Z)=Some (Vint32 (Int.repr 38)) /\
  V293_task_record Mf WhileHead (Int.repr 10) rdy Vnull /\
  V293_task_record Mf WhileSecond (Int.repr 2) (wait os_stat_time (Int.repr 2)) Vnull /\
  V293_task_record Mf WhileIdle (Int.repr 12) rdy Vnull /\
  V293_table_loads V293_tcb_type Mf 94%positive RCentries /\
  load Tint32 Mf (90%positive,0%Z)=Some (Vint32 (Int.repr 99)) /\
  get PHnew curtid=Some (oscurt WhileReady) /\ get PHnew absecblsid=Some (absecblist ChainEvents) /\
  (forall k, k<4 -> get Mf (70%positive,Z.of_nat k)=None /\ get Mf (71%positive,Z.of_nat k)=None).
Proof.
  intros sd P ks Program. destruct (LRliteral sd P ks Program)
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
              ** assert (Canary : LRstate LRcaller Mf PHnew |= V293_owned_record_cells WhileFrameCells ** Atrue).
                 { unfold LRresult,V293_tick_lossless_return_payload in Result.
                   cbn [app V293_owned_record_cells] in Result. clear -Result. sep auto. }
                 change (load Tint32 (getmem (LRstate LRcaller Mf PHnew)) (90%positive,0%Z)=Some (Vint32 (Int.repr 99))).
                 eapply V293_record_star_load_l;[ |exact Canary].
                 apply V293_owned_record_cells_load. left;reflexivity.
              ** split;[rewrite Slots by discriminate;exact Current| ].
                 split;[rewrite Slots by discriminate;exact Events|exact Gone].
Qed.


Definition LRresidual := V293_tick_chain_residual WhileBindings WhileIdle.
Theorem LRresidual_layout : LRresidual =
  [((81%positive,28%Z),Tcom_ptr 410%Z,Vptr WhileSecond);
   ((81%positive,52%Z),Tint32,Vint32 Int.zero);
   ((81%positive,57%Z),Tint8,V293_byteval 1);
   ((81%positive,36%Z),Tcom_ptr 411%Z,Vptr (84%positive,Int.repr 4));
   ((81%positive,148%Z),Tcom_ptr 410%Z,Vptr WhileReady);
   ((81%positive,177%Z),Tint8,V293_byteval 7);
   ((81%positive,268%Z),Tcom_ptr 410%Z,Vptr WhileIdle);
   ((81%positive,292%Z),Tint32,Vint32 Int.zero);
   ((81%positive,297%Z),Tint8,V293_byteval 7)] /\
  length (V293_tick_chain_layouts WhileBindings)=22 /\
  length (V293_tick_chain_cells (map V293_tick_task_after (map fst WhileBindings)) WhileIdle ++
    concat (map V293_tick_binding_extra WhileBindings))=31.
Proof. repeat split;reflexivity. Qed.

(* All represented waiting reasons, including zero delay, expiry, and countdown.
   Counts do not replace the general exact permutation proof. *)
Definition LRwaitbinding reason d :=
  (V293_tick_wait_node 81%positive 8%Z d reason 7 10,(wait reason (Int.repr d),Vnull)).
Theorem LRall_reason_counts : forall reason,
  Forall (fun d =>
    let binding := LRwaitbinding reason d in
    length (V293_tick_task_cells (V293_tick_task_after (fst binding)) WhileSecond ++
      V293_tick_binding_extra binding) =
      length (V293_tick_after_layout binding) + length (V293_tick_residual_cells binding WhileSecond) /\
    hd_error (V293_tick_residual_cells binding WhileSecond) =
      Some ((81%positive,28%Z),Tcom_ptr 410%Z,Vptr WhileSecond) /\
    V293_tick_delay_value (V293_tick_task_after (fst binding)) = Z.max 0 (d-1) /\
    V293_tick_pend_value (V293_tick_task_after (fst binding)) =
      (if Z.eqb d 1 then match reason with os_stat_time => 0 | _ => 1 end else 7)) [0%Z;1%Z;3%Z].
Proof.
  intro reason. destruct reason;
    repeat (apply Forall_cons; [vm_compute;repeat split;reflexivity | ]);apply Forall_nil.
Qed.

Theorem LRreturned_core : forall (sd : ossched) P ks,
  P 1100%Z=Some LRfunction -> exists M Mf,
  LRexecution P ks M Mf /\ LRresult Mf /\
  LRstate LRcaller Mf PHnew |= V293_ready_core 93%positive 92%positive 94%positive **
    (V293_owned_record_cells
      ([((101%positive,0%Z),Tint32,Vint32 (Int.repr 38));
        ((102%positive,0%Z),Tint8,V293_byteval 1);
        ((103%positive,0%Z),Tptr V293_tcb_type,Vptr WhileHead)] ++ WhileFrameCells) **
      V293_owned_record_cells LRresidual).
Proof.
  intros sd P ks Program. destruct (LRliteral sd P ks Program)
    as (M&Ms&Mf&Prefix&Scan&Saved&Abstract&Slots&Exec&Time&Pointer&Records&Group&Rel&Loads&Result&Frame&Gone).
  exists M. exists Mf. split;[exact Exec| ]. split;[exact Result| ].
  exact (V293_tick_lossless_return_ready_core 93%positive 92%positive 94%positive WhileNewTasks
    101%positive (Int.repr 38) 102%positive 103%positive WhileHead WhileReady ChainEvents WhileFrameCells
    LRresidual (LRstate LRcaller Mf PHnew) Result).
Qed.

Theorem LRreturned_residual_loads : forall (sd : ossched) P ks,
  P 1100%Z=Some LRfunction -> exists M Mf,
  LRexecution P ks M Mf /\ LRresult Mf /\
  (forall a tp v, In (a,tp,v) LRresidual -> load tp Mf a=Some v).
Proof.
  intros sd P ks Program. destruct (LRliteral sd P ks Program)
    as (M&Ms&Mf&Prefix&Scan&Saved&Abstract&Slots&Exec&Time&Pointer&Records&Group&Rel&Loads&Result&Frame&Gone).
  exists M. exists Mf. split;[exact Exec| ]. split;[exact Result| ].
  assert (Residual : LRstate LRcaller Mf PHnew |= V293_owned_record_cells LRresidual ** Atrue).
  { unfold LRresult,V293_tick_lossless_return_payload in Result. clear -Result. sep auto. }
  intros a tp v Member. change (load tp (getmem (LRstate LRcaller Mf PHnew)) a=Some v).
  eapply V293_record_star_load_l;[ |exact Residual].
  apply V293_owned_record_cells_load. exact Member.
Qed.

Definition LRrest Mf O := LRstate LRcaller Mf O |=
  V293_tick_lossless_return_payload 93%positive 92%positive 94%positive WhileNewTasks
    101%positive (Int.repr 38) 102%positive 103%positive WhileHead WhileReady ChainEvents WhileFrameCells
    (tl LRresidual).

(* Permission ablation: split only the first next-link ownership out of the
   SAME correct returned heap. No byte of that heap, code or execution changes.
   Its complementary fragment keeps every other resource but cannot own next. *)
Theorem LRnext_ownership_control : forall (sd : ossched) P ks,
  P 1100%Z=Some LRfunction -> exists M Mf mn mr onext orest,
  LRexecution P ks M Mf /\ LRresult Mf /\
  join mn mr Mf /\ join onext orest PHnew /\
  onext=emp /\ orest=PHnew /\
  LRstate LRcaller mn onext |=
    V293_owned_record_cell ((81%positive,28%Z),Tcom_ptr 410%Z,Vptr WhileSecond) /\
  LRrest mr orest /\
  get mr ((81%positive,28%Z):addr)=None /\
  ~ (LRstate LRcaller mr orest |= V293_owned_record_cells LRresidual ** Atrue).
Proof.
  intros sd P ks Program. destruct (LRliteral sd P ks Program)
    as (M&Ms&Mf&Prefix&Scan&Saved&Abstract&Slots&Exec&Time&Pointer&Records&Group&Rel&Loads&Result&Frame&Gone).
  assert (Focus : LRstate LRcaller Mf PHnew |=
    V293_owned_record_cell ((81%positive,28%Z),Tcom_ptr 410%Z,Vptr WhileSecond) **
    V293_tick_lossless_return_payload 93%positive 92%positive 94%positive WhileNewTasks
      101%positive (Int.repr 38) 102%positive 103%positive WhileHead WhileReady ChainEvents WhileFrameCells
      (tl LRresidual)).
  { unfold LRresult,V293_tick_lossless_return_payload in Result |- *.
    change (V293_tick_chain_residual WhileBindings WhileIdle) with LRresidual in Result.
    rewrite (proj1 LRresidual_layout) in Result |- *.
    cbn [tl V293_owned_record_cells]. clear -Result. sep auto. }
  apply sat_split in Focus.
  destruct Focus as (mn&mr&onext&orest&JM&JO&Next&Rest).
  assert (EmptyNext : onext=emp).
  { pose proof Next as N. unfold V293_owned_record_cell in N.
    apply astar_l_apure_elim in N. destruct N as [_ [_ Empty]]. exact Empty. }
  assert (SameAbstract : orest=PHnew).
  { rewrite EmptyNext in JO. eapply map_join_emp''. exact JO. }
  assert (Missing : get mr ((81%positive,28%Z):addr)=None).
  { unfold V293_owned_record_cell in Next. apply astar_l_apure_elim in Next.
    destruct Next as [_ [Points Empty]]. destruct Points as (bytes&Encoding&Cells).
    rewrite <-Encoding in Cells. cbn [encode_val ptomvallist] in Cells.
    destruct Cells as (m0&mt&J0&Byte0&Tail).
    unfold ptomval in Byte0. subst m0.
    assert (D : disjoint (sig ((81%positive,28%Z):addr)
      (true,memory.Pointer 81%positive (Int.repr 128) 3)) mr).
    { eapply mem_join_join_disjoint;[exact J0|exact JM]. }
    destruct D as (combined&DisjointJoin).
    eapply mem_join_get_none'. exact DisjointJoin. }
  exists M. exists Mf. exists mn. exists mr. exists onext. exists orest.
  split;[exact Exec| ]. split;[exact Result| ]. split;[exact JM| ]. split;[exact JO| ].
  split;[exact EmptyNext| ]. split;[exact SameAbstract| ].
  split;[exact Next| ]. split;[exact Rest| ]. split;[exact Missing| ].
  intro Bad.
  assert (Wrong : load (Tcom_ptr 410%Z) mr (81%positive,28%Z)=Some (Vptr WhileSecond)).
  { change (load (Tcom_ptr 410%Z) (getmem (LRstate LRcaller mr orest)) (81%positive,28%Z)=Some (Vptr WhileSecond)).
    eapply V293_record_star_load_l;[ |exact Bad].
    apply V293_owned_record_cells_load. rewrite (proj1 LRresidual_layout). left;reflexivity. }
  unfold load,loadm in Wrong. cbn [typelen loadbytes] in Wrong.
  rewrite Missing in Wrong. discriminate.
Qed.
