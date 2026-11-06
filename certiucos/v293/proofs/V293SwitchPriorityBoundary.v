(* A source-level switch-boundary obstruction, not a CPU-port model.
   The framework's GoodI requires preservation after updating only OSTCBCur.
   Its update does not synchronize a distinct OSPrioCur byte. No statement
   here asserts initialization reachability or adopts an additional C repair. *)
Require Import CertiOS.certiucos.v293.proofs.V293SharedStateWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCurrentWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCurrent.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTargetWitness.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

(* The actual abstract table, abstract current task and physical byte must
   agree. The byte is not a task-private frame or a stale pure snapshot. *)
Definition V293_current_priority_coherent (b : block) (o : taskst) (O : osabst) : Prop :=
  exists tasks current nc,
    get O abstcblsid = Some (abstcblist tasks) /\
    get O curtid = Some (oscurt current) /\
    load Tint8 (get_mem (get_smem o)) (b, 0%Z) = Some (V293_byteval nc) /\
    V293_current_task tasks current nc.

Definition V293_priority_boundary_ge : env :=
  set V293_shared_fixture_ge 108%Z (2%positive, Tint8).
Definition V293_priority_boundary_memory : mem :=
  merge (V293_shared_fixture_mem V293_idle_tid)
    (V293_encoded_memory 2%positive 0 true (encode_val Tint8 (V293_byteval 4))).
Definition V293_priority_boundary_abs : osabst :=
  V293_shared_fixture_abs V293_idle_tid V293_current_tasks (emp : EcbMod.map) Int.zero.
Definition V293_priority_boundary_task (M : mem) : taskst :=
  (V293_priority_boundary_ge, emp, M, (fun _ => false), (false, nil, nil)).
(* Concrete byte updates, with successful framework store equations below. *)
Definition V293_priority_boundary_pointer_memory : mem :=
  set (set (set (set V293_priority_boundary_memory
    (1%positive, 3%Z) (true, Pointer 15%positive Int.zero 0))
    (1%positive, 2%Z) (true, Pointer 15%positive Int.zero 1))
    (1%positive, 1%Z) (true, Pointer 15%positive Int.zero 2))
    (1%positive, 0%Z) (true, Pointer 15%positive Int.zero 3).
Definition V293_priority_boundary_next_abs : osabst :=
  set V293_priority_boundary_abs curtid (oscurt V293_current_next).
Definition V293_priority_boundary_synchronized_memory : mem :=
  set V293_priority_boundary_pointer_memory (2%positive, 0%Z) (true, Byte (Byte.repr 12)).

Local Ltac boundary_compute :=
  cbv beta iota zeta delta [V293_priority_boundary_task get_smem get_mem load loadm typelen loadbytes
    V293_priority_boundary_pointer_memory V293_priority_boundary_synchronized_memory
    V293_priority_boundary_memory V293_shared_fixture_mem V293_encoded_memory store storebytes
    encode_val inj_pointer inj_bytes List.map encode_int V293_idle_tid V293_current_next V293_byteval];
  repeat first [rewrite map_merge_semp by reflexivity | rewrite map_get_sig |
    rewrite map_get_sig' by (intro E; inversion E; lia) | rewrite map_emp_get |
    rewrite map_get_set | rewrite map_get_set' by (intro E; inversion E; lia)];
  reflexivity.

Lemma V293_priority_boundary_next_priority : forall nc,
  V293_current_task V293_current_tasks V293_current_next nc -> nc = 12.
Proof.
  intros nc [Hnc [st [m Hget]]].
  assert (Hnext : get V293_current_tasks V293_current_next = Some (Int.repr 12, rdy, Vnull))
    by (reflexivity).
  unfold get, TcbMap in Hget, Hnext.
  rewrite Hnext in Hget.
  pose proof (f_equal (fun x : option (priority * taskstatus * msg) =>
    match x with Some (p, _, _) => p | None => Int.zero end) Hget) as E.
  change (Int.repr 12 = Int.repr (Z.of_nat nc)) in E.
  apply V293_priority_repr_injective; [exact Hnc | lia | symmetry; exact E].
Qed.

Theorem V293_priority_boundary_before :
  V293_current_priority_coherent 2%positive
    (V293_priority_boundary_task V293_priority_boundary_memory) V293_priority_boundary_abs.
Proof.
  exists V293_current_tasks. exists V293_idle_tid. exists 4.
  split; [reflexivity | ]. split; [reflexivity | ].
  split; [boundary_compute | ]. exact (proj2 (proj2 V293_current_relations)).
Qed.

(* These are exactly the physical and abstract updates appearing in GoodI's
   third conjunct. Target12 is highest ready; old current4 is a live member. *)
Theorem V293_priority_boundary_pointer_store :
  get V293_priority_boundary_ge OSTCBCur = Some (1%positive, Tptr Tvoid) /\
  load (Tptr Tvoid) V293_priority_boundary_memory (1%positive, 0%Z) = Some (Vptr V293_idle_tid) /\
  store (Tptr Tvoid) V293_priority_boundary_memory (1%positive, 0%Z) (Vptr V293_current_next) =
    Some V293_priority_boundary_pointer_memory /\
  load (Tptr Tvoid) V293_priority_boundary_pointer_memory (1%positive, 0%Z) = Some (Vptr V293_current_next) /\
  load Tint8 V293_priority_boundary_pointer_memory (2%positive, 0%Z) = Some (V293_byteval 4) /\
  get V293_priority_boundary_next_abs curtid = Some (oscurt V293_current_next) /\
  get V293_priority_boundary_next_abs abstcblsid = Some (abstcblist V293_current_tasks) /\
  indom V293_current_tasks V293_idle_tid /\
  V293_highest_ready V293_current_tasks V293_current_next.
Proof.
  split; [reflexivity | ]. split; [boundary_compute | ].
  split; [boundary_compute | ]. split; [boundary_compute | ].
  split; [boundary_compute | ]. split; [reflexivity | ]. split; [reflexivity | ].
  split.
  - exists (Int.repr 4, wait os_stat_time Int.one, Vnull). reflexivity.
  - exact (V293_shared_case_highest true).
Qed.

Theorem V293_priority_boundary_pointer_only_breaks :
  ~ V293_current_priority_coherent 2%positive
    (V293_priority_boundary_task V293_priority_boundary_pointer_memory) V293_priority_boundary_next_abs.
Proof.
  intros (tasks & current & nc & Htasks & Hcurrent & Hload & Htask).
  assert (HT : get V293_priority_boundary_next_abs abstcblsid = Some (abstcblist V293_current_tasks))
    by (reflexivity).
  assert (HC : get V293_priority_boundary_next_abs curtid = Some (oscurt V293_current_next))
    by (reflexivity).
  rewrite HT in Htasks. inversion Htasks; subst tasks.
  rewrite HC in Hcurrent. inversion Hcurrent; subst current.
  apply V293_priority_boundary_next_priority in Htask. subst nc.
  change (load Tint8 V293_priority_boundary_pointer_memory (2%positive, 0%Z) = Some (V293_byteval 12)) in Hload.
  destruct V293_priority_boundary_pointer_store as [_ [_ [_ [_ [HL _]]]]].
  rewrite HL in Hload. vm_compute in Hload. discriminate.
Qed.

(* Single-factor positive control: keep everything above unchanged, then
   perform one explicit byte store. This is NOT equated with bare switch. *)
Theorem V293_priority_boundary_explicit_sync :
  store Tint8 V293_priority_boundary_pointer_memory (2%positive, 0%Z) (V293_byteval 12) =
    Some V293_priority_boundary_synchronized_memory /\
  V293_current_priority_coherent 2%positive
    (V293_priority_boundary_task V293_priority_boundary_synchronized_memory) V293_priority_boundary_next_abs.
Proof.
  split; [boundary_compute | ].
  exists V293_current_tasks. exists V293_current_next. exists 12.
  split; [reflexivity | ]. split; [reflexivity | ].
  split; [boundary_compute | ].
  split; [lia | ]. exists rdy. exists Vnull. reflexivity.
Qed.

(* Bounded impossibility: ANY GoodI candidate accepting this precise entry and
   implying the exact current-byte relation contradicts its live-switch case.
   The acceptance and implication are explicit premises, not hidden axioms.
   No claim is made about invariants excluding this entry, or synchronized
   port transitions different from the framework's pointer-only primitive. *)
Theorem V293_priority_boundary_GoodI_obstruction : forall (I : Inv) (li : LocalInv),
  (V293_priority_boundary_task V293_priority_boundary_memory,
    V293_priority_boundary_abs, spec_done None) |= SWINVt I V293_idle_tid ->
  (forall o O op t, (o, O, op) |= SWINVt I t ->
    V293_current_priority_coherent 2%positive o O) ->
  ~ GoodI I V293_scheduler li.
Proof.
  intros I li Hentry Hcoherent [_ [_ [Hswitch _]]].
  assert (Hhighest : (V293_priority_boundary_task V293_priority_boundary_memory,
      V293_priority_boundary_abs, spec_done None) |= AHprio V293_scheduler V293_current_next ** Atrue).
  { change (V293_target_wstate V293_priority_boundary_ge emp V293_priority_boundary_memory
      V293_priority_boundary_abs |= AHprio V293_scheduler V293_current_next ** Atrue).
    eapply V293_target_wstate_star with (m1 := emp) (m2 := V293_priority_boundary_memory)
      (o1 := V293_priority_boundary_abs) (o2 := emp).
    - apply map_join_comm. apply map_join_emp.
    - apply map_join_emp.
    - split; [ | reflexivity]. exists V293_current_tasks.
      split; [reflexivity | exact (V293_shared_case_highest true)].
    - exact Logic.I. }
  destruct V293_priority_boundary_pointer_store as [Hge [_ [Hstore [_ [_ [_ [_ [Hmember _]]]]]]]].
  specialize (Hswitch (V293_priority_boundary_task V293_priority_boundary_memory)
    V293_priority_boundary_abs (spec_done None) V293_current_next 1%positive Tvoid
    V293_priority_boundary_pointer_memory V293_idle_tid Hentry Hhighest Hge Hstore).
  destruct Hswitch as (tasks & Htasks & [[_ Hpost] | [Hdead _]]).
  - apply V293_priority_boundary_pointer_only_breaks.
    exact (Hcoherent _ _ _ _ Hpost).
  - assert (HT : get V293_priority_boundary_abs abstcblsid = Some (abstcblist V293_current_tasks))
      by (reflexivity).
    rewrite HT in Htasks. inversion Htasks; subst tasks. contradiction.
Qed.

(* The actual ready invariant accepts this full-storage fixture. Unlike the
   earlier generic obstruction, no acceptance premise is left to a caller. *)
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedStorageConnectWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedStoragePrefix.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedStoragePrefixWitness.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchStorage.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchState.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.sep_combine_lemmas.
Require Import CertiOS.framework.proof.rulesoundlib.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Import ListNotations.
Local Open Scope nat_scope.

Definition V293_ready_boundary_inv :=
  V293_ready_inv 1%positive 2%positive 3%positive 4%positive 8%positive Tvoid
    [((13%positive, 0%Z), Tint32); ((12%positive, 0%Z), Tint8)] 107%Z.
Definition V293_ready_boundary_memory : mem :=
  merge (merge (V293_storage_prefix_memory true)
    (V293_conditional_priority_memory true)) (V293_conditional_counter_memory Int.zero).
Definition V293_ready_boundary_abs :=
  V293_shared_fixture_abs V293_idle_tid V293_current_tasks (emp : EcbMod.map) Int.zero.
Definition V293_ready_boundary_task (M : mem) : taskst :=
  (V293_conditional_fixture_ge, emp, M, (fun _ => false), (false, nil, nil)).
Definition V293_ready_boundary_frame :=
  V293_shared_flags **
    (V293_shared_fields V293_idle_tid V293_current_tasks (emp : EcbMod.map) Int.zero **
      ((GV 107%Z @ (Tptr Tvoid) |-> (Vptr V293_idle_tid)) **
        V293_retained_prefix_entry_heap 1%positive 2%positive 3%positive 4%positive 8%positive
          Tvoid 0 16 V293_current_entries
          ((PV (13%positive, Int.zero) @ Tint32 |-> (Vint32 Int.zero)) **
            (PV (12%positive, Int.zero) @ Tint8 |-> (V293_byteval 4))) (V293_byteval 0))).

Lemma V293_ready_boundary_physical :
  (V293_ready_boundary_task V293_ready_boundary_memory,
    V293_ready_boundary_abs, spec_done None) |=
      (GV OSTCBCur @ (Tptr Tvoid) |-> (Vptr V293_idle_tid)) ** V293_ready_boundary_frame.
Proof.
  pose proof (V293_conditional_fixture_physical V293_conditional_fixture_ge true 4 Int.zero
    eq_refl eq_refl) as HP.
  set (fields := V293_shared_fields V293_idle_tid V293_current_tasks (emp : EcbMod.map) Int.zero).
  assert (HA : V293_target_wstate V293_conditional_fixture_ge emp emp V293_ready_boundary_abs |= fields).
  { unfold fields, V293_ready_boundary_abs, V293_shared_fixture_abs, V293_shared_fields.
    repeat (eapply V293_target_wstate_star; [apply map_join_emp | apply map_join_merge;
      apply map_disjoint; intros key; destruct key; simpl; auto | split; reflexivity | ]).
    split; reflexivity. }
  assert (HF : V293_target_wstate V293_conditional_fixture_ge emp emp emp |= V293_shared_flags).
  { unfold V293_shared_flags.
    repeat (eapply V293_target_wstate_star with (m1 := emp) (m2 := emp) (o1 := emp) (o2 := emp);
      [apply map_join_emp | apply map_join_emp | | ]).
    - exists (fun _ : hid => false). split; repeat split; reflexivity.
    - repeat split; reflexivity.
    - exists INUM. repeat split; reflexivity. }
  assert (HS : V293_target_wstate V293_conditional_fixture_ge emp V293_ready_boundary_memory
    V293_ready_boundary_abs |= V293_shared_flags **
      (((V293_conditional_fixture_base true **
        (PV (12%positive, Int.zero) @ Tint8 |-> (V293_byteval 4))) **
        (PV (13%positive, Int.zero) @ Tint32 |-> (Vint32 Int.zero))) ** fields)).
  { eapply V293_target_wstate_star with (m1 := emp) (o1 := emp).
    - apply map_join_comm. apply map_join_emp.
    - apply map_join_comm. apply map_join_emp.
    - exact HF.
    - eapply V293_target_wstate_star with (m2 := emp) (o1 := emp).
      + apply map_join_emp.
      + apply map_join_comm. apply map_join_emp.
      + exact HP.
      + exact HA. }
  assert (HC : can_change_aop
    ((GV OSTCBCur @ (Tptr Tvoid) |-> (Vptr V293_idle_tid)) ** V293_ready_boundary_frame)).
  { unfold V293_ready_boundary_frame, V293_shared_flags, V293_shared_fields,
      V293_retained_prefix_entry_heap, V293_inputs_full, Agvarmapsto, Aptrmapsto.
    cbn [can_change_aop]. repeat split; try exact I; intros; repeat split; try exact I;
      apply V293_array_aop_independent. }
  assert (HK : V293_target_wstate V293_conditional_fixture_ge emp V293_ready_boundary_memory
    V293_ready_boundary_abs |=
      (GV OSTCBCur @ (Tptr Tvoid) |-> (Vptr V293_idle_tid)) ** V293_ready_boundary_frame).
  { unfold V293_ready_boundary_frame, V293_retained_prefix_entry_heap,
      V293_conditional_fixture_base, fields in *. clear HP HA HF. sep auto. }
  exact (@change_aop_rule _ _ _ (spec_done None) _ HK HC).
Qed.

Lemma V293_ready_boundary_close :
  (GV OSTCBCur @ (Tptr Tvoid) |-> (Vptr V293_idle_tid)) ** V293_ready_boundary_frame ==>
    SWINVt V293_ready_boundary_inv V293_idle_tid.
Proof.
  intros s Hs. unfold V293_ready_boundary_inv. apply V293_ready_switch_halves.
  assert (HK : ((PV (13%positive, Int.zero) @ Tint32 |-> (Vint32 Int.zero)) **
      (PV (12%positive, Int.zero) @ Tint8 |-> (V293_byteval 4))) ==>
    V293_storage (cons ((13%positive, 0%Z), Tint32) (cons ((12%positive, 0%Z), Tint8) nil))).
  { intros st H. cbn [V293_storage]. unfold V293_storage_cell. sep auto. }
  assert (HR : exists p, V293_bitmap_ready 0 16 p).
  { exists 12. right. split; [lia | ]. split; [lia | vm_compute; reflexivity]. }
  destruct V293_current_relations as [HB [HT HC]].
  assert (HTy : Forall (fun v => rule_type_val_match (Tptr Tvoid) v = true) V293_current_entries)
    by (vm_compute; repeat constructor).
  unfold V293_ready_full, V293_ready_resources.
  unfold V293_ready_boundary_frame, V293_retained_prefix_entry_heap in Hs.
  eapply astar_mono in Hs; [ | intros st H; exact H | apply astar_mono;
    [intros st H; exact H | apply astar_mono; [intros st H; exact H | apply astar_mono;
      [intros st H; exact H | apply astar_mono; [intros st H; exact H | apply astar_mono;
        [intros st H; exact H | apply astar_mono; [intros st H; exact H | exact HK]]]]]]].
  unfold V293_retained_prefix_entry_heap, V293_dispatch_cell. sep auto.
  repeat first [assumption | split | lia | reflexivity].
Qed.

Lemma V293_boundary_byte_read : forall b n s,
  n < 256 ->
  s |= (PV (b, Int.zero) @ Tint8 |-> (V293_byteval n)) ** Atrue ->
  load Tint8 (getmem s) (b, 0%Z) = Some (V293_byteval n).
Proof.
  intros b n [[[[[[ge le] M] ir] aux] O] op] Hn Hs.
  apply sat_split in Hs. destruct Hs as (m1 & m2 & o1 & o2 & JM & JO & [HM HO] & HF).
  eapply load_local; [exact JM | ]. eapply mapstoval_load; [apply V293_byte_type; exact Hn | exact HM].
Qed.

Theorem V293_ready_boundary_entry :
  (V293_ready_boundary_task V293_ready_boundary_memory,
    V293_ready_boundary_abs, spec_done None) |= SWINVt V293_ready_boundary_inv V293_idle_tid /\
  load Tint8 V293_ready_boundary_memory (12%positive, 0%Z) = Some (V293_byteval 4) /\
  V293_current_priority_coherent 12%positive
    (V293_ready_boundary_task V293_ready_boundary_memory) V293_ready_boundary_abs.
Proof.
  pose proof V293_ready_boundary_physical as HP.
  assert (HL : load Tint8 V293_ready_boundary_memory (12%positive, 0%Z) = Some (V293_byteval 4)).
  { eapply (V293_boundary_byte_read 12%positive 4
      (V293_ready_boundary_task V293_ready_boundary_memory, V293_ready_boundary_abs, spec_done None)); [lia | ]. unfold V293_ready_boundary_frame,
      V293_retained_prefix_entry_heap in HP. sep auto. }
  split; [apply V293_ready_boundary_close; exact HP | ]. split; [exact HL | ].
  exists V293_current_tasks. exists V293_idle_tid. exists 4.
  split; [reflexivity | ]. split; [reflexivity | ]. split; [exact HL | ].
  exact (proj2 (proj2 V293_current_relations)).
Qed.

(* A successful real pointer store and curtid update, not an assumed entry.
   The target is highest ready and the old current is still a live member.
   The full SAME ready invariant holds afterwards, but cache coherence fails. *)
Theorem V293_ready_boundary_pointer_only : exists M',
  store (Tptr Tvoid) V293_ready_boundary_memory (6%positive, 0%Z) (Vptr V293_current_next) = Some M' /\
  (V293_ready_boundary_task M', set V293_ready_boundary_abs curtid (oscurt V293_current_next),
    spec_done None) |= SWINVt V293_ready_boundary_inv V293_current_next /\
  load Tint8 M' (12%positive, 0%Z) = Some (V293_byteval 4) /\
  V293_highest_ready V293_current_tasks V293_current_next /\
  indom V293_current_tasks V293_idle_tid /\
  ~ V293_current_priority_coherent 12%positive
    (V293_ready_boundary_task M') (set V293_ready_boundary_abs curtid (oscurt V293_current_next)).
Proof.
  pose proof V293_ready_boundary_physical as HP.
  assert (HE : get V293_conditional_fixture_ge OSTCBCur = Some (6%positive, Tptr Tvoid)) by reflexivity.
  assert (HS : exists M', store (Tptr Tvoid) V293_ready_boundary_memory (6%positive, 0%Z)
    (Vptr V293_current_next) = Some M').
  { apply sat_split in HP. destruct HP as (m1 & m2 & o1 & o2 & JM & JO & HC & HF).
    destruct (V293_dispatch_named_cell_parts _ _ _ _ _ _ _ _ _ _ HC) as (b & GE & HM & HO).
    change (get V293_conditional_fixture_ge OSTCBCur = Some (b, Tptr Tvoid)) in GE.
    assert (E : b = 6%positive).
    { unfold get, EnvMap in HE, GE. rewrite HE in GE. inversion GE. reflexivity. } subst b.
    eapply store_exist_join'; eauto. }
  destruct HS as [M' HS]. exists M'. split; [exact HS | ].
  pose proof (@V293_shared_store_global OSTCBCur Tvoid (Vptr V293_idle_tid)
    (Vptr V293_current_next) V293_ready_boundary_frame _ _ _ _ _ _ _ _ _ HP HE HS) as Hstored.
  assert (HL : load Tint8 M' (12%positive, 0%Z) = Some (V293_byteval 4)).
  { eapply (V293_boundary_byte_read 12%positive 4
      (V293_ready_boundary_task M', V293_ready_boundary_abs, spec_done None)); [lia | ]. unfold V293_ready_boundary_frame,
      V293_retained_prefix_entry_heap in Hstored. sep auto. }
  split.
  - eapply V293_ready_store; [exact (proj1 V293_ready_boundary_entry) | exact HE | exact HS].
  - split; [exact HL | ]. split; [exact (V293_shared_case_highest true) | ].
    split; [exists (Int.repr 4, wait os_stat_time Int.one, Vnull); reflexivity | ].
    intros (tasks & current & nc & HT & HC & Hload & Htask).
    assert (ET : tasks = V293_current_tasks) by (vm_compute in HT; inversion HT; reflexivity).
    assert (EC : current = V293_current_next) by (vm_compute in HC; inversion HC; reflexivity).
    subst tasks current. apply V293_priority_boundary_next_priority in Htask. subst nc.
    change (load Tint8 M' (12%positive, 0%Z) = Some (V293_byteval 12)) in Hload.
    rewrite HL in Hload. vm_compute in Hload. discriminate.
Qed.

Corollary V293_ready_boundary_no_cache_entailment :
  ~ (forall o O op t, (o, O, op) |= SWINVt V293_ready_boundary_inv t ->
    V293_current_priority_coherent 12%positive o O).
Proof.
  intros H. destruct V293_ready_boundary_pointer_only as
    (M' & HS & HI & HL & Hhighest & Hmember & Hbad).
  apply Hbad. exact (H _ _ _ _ HI).
Qed.

(* A small, independently observable instance of the two-memory relation.
   It extends the previous raw boundary fixture with distinct high/target
   cells. It is not an OS_SchedNew execution or initialization witness. *)
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedPointerCompare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewExec.
Require Import CertiOS.certiucos.v293.code.V293OSSchedChange.
Require Import CertiOS.framework.proof.auxdef.
Local Open Scope nat_scope.

Definition V293_cache_observation_ge : env :=
  set (set V293_priority_boundary_ge 109%Z (3%positive, Tint8))
    110%Z (4%positive, Tptr Tvoid).
Definition V293_cache_observation_before : mem :=
  merge V293_priority_boundary_memory
    (merge (V293_encoded_memory 3%positive 0 true (encode_val Tint8 (V293_byteval 12)))
      (V293_encoded_memory 4%positive 0 true (encode_val (Tptr Tvoid) (Vptr V293_current_next)))).
Definition V293_cache_observation_normalized : mem :=
  set (set (set (set V293_cache_observation_before
    (1%positive, 3%Z) (true, Pointer 15%positive Int.zero 0))
    (1%positive, 2%Z) (true, Pointer 15%positive Int.zero 1))
    (1%positive, 1%Z) (true, Pointer 15%positive Int.zero 2))
    (1%positive, 0%Z) (true, Pointer 15%positive Int.zero 3).
Definition V293_cache_observation_source : mem :=
  V293_write_byte V293_cache_observation_normalized 2%positive 12.

Local Ltac cache_observation_compute :=
  cbv beta iota zeta delta [V293_cache_observation_source V293_write_byte
    V293_cache_observation_normalized V293_cache_observation_before
    V293_priority_boundary_memory V293_shared_fixture_mem V293_encoded_memory
    load loadm typelen loadbytes store storebytes encode_val inj_pointer inj_bytes
    List.map encode_int V293_idle_tid V293_current_next V293_byteval];
  repeat first [rewrite map_merge_semp by reflexivity | rewrite map_get_sig |
    rewrite map_get_sig' by (intro E; inversion E; lia) | rewrite map_emp_get |
    rewrite map_get_set | rewrite map_get_set' by (intro E; inversion E; lia)];
  reflexivity.

Theorem V293_cache_observation_stores :
  store (Tptr Tvoid) V293_cache_observation_before (1%positive, 0%Z) (Vptr V293_current_next) =
    Some V293_cache_observation_normalized /\
  store Tint8 V293_cache_observation_normalized (2%positive, 0%Z) (V293_byteval 12) =
    Some V293_cache_observation_source /\
  V293_cache_correspondence 2%positive 12
    V293_cache_observation_source V293_cache_observation_normalized /\
  load Tint8 V293_cache_observation_normalized (2%positive, 0%Z) = Some (V293_byteval 4).
Proof.
  split; [cache_observation_compute | ]. split; [cache_observation_compute | ].
  split.
  - split; [apply V293_write_byte_load; lia | ].
    intros a Ha. unfold V293_cache_observation_source, V293_write_byte.
    apply map_get_set'. congruence.
  - cache_observation_compute.
Qed.

(* Same real high/current/target observations in both memories. The raw
   normalized cache read disagrees with the source: erasure alone is NOT
   an observational simulation of the unchanged priority expression. *)
Theorem V293_cache_observation_decisions :
  evalval (V293_OSSched_different 109%Z 108%Z)
    (V293_cache_observation_ge, emp, V293_cache_observation_source) = Some (Vint32 Int.zero) /\
  evalval (V293_OSSched_pointer_different 110%Z OSTCBCur)
    (V293_cache_observation_ge, emp, V293_cache_observation_normalized) = Some (Vint32 Int.zero) /\
  evalval (V293_OSSched_different 109%Z 108%Z)
    (V293_cache_observation_ge, emp, V293_cache_observation_normalized) = Some (Vint32 Int.one) /\
  evalval (evar 108%Z) (V293_cache_observation_ge, emp, V293_cache_observation_source) =
    Some (V293_byteval 12) /\
  evalval (evar 108%Z) (V293_cache_observation_ge, emp, V293_cache_observation_normalized) =
    Some (V293_byteval 4).
Proof.
  assert (GS : get V293_cache_observation_ge 109%Z = Some (3%positive, Tint8)) by reflexivity.
  assert (GC : get V293_cache_observation_ge 108%Z = Some (2%positive, Tint8)) by reflexivity.
  assert (GT : get V293_cache_observation_ge 110%Z = Some (4%positive, Tptr Tvoid)) by reflexivity.
  assert (GCur : get V293_cache_observation_ge OSTCBCur = Some (1%positive, Tptr Tvoid)) by reflexivity.
  assert (HS : load Tint8 V293_cache_observation_source (3%positive, 0%Z) = Some (V293_byteval 12))
    by cache_observation_compute.
  assert (CS : load Tint8 V293_cache_observation_source (2%positive, 0%Z) = Some (V293_byteval 12))
    by (apply V293_write_byte_load; lia).
  assert (HN : load Tint8 V293_cache_observation_normalized (3%positive, 0%Z) = Some (V293_byteval 12))
    by cache_observation_compute.
  assert (CN : load Tint8 V293_cache_observation_normalized (2%positive, 0%Z) = Some (V293_byteval 4))
    by cache_observation_compute.
  assert (TN : load (Tptr Tvoid) V293_cache_observation_normalized (4%positive, 0%Z) = Some (Vptr V293_current_next))
    by cache_observation_compute.
  assert (CurN : load (Tptr Tvoid) V293_cache_observation_normalized (1%positive, 0%Z) = Some (Vptr V293_current_next))
    by cache_observation_compute.
  destruct (V293_OSSched_byte_comparison_eval V293_cache_observation_ge emp V293_cache_observation_source
    109%Z 108%Z 3%positive 2%positive 12 12 ltac:(lia) ltac:(lia)
    ltac:(apply map_emp_get) ltac:(apply map_emp_get) GS GC HS CS) as [ES _].
  destruct (V293_OSSched_pointer_comparison_eval V293_cache_observation_ge emp V293_cache_observation_normalized
    110%Z OSTCBCur 4%positive 1%positive Tvoid Tvoid V293_current_next V293_current_next
    ltac:(apply map_emp_get) ltac:(apply map_emp_get) GT GCur TN CurN) as [EP _].
  destruct (V293_OSSched_byte_comparison_eval V293_cache_observation_ge emp V293_cache_observation_normalized
    109%Z 108%Z 3%positive 2%positive 12 4 ltac:(lia) ltac:(lia)
    ltac:(apply map_emp_get) ltac:(apply map_emp_get) GS GC HN CN) as [EN _].
  split; [exact ES | ]. split.
  - destruct (tid_eq_dec V293_current_next V293_current_next) in EP; [exact EP | contradiction].
  - split; [exact EN | ]. split;
      cbn [evalval evaltype get_lenv get_genv get_mem]; assumption.
Qed.

(* The general source/pointer correspondence theorem is really instantiated
   on the fixture, including its shared task table and typed expressions. *)
Theorem V293_cache_observation_refinement :
  evalval (V293_OSSched_different 109%Z 108%Z)
    (V293_cache_observation_ge, emp, V293_cache_observation_source) =
  evalval (V293_OSSched_pointer_different 110%Z OSTCBCur)
    (V293_cache_observation_ge, emp, V293_cache_observation_normalized) /\
  evalval (evar 108%Z) (V293_cache_observation_ge, emp, V293_cache_observation_source) =
    Some (V293_byteval 12) /\
  evaltype (V293_OSSched_different 109%Z 108%Z)
    (V293_cache_observation_ge, emp, V293_cache_observation_source) = Some Tint32 /\
  evaltype (V293_OSSched_pointer_different 110%Z OSTCBCur)
    (V293_cache_observation_ge, emp, V293_cache_observation_normalized) = Some Tint32.
Proof.
  eapply (V293_OSSched_cross_memory_comparison V293_cache_observation_ge emp
    V293_cache_observation_source V293_cache_observation_normalized
    109%Z 108%Z 110%Z OSTCBCur 3%positive 2%positive 4%positive 1%positive Tvoid Tvoid
    0 16 V293_current_entries V293_current_tasks V293_current_next 12 V293_current_next).
  - lia.
  - lia.
  - exists 12. vm_compute; intuition lia.
  - exact (proj1 V293_current_relations).
  - exact (proj1 (proj2 V293_current_relations)).
  - split; [lia | ]. exists rdy. exists Vnull. reflexivity.
  - exact (V293_shared_case_highest true).
  - exact (proj1 (proj2 (proj2 V293_cache_observation_stores))).
  - discriminate.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - change (load Tint8 V293_cache_observation_normalized (3%positive, 0%Z) = Some (V293_byteval 12)).
    cache_observation_compute.
  - cache_observation_compute.
  - cache_observation_compute.
Qed.

(* Actual source guard/increment execution up to, NOT THROUGH, the chosen
   boundary suffix. This needs no current/target inequality or accurate cache.
   The store premise is a real UINT32 store; its existence is witnessed below. *)
Require Import CertiOS.framework.proof.cstepLib.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.

Lemma V293_assign_counter_execution : forall P ge le M M' counter b c ks,
  get le counter = None -> get ge counter = Some (b, Tint32) ->
  load Tint32 M (b, 0%Z) = Some (Vint32 c) ->
  store Tint32 M (b, 0%Z) (Vint32 (Int.add c Int.one)) = Some M' ->
  cstepstar P (curs (V293_OSSched_increment counter), (kenil, ks)) (ge, le, M)
    (curs (sskip None), (kenil, ks)) (ge, le, M').
Proof.
  intros P ge le M M' counter b c ks N G L S.
  assert (E : evalval (ebinop oplus (evar counter) (econst32 Int.one)) (ge, le, M) =
    Some (Vint32 (Int.add c Int.one))).
  { cbn [evalval evaltype get_lenv get_genv get_mem]. rewrite N, G.
    cbn -[load]. rewrite L. reflexivity. }
  assert (A : evaladdr (evar counter) (ge, le, M) = Some (Vptr (b, Int.zero))).
  { cbn [evaladdr get_lenv get_genv]. rewrite N, G. reflexivity. }
  assert (T : evaltype (evar counter) (ge, le, M) = Some Tint32).
  { cbn [evaltype]. rewrite N, G. reflexivity. }
  unfold V293_OSSched_increment.
  eapply c_stepstarn.
  { eapply stmt_step; [reflexivity | ]. eapply sassign_step with (t1 := Tint32) (t2 := Tint32).
    - exact T.
    - cbn [evaltype]. rewrite N, G. reflexivity.
    - apply eq_int. auto. }
  eapply V293_cstepstar_trans.
  { apply V293_expr_steps. apply evalval_imply_estepstar. exact E. }
  eapply c_stepstarn. { eapply stmt_step; [reflexivity | ]. constructor. }
  eapply V293_cstepstar_trans.
  { apply V293_expr_steps. apply evalval_imply_estepstar. eapply evaladdr_val_eq; eassumption. }
  eapply c_stepstarn.
  { eapply stmt_step; [reflexivity | ]. eapply sassignend_step; try reflexivity. exact S. }
  apply c_stepstar0.
Qed.

Theorem V293_OSSched_changed_execution : forall P ks ge le M M' high cached counter
    bh bc bcounter nh nc c suffix,
  nh < 256 -> nc < 256 -> nh <> nc ->
  get le high = None -> get le cached = None -> get le counter = None ->
  get ge high = Some (bh, Tint8) -> get ge cached = Some (bc, Tint8) ->
  get ge counter = Some (bcounter, Tint32) ->
  load Tint8 M (bh, 0%Z) = Some (V293_byteval nh) ->
  load Tint8 M (bc, 0%Z) = Some (V293_byteval nc) ->
  load Tint32 M (bcounter, 0%Z) = Some (Vint32 c) ->
  store Tint32 M (bcounter, 0%Z) (Vint32 (Int.add c Int.one)) = Some M' ->
  cstepstar P (curs (V293_OSSched_change high cached counter suffix), (kenil, ks)) (ge, le, M)
    (curs suffix, (kenil, ks)) (ge, le, M').
Proof.
  intros P ks ge le M M' high cached counter bh bc bcounter nh nc c suffix
    Hnh Hnc Hne Nh Nc Nctr Gh Gc Gctr Lh Lc Lctr Store.
  destruct (V293_OSSched_byte_comparison_eval ge le M high cached bh bc nh nc
    Hnh Hnc Nh Nc Gh Gc Lh Lc) as [E T].
  assert (D : Nat.eqb nh nc = false) by (apply Nat.eqb_neq; exact Hne).
  rewrite D in E. unfold V293_OSSched_change.
  eapply c_stepstarn. { eapply stmt_step; [reflexivity | ]. constructor. }
  eapply V293_cstepstar_trans.
  { apply V293_expr_steps. apply evalval_imply_estepstar. exact E. }
  eapply c_stepstarn. { eapply stmt_step; [reflexivity | ]. apply svift_step. reflexivity. }
  eapply c_stepstarn. { eapply stmt_step; [reflexivity | ]. constructor. }
  eapply V293_cstepstar_trans.
  { eapply V293_assign_counter_execution; eassumption. }
  eapply c_stepstarn. { eapply stmt_step; [reflexivity | ]. constructor. }
  apply c_stepstar0.
Qed.

(* Constant observation fixture matching the successful controlled C case:
   cached=8, high=6, same target/current pointer, UINT32 counter=17.
   No physical TCB, API prefix or OS_SchedNew reachability is claimed here. *)
Definition V293_cache_lag_ge : env :=
  set V293_cache_observation_ge 111%Z (5%positive, Tint32).
Definition V293_cache_lag_memory : mem :=
  merge (V293_shared_fixture_mem V293_current_next)
    (merge (V293_encoded_memory 2%positive 0 true (encode_val Tint8 (V293_byteval 8)))
      (merge (V293_encoded_memory 3%positive 0 true (encode_val Tint8 (V293_byteval 6)))
        (merge (V293_encoded_memory 4%positive 0 true (encode_val (Tptr Tvoid) (Vptr V293_current_next)))
          (V293_encoded_memory 5%positive 0 true
            [Byte (Byte.repr 17); Byte (Byte.repr 0); Byte (Byte.repr 0); Byte (Byte.repr 0)])))).
Definition V293_cache_lag_incremented : mem :=
  set (set (set (set V293_cache_lag_memory
    (5%positive, 3%Z) (true, Byte (Byte.repr 0)))
    (5%positive, 2%Z) (true, Byte (Byte.repr 0)))
    (5%positive, 1%Z) (true, Byte (Byte.repr 0)))
    (5%positive, 0%Z) (true, Byte (Byte.repr 18)).

Local Ltac cache_lag_compute :=
  unfold addr, offset, block in *;
  cbv beta iota zeta delta [V293_cache_lag_incremented V293_cache_lag_memory
    V293_shared_fixture_mem
    load loadm typelen loadbytes store storebytes encode_val inj_pointer inj_bytes
    List.map encode_int V293_current_next V293_byteval];
  repeat first [rewrite map_get_set | rewrite map_get_set' by (intro E; inversion E; lia) |
    rewrite map_merge_semp by reflexivity |
    rewrite V293_encoded_memory_outside by (left; discriminate) |
    rewrite map_get_sig | rewrite map_get_sig' by (intro E; inversion E; lia) |
    rewrite map_emp_get | progress cbn [V293_encoded_memory]];
  reflexivity.

(* The counter store changes only block 5, at four byte addresses. *)
Local Lemma V293_cache_lag_load_unchanged : forall tau b off,
  b <> 5%positive ->
  load tau V293_cache_lag_incremented (b, off) =
  load tau V293_cache_lag_memory (b, off).
Proof.
  intros tau b off Hb. unfold load, loadm.
  assert (E : forall n i,
    loadbytes V293_cache_lag_incremented (b, i) n =
    loadbytes V293_cache_lag_memory (b, i) n).
  { induction n as [ |n IH]; intro i; [reflexivity | ].
    cbn [loadbytes]. unfold V293_cache_lag_incremented at 1.
    repeat rewrite map_get_set' by congruence. rewrite IH. reflexivity. }
  rewrite E. reflexivity.
Qed.

(* Keep the large finite memory opaque while assembling four-byte loads. *)
Local Ltac cache_lag_pointer_load :=
  lazymatch goal with
  | |- load (Tptr Tvoid) ?M (?b, 0%Z) = _ =>
    let G0 := fresh "P0" in let G1 := fresh "P1" in
    let G2 := fresh "P2" in let G3 := fresh "P3" in
    assert (G0 : get M (b, 0%Z) = Some (true, Pointer 15%positive Int.zero 3)) by cache_lag_compute;
    assert (G1 : get M (b, 1%Z) = Some (true, Pointer 15%positive Int.zero 2)) by cache_lag_compute;
    assert (G2 : get M (b, 2%Z) = Some (true, Pointer 15%positive Int.zero 1)) by cache_lag_compute;
    assert (G3 : get M (b, 3%Z) = Some (true, Pointer 15%positive Int.zero 0)) by cache_lag_compute;
    unfold load, loadm; cbn [typelen loadbytes]; unfold addr, offset, block in *;
    rewrite G0; cbn [Z.add Pos.add Pos.succ];
    rewrite G1; cbn [Z.add Pos.add Pos.succ];
    rewrite G2; cbn [Z.add Pos.add Pos.succ]; rewrite G3; reflexivity
  end.

Theorem V293_cache_lag_observations :
  load Tint8 V293_cache_lag_memory (2%positive, 0%Z) = Some (V293_byteval 8) /\
  load Tint8 V293_cache_lag_memory (3%positive, 0%Z) = Some (V293_byteval 6) /\
  load Tint32 V293_cache_lag_memory (5%positive, 0%Z) = Some (Vint32 (Int.repr 17)) /\
  store Tint32 V293_cache_lag_memory (5%positive, 0%Z) (Vint32 (Int.repr 18)) =
    Some V293_cache_lag_incremented /\
  load Tint32 V293_cache_lag_incremented (5%positive, 0%Z) = Some (Vint32 (Int.repr 18)) /\
  load Tint8 V293_cache_lag_incremented (2%positive, 0%Z) = Some (V293_byteval 8) /\
  load (Tptr Tvoid) V293_cache_lag_incremented (1%positive, 0%Z) = Some (Vptr V293_current_next) /\
  load (Tptr Tvoid) V293_cache_lag_incremented (4%positive, 0%Z) = Some (Vptr V293_current_next).
Proof.
  assert (G0 : get V293_cache_lag_memory (5%positive, 0%Z) = Some (true, Byte (Byte.repr 17)))
    by cache_lag_compute.
  assert (G1 : get V293_cache_lag_memory (5%positive, 1%Z) = Some (true, Byte (Byte.repr 0)))
    by cache_lag_compute.
  assert (G2 : get V293_cache_lag_memory (5%positive, 2%Z) = Some (true, Byte (Byte.repr 0)))
    by cache_lag_compute.
  assert (G3 : get V293_cache_lag_memory (5%positive, 3%Z) = Some (true, Byte (Byte.repr 0)))
    by cache_lag_compute.
  split; [cache_lag_compute | ].
  split; [cache_lag_compute | ].
  split.
  - unfold load, loadm. cbn [typelen loadbytes]. unfold addr, offset, block in *.
    rewrite G0. cbn [Z.add Pos.add Pos.succ].
    rewrite G1. cbn [Z.add Pos.add Pos.succ].
    rewrite G2. cbn [Z.add Pos.add Pos.succ]. rewrite G3. vm_compute. reflexivity.
  - split.
    + change (storebytes V293_cache_lag_memory (5%positive, 0%Z)
        [Byte (Byte.repr 18); Byte (Byte.repr 0); Byte (Byte.repr 0); Byte (Byte.repr 0)] =
        Some V293_cache_lag_incremented).
      cbn [storebytes]. unfold addr, offset, block in *. rewrite G0. cbn [Z.add Pos.add Pos.succ].
    rewrite G1. cbn [Z.add Pos.add Pos.succ].
    rewrite G2. cbn [Z.add Pos.add Pos.succ]. rewrite G3. reflexivity.
    + split.
      * unfold load, loadm. cbn [typelen loadbytes]. unfold V293_cache_lag_incremented.
        repeat first [rewrite map_get_set | rewrite map_get_set' by (intro E; inversion E; lia)].
        vm_compute. reflexivity.
      * rewrite V293_cache_lag_load_unchanged by discriminate.
        split; [cache_lag_compute | ]. split;
          rewrite V293_cache_lag_load_unchanged by discriminate; cache_lag_pointer_load.
Qed.

Theorem V293_cache_lag_same_pointer_execution : forall P ks boundary,
  evalval (V293_OSSched_different 109%Z 108%Z)
    (V293_cache_lag_ge, emp, V293_cache_lag_memory) = Some (Vint32 Int.one) /\
  evalval (V293_OSSched_pointer_different 110%Z OSTCBCur)
    (V293_cache_lag_ge, emp, V293_cache_lag_memory) = Some (Vint32 Int.zero) /\
  cstepstar P
    (curs (V293_OSSched_change 109%Z 108%Z 111%Z (scall boundary nil)), (kenil, ks))
    (V293_cache_lag_ge, emp, V293_cache_lag_memory)
    (curs (scall boundary nil), (kenil, ks))
    (V293_cache_lag_ge, emp, V293_cache_lag_incremented).
Proof.
  intros P ks boundary.
  destruct V293_cache_lag_observations as (Lc & Lh & Lctr & Store & Lafter & Lcache & Lcur & Ltarget).
  assert (Cur : load (Tptr Tvoid) V293_cache_lag_memory (1%positive, 0%Z) = Some (Vptr V293_current_next))
    by (rewrite <- V293_cache_lag_load_unchanged by discriminate; exact Lcur).
  assert (Target : load (Tptr Tvoid) V293_cache_lag_memory (4%positive, 0%Z) = Some (Vptr V293_current_next))
    by (rewrite <- V293_cache_lag_load_unchanged by discriminate; exact Ltarget).
  destruct (V293_OSSched_byte_comparison_eval V293_cache_lag_ge emp V293_cache_lag_memory
    109%Z 108%Z 3%positive 2%positive 6 8 ltac:(lia) ltac:(lia)
    ltac:(apply map_emp_get) ltac:(apply map_emp_get) ltac:(reflexivity) ltac:(reflexivity) Lh Lc) as [E _].
  split; [exact E | ].
  destruct (V293_OSSched_pointer_comparison_eval V293_cache_lag_ge emp V293_cache_lag_memory
    110%Z OSTCBCur 4%positive 1%positive Tvoid Tvoid V293_current_next V293_current_next
    ltac:(apply map_emp_get) ltac:(apply map_emp_get) ltac:(reflexivity) ltac:(reflexivity) Target Cur) as [EP _].
  split.
  - destruct (tid_eq_dec V293_current_next V293_current_next) in EP; [exact EP | contradiction].
  - eapply V293_OSSched_changed_execution with (nh := 6) (nc := 8) (c := Int.repr 17);
      try eassumption; try lia; try reflexivity; apply map_emp_get.
Qed.

(* Single-factor semantic ablation: ONLY replace the source guard by the
   pointer guard. Same memory, increment and call suffix; now neither runs. *)
Theorem V293_cache_lag_pointer_rewrite_execution : forall P ks boundary,
  cstepstar P
    (curs (sifthen (V293_OSSched_pointer_different 110%Z OSTCBCur)
      (sseq (V293_OSSched_increment 111%Z) (scall boundary nil))), (kenil, ks))
    (V293_cache_lag_ge, emp, V293_cache_lag_memory)
    (curs (sskip None), (kenil, ks)) (V293_cache_lag_ge, emp, V293_cache_lag_memory) /\
  load Tint32 V293_cache_lag_memory (5%positive, 0%Z) = Some (Vint32 (Int.repr 17)).
Proof.
  intros P ks boundary.
  destruct (V293_cache_lag_same_pointer_execution P ks boundary) as [_ [E _]].
  split.
  - eapply c_stepstarn. { eapply stmt_step; [reflexivity | ]. constructor. }
    eapply V293_cstepstar_trans.
    { apply V293_expr_steps. apply evalval_imply_estepstar. exact E. }
    eapply c_stepstarn. { eapply stmt_step; [reflexivity | ]. apply sviff_step. reflexivity. }
    apply c_stepstar0.
  - exact (proj1 (proj2 (proj2 V293_cache_lag_observations))).
Qed.
