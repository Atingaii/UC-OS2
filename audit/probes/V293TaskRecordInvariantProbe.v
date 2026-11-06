(* Independent, nonempty physical record fixtures; these are not boot or API
   reachability proofs. The negative control changes one actual priority byte. *)
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293SharedStateWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCurrent.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTarget.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTargetWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.audit.probes.V293TaskRecordOwnershipProbe.
Require Import CertiOS.certiucos.v293.code.V293ReadyTable.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.auxdef.
Require Import CertiOS.framework.proof.memory_prop.
Require Import CertiOS.framework.proof.lmachLib.
Require Import CertiOS.framework.proof.rulesoundlib.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Definition RIcurrent (live : bool) : tid :=
  if live then OwnershipWaiting else (999%positive,Int.zero).
Definition RImemory ct := merge (V293_shared_fixture_mem ct) OwnershipMemory.
Definition RIabstract ct :=
  V293_shared_fixture_abs ct OwnershipTasks (emp : EcbMod.map) Int.zero.
Definition RIstate ct M := V293_target_wstate V293_shared_fixture_ge emp M (RIabstract ct).

Lemma RIjoin : forall ct,
  join (V293_shared_fixture_mem ct) OwnershipMemory (RImemory ct).
Proof.
  intro ct. apply map_join_merge. apply map_disjoint. intros [b i].
  destruct (Pos.eq_dec b 1%positive) as [Same | Apart].
  - subst b. right; left. apply OwnershipCellsOutside.
    intro Member. vm_compute in Member. intuition congruence.
  - left. apply V293_encoded_memory_outside. left; exact Apart.
Qed.
Lemma RIfixed_tasks : forall ct,
  get (RIabstract ct) abstcblsid=Some (abstcblist OwnershipTasks).
Proof.
  intro ct. exact (proj1 (proj2 (V293_shared_fields_get _ _ _ _ _
    (V293_shared_fixture_fields ct OwnershipTasks (emp : EcbMod.map) Int.zero)))).
Qed.
Theorem RIliteral_spatial : forall ct,
  RIstate ct (RImemory ct) |= SWINVt V293_records_inv ct.
Proof.
  intro ct. apply V293_records_switch_halves.
  eapply V293_target_wstate_star with (m1:=emp) (m2:=RImemory ct)
    (o1:=emp) (o2:=RIabstract ct).
  - apply map_join_comm; apply map_join_emp.
  - apply map_join_comm; apply map_join_emp.
  - apply V293_shared_fixture_flags.
  - unfold V293_records_full. exists OwnershipTasks. exists (emp : EcbMod.map). exists Int.zero.
    eapply V293_target_wstate_star with (m1:=V293_shared_fixture_mem ct) (m2:=OwnershipMemory)
      (o1:=emp) (o2:=RIabstract ct).
    + apply RIjoin.
    + apply map_join_comm; apply map_join_emp.
    + exists Tvoid. apply V293_shared_fixture_pointer.
    + eapply V293_target_wstate_star with (m1:=emp) (m2:=OwnershipMemory)
        (o1:=RIabstract ct) (o2:=emp).
      * apply map_join_comm; apply map_join_emp.
      * apply map_join_emp.
      * apply V293_shared_fixture_fields.
      * eapply V293_task_list_context. exact OwnershipLiteralSpatial.
Qed.
Lemma RIhighest : V293_highest_ready OwnershipTasks OwnershipReady.
Proof.
  exists (Int.repr 4). exists Vnull. split; [vm_compute; reflexivity | ].
  intros t p m H. unfold OwnershipTasks in H.
  destruct (tid_eq_dec OwnershipWaiting t) as [E | E].
  - subst t. rewrite map_get_set in H. discriminate.
  - rewrite map_get_set' in H by exact E.
    destruct (tid_eq_dec OwnershipReady t) as [Er | Er].
    + subst t. rewrite map_get_sig in H. inversion H; subst. lia.
    + rewrite map_get_sig' in H by exact Er. discriminate.
Qed.
Theorem RIswitch_cases : forall live,
  exists M',
    RIstate (RIcurrent live) (RImemory (RIcurrent live)) |=
      SWINVt V293_records_inv (RIcurrent live) /\
    RIstate (RIcurrent live) (RImemory (RIcurrent live)) |=
      AHprio V293_scheduler OwnershipReady ** Atrue /\
    get OwnershipTasks (RIcurrent live)=
      (if live then Some (Int.repr 6,wait (os_stat_sem (72%positive,Int.repr 5)) Int.one,
        Vptr (120%positive,Int.repr 7)) else None) /\
    store (Tptr Tvoid) (RImemory (RIcurrent live)) (1%positive,0%Z)
      (Vptr OwnershipReady)=Some M' /\
    V293_target_wstate V293_shared_fixture_ge emp M'
      (set (RIabstract (RIcurrent live)) curtid (oscurt OwnershipReady)) |=
      SWINVt V293_records_inv OwnershipReady /\
    V293_task_records M' OwnershipTasks /\
    (forall b off, b<>1%positive -> get M' (b,off)=get (RImemory (RIcurrent live)) (b,off)).
Proof.
  intro live. set (ct:=RIcurrent live).
  assert (HM : mapstoval (1%positive,0%Z) (Tptr Tvoid) true (Vptr ct)
    (V293_shared_fixture_mem ct)) by apply V293_encoded_memory_mapsto.
  destruct (store_exist_join' _ _ _ (Vptr OwnershipReady) _ _ _ HM (RIjoin ct)) as [M' Store].
  pose proof (RIliteral_spatial ct) as Held.
  assert (After : V293_target_wstate V293_shared_fixture_ge emp M'
    (set (RIabstract ct) curtid (oscurt OwnershipReady)) |= SWINVt V293_records_inv OwnershipReady).
  { eapply V293_records_store; [exact Held | apply map_get_sig | exact Store]. }
  exists M'. split; [exact Held | ]. split.
  - apply V293_records_switch_full in Held. unfold V293_records_full in Held.
    sep normal in Held. sep destruct Held.
    assert (E : x=OwnershipTasks).
    { assert (T : get (RIabstract ct) abstcblsid=Some (abstcblist x)).
      { change (get (getabst (RIstate ct (RImemory ct))) abstcblsid=Some (abstcblist x)).
        eapply V293_star_abst_get_l with (p:=Aabsdata abstcblsid (abstcblist x)) (q:=Atrue).
        - apply V293_shared_abs_get.
        - unfold V293_shared_fields in Held. sep auto. }
      pose proof (RIfixed_tasks ct). congruence. } subst x.
    eapply astar_mono with (P:=Aabsdata abstcblsid (abstcblist OwnershipTasks)) (Q:=Atrue).
    + apply V293_tasks_highest_spatial. exact RIhighest.
    + intros st H; exact H.
    + unfold V293_shared_fields in Held. sep auto.
  - split; [destruct live; vm_compute; reflexivity | ]. split; [exact Store | ].
    split; [exact After | ]. split.
    + apply astar_r_aemp_intro in After.
      destruct (V293_records_switch_sound _ _ _ After) as [tasks [Lookup Records]].
    change (get (set (RIabstract ct) curtid (oscurt OwnershipReady)) abstcblsid=
      Some (abstcblist tasks)) in Lookup.
    rewrite map_get_set' in Lookup by discriminate.
    pose proof (RIfixed_tasks ct). assert (tasks=OwnershipTasks) by congruence. subst tasks. exact Records.
    + intros b off Apart. eapply V293_storebytes_outside; [exact Store | left; exact Apart].
Qed.

(* Erasing the semantic record ownership leaves precisely the old four-slot
   invariant with an unconstrained physical frame, in the SAME state. *)
Lemma RIweak_frame : forall ct extra M,
  join (V293_shared_fixture_mem ct) extra M ->
  RIstate ct M |= SWINVt V293_shared_inv ct ** Atrue.
Proof.
  intros ct extra M JM.
  eapply V293_target_wstate_star with (m1:=V293_shared_fixture_mem ct) (m2:=extra)
    (o1:=RIabstract ct) (o2:=emp).
  - exact JM.
  - apply map_join_emp.
  - apply V293_shared_fixture_spatial.
  - exact I.
Qed.
Definition RIBadRecords := set OwnershipMemory (60%positive,50%Z) (true,Byte (Byte.repr 5)).
Lemma RIbad_record_store :
  store Tint8 OwnershipMemory (60%positive,50%Z) (V293_byteval 5)=Some RIBadRecords.
Proof.
  change (match get OwnershipMemory (60%positive,50%Z) with
    | Some (true,_) => Some RIBadRecords | _ => None end=Some RIBadRecords).
  pose proof (OwnershipCellsSpatial _ OwnershipLiteralSeparated OwnershipLiteralValid emp emp) as Cells.
  apply astar_r_aemp_intro in Cells.
  destruct (V293_owned_cells_byte_writable OwnershipAllCells (60%positive,50%Z) (V293_byteval 4) _
    _ _ _ _ _ _ _ ltac:(vm_compute; intuition congruence) Cells) as [v Writable].
  change (get OwnershipMemory (60%positive,50%Z)=Some (true,v)) in Writable.
  rewrite Writable. reflexivity.
Qed.
Lemma RIbad_record_load : load Tint8 RIBadRecords (60%positive,50%Z)=Some (V293_byteval 5).
Proof.
  unfold RIBadRecords.
  replace (Byte.repr 5) with (Byte.repr (Int.unsigned (Int.repr (Z.of_nat 5))))
    by (vm_compute; reflexivity).
  apply V293_put_byte_load. lia.
Qed.
Lemma RIoriginal_record_load : load Tint8 OwnershipMemory (60%positive,50%Z)=Some (V293_byteval 4).
Proof.
  eapply V293_owned_record_cells_load with (cells:=OwnershipAllCells)
    (s:=V293_wstate emp emp OwnershipMemory).
  - vm_compute; intuition congruence.
  - apply OwnershipCellsSpatial; [apply OwnershipLiteralSeparated | apply OwnershipLiteralValid].
Qed.

Theorem RIone_byte_ablation : exists Mbad,
  RIstate OwnershipWaiting (RImemory OwnershipWaiting) |= SWINVt V293_records_inv OwnershipWaiting /\
  RIstate OwnershipWaiting (RImemory OwnershipWaiting) |= SWINVt V293_shared_inv OwnershipWaiting ** Atrue /\
  store Tint8 (RImemory OwnershipWaiting) (60%positive,50%Z) (V293_byteval 5)=Some Mbad /\
  (forall a, a<>(60%positive,50%Z) -> get Mbad a=get (RImemory OwnershipWaiting) a) /\
  load Tint8 (RImemory OwnershipWaiting) (60%positive,50%Z)=Some (V293_byteval 4) /\
  load Tint8 Mbad (60%positive,50%Z)=Some (V293_byteval 5) /\
  RIstate OwnershipWaiting Mbad |= SWINVt V293_shared_inv OwnershipWaiting ** Atrue /\
  (forall t R, ~ RIstate OwnershipWaiting Mbad |= SWINVt V293_records_inv t ** R).
Proof.
  pose proof (RIjoin OwnershipWaiting) as Join.
  assert (ReverseJoin : join OwnershipMemory (V293_shared_fixture_mem OwnershipWaiting)
    (RImemory OwnershipWaiting)) by (apply map_join_comm; exact Join).
  destruct (store_mono _ _ _ _ _ _ _ ReverseJoin RIbad_record_store) as [Mbad Store].
  assert (BadJoin : join (V293_shared_fixture_mem OwnershipWaiting) RIBadRecords Mbad).
  { eapply join_store_join; [exact Join | exact RIbad_record_store | exact Store]. }
  assert (NewLoad : load Tint8 Mbad (60%positive,50%Z)=Some (V293_byteval 5)).
  { eapply load_mem_mono; [exact RIbad_record_load | exists (V293_shared_fixture_mem OwnershipWaiting); apply map_join_comm; exact BadJoin]. }
  exists Mbad. split; [apply RIliteral_spatial | ]. split; [eapply RIweak_frame; exact Join | ].
  split; [exact Store | ]. split.
  - intros a Apart.
    change (match get (RImemory OwnershipWaiting) (60%positive,50%Z) with
      | Some (true,_) => Some (set (RImemory OwnershipWaiting) (60%positive,50%Z) (true,Byte (Byte.repr 5)))
      | _ => None end=Some Mbad) in Store.
    destruct (get (RImemory OwnershipWaiting) (60%positive,50%Z)) as [[permission v] | ];
      try discriminate. destruct permission; try discriminate.
    inversion Store; subst Mbad. apply map_get_set'. congruence.
  - split.
    + eapply load_mem_mono; [exact RIoriginal_record_load | exists (V293_shared_fixture_mem OwnershipWaiting); exact ReverseJoin].
    + split; [exact NewLoad | ]. split; [eapply RIweak_frame; exact BadJoin | ].
      intros t R Held.
      destruct (V293_records_switch_sound _ _ _ Held) as [tasks [Lookup Records]].
      change (get (RIabstract OwnershipWaiting) abstcblsid=Some (abstcblist tasks)) in Lookup.
      pose proof (RIfixed_tasks OwnershipWaiting). assert (tasks=OwnershipTasks) by congruence. subst tasks.
      assert (Ready : get OwnershipTasks OwnershipReady=Some (Int.repr 4,rdy,Vnull)) by (vm_compute; reflexivity).
      destruct (Records _ _ _ _ Ready) as [p [Bound [Priority [Fields Payload]]]].
      assert (P4 : p=4).
      { eapply V293_priority_repr_injective; [exact Bound | lia | symmetry; exact Priority]. }
      subst p. destruct Fields as [OldLoad _].
      change (load Tint8 Mbad (60%positive,50%Z)=Some (V293_byteval 4)) in OldLoad.
      rewrite NewLoad in OldLoad. vm_compute in OldLoad. discriminate.
Qed.

Theorem RIclosed_good : GoodI V293_records_inv V293_scheduler V293_shared_li.
Proof. exact V293_records_invariant_good. Qed.
