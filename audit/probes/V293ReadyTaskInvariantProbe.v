(* Independent literal ready/table resources; not boot reachability. *)
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
Require Import CertiOS.certiucos.v293.proofs.V293ReadyTaskInvariant.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.audit.probes.V293TaskRecordInvariantProbe.
Import ListNotations.
Local Open Scope nat_scope.

Definition RTentries : list val :=
  [Vnull;Vnull;Vnull;Vnull;Vptr OwnershipReady;Vnull;Vptr OwnershipWaiting;
   Vnull;Vnull;Vnull;Vnull;Vnull;Vnull].
Definition RTcells := V293_ready_cells 80%positive 81%positive 82%positive 16 0 RTentries.
Definition RTmemory := OwnershipCellsMemory RTcells.
Definition RTfull ct := merge (RImemory ct) RTmemory.
Definition RTstate ct M := RIstate ct M.

Lemma RTonly_ready : forall p t m,
  p<13 -> get OwnershipTasks t=Some (Int.repr (Z.of_nat p),rdy,m) ->
  p=4 /\ t=OwnershipReady /\ m=Vnull.
Proof.
  intros p t m Bound H. unfold OwnershipTasks in H.
  destruct (tid_eq_dec OwnershipWaiting t) as [E | E].
  - subst t. rewrite map_get_set in H. discriminate.
  - rewrite map_get_set' in H by exact E.
    destruct (tid_eq_dec OwnershipReady t) as [Er | Er].
    + subst t. rewrite map_get_sig in H. inversion H.
      split; [  |  auto ].
      change (Int.unsigned (Int.repr (Z.of_nat 4))=Int.unsigned (Int.repr (Z.of_nat p))) in H1.
      rewrite !V293_priority_repr_unsigned in H1 by lia. lia.
    + rewrite map_get_sig' in H by exact Er. discriminate.
Qed.
Lemma RTliteral_rel : V293_ready_rel 16 0 RTentries OwnershipTasks.
Proof.
  split; [lia | ]. split; [lia | ]. split.
  - exists 4. left. split; [lia | vm_compute; reflexivity].
  - split.
    + intros p Bound. assert (Bit : V293_bitmap_ready 16 0 p <-> p=4).
      { do 13 (destruct p as [ | p]; [vm_compute; intuition lia | ]). lia. }
      rewrite Bit. split.
      * intro E. subst p. exists OwnershipReady. exists Vnull. vm_compute; reflexivity.
      * intros (t&m&H). exact (proj1 (RTonly_ready _ _ _ Bound H)).
    + split; [reflexivity | ]. intros t p st m H. unfold OwnershipTasks in H.
      destruct (tid_eq_dec OwnershipWaiting t) as [E | E].
      * subst t. rewrite map_get_set in H. inversion H; subst.
        exists 6. repeat split; reflexivity  ||  lia.
      * rewrite map_get_set' in H by exact E.
        destruct (tid_eq_dec OwnershipReady t) as [Er | Er].
        -- subst t. rewrite map_get_sig in H. inversion H; subst.
           exists 4. repeat split; reflexivity  ||  lia.
        -- rewrite map_get_sig' in H by exact Er. discriminate.
Qed.
Lemma RTliteral_separated : OwnershipCellsSeparated RTcells.
Proof. vm_compute. repeat split; intros; intuition congruence. Qed.
Lemma RTliteral_valid : Forall
  (fun cell => let '(_,tp,v) := cell in rule_type_val_match tp v=true) RTcells.
Proof. repeat constructor; vm_compute; reflexivity. Qed.
Lemma RTliteral_cells : V293_wstate emp emp RTmemory  |= V293_owned_record_cells RTcells.
Proof. apply OwnershipCellsSpatial; [exact RTliteral_separated | exact RTliteral_valid]. Qed.
Lemma RTliteral_ready : V293_wstate emp emp RTmemory  |=
  V293_ready_owned 80%positive 81%positive 82%positive OwnershipTasks.
Proof. exists 16. exists 0. exists RTentries.
  apply astar_l_apure_intro; [exact RTliteral_cells | exact RTliteral_rel]. Qed.
Lemma RTjoin : forall ct, join (RImemory ct) RTmemory (RTfull ct).
Proof.
  intro ct. apply map_join_merge. apply map_disjoint. intros [b i].
  destruct (Pos.eq_dec b 80%positive) as [E | N80]; [subst b | ];
  [left | destruct (Pos.eq_dec b 81%positive) as [E | N81]; [subst b;left | ]];
  try (destruct (Pos.eq_dec b 82%positive) as [E | N82]; [subst b;left | right;left]);
  try (apply OwnershipCellsOutside; intro H; vm_compute in H; intuition congruence).
  all: unfold RImemory,V293_shared_fixture_mem; rewrite map_merge_semp by reflexivity;
    rewrite V293_encoded_memory_outside by (left;discriminate);
    unfold OwnershipMemory; rewrite OwnershipCellsOutside by
      (intro H; vm_compute in H; intuition congruence); reflexivity.
Qed.
Theorem RTliteral_spatial : forall ct,
  RTstate ct (RTfull ct)  |= SWINVt (V293_ready_inv 80%positive 81%positive 82%positive) ct.
Proof.
  intro ct.
  assert (Raw : RTstate ct (RTfull ct)  |= SWINVt V293_records_inv ct **
    V293_ready_owned 80%positive 81%positive 82%positive OwnershipTasks).
  { eapply V293_target_wstate_star with (m1:=RImemory ct) (m2:=RTmemory)
      (o1:=RIabstract ct) (o2:=emp).
    - apply RTjoin.
    - apply map_join_emp.
    - exact (RIliteral_spatial ct).
    - exists 16. exists 0. exists RTentries. apply astar_l_apure_intro.
      + eapply V293_owned_cells_context; exact RTliteral_cells.
      + exact RTliteral_rel.
  }
  assert (Opened : RTstate ct (RTfull ct)  |=
    (V293_shared_flags ** V293_records_full ct) **
    V293_ready_owned 80%positive 81%positive 82%positive OwnershipTasks).
  { eapply astar_mono; [apply V293_records_switch_full | intros st H;exact H | exact Raw]. }
  unfold V293_records_full in Opened. sep normal in Opened. sep destruct Opened.
  assert (Fixed : x=OwnershipTasks).
  { assert (Lookup : get (RIabstract ct) abstcblsid=Some (abstcblist x)).
    { change (get (getabst (RTstate ct (RTfull ct))) abstcblsid=Some (abstcblist x)).
      eapply V293_star_abst_get_l with (p:=Aabsdata abstcblsid (abstcblist x)) (q:=Atrue).
      - apply V293_shared_abs_get.
      - unfold V293_shared_fields in Opened. clear Raw. sep auto. }
    pose proof (RIfixed_tasks ct). congruence. } subst x.
  apply V293_ready_switch_halves. unfold V293_ready_full,V293_ready_payload.
  clear Raw. sep auto.
Qed.

Lemma RTrecords_cells : forall ct,
  RTstate ct (RTfull ct) |= V293_owned_record_cells RTcells ** SWINVt V293_records_inv ct.
Proof.
  intro ct. apply astar_comm.
  eapply V293_target_wstate_star with (m1:=RImemory ct) (m2:=RTmemory)
    (o1:=RIabstract ct) (o2:=emp).
  - apply RTjoin.
  - apply map_join_emp.
  - apply RIliteral_spatial.
  - eapply V293_owned_cells_context; exact RTliteral_cells.
Qed.
Lemma RTliteral_loads : forall ct,
  V293_ready_loads (RTfull ct) 80%positive 81%positive 82%positive 16 0 RTentries.
Proof.
  intro ct. eapply V293_ready_loads_sub with (M:=RTmemory).
  - exists (RImemory ct). apply map_join_comm; apply RTjoin.
  - exact (V293_ready_cells_loads 80%positive 81%positive 82%positive 16 0 RTentries (V293_wstate emp emp RTmemory)
      eq_refl RTliteral_cells).
Qed.
Theorem RTswitch_cases : forall live,
  exists Mf,
    RTstate (RIcurrent live) (RTfull (RIcurrent live)) |=
      SWINVt (V293_ready_inv 80%positive 81%positive 82%positive) (RIcurrent live) /\
    get OwnershipTasks (RIcurrent live)=
      (if live then Some (Int.repr 6,wait (os_stat_sem (72%positive,Int.repr 5)) Int.one,
        Vptr (120%positive,Int.repr 7)) else None) /\
    store (Tptr Tvoid) (RTfull (RIcurrent live)) (1%positive,0%Z)
      (Vptr OwnershipReady)=Some Mf /\
    V293_target_wstate V293_shared_fixture_ge emp Mf
      (set (RIabstract (RIcurrent live)) curtid (oscurt OwnershipReady)) |=
      SWINVt (V293_ready_inv 80%positive 81%positive 82%positive) OwnershipReady /\
    V293_task_records Mf OwnershipTasks /\
    V293_ready_loads Mf 80%positive 81%positive 82%positive 16 0 RTentries /\
    (forall b off, b<>1%positive -> get Mf (b,off)=get (RTfull (RIcurrent live)) (b,off)).
Proof.
  intro live. set (ct:=RIcurrent live).
  destruct (RIswitch_cases live) as (Ma&Old&Highest&Member&StoreOld&AfterOld&RecordsOld&FrameOld).
  destruct (store_mono _ _ _ _ _ _ _ (RTjoin ct) StoreOld) as [Mf Store].
  assert (After : V293_target_wstate V293_shared_fixture_ge emp Mf
    (set (RIabstract ct) curtid (oscurt OwnershipReady)) |=
    SWINVt (V293_ready_inv 80%positive 81%positive 82%positive) OwnershipReady).
  { eapply V293_ready_store; [apply RTliteral_spatial | apply map_get_sig | exact Store]. }
  assert (Loads : V293_ready_loads Mf 80%positive 81%positive 82%positive 16 0 RTentries).
  { eapply V293_ready_loads_sub with (M:=RTmemory).
    - exists Ma. eapply join_store_join; [apply map_join_comm; apply RTjoin | exact StoreOld | exact Store].
    - exact (V293_ready_cells_loads 80%positive 81%positive 82%positive 16 0 RTentries (V293_wstate emp emp RTmemory) eq_refl RTliteral_cells). }
  exists Mf. split; [apply RTliteral_spatial | ]. split; [exact Member | ]. split; [exact Store | ].
  split; [exact After | ]. split.
  - apply astar_r_aemp_intro in After.
    destruct (V293_ready_switch_sound _ _ _ _ _ _ After) as (ts&lo&hi&es&Lookup&Records&Rel&Reads).
    change (get (set (RIabstract ct) curtid (oscurt OwnershipReady)) abstcblsid=Some (abstcblist ts)) in Lookup.
    rewrite map_get_set' in Lookup by discriminate.
    pose proof (RIfixed_tasks ct). assert (ts=OwnershipTasks) by congruence. subst ts. exact Records.
  - split; [exact Loads | ]. intros b off Apart. eapply V293_storebytes_outside; [exact Store | left;exact Apart].
Qed.

Lemma RTbyte_injective : forall n m,
  n<256 -> m<256 -> V293_byteval n=V293_byteval m -> n=m.
Proof.
  intros n m N M E.
  apply (f_equal (fun v => match v with Vint32 i => Int.unsigned i | _ => 0%Z end)) in E.
  change (Int.unsigned (Int.repr (Z.of_nat n))=Int.unsigned (Int.repr (Z.of_nat m))) in E.
  rewrite !Int.unsigned_repr in E by (unfold Int.max_unsigned,Int.modulus,Int.wordsize; simpl;lia). lia.
Qed.
Lemma RTreject_zero : forall ct M,
  load Tint8 M (80%positive,0%Z)=Some (V293_byteval 0) ->
  forall t R, ~ RTstate ct M |= SWINVt (V293_ready_inv 80%positive 81%positive 82%positive) t ** R.
Proof.
  intros ct M Zero t R Held.
  destruct (V293_ready_switch_sound _ _ _ _ _ _ Held) as (ts&lo&hi&es&Lookup&Records&Rel&Reads).
  change (get (RIabstract ct) abstcblsid=Some (abstcblist ts)) in Lookup.
  pose proof (RIfixed_tasks ct). assert (ts=OwnershipTasks) by congruence. subst ts.
  destruct Rel as [Lo [Hi [Nonempty [Bitmap Table]]]]. destruct Reads as [Low Rest].
  change (load Tint8 M (80%positive,0%Z)=Some (V293_byteval lo)) in Low.
  assert (L0 : lo=0).
  { eapply RTbyte_injective; [exact Lo | lia | congruence]. } subst lo.
  assert (Ready : exists t m, get OwnershipTasks t=Some (Int.repr (Z.of_nat 4),rdy,m)).
  { exists OwnershipReady. exists Vnull. vm_compute;reflexivity. }
  apply (proj2 (Bitmap 4 ltac:(lia))) in Ready. vm_compute in Ready. intuition lia.
Qed.
Theorem RTbitmap_ablation : exists Mbad,
  RTstate OwnershipWaiting (RTfull OwnershipWaiting) |=
    SWINVt (V293_ready_inv 80%positive 81%positive 82%positive) OwnershipWaiting /\
  store Tint8 (RTfull OwnershipWaiting) (80%positive,0%Z) (V293_byteval 0)=Some Mbad /\
  (forall a, a<>(80%positive,0%Z) -> get Mbad a=get (RTfull OwnershipWaiting) a) /\
  load Tint8 (RTfull OwnershipWaiting) (80%positive,0%Z)=Some (V293_byteval 16) /\
  load Tint8 Mbad (80%positive,0%Z)=Some (V293_byteval 0) /\
  RTstate OwnershipWaiting Mbad |= SWINVt V293_records_inv OwnershipWaiting ** Atrue /\
  (forall t R, ~ RTstate OwnershipWaiting Mbad |=
    SWINVt (V293_ready_inv 80%positive 81%positive 82%positive) t ** R).
Proof.
  pose proof (RTrecords_cells OwnershipWaiting) as Raw.
  change (RTstate OwnershipWaiting (RTfull OwnershipWaiting) |=
    (V293_owned_record_cell ((80%positive,0%Z),Tint8,V293_byteval 16) **
      V293_owned_record_cells (tl RTcells)) ** SWINVt V293_records_inv OwnershipWaiting) in Raw.
  apply astar_assoc_elim in Raw.
  destruct (V293_owned_byte_update _ _ 0 _ _ _ _ _ _ _ _ ltac:(lia) Raw) as [[v Writable] After].
  set (Mbad:=V293_put_byte (RTfull OwnershipWaiting) (80%positive,0%Z) 0) in *.
  assert (Zero : load Tint8 Mbad (80%positive,0%Z)=Some (V293_byteval 0)).
  { apply V293_put_byte_load. lia. }
  exists Mbad. split; [apply RTliteral_spatial | ]. split.
  - apply V293_put_byte_store with (old:=v). exact Writable.
  - split.
    + intros a Apart. unfold Mbad,V293_put_byte. apply map_get_set'. congruence.
    + split; [exact (proj1 (RTliteral_loads OwnershipWaiting)) | ]. split; [exact Zero | ]. split.
      * clear Raw. sep auto.
      * apply RTreject_zero; exact Zero.
Qed.

Lemma RTreject_slot : forall ct M,
  load (Tptr V293_tcb_type) M (82%positive,16%Z)=Some (Vptr OwnershipWaiting) ->
  forall t R, ~ RTstate ct M |= SWINVt (V293_ready_inv 80%positive 81%positive 82%positive) t ** R.
Proof.
  intros ct M Bad t R Held.
  destruct (V293_ready_switch_sound _ _ _ _ _ _ Held) as (ts&lo&hi&es&Lookup&Records&Rel&Reads).
  change (get (RIabstract ct) abstcblsid=Some (abstcblist ts)) in Lookup.
  pose proof (RIfixed_tasks ct). assert (ts=OwnershipTasks) by congruence. subst ts.
  destruct Rel as [Lo [Hi [Nonempty [Bitmap [Len Table]]]]].
  assert (Ready : get OwnershipTasks OwnershipReady=Some (Int.repr 4,rdy,Vnull)) by (vm_compute;reflexivity).
  destruct (Table _ _ _ _ Ready) as (p&Bound&Priority&Slot).
  assert (P4 : p=4).
  { eapply V293_priority_repr_injective; [exact Bound | lia | symmetry;exact Priority]. } subst p.
  pose proof (proj2 (proj2 (proj2 Reads)) 4 ltac:(lia)) as Actual.
  rewrite Slot in Actual. change (load (Tptr V293_tcb_type) M (82%positive,16%Z)=Some (Vptr OwnershipReady)) in Actual.
  rewrite Bad in Actual. vm_compute in Actual. discriminate.
Qed.
Theorem RTslot_ablation : exists Mbad,
  RTstate OwnershipWaiting (RTfull OwnershipWaiting) |=
    SWINVt (V293_ready_inv 80%positive 81%positive 82%positive) OwnershipWaiting /\
  store (Tptr V293_tcb_type) (RTfull OwnershipWaiting) (82%positive,16%Z)
    (Vptr OwnershipWaiting)=Some Mbad /\
  (forall b i, b<>82%positive \/ (i<16)%Z \/ (20<=i)%Z ->
    get Mbad (b,i)=get (RTfull OwnershipWaiting) (b,i)) /\
  load (Tptr V293_tcb_type) (RTfull OwnershipWaiting) (82%positive,16%Z)=Some (Vptr OwnershipReady) /\
  load (Tptr V293_tcb_type) Mbad (82%positive,16%Z)=Some (Vptr OwnershipWaiting) /\
  RTstate OwnershipWaiting Mbad |= SWINVt V293_records_inv OwnershipWaiting ** Atrue /\
  (forall t R, ~ RTstate OwnershipWaiting Mbad |=
    SWINVt (V293_ready_inv 80%positive 81%positive 82%positive) t ** R).
Proof.
  assert (Member : In ((82%positive,16%Z),Tptr V293_tcb_type,Vptr OwnershipReady) RTcells)
    by (vm_compute;intuition congruence).
  apply in_split in Member. destruct Member as (prefix&suffix&Same).
  pose proof (RTrecords_cells OwnershipWaiting) as Raw. rewrite Same in Raw.
  assert (Focus : RTstate OwnershipWaiting (RTfull OwnershipWaiting) |=
    V293_owned_record_cell ((82%positive,16%Z),Tptr V293_tcb_type,Vptr OwnershipReady) **
    ((V293_owned_record_cells prefix ** V293_owned_record_cells suffix) ** SWINVt V293_records_inv OwnershipWaiting)).
  { eapply astar_mono in Raw; [ | intros st H;apply OwnershipCellsAppend in H;exact H | intros st H;exact H].
    cbn [V293_owned_record_cells] in Raw. sep auto. }
  destruct (V293_owned_record_cell_update (82%positive,16%Z) (Tptr V293_tcb_type) (Vptr OwnershipReady) (Vptr OwnershipWaiting) _ _ _ _ _ _ _ _ eq_refl Focus)
    as (Mbad&Store&After).
  assert (Bad : load (Tptr V293_tcb_type) Mbad (82%positive,16%Z)=Some (Vptr OwnershipWaiting)).
  { eapply V293_store_readback; [reflexivity | exact Store]. }
  exists Mbad. split; [apply RTliteral_spatial | ]. split; [exact Store | ]. split.
  - intros b i Outside. eapply V293_storebytes_outside; [exact Store | exact Outside].
  - split.
    + exact (proj2 (proj2 (proj2 (RTliteral_loads OwnershipWaiting))) 4 ltac:(lia)).
    + split; [exact Bad | ]. split.
      * clear Raw Focus. sep auto.
      * apply RTreject_slot; exact Bad.
Qed.
Theorem RTclosed_good : GoodI (V293_ready_inv 80%positive 81%positive 82%positive)
  V293_scheduler V293_shared_li.
Proof. exact (V293_ready_invariant_good _ _ _). Qed.

(* A joint literal entry for the execution theorem, including actual readonly
   decoder bytes and two independent writable output cells. *)
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.code.V293OSSchedNew.
Require Import CertiOS.certiucos.v293.code.V293OSSchedDispatch.
Lemma RTenv_spatial : forall ge le ct,
  get ge OSTCBCur=Some (1%positive,Tptr Tvoid) ->
  V293_target_wstate ge le (RTfull ct) (RIabstract ct) |=
    SWINVt (V293_ready_inv 80%positive 81%positive 82%positive) ct.
Proof.
  intros ge le ct Cur.
  assert (Flags : V293_target_wstate ge le emp emp |= V293_shared_flags).
  { unfold V293_shared_flags.
    repeat (eapply V293_target_wstate_star with (m1:=emp) (m2:=emp) (o1:=emp) (o2:=emp);
      [apply map_join_emp | apply map_join_emp | | ]).
    - exists (fun _ : hid => false). split; repeat split; reflexivity.
    - repeat split; reflexivity.
    - exists INUM. repeat split; reflexivity. }
  assert (Fields : V293_target_wstate ge le emp (RIabstract ct) |=
    V293_shared_fields ct OwnershipTasks (emp : EcbMod.map) Int.zero).
  { unfold V293_shared_fields,RIabstract,V293_shared_fixture_abs.
    repeat (eapply V293_target_wstate_star;
      [apply map_join_emp | apply map_join_merge;apply map_disjoint;intros key;destruct key;simpl;auto | split;reflexivity | ]).
    split;reflexivity. }
  assert (Pointer : V293_target_wstate ge le (V293_shared_fixture_mem ct) emp |=
    GV OSTCBCur @ (Tptr Tvoid) |-> (Vptr ct)).
  { exists 1%positive. eapply V293_target_wstate_star with
      (m1:=emp) (m2:=V293_shared_fixture_mem ct) (o1:=emp) (o2:=emp).
    - apply map_join_comm;apply map_join_emp.
    - apply map_join_emp.
    - exists 1%positive. split; [exact Cur | ]. repeat split;reflexivity.
    - split; [apply V293_encoded_memory_mapsto | reflexivity]. }
  assert (Core : V293_target_wstate ge le (RImemory ct) (RIabstract ct) |=
    (EX tp : type, GV OSTCBCur @ (Tptr tp) |-> (Vptr ct)) **
    (V293_shared_fields ct OwnershipTasks (emp : EcbMod.map) Int.zero **
      V293_owned_task_records OwnershipTasks)).
  { eapply V293_target_wstate_star with (m1:=V293_shared_fixture_mem ct) (m2:=OwnershipMemory)
      (o1:=emp) (o2:=RIabstract ct).
    - apply RIjoin.
    - apply map_join_comm;apply map_join_emp.
    - exists Tvoid. exact Pointer.
    - eapply V293_target_wstate_star with (m1:=emp) (m2:=OwnershipMemory)
        (o1:=RIabstract ct) (o2:=emp).
      + apply map_join_comm;apply map_join_emp.
      + apply map_join_emp.
      + exact Fields.
      + eapply V293_task_list_context;exact OwnershipLiteralSpatial. }
  assert (Raw : V293_target_wstate ge le (RTfull ct) (RIabstract ct) |=
    ((EX tp : type, GV OSTCBCur @ (Tptr tp) |-> (Vptr ct)) **
     (V293_shared_fields ct OwnershipTasks (emp : EcbMod.map) Int.zero **
       V293_owned_task_records OwnershipTasks)) **
    V293_ready_owned 80%positive 81%positive 82%positive OwnershipTasks).
  { eapply V293_target_wstate_star with (m1:=RImemory ct) (m2:=RTmemory)
      (o1:=RIabstract ct) (o2:=emp).
    - apply RTjoin.
    - apply map_join_emp.
    - exact Core.
    - exists 16. exists 0. exists RTentries. apply astar_l_apure_intro.
      + eapply V293_owned_cells_context;exact RTliteral_cells.
      + exact RTliteral_rel. }
  apply V293_ready_switch_halves.
  eapply V293_target_wstate_star with (m1:=emp) (m2:=RTfull ct)
    (o1:=emp) (o2:=RIabstract ct).
  - apply map_join_comm;apply map_join_emp.
  - apply map_join_comm;apply map_join_emp.
  - exact Flags.
  - unfold V293_ready_full,V293_ready_payload. clear Core Fields Pointer Flags. sep auto.
Qed.
Definition RToutput_cells : list V293_record_cell :=
  [((90%positive,0%Z),Tint8,V293_byteval 99); ((91%positive,0%Z),Tint8,V293_byteval 88)].
Definition RToutputs := OwnershipCellsMemory RToutput_cells.
Definition RTdecoder := V293_nat_memory 92%positive 0%Z V293_ready_table.
Definition RTwith_outputs ct := merge (RTfull ct) RToutputs.
Definition RTexec_memory ct := merge (RTwith_outputs ct) RTdecoder.
Definition RTge : env :=
  set (set (set (set (set V293_shared_fixture_ge
    100%Z (92%positive,Tarray Tint8 256)) 101%Z (81%positive,Tint8))
    102%Z (80%positive,Tarray Tint8 2)) 103%Z (91%positive,Tint8))
    105%Z (82%positive,Tarray (Tptr V293_tcb_type) 13).
Definition RTle : env := sig 104%Z (90%positive,Tint8).
Lemma RToutside : forall ct b i,
  b<>1%positive -> b<>41%positive -> b<>60%positive ->
  b<>80%positive -> b<>81%positive -> b<>82%positive ->
  get (RTfull ct) (b,i)=None.
Proof.
  intros ct b i N1 N41 N60 N80 N81 N82.
  assert (Old : get (RImemory ct) (b,i)=None).
  { unfold RImemory,V293_shared_fixture_mem. rewrite map_merge_semp by reflexivity.
    rewrite V293_encoded_memory_outside by (left;exact N1).
    unfold OwnershipMemory. rewrite OwnershipCellsOutside by
      (intro H;vm_compute in H;intuition congruence). reflexivity. }
  unfold RTfull. rewrite map_merge_semp by reflexivity. rewrite Old.
  unfold RTmemory. rewrite OwnershipCellsOutside by
    (intro H;vm_compute in H;intuition congruence). reflexivity.
Qed.
Lemma RToutputs_join : forall ct, join (RTfull ct) RToutputs (RTwith_outputs ct).
Proof.
  intro ct. apply map_join_merge;apply map_disjoint;intros [b i].
  destruct (Pos.eq_dec b 90%positive) as [E | N90]; [subst b;left | ];
  [apply RToutside;discriminate | ].
  destruct (Pos.eq_dec b 91%positive) as [E | N91]; [subst b;left;apply RToutside;discriminate | ].
  right;left. apply OwnershipCellsOutside. intro H;vm_compute in H;intuition congruence.
Qed.
Lemma RTdecoder_join : forall ct, join (RTwith_outputs ct) RTdecoder (RTexec_memory ct).
Proof.
  intro ct. apply map_join_merge;apply map_disjoint;intros [b i].
  destruct (Pos.eq_dec b 92%positive) as [E | N92].
  - subst b. left. unfold RTwith_outputs;rewrite map_merge_semp by reflexivity.
    rewrite RToutside by discriminate. unfold RToutputs.
    rewrite OwnershipCellsOutside by (intro H;vm_compute in H;intuition congruence). reflexivity.
  - right;left. apply V293_encoded_memory_outside. left;exact N92.
Qed.
Lemma RTexec_entry : forall ct,
  V293_target_wstate RTge RTle (RTexec_memory ct) (RIabstract ct) |=
    (V293_owned_record_cell ((90%positive,0%Z),Tint8,V293_byteval 99) **
     V293_owned_record_cell ((91%positive,0%Z),Tint8,V293_byteval 88)) **
    (SWINVt (V293_ready_inv 80%positive 81%positive 82%positive) ct **
     V293_read_bytes 92%positive 0%Z V293_ready_table).
Proof.
  intro ct.
  assert (Outputs : V293_target_wstate RTge RTle RToutputs emp |=
    V293_owned_record_cell ((90%positive,0%Z),Tint8,V293_byteval 99) **
    V293_owned_record_cell ((91%positive,0%Z),Tint8,V293_byteval 88)).
  { pose proof (OwnershipCellsSpatial RToutput_cells ltac:(vm_compute;repeat split;intros;intuition congruence)
      ltac:(repeat constructor;vm_compute;reflexivity) RTge RTle) as Out.
    cbn [RToutput_cells V293_owned_record_cells] in Out. sep auto. }
  assert (First : V293_target_wstate RTge RTle (RTwith_outputs ct) (RIabstract ct) |=
    SWINVt (V293_ready_inv 80%positive 81%positive 82%positive) ct **
    (V293_owned_record_cell ((90%positive,0%Z),Tint8,V293_byteval 99) **
     V293_owned_record_cell ((91%positive,0%Z),Tint8,V293_byteval 88))).
  { eapply V293_target_wstate_star with (m1:=RTfull ct) (m2:=RToutputs)
      (o1:=RIabstract ct) (o2:=emp).
    - apply RToutputs_join.
    - apply map_join_emp.
    - apply RTenv_spatial. vm_compute;reflexivity.
    - exact Outputs. }
  assert (Raw : V293_target_wstate RTge RTle (RTexec_memory ct) (RIabstract ct) |=
    (SWINVt (V293_ready_inv 80%positive 81%positive 82%positive) ct **
     (V293_owned_record_cell ((90%positive,0%Z),Tint8,V293_byteval 99) **
      V293_owned_record_cell ((91%positive,0%Z),Tint8,V293_byteval 88))) **
    V293_read_bytes 92%positive 0%Z V293_ready_table).
  { eapply V293_target_wstate_star with (m1:=RTwith_outputs ct) (m2:=RTdecoder)
      (o1:=RIabstract ct) (o2:=emp).
    - apply RTdecoder_join.
    - apply map_join_emp.
    - exact First.
    - apply V293_read_bytes_witness. }
  clear First Outputs. sep auto.
Qed.
Lemma RTdecoder_loads : forall ct n, n<256 ->
  load Tint8 (RTexec_memory ct) (92%positive,Z.of_nat n)=Some (V293_byteval (V293_ready_lookup n)).
Proof.
  intros ct n Bound.
  assert (RowBound : nth n V293_ready_table 0<256).
  { change (V293_ready_lookup n<256). pose proof (proj1 (V293_ready_row_spec n Bound)). lia. }
  eapply load_mem_mono with (M:=RTdecoder).
  - replace (Z.of_nat n) with (0+Z.of_nat n)%Z by lia.
    apply (V293_read_bytes_load V293_ready_table 92%positive 0%Z n Bound RowBound
      (V293_wstate emp emp RTdecoder)). apply V293_read_bytes_witness.
  - exists (RTwith_outputs ct). apply map_join_comm;apply RTdecoder_join.
Qed.
Theorem RTjoint_execution : forall P ks live, exists Mf,
  cstepstar P (curs (V293_OSSchedNew_updates 100%Z 101%Z 102%Z 103%Z 104%Z),(kenil,ks))
    (RTge,RTle,RTexec_memory (RIcurrent live))
    (curs (sskip None),(kenil,ks)) (RTge,RTle,Mf) /\
  V293_target_wstate RTge RTle Mf (RIabstract (RIcurrent live)) |=
    SWINVt (V293_ready_inv 80%positive 81%positive 82%positive) (RIcurrent live) ** Atrue /\
  load Tint8 Mf (91%positive,0%Z)=Some (V293_byteval 4) /\
  evalval (V293_OSSched_target_expr 105%Z 103%Z) (RTge,RTle,Mf)=Some (Vptr OwnershipReady) /\
  V293_task_records Mf OwnershipTasks /\
  (forall a, a<>(90%positive,0%Z) -> a<>(91%positive,0%Z) ->
    get Mf a=get (RTexec_memory (RIcurrent live)) a).
Proof.
  intros P ks live. set (ct:=RIcurrent live).
  destruct (V293_ready_sched_updates 80%positive 81%positive 82%positive P ks RTge RTle
    (RTexec_memory ct) (fun _=>false) (false,nil,nil) (RIabstract ct) (spec_done None)
    ct (V293_read_bytes 92%positive 0%Z V293_ready_table)
    100%Z 101%Z 102%Z 103%Z 104%Z 105%Z 92%positive 91%positive 90%positive
    (V293_byteval 99) (V293_byteval 88)
    ltac:(repeat split;vm_compute;reflexivity) eq_refl eq_refl eq_refl eq_refl eq_refl
    ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
    ltac:(discriminate) ltac:(discriminate) (RTdecoder_loads ct) (RTexec_entry ct))
    as (ts&lo&hi&es&t&msg&Mf&Lookup&Rel&Task&Execution&After&High&Value&TargetType&Sched&Frame).
  pose proof (RIfixed_tasks ct). assert (ts=OwnershipTasks) by congruence. subst ts.
  assert (SelectedBound : V293_ready_select lo hi (V293_ready_group lo hi)<13).
  { apply V293_ready_selection_range; [exact (proj1 Rel) | exact (proj1 (proj2 Rel)) | reflexivity | exact (proj1 (proj2 (proj2 Rel)))]. }
  destruct (RTonly_ready _ _ _ SelectedBound Task) as [Selected [Target Message]]. subst t.
  exists Mf. split; [exact Execution | ]. split.
  - sep auto.
  - split; [rewrite Selected in High;exact High | ]. split; [exact Value | ]. split.
    + assert (Inv : V293_target_wstate RTge RTle Mf (RIabstract ct) |=
        SWINVt (V293_ready_inv 80%positive 81%positive 82%positive) ct ** Atrue) by (sep auto).
      destruct (V293_ready_switch_sound _ _ _ _ _ _ Inv) as (ts&l&h&entries&Map&Records&Relation&Reads).
      change (get (RIabstract ct) abstcblsid=Some (abstcblist ts)) in Map.
      pose proof (RIfixed_tasks ct). assert (ts=OwnershipTasks) by congruence. subst ts. exact Records.
    + exact Frame.
Qed.
