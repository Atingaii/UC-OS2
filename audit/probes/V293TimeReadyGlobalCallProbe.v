Require Import CertiOS.certiucos.v293.proofs.V293TimeSourceAPI.
Require Import CertiOS.certiucos.v293.proofs.V293TimeSourceReadyCall.
Require Import CertiOS.certiucos.v293.proofs.V293ReadySwitchStep.
Require Import CertiOS.certiucos.v293.proofs.V293TimeAPICall.
Require Import CertiOS.certiucos.v293.proofs.V293TimeShared.
Require Import CertiOS.certiucos.v293.proofs.V293TimeSharedSet.
Require Import CertiOS.certiucos.v293.proofs.V293TimeGetAPI.
Require Import CertiOS.certiucos.v293.proofs.V293TimeSetAPI.
Require Import CertiOS.certiucos.v293.proofs.V293TimeAccess.
Require Import CertiOS.certiucos.v293.code.V293TimeSource.
Require Import CertiOS.certiucos.v293.proofs.V293TimeReadyShared.
Require Import CertiOS.certiucos.v293.proofs.V293TimeReadyEntry.
Require Import Coq.Lists.List.
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

Require Import CertiOS.certiucos.v293.proofs.V293TimeReadyGlobalCall.
Require Import CertiOS.audit.probes.V293TimeSourceReadyCallProbe.

(* The unused table slot0 aliases the ready task, permitted by the existing
   one-way ready relation. This is not canonical initialization or a scheduler
   selection proof. Both canonical task records and bitmap16 are unchanged. *)
Definition GGE : env := set (set V293_shared_fixture_ge 1001%Z (150%positive,Tint32))
  1040%Z (82%positive,Tptr Tvoid).
Definition GRstate ct M := V293_target_wstate GGE emp M (RIabstract ct).
Theorem GRliteral_spatial : forall ct, GRstate ct (RImemory ct) |= SWINVt V293_records_inv ct.
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
    + exists Tvoid. exact (V293_shared_fixture_pointer ct).
    + eapply V293_target_wstate_star with (m1:=emp) (m2:=OwnershipMemory)
        (o1:=RIabstract ct) (o2:=emp).
      * apply map_join_comm; apply map_join_emp.
      * apply map_join_emp.
      * apply V293_shared_fixture_fields.
      * eapply V293_task_list_context. exact OwnershipLiteralSpatial.
Qed.
Definition GRTentries : list val :=
  [Vptr OwnershipReady;Vnull;Vnull;Vnull;Vptr OwnershipReady;Vnull;Vptr OwnershipWaiting;
   Vnull;Vnull;Vnull;Vnull;Vnull;Vnull].
Definition GRTcells := V293_ready_cells 80%positive 81%positive 82%positive 16 0 GRTentries.
Definition GRTmemory := OwnershipCellsMemory GRTcells.
Definition GRTfull ct := merge (RImemory ct) GRTmemory.
Definition GRTstate ct M := GRstate ct M.

Lemma GRTonly_ready : forall p t m,
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
Lemma GRTliteral_rel : V293_ready_rel 16 0 GRTentries OwnershipTasks.
Proof.
  split; [lia | ]. split; [lia | ]. split.
  - exists 4. left. split; [lia | vm_compute; reflexivity].
  - split.
    + intros p Bound. assert (Bit : V293_bitmap_ready 16 0 p <-> p=4).
      { do 13 (destruct p as [ | p]; [vm_compute; intuition lia | ]). lia. }
      rewrite Bit. split.
      * intro E. subst p. exists OwnershipReady. exists Vnull. vm_compute; reflexivity.
      * intros (t&m&H). exact (proj1 (GRTonly_ready _ _ _ Bound H)).
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
Lemma GRTliteral_separated : OwnershipCellsSeparated GRTcells.
Proof. vm_compute. repeat split; intros; intuition congruence. Qed.
Lemma GRTliteral_valid : Forall
  (fun cell => let '(_,tp,v) := cell in rule_type_val_match tp v=true) GRTcells.
Proof. repeat constructor; vm_compute; reflexivity. Qed.
Lemma GRTliteral_cells : V293_wstate emp emp GRTmemory  |= V293_owned_record_cells GRTcells.
Proof. apply OwnershipCellsSpatial; [exact GRTliteral_separated | exact GRTliteral_valid]. Qed.
Lemma GRTliteral_ready : V293_wstate emp emp GRTmemory  |=
  V293_ready_owned 80%positive 81%positive 82%positive OwnershipTasks.
Proof. exists 16. exists 0. exists GRTentries.
  apply astar_l_apure_intro; [exact GRTliteral_cells | exact GRTliteral_rel]. Qed.
Lemma GRTjoin : forall ct, join (RImemory ct) GRTmemory (GRTfull ct).
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
Theorem GRTliteral_spatial : forall ct,
  GRTstate ct (GRTfull ct)  |= SWINVt (V293_ready_inv 80%positive 81%positive 82%positive) ct.
Proof.
  intro ct.
  assert (Raw : GRTstate ct (GRTfull ct)  |= SWINVt V293_records_inv ct **
    V293_ready_owned 80%positive 81%positive 82%positive OwnershipTasks).
  { eapply V293_target_wstate_star with (m1:=RImemory ct) (m2:=GRTmemory)
      (o1:=RIabstract ct) (o2:=emp).
    - apply GRTjoin.
    - apply map_join_emp.
    - exact (GRliteral_spatial ct).
    - exists 16. exists 0. exists GRTentries. apply astar_l_apure_intro.
      + eapply V293_owned_cells_context; exact GRTliteral_cells.
      + exact GRTliteral_rel.
  }
  assert (Opened : GRTstate ct (GRTfull ct)  |=
    (V293_shared_flags ** V293_records_full ct) **
    V293_ready_owned 80%positive 81%positive 82%positive OwnershipTasks).
  { eapply astar_mono; [apply V293_records_switch_full | intros st H;exact H | exact Raw]. }
  unfold V293_records_full in Opened. sep normal in Opened. sep destruct Opened.
  assert (Fixed : x=OwnershipTasks).
  { assert (Lookup : get (RIabstract ct) abstcblsid=Some (abstcblist x)).
    { change (get (getabst (GRTstate ct (GRTfull ct))) abstcblsid=Some (abstcblist x)).
      eapply V293_star_abst_get_l with (p:=Aabsdata abstcblsid (abstcblist x)) (q:=Atrue).
      - apply V293_shared_abs_get.
      - unfold V293_shared_fields in Opened. clear Raw. sep auto. }
    pose proof (RIfixed_tasks ct). congruence. } subst x.
  apply V293_ready_switch_halves. unfold V293_ready_full,V293_ready_payload.
  clear Raw. sep auto.
Qed.

Lemma GRTrecords_cells : forall ct,
  GRTstate ct (GRTfull ct) |= V293_owned_record_cells GRTcells ** SWINVt V293_records_inv ct.
Proof.
  intro ct. apply astar_comm.
  eapply V293_target_wstate_star with (m1:=RImemory ct) (m2:=GRTmemory)
    (o1:=RIabstract ct) (o2:=emp).
  - apply GRTjoin.
  - apply map_join_emp.
  - apply GRliteral_spatial.
  - eapply V293_owned_cells_context; exact GRTliteral_cells.
Qed.
Lemma GRTliteral_loads : forall ct,
  V293_ready_loads (GRTfull ct) 80%positive 81%positive 82%positive 16 0 GRTentries.
Proof.
  intro ct. eapply V293_ready_loads_sub with (M:=GRTmemory).
  - exists (RImemory ct). apply map_join_comm; apply GRTjoin.
  - exact (V293_ready_cells_loads 80%positive 81%positive 82%positive 16 0 GRTentries (V293_wstate emp emp GRTmemory)
      eq_refl GRTliteral_cells).
Qed.
Definition GTRclock n := V293_encoded_memory 150%positive 0 true (encode_val Tint32 (Vint32 n)).
Definition GTRabstract ct n := set (RIabstract ct) ostmid (ostm n).
Definition GTRstate ct n M := V293_target_wstate GGE emp M (GTRabstract ct n).
Definition GTRmemory ct n := merge (GRTfull ct) (GTRclock n).
Definition GTRinv := V293_time_ready_inv 80%positive 81%positive 82%positive 150%positive.

Lemma GTRretime : forall ct n,
  GTRstate ct n (GRTfull ct) |= SWINVt (V293_ready_inv 80%positive 81%positive 82%positive) ct.
Proof.
  intros ct n. pose proof (GRTliteral_spatial ct) as H.
  apply V293_ready_switch_full in H. unfold V293_ready_full,V293_shared_fields in H.
  sep normal in H. sep destruct H.
  assert (Packed : GRTstate ct (GRTfull ct) |= Aabsdata ostmid (ostm x1) **
    (V293_shared_flags ** ((GV OSTCBCur @ (Tptr x2) |-> Vptr ct) **
      (Aabsdata curtid (oscurt ct) ** (Aabsdata abstcblsid (abstcblist x) **
        (Aabsdata absecblsid (absecblist x0) ** V293_ready_payload 80%positive 81%positive 82%positive x)))))).
  { clear -H. sep auto. }
  apply V293_shared_replace_slot with (new:=ostm n) in Packed.
  apply V293_ready_switch_halves. unfold V293_ready_full,V293_shared_fields.
  clear H. sep auto.
Qed.

Lemma GTRclock_join : forall ct n, join (GRTfull ct) (GTRclock n) (GTRmemory ct n).
Proof.
  intros ct n. apply map_join_merge. apply map_disjoint. intros [b off].
  destruct (Pos.eq_dec b 150%positive) as [E | E].
  - subst b. left. unfold GRTfull,RImemory,GRTmemory,OwnershipMemory,V293_shared_fixture_mem.
    repeat rewrite map_merge_semp by reflexivity.
    rewrite V293_encoded_memory_outside by (left;discriminate).
    repeat rewrite OwnershipCellsOutside by
      (intro Member; vm_compute in Member; intuition congruence). reflexivity.
  - right;left. apply V293_encoded_memory_outside;left;exact E.
Qed.

Theorem GTRliteral_spatial : forall ct n,
  GTRstate ct n (GTRmemory ct n) |= SWINVt GTRinv ct.
Proof.
  intros ct n.
  assert (Raw : GTRstate ct n (GTRmemory ct n) |=
    SWINVt (V293_ready_inv 80%positive 81%positive 82%positive) ct **
      PV (150%positive,Int.zero) @ Tint32 |-> Vint32 n).
  { eapply V293_target_wstate_star with (m1:=GRTfull ct) (m2:=GTRclock n)
      (o1:=GTRabstract ct n) (o2:=emp).
    - apply GTRclock_join.
    - apply map_join_emp.
    - apply GTRretime.
    - split;[apply V293_encoded_memory_mapsto | reflexivity]. }
  assert (Opened : GTRstate ct n (GTRmemory ct n) |=
    (V293_shared_flags ** V293_ready_full 80%positive 81%positive 82%positive ct) **
      PV (150%positive,Int.zero) @ Tint32 |-> Vint32 n).
  { eapply astar_mono;[apply V293_ready_switch_full | intros st H;exact H | exact Raw]. }
  unfold V293_ready_full in Opened. sep normal in Opened. sep destruct Opened.
  assert (Time : get (GTRabstract ct n) ostmid=Some(ostm x1)).
  { change (get (getabst (GTRstate ct n (GTRmemory ct n))) ostmid=Some(ostm x1)).
    eapply V293_star_abst_get_l with (p:=Aabsdata ostmid (ostm x1)) (q:=Atrue).
    - apply V293_shared_abs_get.
    - unfold V293_shared_fields in Opened. clear Raw. sep auto. }
  unfold GTRabstract in Time. rewrite map_get_set in Time. assert (x1=n) by congruence. subst x1.
  unfold GTRinv. apply V293_time_ready_switch_full_close.
  unfold V293_time_ready_switch_full,V293_time_ready_switch_fields.
  clear Raw Time. sep auto.
Qed.


Definition Gtasks f args ks := set
  (sig OwnershipWaiting (curs(sprim(switch 1040%Z)),(kenil,ks)))
  OwnershipReady (curs(scall f args),(kenil,ks)).
Definition Gles selected := set (sig OwnershipWaiting (emp : env)) OwnershipReady selected.
Definition Gaux enabled := set (sig OwnershipWaiting (false,[],[])) OwnershipReady (enabled,[],[]).
Definition Gswitch pc ip cst ks selected clock enabled f args Ms :=
  lpstep(pc,(SRprogram,(fun _ => None),ip))(Gtasks f args ks)cst
    (GGE,Gles selected,GTRmemory OwnershipWaiting clock,empisr,Gaux enabled)OwnershipWaiting
    (set(Gtasks f args ks)OwnershipWaiting(SKIP,(kenil,ks)))cst
    (GGE,Gles selected,Ms,empisr,Gaux enabled)OwnershipReady.
Definition Gstate selected enabled M O op : RstateOP :=
  (GGE,selected,M,empisr,(enabled,[],[]),O,op).
Definition Gafter clock := set(GTRabstract OwnershipWaiting clock)curtid(oscurt OwnershipReady).

Lemma Gtarget : forall clock,
  load(Tptr Tvoid)(GTRmemory OwnershipWaiting clock)(82%positive,0%Z)=Some(Vptr OwnershipReady).
Proof.
  intro clock. eapply load_mem_mono with(M:=GRTfull OwnershipWaiting).
  - exact(proj2(proj2(proj2(GRTliteral_loads OwnershipWaiting)))0 ltac:(lia)).
  - exists(GTRclock clock);apply GTRclock_join.
Qed.
Lemma Gfresh : forall clock b,
  b=160%positive \/ b=161%positive -> fresh(GTRmemory OwnershipWaiting clock)b.
Proof.
  intros clock b B l i Equal [v Bound];subst l.
  change(get(GTRmemory OwnershipWaiting clock)(b,i)=Some v)in Bound.
  assert(Empty:get(GTRmemory OwnershipWaiting clock)(b,i)=None).
  { destruct B;subst b;unfold GTRmemory,GRTfull,RImemory,GRTmemory,OwnershipMemory,
      V293_shared_fixture_mem,GTRclock;repeat rewrite map_merge_semp by reflexivity;
      repeat rewrite V293_encoded_memory_outside by(left;discriminate);
      repeat rewrite OwnershipCellsOutside by(intro H;vm_compute in H;intuition congruence);reflexivity. }
  congruence.
Qed.
Lemma Ginput : forall clock op,
  (GGE,emp,GTRmemory OwnershipWaiting clock,empisr,(false,[],[]),GTRabstract OwnershipWaiting clock,op) |=
    SWINVt GTRinv OwnershipWaiting.
Proof. intros. exact(swinv_aop_irev _ _ _ _ _ (GTRliteral_spatial OwnershipWaiting clock) op). Qed.
Lemma Gslot : forall clock,get(GTRabstract OwnershipWaiting clock)ostmid=Some(ostm clock).
Proof. intros;unfold GTRabstract;apply map_get_set. Qed.
Lemma Gcurrent : forall clock,get(GTRabstract OwnershipWaiting clock)curtid=Some(oscurt OwnershipWaiting).
Proof.
  intros;unfold GTRabstract;rewrite map_get_set' by discriminate.
  exact(proj1(V293_shared_fields_get _ _ _ _ _
    (V293_shared_fixture_fields OwnershipWaiting OwnershipTasks (emp : EcbMod.map) Int.zero))).
Qed.

Theorem Gget_nonempty_both_IE : forall pc ip cst ks selected clock enabled,
  exists Ms Mc Mf,
    Gswitch pc ip cst ks selected clock enabled 203%Z [] Ms /\
    V293_local_steps(pumerge SRprogram(fun _ => None))(curs(scall 203%Z []),(kenil,ks))
      ((GGE,selected,Ms),empisr,(enabled,[],[]))
      (curs(sskip(Some(Vint32 clock))),(kenil,ks))((GGE,selected,Mf),empisr,(enabled,[],[])) /\
    spec_step V293_scheduler V293_time_get_action(Gafter clock)(END(Some(Vint32 clock)))(Gafter clock) /\
    Gstate selected enabled Mf(Gafter clock)(END(Some(Vint32 clock))) |= SRcore ** CurTid OwnershipReady /\
    load Tint32 Mf(150%positive,0%Z)=Some(Vint32 clock) /\
    (forall k,k<4 ->get Mf(160%positive,Z.of_nat k)=None /\get Mf(161%positive,Z.of_nat k)=None) /\
    freels(getaddr(V293_time_call_locals 1002%Z 1003%Z 160%positive 161%positive))Mc Mf.
Proof.
  intros pc ip cst ks selected clock enabled.
  assert(Code:SRprogram 203%Z=Some(V293_source_OSTimeGet_function 1001%Z 1002%Z 1003%Z)).
  { exact(proj1(V293_source_time_entries 203%Z 202%Z 1001%Z 1002%Z 1003%Z ltac:(discriminate))). }
  destruct(V293_time_switch_source_get 80%positive 81%positive 82%positive 150%positive
    pc SRprogram(fun _ => None)ip(Gtasks 203%Z [] ks)cst ks ks OwnershipWaiting OwnershipReady
    1040%Z 82%positive 1%positive GGE emp selected(Gles selected)(GTRmemory OwnershipWaiting clock)
    empisr(false,[],[])enabled [] [](Gaux enabled)(GTRabstract OwnershipWaiting clock)Tvoid
    V293_scheduler 203%Z 1001%Z 1002%Z 1003%Z 160%positive 161%positive clock
    Code ltac:(discriminate)eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl(Gtarget clock)eq_refl
    ltac:(discriminate)ltac:(discriminate)ltac:(discriminate)eq_refl
    (Gfresh clock _ (or_introl eq_refl))(Gfresh clock _ (or_intror eq_refl))
    ltac:(discriminate)ltac:(discriminate)ltac:(discriminate)(Gslot clock)(Ginput clock V293_time_get_action))
    as(Ms&Mc&Mf&Switch&NextCode&Store&Exec&Step&Final&Freed).
  exists Ms. exists Mc. exists Mf. split;[exact Switch | ]. split;[exact Exec | ].
  split;[exact Step | ]. split;[exact Final | ]. split.
  - eapply V293_source_time_clock_owned;[ | exact Final].
    unfold Gafter;rewrite map_get_set' by discriminate;apply Gslot.
  - split;[eapply SRremoved;exact Freed | exact Freed].
Qed.

Theorem Gset_nonempty_both_IE : forall pc ip cst ks selected clock enabled n,
  exists Ms Mc Mf,
    Gswitch pc ip cst ks selected clock enabled 202%Z [econst32 n] Ms /\
    V293_local_steps(pumerge SRprogram(fun _ => None))(curs(scall 202%Z [econst32 n]),(kenil,ks))
      ((GGE,selected,Ms),empisr,(enabled,[],[]))
      (curs(sskip None),(kenil,ks))((GGE,selected,Mf),empisr,(enabled,[],[])) /\
    spec_step V293_scheduler(V293_time_set_action n)(Gafter clock)(END None)(set(Gafter clock)ostmid(ostm n)) /\
    Gstate selected enabled Mf(set(Gafter clock)ostmid(ostm n))(END None) |= SRcore ** CurTid OwnershipReady /\
    load Tint32 Mf(150%positive,0%Z)=Some(Vint32 n) /\
    (forall k,k<4 ->get Mf(160%positive,Z.of_nat k)=None /\get Mf(161%positive,Z.of_nat k)=None) /\
    freels(getaddr(V293_time_call_locals 1002%Z 1003%Z 160%positive 161%positive))Mc Mf.
Proof.
  intros pc ip cst ks selected clock enabled n.
  assert(Code:SRprogram 202%Z=Some(V293_source_OSTimeSet_function 1001%Z 1002%Z 1003%Z)).
  { exact(proj1(proj2(V293_source_time_entries 203%Z 202%Z 1001%Z 1002%Z 1003%Z ltac:(discriminate)))). }
  destruct(V293_time_switch_source_set 80%positive 81%positive 82%positive 150%positive
    pc SRprogram(fun _ => None)ip(Gtasks 202%Z [econst32 n] ks)cst ks ks OwnershipWaiting OwnershipReady
    1040%Z 82%positive 1%positive GGE emp selected(Gles selected)(GTRmemory OwnershipWaiting clock)
    empisr(false,[],[])enabled [] [](Gaux enabled)(GTRabstract OwnershipWaiting clock)Tvoid
    V293_scheduler 202%Z 1001%Z 1002%Z 1003%Z 160%positive 161%positive clock n
    Code ltac:(discriminate)eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl(Gtarget clock)eq_refl
    ltac:(discriminate)ltac:(discriminate)ltac:(discriminate)eq_refl
    (Gfresh clock _ (or_introl eq_refl))(Gfresh clock _ (or_intror eq_refl))
    ltac:(discriminate)ltac:(discriminate)ltac:(discriminate)(Gslot clock)(Ginput clock(V293_time_set_action n)))
    as(Ms&Mc&Mf&Switch&NextCode&Store&Exec&Step&Final&Freed).
  exists Ms. exists Mc. exists Mf. split;[exact Switch | ]. split;[exact Exec | ].
  split;[exact Step | ]. split;[exact Final | ]. split.
  - eapply V293_source_time_clock_owned;[apply map_get_set | exact Final].
  - split;[eapply SRremoved;exact Freed | exact Freed].
Qed.

Theorem Gfixture_nonempty_canonical_records :
  get OwnershipTasks OwnershipReady=Some(Int.repr 4,rdy,Vnull) /\
  get OwnershipTasks OwnershipWaiting=Some(Int.repr 6,
    wait(os_stat_sem(72%positive,Int.repr 5))Int.one,Vptr(120%positive,Int.repr 7)) /\
  V293_highest_ready OwnershipTasks OwnershipReady /\
  nth 0 GRTentries Vnull=Vptr OwnershipReady /\
  nth 4 GRTentries Vnull=Vptr OwnershipReady.
Proof. split;[reflexivity | ]. split;[reflexivity | ]. split;[apply RIhighest | auto]. Qed.

(* Same actual switch, physical heap, selected context and clock. Only the
   interpretation of the abstract current slot is retained at its old value. *)
Theorem Gswitch_stale_current_control : forall pc ip cst ks selected clock enabled,
  exists Ms,
    Gswitch pc ip cst ks selected clock enabled 203%Z [] Ms /\
    store(Tptr Tvoid)(GTRmemory OwnershipWaiting clock)(1%positive,0%Z)(Vptr OwnershipReady)=Some Ms /\
    load(Tptr Tvoid)Ms(1%positive,0%Z)=Some(Vptr OwnershipReady) /\
    Gstate selected enabled Ms(Gafter clock)V293_time_get_action |= SRcore ** CurTid OwnershipReady /\
    ~ Gstate selected enabled Ms(GTRabstract OwnershipWaiting clock)V293_time_get_action |= SRcore ** CurTid OwnershipReady /\
    (forall b i,b<>1%positive ->get Ms(b,i)=get(GTRmemory OwnershipWaiting clock)(b,i)).
Proof.
  intros pc ip cst ks selected clock enabled.
  destruct(V293_time_ready_global_switch 80%positive 81%positive 82%positive 150%positive
    pc SRprogram(fun _ => None)ip(Gtasks 203%Z [] ks)cst ks OwnershipWaiting OwnershipReady
    1040%Z 82%positive 1%positive GGE emp selected(Gles selected)(GTRmemory OwnershipWaiting clock)
    empisr(false,[],[])(enabled,[],[])(Gaux enabled)(GTRabstract OwnershipWaiting clock)
    V293_time_get_action Tvoid eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl(Gtarget clock)eq_refl
    (Ginput clock V293_time_get_action))as(Ms&Switch&Store&Strong&Load&Outside).
  exists Ms. split;[exact Switch | ]. split;[exact Store | ]. split;[exact Load | ].
  split;[exact Strong | ]. split.
  - intro Wrong. destruct(V293_time_ready_current_owned 80%positive 81%positive 82%positive 150%positive
      (CurTid OwnershipReady)GGE selected Ms empisr(enabled,[],[])(GTRabstract OwnershipWaiting clock)
      V293_time_get_action Wrong)as(t&b&tp&Slot&Name&Read).
    rewrite Gcurrent in Slot. assert(t=OwnershipWaiting)by congruence;subst t.
    change(Some(1%positive,Tptr Tvoid)=Some(b,Tptr tp))in Name.
    inversion Name;subst b tp.
    change(load(Tptr Tvoid)Ms(1%positive,0%Z)=Some(Vptr OwnershipWaiting))in Read.
    assert(Same:Some(Vptr OwnershipReady)=Some(Vptr OwnershipWaiting))
      by exact(eq_trans(eq_sym Load)Read). discriminate Same.
  - intros b i Apart;apply Outside;left;exact Apart.
Qed.
