(* Independent nonempty bytes. Retiming below constructs fixtures, not an
   execution or initialization theorem. Negative controls keep other fields. *)
Require Import CertiOS.certiucos.v293.proofs.V293TimeReadyShared.
Require Import CertiOS.certiucos.v293.proofs.V293TimeShared.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyTaskInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293SharedStateWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTargetWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTarget.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.audit.probes.V293TaskRecordOwnershipProbe.
Require Import CertiOS.audit.probes.V293TaskRecordInvariantProbe.
Require Import CertiOS.audit.probes.V293ReadyTaskInvariantProbe.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.memory_prop.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.framework.proof.lmachLib.
Require Import CertiOS.framework.proof.rulesoundlib.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Definition TRclock n := V293_encoded_memory 150%positive 0 true (encode_val Tint32 (Vint32 n)).
Definition TRabstract ct n := set (RIabstract ct) ostmid (ostm n).
Definition TRstate ct n M := V293_target_wstate V293_shared_fixture_ge emp M (TRabstract ct n).
Definition TRmemory ct n := merge (RTfull ct) (TRclock n).
Definition TRinv := V293_time_ready_inv 80%positive 81%positive 82%positive 150%positive.

Lemma TRretime : forall ct n,
  TRstate ct n (RTfull ct) |= SWINVt (V293_ready_inv 80%positive 81%positive 82%positive) ct.
Proof.
  intros ct n. pose proof (RTliteral_spatial ct) as H.
  apply V293_ready_switch_full in H. unfold V293_ready_full,V293_shared_fields in H.
  sep normal in H. sep destruct H.
  assert (Packed : RTstate ct (RTfull ct) |= Aabsdata ostmid (ostm x1) **
    (V293_shared_flags ** ((GV OSTCBCur @ (Tptr x2) |-> Vptr ct) **
      (Aabsdata curtid (oscurt ct) ** (Aabsdata abstcblsid (abstcblist x) **
        (Aabsdata absecblsid (absecblist x0) ** V293_ready_payload 80%positive 81%positive 82%positive x)))))).
  { clear -H. sep auto. }
  apply V293_shared_replace_slot with (new:=ostm n) in Packed.
  apply V293_ready_switch_halves. unfold V293_ready_full,V293_shared_fields.
  clear H. sep auto.
Qed.

Lemma TRclock_join : forall ct n, join (RTfull ct) (TRclock n) (TRmemory ct n).
Proof.
  intros ct n. apply map_join_merge. apply map_disjoint. intros [b off].
  destruct (Pos.eq_dec b 150%positive) as [E | E].
  - subst b. left. unfold RTfull,RImemory,RTmemory,OwnershipMemory,V293_shared_fixture_mem.
    repeat rewrite map_merge_semp by reflexivity.
    rewrite V293_encoded_memory_outside by (left;discriminate).
    repeat rewrite OwnershipCellsOutside by
      (intro Member; vm_compute in Member; intuition congruence). reflexivity.
  - right;left. apply V293_encoded_memory_outside;left;exact E.
Qed.

Theorem TRliteral_spatial : forall ct n,
  TRstate ct n (TRmemory ct n) |= SWINVt TRinv ct.
Proof.
  intros ct n.
  assert (Raw : TRstate ct n (TRmemory ct n) |=
    SWINVt (V293_ready_inv 80%positive 81%positive 82%positive) ct **
      PV (150%positive,Int.zero) @ Tint32 |-> Vint32 n).
  { eapply V293_target_wstate_star with (m1:=RTfull ct) (m2:=TRclock n)
      (o1:=TRabstract ct n) (o2:=emp).
    - apply TRclock_join.
    - apply map_join_emp.
    - apply TRretime.
    - split;[apply V293_encoded_memory_mapsto | reflexivity]. }
  assert (Opened : TRstate ct n (TRmemory ct n) |=
    (V293_shared_flags ** V293_ready_full 80%positive 81%positive 82%positive ct) **
      PV (150%positive,Int.zero) @ Tint32 |-> Vint32 n).
  { eapply astar_mono;[apply V293_ready_switch_full | intros st H;exact H | exact Raw]. }
  unfold V293_ready_full in Opened. sep normal in Opened. sep destruct Opened.
  assert (Time : get (TRabstract ct n) ostmid=Some(ostm x1)).
  { change (get (getabst (TRstate ct n (TRmemory ct n))) ostmid=Some(ostm x1)).
    eapply V293_star_abst_get_l with (p:=Aabsdata ostmid (ostm x1)) (q:=Atrue).
    - apply V293_shared_abs_get.
    - unfold V293_shared_fields in Opened. clear Raw. sep auto. }
  unfold TRabstract in Time. rewrite map_get_set in Time. assert (x1=n) by congruence. subst x1.
  unfold TRinv. apply V293_time_ready_switch_full_close.
  unfold V293_time_ready_switch_full,V293_time_ready_switch_fields.
  clear Raw Time. sep auto.
Qed.

Lemma TRclock_load : forall ct n,
  load Tint32 (TRmemory ct n) (150%positive,0%Z)=Some(Vint32 n).
Proof.
  intros ct n. eapply load_mem_mono with (M:=TRclock n).
  - eapply mapstoval_load;[reflexivity | apply V293_encoded_memory_mapsto].
  - exists (RTfull ct). apply map_join_comm;apply TRclock_join.
Qed.
Lemma TRready_loads : forall ct n,
  V293_ready_loads (TRmemory ct n) 80%positive 81%positive 82%positive 16 0 RTentries.
Proof.
  intros ct n. eapply V293_ready_loads_sub;[exists (TRclock n);apply TRclock_join | apply RTliteral_loads].
Qed.
Lemma TRreject_clock : forall ct n bad,
  bad<>n -> ~ TRstate ct n (TRmemory ct bad) |= SWINVt TRinv ct.
Proof.
  intros ct n bad Different Held.
  apply V293_time_ready_switch_core_frame in Held.
  destruct (V293_time_ready_clock_agreement _ _ _ _ _ _ Held) as [clock [Time Physical]].
  change (get (TRabstract ct n) ostmid=Some(ostm clock)) in Time.
  unfold TRabstract in Time. rewrite map_get_set in Time.
  change (load Tint32 (TRmemory ct bad) (150%positive,0%Z)=Some(Vint32 clock)) in Physical.
  pose proof (TRclock_load ct bad). assert (clock=n) by congruence. congruence.
Qed.

(* The old abstract time is deliberately retained while the physical value
   changes. These are constructed byte states, not runs of a deleted AST. *)
Theorem TRclock_ablation : forall ct n bad,
  bad<>n ->
  TRstate ct n (TRmemory ct n) |= SWINVt TRinv ct /\
  V293_ready_loads (TRmemory ct bad) 80%positive 81%positive 82%positive 16 0 RTentries /\
  (forall b off, b<>150%positive -> get (TRmemory ct bad) (b,off)=get (TRmemory ct n) (b,off)) /\
  ~ TRstate ct n (TRmemory ct bad) |= SWINVt TRinv ct.
Proof.
  intros ct n bad Different. split;[apply TRliteral_spatial | ].
  split;[apply TRready_loads | ]. split;[ | apply TRreject_clock;exact Different].
  intros b off Apart. unfold TRmemory,TRclock. repeat rewrite map_merge_semp by reflexivity.
  repeat rewrite V293_encoded_memory_outside by (left;exact Apart). reflexivity.
Qed.
Theorem TRincrement_ablation_cases :
  ~ TRstate OwnershipWaiting Int.zero (TRmemory OwnershipWaiting Int.one) |= SWINVt TRinv OwnershipWaiting /\
  ~ TRstate OwnershipWaiting (Int.repr 4294967295) (TRmemory OwnershipWaiting Int.zero) |= SWINVt TRinv OwnershipWaiting /\
  Int.add (Int.repr 4294967295) Int.one=Int.zero.
Proof.
  split;[apply TRreject_clock;vm_compute;discriminate | ].
  split;[apply TRreject_clock;vm_compute;discriminate | vm_compute;apply Int.mkint_eq;reflexivity].
Qed.

Lemma TRreject_ready_32 : forall ct n M,
  load Tint8 M (80%positive,0%Z)=Some(V293_byteval 32) ->
  ~ TRstate ct n M |= SWINVt TRinv ct.
Proof.
  intros ct n M Wrong Held. apply V293_time_ready_switch_project in Held.
  destruct (V293_ready_switch_sound _ _ _ _ _ _ Held) as (ts&lo&hi&es&Lookup&Records&Rel&Reads).
  change (get (TRabstract ct n) abstcblsid=Some(abstcblist ts)) in Lookup.
  unfold TRabstract in Lookup. rewrite map_get_set' in Lookup by discriminate.
  pose proof (RIfixed_tasks ct). assert (ts=OwnershipTasks) by congruence. subst ts.
  destruct Rel as [Lo [Hi [Nonempty [Bitmap Table]]]]. destruct Reads as [Low Rest].
  change (load Tint8 M (80%positive,0%Z)=Some(V293_byteval lo)) in Low.
  assert (L32 : lo=32).
  { eapply RTbyte_injective;[exact Lo | lia | congruence]. } subst lo.
  assert (Ready : exists t m, get OwnershipTasks t=Some(Int.repr(Z.of_nat 4),rdy,m)).
  { exists OwnershipReady. exists Vnull. vm_compute;reflexivity. }
  apply (proj2 (Bitmap 4 ltac:(lia))) in Ready. vm_compute in Ready. intuition lia.
Qed.

(* Change just the low ready byte 16 -> 32. Both bitmaps are nonempty and
   have group=1, so nonemptiness/group consistency cannot explain rejection.
   Priority 4's task is still ready in the same abstract task map. *)
Theorem TRready_ablation : forall ct n, exists Mf,
  TRstate ct n (TRmemory ct n) |= SWINVt TRinv ct /\
  store Tint8 (TRmemory ct n) (80%positive,0%Z) (V293_byteval 32)=Some Mf /\
  (forall a, a<>(80%positive,0%Z) -> get Mf a=get (TRmemory ct n) a) /\
  load Tint8 Mf (80%positive,0%Z)=Some(V293_byteval 32) /\
  load Tint32 Mf (150%positive,0%Z)=Some(Vint32 n) /\
  V293_bitmap_ready 32 0 5 /\
  V293_ready_group 32 0=V293_ready_group 16 0 /\
  ~ TRstate ct n Mf |= SWINVt TRinv ct.
Proof.
  intros ct n.
  assert (Packed : V293_target_wstate V293_shared_fixture_ge emp (TRmemory ct n) (RIabstract ct) |=
    (V293_owned_record_cells RTcells ** SWINVt V293_records_inv ct) **
      PV (150%positive,Int.zero) @ Tint32 |-> Vint32 n).
  { eapply V293_target_wstate_star with (m1:=RTfull ct) (m2:=TRclock n)
      (o1:=RIabstract ct) (o2:=emp).
    - apply TRclock_join.
    - apply map_join_emp.
    - apply RTrecords_cells.
    - split;[apply V293_encoded_memory_mapsto | reflexivity]. }
  assert (Raw : V293_target_wstate V293_shared_fixture_ge emp (TRmemory ct n) (RIabstract ct) |=
    V293_owned_record_cell ((80%positive,0%Z),Tint8,V293_byteval 16) **
    (V293_owned_record_cells (tl RTcells) ** (SWINVt V293_records_inv ct **
      PV (150%positive,Int.zero) @ Tint32 |-> Vint32 n))).
  { change (V293_target_wstate V293_shared_fixture_ge emp (TRmemory ct n) (RIabstract ct) |=
      ((V293_owned_record_cell ((80%positive,0%Z),Tint8,V293_byteval 16) **
        V293_owned_record_cells (tl RTcells)) ** SWINVt V293_records_inv ct) **
        PV (150%positive,Int.zero) @ Tint32 |-> Vint32 n) in Packed. sep auto. }
  destruct (V293_owned_byte_update _ _ 32 _ _ _ _ _ _ _ _ ltac:(lia) Raw) as [[v Writable] After].
  set (Mf:=V293_put_byte (TRmemory ct n) (80%positive,0%Z) 32) in *.
  assert (Byte : load Tint8 Mf (80%positive,0%Z)=Some(V293_byteval 32)).
  { apply V293_put_byte_load. lia. }
  assert (Clock : load Tint32 Mf (150%positive,0%Z)=Some(Vint32 n)).
  { assert (Cell : V293_target_wstate V293_shared_fixture_ge emp Mf (RIabstract ct) |=
      (PV (150%positive,Int.zero) @ Tint32 |-> Vint32 n) ** Atrue) by (clear Packed Raw;sep auto).
    change (load Tint32 (getmem (V293_target_wstate V293_shared_fixture_ge emp Mf (RIabstract ct)))
      (150%positive,0%Z)=Some(Vint32 n)).
    eapply V293_star_load_l;[ | exact Cell]. intros st [P _]. eapply mapstoval_load;[reflexivity | exact P]. }
  exists Mf. split;[apply TRliteral_spatial | ]. split.
  - apply V293_put_byte_store with (old:=v). exact Writable.
  - split.
    + intros a Apart. unfold Mf,V293_put_byte. apply map_get_set'. congruence.
    + split;[exact Byte | ]. split;[exact Clock | ].
      split;[vm_compute;auto | ]. split;[reflexivity | apply TRreject_ready_32;exact Byte].
Qed.

Theorem TRclosed_good : GoodI TRinv V293_scheduler V293_shared_li.
Proof. apply V293_time_ready_good. Qed.
