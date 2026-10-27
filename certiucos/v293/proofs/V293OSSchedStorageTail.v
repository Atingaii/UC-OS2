(* Borrowed full-write globals return to the shared invariant BEFORE switch.
   Only environment bindings and actual thread-private Px cross as a frame. *)
Require Import CertiOS.certiucos.v293.proofs.V293DispatchStorage.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchState.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedSwitch.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedSwitchPre.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCurrent.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedChange.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.certiucos.v293.code.V293OSSchedChange.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Definition V293_storage_open target tp tid tasks events now next :=
  V293_shared_flags ** ((CurTid tid ** V293_shared_fields tid tasks events now) **
    (GV target @ (Tptr tp) |-> (Vptr next))).
Lemma V293_storage_return : forall cells target tp tid tasks events now next,
  V293_storage_open target tp tid tasks events now next ** V293_storage cells ==>
  SWINV (V293_storage_inv cells target tp).
Proof.
  intros cells target tp tid tasks events now next s Hs.
  apply V293_storage_switch_close. unfold V293_storage_open, V293_storage_core,
    V293_shared_core, V293_dispatch_cell in *. sep auto.
Qed.

Section StorageTail.
Variables target counter : var.
Variable tp : type.
Variable bcounter : block.
Variable rest : list (addr * type).
Variable tid : Modules.tid.
Variable tasks : TcbMod.map.
Variable events : EcbMod.map.
Variable now : int32.
Variable next : Modules.tid.
Variable aop : spec_code.
Variable stack : list hid.
Variable critical : list bool.
Variable px : asrt.
Let cells := ((bcounter, 0%Z), Tint32) :: rest.
Definition V293_storage_switch_payload c :=
  <||sched;;aop||> **
    ((V293_storage_open target tp tid tasks events now next ** CurTid tid) **
      ((Ais stack ** Acs critical) **
        ((PV (bcounter, Int.zero) @ Tint32 |-> (Vint32 c)) ** V293_storage rest))).
Definition V293_storage_tail c :=
  V293_storage_switch_payload c ** (V293_counter_bindings counter bcounter ** px).
Definition V293_storage_resumed :=
  <||aop||> ** SWINVt (V293_storage_inv cells target tp) tid ** Ais stack ** Acs critical **
    (V293_counter_bindings counter bcounter ** px).

Lemma V293_storage_tail_return : forall c,
  V293_storage_switch_payload c ==>
  <||sched;;aop||> ** SWINVt (V293_storage_inv cells target tp) tid ** Ais stack ** Acs critical.
Proof.
  intros c s Hs. unfold V293_storage_switch_payload in Hs.
  assert (HP : s |=
    (V293_storage_open target tp tid tasks events now next **
      (PV (bcounter, Int.zero) @ Tint32 |-> (Vint32 c) ** V293_storage rest)) **
      (<||sched;;aop||> ** (CurTid tid ** (Ais stack ** Acs critical)))) by (sep auto).
  assert (HR : PV (bcounter, Int.zero) @ Tint32 |-> (Vint32 c) ** V293_storage rest ==>
    V293_storage cells).
  { intros st H. cbn [cells V293_storage]. unfold V293_storage_cell.
    eapply astar_mono with (P := PV (bcounter, Int.zero) @ Tint32 |-> (Vint32 c));
      [intros st0 H0; exists (Vint32 c); sep auto | intros st0 H0; exact H0 | exact H]. }
  eapply astar_mono in HP; [ | apply astar_mono; [intros st H; exact H | exact HR] | intros st H; exact H].
  eapply astar_mono in HP; [ | apply V293_storage_return | intros st H; exact H].
  change (s |= <||sched;;aop||> **
    (SWINV (V293_storage_inv cells target tp) ** CurTid tid) ** Ais stack ** Acs critical).
  clear Hs. sep auto.
Qed.

Lemma V293_storage_tail_switch_pre : forall c,
  indom tasks tid -> V293_highest_ready tasks next ->
  V293_storage_switch_payload c ==> SWPRE_NDEAD V293_scheduler target tid.
Proof.
  intros c Hmem Hhighest s Hs.
  unfold V293_storage_switch_payload, V293_storage_open, V293_shared_fields in Hs.
  unfold SWPRE_NDEAD. split.
  - assert (HK : s |= (CurTid tid ** CurTid tid) **
      (Aabsdata abstcblsid (abstcblist tasks) **
        ((GV target @ (Tptr tp) |-> (Vptr next)) ** (isrclr ** Atrue)))).
    { unfold V293_shared_flags in Hs. sep auto. }
    eapply astar_mono in HK; [ | apply V293_current_halves_write | ].
    2: { apply astar_mono; [apply V293_tasks_highest_spatial; exact Hhighest | intros st H; exact H]. }
    unfold SWPRE. exists next. clear Hs. sep auto.
  - exists tasks. sep auto.
Qed.

Theorem V293_storage_tail_increment : forall Spec r ri c,
  (px ==> LINV V293_shared_li tid nil ** Atrue) ->
  InfRules Spec V293_scheduler V293_shared_li (V293_storage_inv cells target tp) r ri
    (V293_storage_tail c) (V293_OSSched_increment counter)
    (V293_storage_tail (Int.add c Int.one)) tid.
Proof.
  intros Spec r ri c Hlocal.
  eapply conseq_rule with
    (p := <||sched;;aop||> **
      (((V293_storage_open target tp tid tasks events now next ** CurTid tid) **
        ((Ais stack ** Acs critical) ** (V293_storage rest ** px))) **
        V293_counter_cell counter bcounter c))
    (q := <||sched;;aop||> **
      (((V293_storage_open target tp tid tasks events now next ** CurTid tid) **
        ((Ais stack ** Acs critical) ** (V293_storage rest ** px))) **
        V293_counter_cell counter bcounter (Int.add c Int.one))).
  + unfold V293_storage_tail, V293_storage_switch_payload, V293_counter_cell.
    intros s Hs. sep auto.
  + unfold V293_storage_tail, V293_storage_switch_payload, V293_counter_cell.
    intros s Hs. sep auto.
  + apply V293_OSSched_counter_increment.
    intros s Hs. unfold CurLINV. exists (nil : list logicvar).
    assert (HP : s |= CurTid tid ** (px ** Atrue)).
    { unfold V293_storage_open in Hs. sep auto. }
    eapply astar_mono in HP; [ | intros st H; exact H | apply astar_mono; [exact Hlocal | intros st H; exact H]].
    clear Hs. sep auto.
Qed.

Theorem V293_storage_increment_switch : forall Spec r ri c,
  indom tasks tid -> V293_highest_ready tasks next -> GoodFrm px ->
  (px ==> LINV V293_shared_li tid nil ** Atrue) ->
  InfRules Spec V293_scheduler V293_shared_li (V293_storage_inv cells target tp) r ri
    (V293_storage_tail c)
    (sseq (V293_OSSched_increment counter) (sprim (switch target)))
    V293_storage_resumed tid.
Proof.
  intros Spec r ri c Hmem Hhighest Hpx Hlocal.
  eapply seq_rule with (p' := V293_storage_tail (Int.add c Int.one)).
  - apply V293_storage_tail_increment; exact Hlocal.
  - unfold V293_storage_resumed. eapply switch_rule with
      (P' := V293_storage_switch_payload (Int.add c Int.one))
      (Px := V293_counter_bindings counter bcounter ** px) (lg := nil).
    + unfold V293_counter_bindings. simpl. auto.
    + intros s Hs. exact Hs.
    + apply V293_storage_tail_return.
    + apply V293_storage_tail_switch_pre; assumption.
    + intros s Hs. eapply astar_mono in Hs; [ | intros st H; exact H | exact Hlocal].
      sep auto.
Qed.
End StorageTail.
