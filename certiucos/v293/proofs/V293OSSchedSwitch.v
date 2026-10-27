(* Normal SCAP switch at the shared core. The post describes resumption of
   THIS thread, not execution in the selected thread. Shared values are not
   frozen across the switch. OSCtxSw/source correspondence remains open. *)
Require Import CertiOS.certiucos.v293.proofs.V293DispatchState.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCurrent.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedSwitchPre.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.lmachLib.
Require Import CertiOS.framework.proof.rulesoundlib.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import Coq.Lists.List Lia.
Local Open Scope nat_scope.

Lemma V293_switch_li_good : GoodLInvAsrt V293_shared_li.
Proof.
  intros t lg. split; [exact I | ].
  intros ge le M ir aux O le' M' aux' ir' O' H H'.
  specialize (H (spec_done None)). specialize (H' (spec_done None)).
  destruct H as [HM HO]. destruct H' as [HM' HO'].
  cbn [emptaskst emposabst] in *. split; congruence.
Qed.
Lemma V293_switch_local_empty : forall t lg,
  Aemp ==> LINV V293_shared_li t lg.
Proof.
  intros t lg s Hs. unfold LINV, V293_shared_li.
  sep auto. apply V293_switch_li_good.
Qed.

Definition V293_dispatch_snapshot target tp tid tasks events now next :=
  SWINV (V293_dispatch_inv target tp) //\\
    (((CurTid tid ** V293_shared_fields tid tasks events now) **
      (GV target @ (Tptr tp) |-> (Vptr next))) ** Atrue).
Lemma V293_dispatch_snapshot_open : forall target tp tid tasks events now next,
  V293_dispatch_snapshot target tp tid tasks events now next ==>
  V293_shared_flags ** ((CurTid tid ** V293_shared_fields tid tasks events now) **
    (GV target @ (Tptr tp) |-> (Vptr next))).
Proof.
  intros target tp tid tasks events now next s [HI HO].
  apply V293_dispatch_switch_open in HI.
  unfold V293_dispatch_core, V293_shared_core, V293_dispatch_cell in HI.
  sep normal in HI. sep destruct HI. sep split in HI.
  assert (HP : s |= (CurTid x ** V293_shared_fields x x0 x1 x2) ** Atrue) by (sep auto).
  assert (HQ : s |= (CurTid tid ** V293_shared_fields tid tasks events now) ** Atrue) by (clear HI HP; sep auto).
  pose proof (V293_shared_fields_core_get _ _ _ _ _ _ HP) as [HC [HT [HE HN]]].
  pose proof (V293_shared_fields_core_get _ _ _ _ _ _ HQ) as [HC' [HT' [HE' HN']]].
  assert (x = tid) by congruence. assert (x0 = tasks) by congruence.
  assert (x1 = events) by congruence. assert (x2 = now) by congruence. subst.
  assert (L1 : s |= (GV target @ (Tptr tp) |-> x3) ** Atrue) by (clear HP HQ HO; sep auto).
  assert (L2 : s |= (GV target @ (Tptr tp) |-> (Vptr next)) ** Atrue).
  { clear HP HQ HI L1. sep auto. }
  (* The two views use one common memory, so a typed full cell has one value. *)
  assert (V : x3 = Vptr next).
  { destruct s as [[[[[[ge le] M] ir] aux] O] op].
    apply sat_split in L1. destruct L1 as (m1 & m2 & o1 & o2 & JM1 & JO1 & H1 & _).
    apply sat_split in L2. destruct L2 as (m3 & m4 & o3 & o4 & JM2 & JO2 & H2 & _).
    destruct (V293_dispatch_named_cell_parts _ _ _ _ _ _ _ _ _ _ H1) as (b1 & G1 & P1 & E1).
    destruct (V293_dispatch_named_cell_parts _ _ _ _ _ _ _ _ _ _ H2) as (b2 & G2 & P2 & E2).
    pose proof (@mapstoval_load _ _ _ _ _ H P1) as Load1.
    assert (T2 : rule_type_val_match (Tptr tp) (Vptr next) = true) by reflexivity.
    pose proof (@mapstoval_load _ _ _ _ _ T2 P2) as Load2.
    rewrite <- (@lmachLib.load_mono _ _ _ _ _ _ JM1 Load1) in Load1.
    rewrite <- (@lmachLib.load_mono _ _ _ _ _ _ JM2 Load2) in Load2.
    assert (b1 = b2) by congruence. subst b2. congruence. }
  subst x3. clear HP HQ HO L1 L2. sep auto.
Qed.
Lemma V293_dispatch_snapshot_close : forall target tp tid tasks events now next,
  V293_shared_flags ** ((CurTid tid ** V293_shared_fields tid tasks events now) **
    (GV target @ (Tptr tp) |-> (Vptr next))) ==>
  V293_dispatch_snapshot target tp tid tasks events now next.
Proof.
  intros target tp tid tasks events now next s Hs. split; [ | sep auto].
  apply V293_dispatch_switch_close. unfold V293_dispatch_core, V293_shared_core, V293_dispatch_cell.
  sep auto.
Qed.
Definition V293_switch_payload target tp tid tasks events now next aop stack critical :=
  <||sched;;aop||> ** ((V293_dispatch_snapshot target tp tid tasks events now next ** CurTid tid) **
    (Ais stack ** Acs critical)).
Theorem V293_shared_payload_switch_pre : forall target tp tid tasks events now next aop stack critical,
  indom tasks tid -> V293_highest_ready tasks next ->
  V293_switch_payload target tp tid tasks events now next aop stack critical ==>
  SWPRE_NDEAD V293_scheduler target tid.
Proof.
  intros target tp tid tasks events now next aop stack critical Hmember Hhighest s Hs.
  unfold V293_switch_payload in Hs.
  assert (HP : s |= V293_dispatch_snapshot target tp tid tasks events now next ** (CurTid tid ** Atrue)) by (sep auto).
  eapply astar_mono in HP; [ | apply V293_dispatch_snapshot_open | intros st H; exact H].
  unfold V293_shared_fields in HP. unfold SWPRE_NDEAD. split.
  - assert (HK : s |= (CurTid tid ** CurTid tid) **
      (Aabsdata abstcblsid (abstcblist tasks) **
        ((GV target @ (Tptr tp) |-> (Vptr next)) ** (isrclr ** Atrue)))).
    { unfold V293_shared_flags in HP. sep auto. }
    eapply astar_mono in HK; [ | apply V293_current_halves_write | ].
    2: { apply astar_mono; [apply V293_tasks_highest_spatial; exact Hhighest | intros st H; exact H]. }
    unfold SWPRE. exists next. sep auto.
  - exists tasks. sep auto.
Qed.
Definition V293_switch_resume target tp tid aop stack critical px :=
  <||aop||> ** SWINVt (V293_dispatch_inv target tp) tid ** Ais stack ** Acs critical ** px.
Theorem V293_shared_normal_switch : forall Spec r ri target tp tid aop tasks events now next stack critical px,
  indom tasks tid -> V293_highest_ready tasks next -> GoodFrm px ->
  (px ==> LINV V293_shared_li tid nil ** Atrue) ->
  InfRules Spec V293_scheduler V293_shared_li (V293_dispatch_inv target tp) r ri
    (V293_switch_payload target tp tid tasks events now next aop stack critical ** px)
    (sprim (switch target)) (V293_switch_resume target tp tid aop stack critical px) tid.
Proof.
  intros Spec r ri target tp tid aop tasks events now next stack critical px Hmember Hhighest Hpx Hlocal.
  unfold V293_switch_resume. eapply switch_rule with (lg := nil).
  - exact Hpx.
  - intros s Hs; exact Hs.
  - unfold V293_switch_payload. intros s Hs.
    eapply astar_mono with (P' := <||sched;;aop||>) in Hs; [ | intros st H; exact H | ].
    2: { apply astar_mono; [ | intros st H; exact H].
         apply astar_mono with (P' := SWINV (V293_dispatch_inv target tp));
           [intros st H; exact (proj1 H) | intros st H; exact H]. }
    unfold SWINVt. sep auto.
  - apply V293_shared_payload_switch_pre; assumption.
  - exact Hlocal.
Qed.
