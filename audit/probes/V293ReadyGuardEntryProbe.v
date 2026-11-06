(* LOCAL candidate pointer critical program, not frozen-C coverage. *)
(* Independent connected-segment types and literal AST, not candidate signatures. *)
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedStoragePrefix.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedStorageTail.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCurrent.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchStorage.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCritical.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedPrefix.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTarget.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedShared.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedSwitch.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.certiucos.v293.code.V293ReadyTable.
Require Import CertiOS.framework.include_frm.
Require Import Coq.Lists.List.
Import ListNotations.
Local Open Scope nat_scope.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedStorageConnect.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedChange.
Require Import CertiOS.framework.proof.auxdef.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedPointerCompare.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedStorageConnectWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedGuards.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCurrentWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTargetWitness.
Require Import Lia.
Import ListNotations.
Local Open Scope nat_scope.
Local Open Scope list_scope.
Fixpoint checked_array (w : bool) (b : block) (offset step : Z) (tau : type) (vs : list val) : asrt :=
  match vs with
  | nil => Aemp
  | v :: tail => Amapsto (b, offset) tau w v ** checked_array w b (offset + step)%Z step tau tail
  end.
Definition checked_entry_snapshot := EX current : Modules.tid, EX tasks : TcbMod.map,
  EX events : EcbMod.map, EX now : int32, EX lo : nat, EX hi : nat,
  EX entries : list val, EX hv : val,
  [|lo < 256 /\ hi < 256 /\ (exists p, V293_bitmap_ready lo hi p) /\
    V293_bitmap_tasks lo hi tasks /\ V293_priority_table entries tasks /\
    Forall (fun v => rule_type_val_match (Tptr Tvoid) v = true) entries /\
    rule_type_val_match Tint8 hv = true|] **
  (CurTid current ** (V293_shared_fields current tasks events now **
    ((EX old : val, [|rule_type_val_match (Tptr Tvoid) old = true|] ** (GV 107%Z @ (Tptr Tvoid) |-> old)) **
      (((checked_array true 1%positive 0 1 Tint8 (map V293_byteval V293_ready_table) **
        checked_array true 3%positive 0 1 Tint8 (map V293_byteval [lo;hi])) **
          Amapsto (2%positive, 0%Z) Tint8 true (V293_byteval (V293_ready_group lo hi))) **
       ((PV (4%positive, Int.zero) @ Tint8 |-> hv) **
         (checked_array true 8%positive 0 4 (Tptr Tvoid) entries ** V293_storage ([((13%positive, 0%Z), Tint32); ((14%positive, 0%Z), Tint8); ((15%positive, 0%Z), Tint8); ((12%positive, 0%Z), Tint8)]))))))).

Definition checked_entry_private :=
  (Agvarenv 108%Z Tint8 (12%positive, 0%Z) //\\ A_notin_lenv 108%Z) ** A_notin_lenv OSTCBCur.
Definition checked_entry_open aop :=
  <||sched;;aop||> ** ((checked_entry_snapshot ** CurTid V293_idle_tid) **
    ((V293_shared_flags ** (Ais nil ** Acs nil)) **
      ((V293_sched_globals 100%Z 101%Z 102%Z 103%Z 1%positive 2%positive 3%positive 4%positive **
        V293_prefix_bindings 106%Z 103%Z 107%Z Tvoid 8%positive 10%positive) **
        (V293_counter_bindings 109%Z 13%positive **
          (((Agvarenv 110%Z Tint8 (14%positive, 0%Z) //\\ A_notin_lenv 110%Z) **
            (Agvarenv 111%Z Tint8 (15%positive, 0%Z) //\\ A_notin_lenv 111%Z)) ** checked_entry_private))))).
Definition checked_entry_guard_values ni nl :=
  (((Agvarenv 110%Z Tint8 (14%positive, 0%Z) //\\ A_notin_lenv 110%Z) **
    Amapsto (14%positive, 0%Z) Tint8 false (V293_byteval ni)) **
   ((Agvarenv 111%Z Tint8 (15%positive, 0%Z) //\\ A_notin_lenv 111%Z) **
    Amapsto (15%positive, 0%Z) Tint8 false (V293_byteval nl))) ** Atrue.

(* The full precondition is spelled independently; no candidate entry aliases. *)
Definition checked_guard_entry_witness : forall different c ni nl events now aop,
  ni < 256 -> nl < 256 -> exists s,
    V293_bitmap_tasks 0 16 (V293_current_mode_tasks different) /\
    V293_priority_table (V293_current_mode_entries different) (V293_current_mode_tasks different) /\
    V293_current_task (V293_current_mode_tasks different) V293_idle_tid (V293_current_mode_priority different) /\
    Forall (fun v => rule_type_val_match (Tptr Tvoid) v = true) (V293_current_mode_entries different) /\
    getlenv s = emp /\
    s |= (checked_entry_open aop //\\ checked_entry_guard_values ni nl) //\\
      (((PV (13%positive, Int.zero) @ Tint32 |-> (Vint32 c)) **
        (PV (12%positive, Int.zero) @ Tint8 |-> (V293_byteval (V293_current_mode_priority different)))) **
        (V293_shared_fields V293_idle_tid (V293_current_mode_tasks different) events now ** Atrue)) :=
  V293_ready_guard_entry_witness.

(* All four loads and both literal guard expressions concern THAT SAME state. *)
Theorem checked_guard_entry_reads : forall different c ni nl events now aop,
  ni < 256 -> nl < 256 -> exists s,
    s |= checked_entry_open aop /\
    s |= V293_shared_fields V293_idle_tid (V293_current_mode_tasks different) events now ** Atrue /\
    load Tint8 (getmem s) (14%positive, 0%Z) = Some (V293_byteval ni) /\
    load Tint8 (getmem s) (15%positive, 0%Z) = Some (V293_byteval nl) /\
    load Tint8 (getmem s) (12%positive, 0%Z) = Some (V293_byteval (V293_current_mode_priority different)) /\
    load Tint32 (getmem s) (13%positive, 0%Z) = Some (Vint32 c) /\
    evalval (ebinop oeq (ecast (evar 110%Z) Tint32) (econst32 (Int.repr 0))) (getsmem s) =
      Some (Vint32 (if Nat.eqb ni 0 then Int.one else Int.zero)) /\
    evaltype (ebinop oeq (ecast (evar 110%Z) Tint32) (econst32 (Int.repr 0))) (getsmem s) = Some Tint32 /\
    evalval (ebinop oeq (ecast (evar 111%Z) Tint32) (econst32 (Int.repr 0))) (getsmem s) =
      Some (Vint32 (if Nat.eqb nl 0 then Int.one else Int.zero)) /\
    evaltype (ebinop oeq (ecast (evar 111%Z) Tint32) (econst32 (Int.repr 0))) (getsmem s) = Some Tint32.
Proof.
  intros different c ni nl events now aop Hni Hnl.
  destruct (checked_guard_entry_witness different c ni nl events now aop Hni Hnl)
    as (s & Hb & Ht & Hcur & Hptr & Hle & [Hopen Hguards] & Hvalues).
  change (s |= (V293_guard_cell 110%Z 14%positive ni **
    V293_guard_cell 111%Z 15%positive nl) ** Atrue) in Hguards.
  assert (Hi : s |= V293_guard_cell 110%Z 14%positive ni ** Atrue).
  { clear Hopen Hvalues. sep auto. }
  assert (Hl : s |= V293_guard_cell 111%Z 15%positive nl ** Atrue).
  { clear Hopen Hvalues Hi. sep auto. }
  destruct (V293_guard_eval _ _ _ _ _ Hni Hi) as [Ei Ti].
  destruct (V293_guard_eval _ _ _ _ _ Hnl Hl) as [El Tl].
  exists s. split; [exact Hopen | ]. split.
  { clear Hopen Hguards Hi Hl. sep auto. }
  split.
  { eapply V293_star_load_l; [ | exact Hi]. intros s0 H0.
    eapply V293_star_load_r; [ | exact H0]. intros; eapply V293_mapsto_load; eauto. }
  split.
  { eapply V293_star_load_l; [ | exact Hl]. intros s0 H0.
    eapply V293_star_load_r; [ | exact H0]. intros; eapply V293_mapsto_load; eauto. }
  split.
  { eapply V293_star_load_l; [ | exact Hvalues]. intros s0 H0.
    eapply V293_star_load_r; [ | exact H0]. intros; eapply V293_mapsto_load; [ | eassumption].
    destruct different; simpl; lia. }
  split.
  { eapply V293_star_load_l; [ | exact Hvalues]. intros s0 H0.
    eapply V293_star_load_l; [ | exact H0]. intros s1 [Hm _].
    eapply mapstoval_load; [reflexivity | exact Hm]. }
  repeat split; assumption.
Qed.

Theorem checked_guard_entry_private_frame :
  GoodFrm checked_entry_private /\
  (checked_entry_private ==> LINV V293_shared_li V293_idle_tid nil ** Atrue) /\
  (checked_entry_private ==> A_notin_lenv OSTCBCur ** Atrue).
Proof.
  split; [simpl; repeat split; exact I | ]. split.
  - intros s H. unfold LINV, V293_shared_li. sep auto; exact V293_switch_li_good.
  - intros s H. unfold checked_entry_private in H. sep auto.
Qed.
Print Assumptions checked_guard_entry_witness.
Print Assumptions checked_guard_entry_reads.
Print Assumptions checked_guard_entry_private_frame.
