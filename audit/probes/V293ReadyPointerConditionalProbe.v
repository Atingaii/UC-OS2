(* LOCAL candidate pointer program, not frozen-C coverage. *)
(* Independent connected-segment types and literal AST, not candidate signatures. *)
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedStoragePrefix.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedStoragePrefixWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedStorageTail.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCurrent.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCurrentWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTargetWitness.
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
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedStorageConnectWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedChange.
Require Import CertiOS.framework.proof.auxdef.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedPointerCompare.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Fixpoint checked_array (w : bool) (b : block) (offset step : Z) (tau : type) (vs : list val) : asrt :=
  match vs with
  | nil => Aemp
  | v :: tail => Amapsto (b, offset) tau w v ** checked_array w b (offset + step)%Z step tau tail
  end.
Section FixedConnect.
Variables unmap group rows high table target counter : var.
Variables bt bg br bh bp bo bcounter : block.
Variable tp : type.
Variables lo hi : nat.
Variable entries : list val.
Variable rest : list (addr * type).
Variable tid : Modules.tid.
Variable tasks : TcbMod.map.
Variable events : EcbMod.map.
Variable now : int32.
Variable aop : spec_code.
Variable stack : list hid.
Variable critical : list bool.
Variable px : asrt.
Let extra := ((bcounter, 0%Z), Tint32) :: rest.
Let physical :=
  ((checked_array true bt 0 1 Tint8 (map V293_byteval V293_ready_table) **
    checked_array true br 0 1 Tint8 (map V293_byteval [lo;hi])) **
    Amapsto (bg, 0%Z) Tint8 true (V293_byteval (V293_ready_group lo hi))) **
  ((PV (bh, Int.zero) @ Tint8 |->
    (V293_byteval (V293_ready_select lo hi (V293_ready_group lo hi)))) **
    (checked_array true bp 0 4 (Tptr tp) entries ** V293_storage rest)).
Let locals := (V293_sched_globals unmap group rows high bt bg br bh **
  V293_prefix_bindings table high target tp bp bo) **
  ((V293_counter_bindings counter bcounter ** px) ** Atrue).
Let payload next c := <||sched;;aop||> **
  ((V293_storage_open target tp tid tasks events now next ** CurTid tid) **
    ((Ais stack ** Acs critical) **
      (physical ** (PV (bcounter, Int.zero) @ Tint32 |-> (Vint32 c))))).
Let tail next c := payload next c ** locals.
Let entry_heap hv :=
  ((checked_array true bt 0 1 Tint8 (map V293_byteval V293_ready_table) **
    checked_array true br 0 1 Tint8 (map V293_byteval [lo;hi])) **
    Amapsto (bg, 0%Z) Tint8 true (V293_byteval (V293_ready_group lo hi))) **
  ((PV (bh, Int.zero) @ Tint8 |-> hv) **
    (checked_array true bp 0 4 (Tptr tp) entries ** V293_storage extra)).
Let readyI := V293_ready_inv bt bg br bh bp tp extra target.
Definition checked_ready_connect_entry old hv :=
  <||sched;;aop||> **
    (((SWINV readyI //\\
      ((V293_shared_flags ** ((CurTid tid ** V293_shared_fields tid tasks events now) **
        (GV target @ (Tptr tp) |-> old))) ** entry_heap hv)) ** CurTid tid) **
      ((Ais stack ** Acs critical) **
        ((V293_sched_globals unmap group rows high bt bg br bh **
          V293_prefix_bindings table high target tp bp bo) ** (V293_counter_bindings counter bcounter ** px)))).
Let ready_resumed := <||aop||> ** SWINVt readyI tid ** Ais stack ** Acs critical ** locals.
Definition checked_pointer_tail : forall next c s,
  (px ==> A_notin_lenv OSTCBCur ** Atrue) ->
  s |= tail next c ->
  evalval (eunop oppsite (ebinop oeq (evar target) (evar OSTCBCur))) (getsmem s) =
    Some (Vint32 (if tid_eq_dec next tid then Int.zero else Int.one)) /\
  evaltype (eunop oppsite (ebinop oeq (evar target) (evar OSTCBCur))) (getsmem s) = Some Tint32 :=
  V293_ready_pointer_comparison unmap group rows high table target counter bt bg br bh bp bo bcounter
    tp lo hi entries rest tid tasks events now aop stack critical px.
Definition checked_pointer_change : forall Spec r ri next c,
  lo < 256 -> hi < 256 -> (exists p, V293_bitmap_ready lo hi p) ->
  V293_bitmap_tasks lo hi tasks -> V293_priority_table entries tasks ->
  Forall (fun v => rule_type_val_match (Tptr tp) v = true) entries ->
  indom tasks tid -> V293_highest_ready tasks next -> GoodFrm px ->
  (px ==> LINV V293_shared_li tid nil ** Atrue) ->
  (px ==> A_notin_lenv OSTCBCur ** Atrue) ->
  InfRules Spec V293_scheduler V293_shared_li readyI r ri (tail next c)
    (sifthen (eunop oppsite (ebinop oeq (evar target) (evar OSTCBCur)))
      (sseq (sassign (evar counter) (ebinop oplus (evar counter) (econst32 Int.one)))
        (sprim (switch target)))) ready_resumed tid :=
  V293_ready_pointer_change unmap group rows high table target counter bt bg br bh bp bo bcounter
    tp lo hi entries rest tid tasks events now aop stack critical px.
Definition checked_pointer_conditional : forall Spec r ri sched_id old hv,
  lo < 256 -> hi < 256 -> (exists p, V293_bitmap_ready lo hi p) ->
  V293_bitmap_tasks lo hi tasks -> V293_priority_table entries tasks ->
  Forall (fun v => rule_type_val_match (Tptr tp) v = true) entries ->
  indom tasks tid -> GoodFrm px -> (px ==> LINV V293_shared_li tid nil ** Atrue) ->
  (px ==> A_notin_lenv OSTCBCur ** Atrue) ->
  Spec sched_id = Some
    (V293_critical_fpre unmap group rows high bt bg br bh V293_shared_li V293_opened_inv V293_switch_li_good,
     V293_critical_fpost unmap group rows high bt bg br bh V293_shared_li V293_opened_inv V293_switch_li_good,
     (Tvoid, nil)) ->
  InfRules Spec V293_scheduler V293_shared_li readyI r ri
    (checked_ready_connect_entry old hv)
    (sseq (sseq (scall sched_id nil) (sassign (evar target) (earrayelem (evar table) (evar high))))
      (sifthen (eunop oppsite (ebinop oeq (evar target) (evar OSTCBCur)))
        (sseq (sassign (evar counter) (ebinop oplus (evar counter) (econst32 Int.one)))
          (sprim (switch target))))) ready_resumed tid.
Proof. exact (V293_ready_OSSched_pointer_conditional unmap group rows high table target counter bt bg br bh bp bo bcounter
    tp lo hi entries rest tid tasks events now aop stack critical px). Qed.
End FixedConnect.

(* The full ready-entry layout and no-shadow frame inhabit the SAME state.
   Both task modes and arbitrary counter/events/time/continuation are covered. *)
Theorem checked_pointer_entry_witness : forall different c events now aop,
  exists s,
    V293_bitmap_tasks 0 16 (V293_current_mode_tasks different) /\
    V293_priority_table (V293_current_mode_entries different) (V293_current_mode_tasks different) /\
    V293_current_task (V293_current_mode_tasks different) V293_idle_tid (V293_current_mode_priority different) /\
    Forall (fun v => rule_type_val_match (Tptr Tvoid) v = true) (V293_current_mode_entries different) /\
    s |= (checked_ready_connect_entry 100%Z 101%Z 102%Z 103%Z 106%Z 107%Z 108%Z
      1%positive 2%positive 3%positive 4%positive 8%positive 10%positive 12%positive Tvoid 0 16
      (V293_current_mode_entries different) nil V293_idle_tid
      (V293_current_mode_tasks different) events now aop nil nil (A_notin_lenv OSTCBCur)
      (Vptr V293_idle_tid) (V293_byteval 0)) //\\
      ((PV (12%positive, Int.zero) @ Tint32 |-> (Vint32 c)) ** Atrue).
Proof.
  intros different c events now aop.
  destruct (V293_ready_connected_entry_witness_empty_locals different c events now aop)
    as (s & Hb & Ht & Hcur & Hptr & Hle & Hs & Hcounter).
  exists s. split; [exact Hb | ]. split; [exact Ht | ].
  split; [exact Hcur | ]. split; [exact Hptr | ]. split; [ | exact Hcounter].
  apply astar_l_anotinlenv_intro with (x := OSTCBCur) in Hs.
  - change (s |= (V293_ready_connected_entry 100%Z 101%Z 102%Z 103%Z 106%Z 107%Z 108%Z
      1%positive 2%positive 3%positive 4%positive 8%positive 10%positive 12%positive Tvoid 0 16
      (V293_current_mode_entries different) nil V293_idle_tid
      (V293_current_mode_tasks different) events now aop nil nil (A_notin_lenv OSTCBCur)
      (Vptr V293_idle_tid) (V293_byteval 0))).
    unfold V293_ready_connected_entry in Hs |- *.
    clear Hcounter. sep auto.
  - rewrite Hle. intros [v H]. discriminate.
Qed.

Theorem checked_no_shadow_frame :
  GoodFrm (A_notin_lenv OSTCBCur) /\
  (A_notin_lenv OSTCBCur ==> LINV V293_shared_li V293_idle_tid nil ** Atrue) /\
  (A_notin_lenv OSTCBCur ==> A_notin_lenv OSTCBCur ** Atrue).
Proof.
  split; [simpl; exact I | ]. split.
  - intros s H. assert (HA : s |= Aemp) by exact (proj2 H). clear H.
    unfold LINV, V293_shared_li. sep auto; exact V293_switch_li_good.
  - intros s H. sep auto.
Qed.
Print Assumptions checked_pointer_tail.
Print Assumptions checked_pointer_change.
Print Assumptions checked_pointer_conditional.
Print Assumptions checked_pointer_entry_witness.
Print Assumptions checked_no_shadow_frame.
