(* LOCAL candidate pointer critical program, not frozen-C coverage. *)
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
Let readyI := V293_ready_inv bt bg br bh bp tp extra target.
Let ready_resumed := <||aop||> ** SWINVt readyI tid ** Ais stack ** Acs critical ** locals.
Definition checked_dead_switch : forall Spec r ri next c,
  lo < 256 -> hi < 256 -> (exists p, V293_bitmap_ready lo hi p) ->
  V293_bitmap_tasks lo hi tasks -> V293_priority_table entries tasks ->
  Forall (fun v => rule_type_val_match (Tptr tp) v = true) entries ->
  ~ indom tasks tid -> V293_highest_ready tasks next -> GoodFrm px ->
  (px ==> LINV V293_shared_li tid nil ** Atrue) ->
  InfRules Spec V293_scheduler V293_shared_li readyI r ri
    (tail next c) (sprim (switch target)) Afalse tid :=
  V293_ready_connected_switch_dead unmap group rows high table target counter bt bg br bh bp bo bcounter
    tp lo hi entries rest tid tasks events now aop stack critical px.
Definition checked_total_pointer_change : forall Spec r ri next c,
  lo < 256 -> hi < 256 -> (exists p, V293_bitmap_ready lo hi p) ->
  V293_bitmap_tasks lo hi tasks -> V293_priority_table entries tasks ->
  Forall (fun v => rule_type_val_match (Tptr tp) v = true) entries ->
  V293_highest_ready tasks next -> GoodFrm px ->
  (px ==> LINV V293_shared_li tid nil ** Atrue) ->
  (px ==> A_notin_lenv OSTCBCur ** Atrue) ->
  InfRules Spec V293_scheduler V293_shared_li readyI r ri (tail next c)
    (sifthen (eunop oppsite (ebinop oeq (evar target) (evar OSTCBCur)))
      (sseq (sassign (evar counter) (ebinop oplus (evar counter) (econst32 Int.one)))
        (sprim (switch target)))) ready_resumed tid :=
  V293_ready_pointer_change_total unmap group rows high table target counter bt bg br bh bp bo bcounter
    tp lo hi entries rest tid tasks events now aop stack critical px.
End FixedConnect.

Section FreshCritical.
Variables unmap group rows high table target counter : var.
Variables bt bg br bh bp bo bcounter : block.
Variable tp : type.
Variable rest : list (addr * type).
Variable tid : Modules.tid.
Variable aop : spec_code.
Variable stack : list hid.
Variable critical : list bool.
Variable px : asrt.
Let extra := ((bcounter, 0%Z), Tint32) :: rest.
Let readyI := V293_ready_inv bt bg br bh bp tp extra target.
Let bindings := V293_sched_globals unmap group rows high bt bg br bh **
  V293_prefix_bindings table high target tp bp bo.
Let private := V293_counter_bindings counter bcounter ** px.
Let locals := bindings ** (private ** Atrue).
(* Observations are bound INSIDE the disabled precondition, not before encrit. *)
Definition checked_snapshot := EX current : Modules.tid, EX tasks : TcbMod.map,
  EX events : EcbMod.map, EX now : int32, EX lo : nat, EX hi : nat,
  EX entries : list val, EX hv : val,
  [|lo < 256 /\ hi < 256 /\ (exists p, V293_bitmap_ready lo hi p) /\
    V293_bitmap_tasks lo hi tasks /\ V293_priority_table entries tasks /\
    Forall (fun v => rule_type_val_match (Tptr tp) v = true) entries /\
    rule_type_val_match Tint8 hv = true|] **
  (CurTid current ** (V293_shared_fields current tasks events now **
    ((EX old : val, [|rule_type_val_match (Tptr tp) old = true|] ** (GV target @ (Tptr tp) |-> old)) **
      (((checked_array true bt 0 1 Tint8 (map V293_byteval V293_ready_table) **
        checked_array true br 0 1 Tint8 (map V293_byteval [lo;hi])) **
          Amapsto (bg, 0%Z) Tint8 true (V293_byteval (V293_ready_group lo hi))) **
       ((PV (bh, Int.zero) @ Tint8 |-> hv) **
         (checked_array true bp 0 4 (Tptr tp) entries ** V293_storage extra)))))).
Definition checked_fresh_body : forall Spec r ri sched_id,
  GoodFrm px -> (px ==> LINV V293_shared_li tid nil ** Atrue) ->
  (px ==> A_notin_lenv OSTCBCur ** Atrue) ->
  Spec sched_id = Some
    (V293_critical_fpre unmap group rows high bt bg br bh V293_shared_li V293_opened_inv V293_switch_li_good,
     V293_critical_fpost unmap group rows high bt bg br bh V293_shared_li V293_opened_inv V293_switch_li_good,
     (Tvoid, nil)) ->
  InfRules Spec V293_scheduler V293_shared_li readyI r ri
    (<||sched;;aop||> ** ((checked_snapshot ** CurTid tid) **
      ((V293_shared_flags ** (Ais stack ** Acs critical)) ** (bindings ** private))))
    (sseq (sseq (scall sched_id nil) (sassign (evar target) (earrayelem (evar table) (evar high))))
      (sifthen (eunop oppsite (ebinop oeq (evar target) (evar OSTCBCur)))
        (sseq (sassign (evar counter) (ebinop oplus (evar counter) (econst32 Int.one)))
          (sprim (switch target)))))
    (<||aop||> ** SWINVt readyI tid ** Ais stack ** Acs critical ** locals) tid :=
  fun Spec r ri sched_id =>
  V293_ready_OSSched_pointer_fresh unmap group rows high table target counter bt bg br bh bp bo bcounter
    tp rest Spec r ri sched_id tid aop stack critical px.
Definition checked_critical_roundtrip : forall Spec r ri sched_id,
  GoodFrm px -> (px ==> LINV V293_shared_li tid nil ** Atrue) ->
  (px ==> A_notin_lenv OSTCBCur ** Atrue) ->
  Spec sched_id = Some
    (V293_critical_fpre unmap group rows high bt bg br bh V293_shared_li V293_opened_inv V293_switch_li_good,
     V293_critical_fpost unmap group rows high bt bg br bh V293_shared_li V293_opened_inv V293_switch_li_good,
     (Tvoid, nil)) ->
  InfRules Spec V293_scheduler V293_shared_li readyI r ri
    (<||sched;;aop||> ** OS[(fun _ : hid => false), true, nil, critical] **
      ATopis INUM ** (CurTid tid ** (bindings ** private)))
    (sseq (sprim encrit)
      (sseq (sseq (sseq (scall sched_id nil)
                       (sassign (evar target) (earrayelem (evar table) (evar high))))
              (sifthen (eunop oppsite (ebinop oeq (evar target) (evar OSTCBCur)))
                (sseq (sassign (evar counter) (ebinop oplus (evar counter) (econst32 Int.one)))
                  (sprim (switch target))))) (sprim excrit)))
    (<||aop||> ** OS[(fun _ : hid => false), true, nil, critical] **
      (CurTid tid ** (bindings ** (private ** Atrue)))) tid :=
  fun Spec r ri sched_id =>
  V293_ready_OSSched_pointer_critical unmap group rows high table target counter bt bg br bh bp bo bcounter
    tp rest Spec r ri sched_id tid aop critical px.
End FreshCritical.
Print Assumptions checked_dead_switch.
Print Assumptions checked_total_pointer_change.
Print Assumptions checked_fresh_body.
Print Assumptions checked_critical_roundtrip.
