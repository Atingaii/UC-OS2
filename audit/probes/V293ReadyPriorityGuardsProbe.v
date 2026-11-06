(* Local post-encrit priority guards; not a complete C/port refinement. *)
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
Fixpoint checked_array (w : bool) (b : block) (offset step : Z) (tau : type) (vs : list val) : asrt :=
  match vs with
  | nil => Aemp
  | v :: tail => Amapsto (b, offset) tau w v ** checked_array w b (offset + step)%Z step tau tail
  end.
Section FixedPriorityGuards.
Variables unmap group rows high table target current counter interrupt lock : var.
Variables bt bg br bh bp bo bcur bcounter bi bl : block.
Variable tp : type.
Variables lo hi nc ni nl : nat.
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
Let guardrest := ((bi, 0%Z), Tint8) :: ((bl, 0%Z), Tint8) :: rest.
Let extra := ((bcounter, 0%Z), Tint32) :: ((bcur, 0%Z), Tint8) :: guardrest.
Let readyI := V293_ready_inv bt bg br bh bp tp extra target.
Let pkept := (EX v : val, [|rule_type_val_match Tint32 v = true|] **
  Amapsto (bcounter, 0%Z) Tint32 true v) ** (PV (bcur, Int.zero) @ Tint8 |-> (V293_byteval nc)) ** V293_storage guardrest.
Let pbindings := V293_counter_bindings counter bcounter **
  ((Agvarenv current Tint8 (bcur, 0%Z) //\\ A_notin_lenv current) **
    ((Agvarenv interrupt Tint8 (bi, 0%Z) //\\ A_notin_lenv interrupt) **
      ((Agvarenv lock Tint8 (bl, 0%Z) //\\ A_notin_lenv lock) ** px))).
Let pheap hv :=
  ((checked_array true bt 0 1 Tint8 (map V293_byteval V293_ready_table) **
    checked_array true br 0 1 Tint8 (map V293_byteval [lo;hi])) **
    Amapsto (bg, 0%Z) Tint8 true (V293_byteval (V293_ready_group lo hi))) **
  ((PV (bh, Int.zero) @ Tint8 |-> hv) **
    (checked_array true bp 0 4 (Tptr tp) entries ** pkept)).
Definition checked_entry old hv :=
 (
  <||sched;;aop||> ** (((SWINV readyI //\\
    ((V293_shared_flags ** ((CurTid tid ** V293_shared_fields tid tasks events now) **
      (GV target @ (Tptr tp) |-> old))) ** pheap hv)) ** CurTid tid) **
    ((Ais stack ** Acs critical) **
      ((V293_sched_globals unmap group rows high bt bg br bh **
        V293_prefix_bindings table high target tp bp bo) ** pbindings)))) //\\
  ((((Agvarenv interrupt Tint8 (bi, 0%Z) //\\ A_notin_lenv interrupt) **
     Amapsto (bi, 0%Z) Tint8 false (V293_byteval ni)) **
    ((Agvarenv lock Tint8 (bl, 0%Z) //\\ A_notin_lenv lock) **
     Amapsto (bl, 0%Z) Tint8 false (V293_byteval nl))) ** Atrue).

Definition checked_resumed continuation := <||continuation||> ** SWINVt readyI tid **
  Ais stack ** Acs critical **
  ((V293_sched_globals unmap group rows high bt bg br bh **
    V293_prefix_bindings table high target tp bp bo) ** (pbindings ** Atrue)).
Definition checked_disabled_pending : forall old hv,
  checked_entry old hv ==> checked_resumed (sched;;aop) :=
  V293_ready_priority_guarded_skip unmap group rows high table target current counter interrupt lock
    bt bg br bh bp bo bcur bcounter bi bl tp lo hi nc ni nl entries rest tid tasks events now
    aop stack critical px.
Definition checked_priority_guards : forall Spec r ri sched_id old hv,
  lo < 256 -> hi < 256 -> (exists p, V293_bitmap_ready lo hi p) -> nc < 256 ->
  ni < 256 -> nl < 256 ->
  V293_bitmap_tasks lo hi tasks -> V293_priority_table entries tasks ->
  Forall (fun v => rule_type_val_match (Tptr tp) v = true) entries ->
  V293_current_task tasks tid nc -> indom tasks tid -> GoodFrm px ->
  (px ==> LINV V293_shared_li tid nil ** Atrue) ->
  Spec sched_id = Some
    (V293_critical_fpre unmap group rows high bt bg br bh V293_shared_li V293_opened_inv V293_switch_li_good,
     V293_critical_fpost unmap group rows high bt bg br bh V293_shared_li V293_opened_inv V293_switch_li_good,
     (Tvoid, nil)) ->
  InfRules Spec V293_scheduler V293_shared_li readyI r ri
    (checked_entry old hv)
    (sifthen (ebinop oeq (ecast (evar interrupt) Tint32) (econst32 (Int.repr 0)))
      (sifthen (ebinop oeq (ecast (evar lock) Tint32) (econst32 (Int.repr 0)))
        (sseq (sseq (scall sched_id nil) (sassign (evar target) (earrayelem (evar table) (evar high))))
          (sifthen (eunop oppsite (ebinop oeq (ecast (evar high) Tint32) (ecast (evar current) Tint32)))
            (sseq (sassign (evar counter) (ebinop oplus (evar counter) (econst32 Int.one)))
              (sprim (switch target)))))))
    (checked_resumed (if Nat.eqb ni 0 && Nat.eqb nl 0 then aop else (sched;;aop))) tid :=
  V293_ready_OSSched_priority_guarded unmap group rows high table target current counter interrupt lock
    bt bg br bh bp bo bcur bcounter bi bl tp lo hi nc ni nl entries rest tid tasks events now
    aop stack critical px.
End FixedPriorityGuards.
Print Assumptions checked_disabled_pending.
Print Assumptions checked_priority_guards.
