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
Fixpoint checked_array (w : bool) (b : block) (offset step : Z) (tau : type) (vs : list val) : asrt :=
  match vs with
  | nil => Aemp
  | v :: tail => Amapsto (b, offset) tau w v ** checked_array w b (offset + step)%Z step tau tail
  end.
Fixpoint checked_cells (b : block) (offset step : Z) (tau : type) (n : nat) : list (addr * type) :=
  match n with
  | O => nil
  | S n' => ((b, offset), tau) :: checked_cells b (offset + step)%Z step tau n'
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
Let cells := (checked_cells bt 0 1 Tint8 256 ++
  checked_cells br 0 1 Tint8 2 ++ [((bg, 0%Z), Tint8)]) ++
  [((bh, 0%Z), Tint8)] ++ checked_cells bp 0 4 (Tptr tp) (length entries) ++ extra.
Let physical :=
  ((checked_array true bt 0 1 Tint8 (map V293_byteval V293_ready_table) **
    checked_array true br 0 1 Tint8 (map V293_byteval [lo;hi])) **
    Amapsto (bg, 0%Z) Tint8 true (V293_byteval (V293_ready_group lo hi))) **
  ((PV (bh, Int.zero) @ Tint8 |->
    (V293_byteval (V293_ready_select lo hi (V293_ready_group lo hi)))) **
    (checked_array true bp 0 4 (Tptr tp) entries ** V293_storage rest)).
Let whole_physical :=
  ((checked_array true bt 0 1 Tint8 (map V293_byteval V293_ready_table) **
    checked_array true br 0 1 Tint8 (map V293_byteval [lo;hi])) **
    Amapsto (bg, 0%Z) Tint8 true (V293_byteval (V293_ready_group lo hi))) **
  ((PV (bh, Int.zero) @ Tint8 |->
    (V293_byteval (V293_ready_select lo hi (V293_ready_group lo hi)))) **
    (checked_array true bp 0 4 (Tptr tp) entries ** V293_storage extra)).
Let locals := (V293_sched_globals unmap group rows high bt bg br bh **
  V293_prefix_bindings table high target tp bp bo) **
  ((V293_counter_bindings counter bcounter ** px) ** Atrue).
Let payload next c := <||sched;;aop||> **
  ((V293_storage_open target tp tid tasks events now next ** CurTid tid) **
    ((Ais stack ** Acs critical) **
      (physical ** (PV (bcounter, Int.zero) @ Tint32 |-> (Vint32 c))))).
Let tail next c := payload next c ** locals.
Let resumed := <||aop||> ** SWINVt (V293_storage_inv cells target tp) tid **
  Ais stack ** Acs critical ** locals.
Let snapshot next := SWINV (V293_storage_inv cells target tp) //\\
  (((CurTid tid ** V293_shared_fields tid tasks events now) **
    (GV target @ (Tptr tp) |-> (Vptr next))) ** (whole_physical ** Atrue)).
Let middle := EX next : Modules.tid, [|V293_highest_ready tasks next|] **
  ((<||sched;;aop||> ** ((snapshot next ** CurTid tid) ** (Ais stack ** Acs critical))) ** locals).
Let entry_heap hv :=
  ((checked_array true bt 0 1 Tint8 (map V293_byteval V293_ready_table) **
    checked_array true br 0 1 Tint8 (map V293_byteval [lo;hi])) **
    Amapsto (bg, 0%Z) Tint8 true (V293_byteval (V293_ready_group lo hi))) **
  ((PV (bh, Int.zero) @ Tint8 |-> hv) **
    (checked_array true bp 0 4 (Tptr tp) entries ** V293_storage extra)).
Definition checked_entry old hv :=
  <||sched;;aop||> **
    (((SWINV (V293_storage_inv cells target tp) //\\
      ((V293_shared_flags ** ((CurTid tid ** V293_shared_fields tid tasks events now) **
        (GV target @ (Tptr tp) |-> (Vptr old)))) ** entry_heap hv)) ** CurTid tid) **
      ((Ais stack ** Acs critical) **
        ((V293_sched_globals unmap group rows high bt bg br bh **
          V293_prefix_bindings table high target tp bp bo) ** (V293_counter_bindings counter bcounter ** px)))).
Definition checked_open : middle ==>
  EX next : Modules.tid, EX c : int32, [|V293_highest_ready tasks next|] ** tail next c :=
  V293_storage_connected_prefix_open unmap group rows high table target counter bt bg br bh bp bo bcounter
    tp lo hi entries rest tid tasks events now aop stack critical px.
Definition checked_return : forall next c,
  lo < 256 -> hi < 256 -> (exists p, V293_bitmap_ready lo hi p) ->
  Forall (fun v => rule_type_val_match (Tptr tp) v = true) entries ->
  payload next c ==> <||sched;;aop||> ** SWINVt (V293_storage_inv cells target tp) tid **
    Ais stack ** Acs critical :=
  V293_storage_connected_return unmap group rows high table target counter bt bg br bh bp bo bcounter
    tp lo hi entries rest tid tasks events now aop stack critical px.
Definition checked_increment : forall Spec r ri next c,
  (px ==> LINV V293_shared_li tid nil ** Atrue) ->
  InfRules Spec V293_scheduler V293_shared_li (V293_storage_inv cells target tp) r ri
    (tail next c) (sassign (evar counter) (ebinop oplus (evar counter) (econst32 Int.one)))
    (tail next (Int.add c Int.one)) tid :=
  V293_storage_connected_increment unmap group rows high table target counter bt bg br bh bp bo bcounter
    tp lo hi entries rest tid tasks events now aop stack critical px.
Definition checked_connect : forall Spec r ri sched_id old hv,
  lo < 256 -> hi < 256 -> (exists p, V293_bitmap_ready lo hi p) ->
  V293_bitmap_tasks lo hi tasks -> V293_priority_table entries tasks ->
  Forall (fun v => rule_type_val_match (Tptr tp) v = true) entries ->
  indom tasks tid -> GoodFrm px -> (px ==> LINV V293_shared_li tid nil ** Atrue) ->
  Spec sched_id = Some
    (V293_critical_fpre unmap group rows high bt bg br bh V293_shared_li V293_opened_inv V293_switch_li_good,
     V293_critical_fpost unmap group rows high bt bg br bh V293_shared_li V293_opened_inv V293_switch_li_good,
     (Tvoid, nil)) ->
  InfRules Spec V293_scheduler V293_shared_li (V293_storage_inv cells target tp) r ri
    (checked_entry old hv)
    (sseq (sseq (scall sched_id nil) (sassign (evar target) (earrayelem (evar table) (evar high))))
      (sseq (sassign (evar counter) (ebinop oplus (evar counter) (econst32 Int.one)))
        (sprim (switch target))))
    resumed tid :=
  V293_OSSched_storage_prefix_increment_switch unmap group rows high table target counter bt bg br bh bp bo bcounter
    tp lo hi entries rest tid tasks events now aop stack critical px.

(* This uses the SAME relational Inv throughout, not the typed-storage Inv.
   Shared observations exist only in the disabled entry and disappear on resume. *)
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
Definition checked_increment_under : forall Spec (RI : Inv) r ri next c,
  (px ==> LINV V293_shared_li tid nil ** Atrue) ->
  InfRules Spec V293_scheduler V293_shared_li RI r ri
    (tail next c) (sassign (evar counter) (ebinop oplus (evar counter) (econst32 Int.one)))
    (tail next (Int.add c Int.one)) tid.
Proof. exact (V293_storage_connected_increment_under unmap group rows high table target counter bt bg br bh bp bo bcounter
    tp lo hi entries rest tid tasks events now aop stack critical px). Qed.
Definition checked_ready_connect_return : forall next c,
  lo < 256 -> hi < 256 -> (exists p, V293_bitmap_ready lo hi p) ->
  V293_bitmap_tasks lo hi tasks -> V293_priority_table entries tasks ->
  Forall (fun v => rule_type_val_match (Tptr tp) v = true) entries ->
  payload next c ==> <||sched;;aop||> ** SWINVt readyI tid ** Ais stack ** Acs critical.
Proof. exact (V293_ready_connected_return unmap group rows high table target counter bt bg br bh bp bo bcounter
    tp lo hi entries rest tid tasks events now aop stack critical px). Qed.
Definition checked_ready_connect_switch : forall Spec r ri next c,
  lo < 256 -> hi < 256 -> (exists p, V293_bitmap_ready lo hi p) ->
  V293_bitmap_tasks lo hi tasks -> V293_priority_table entries tasks ->
  Forall (fun v => rule_type_val_match (Tptr tp) v = true) entries ->
  indom tasks tid -> V293_highest_ready tasks next -> GoodFrm px ->
  (px ==> LINV V293_shared_li tid nil ** Atrue) ->
  InfRules Spec V293_scheduler V293_shared_li readyI r ri
    (tail next c) (sprim (switch target)) ready_resumed tid.
Proof. exact (V293_ready_connected_switch unmap group rows high table target counter bt bg br bh bp bo bcounter
    tp lo hi entries rest tid tasks events now aop stack critical px). Qed.
Definition checked_ready_connect : forall Spec r ri sched_id old hv,
  lo < 256 -> hi < 256 -> (exists p, V293_bitmap_ready lo hi p) ->
  V293_bitmap_tasks lo hi tasks -> V293_priority_table entries tasks ->
  Forall (fun v => rule_type_val_match (Tptr tp) v = true) entries ->
  indom tasks tid -> GoodFrm px -> (px ==> LINV V293_shared_li tid nil ** Atrue) ->
  Spec sched_id = Some
    (V293_critical_fpre unmap group rows high bt bg br bh V293_shared_li V293_opened_inv V293_switch_li_good,
     V293_critical_fpost unmap group rows high bt bg br bh V293_shared_li V293_opened_inv V293_switch_li_good,
     (Tvoid, nil)) ->
  InfRules Spec V293_scheduler V293_shared_li readyI r ri
    (checked_ready_connect_entry old hv)
    (sseq (sseq (scall sched_id nil) (sassign (evar target) (earrayelem (evar table) (evar high))))
      (sseq (sassign (evar counter) (ebinop oplus (evar counter) (econst32 Int.one)))
        (sprim (switch target)))) ready_resumed tid.
Proof. exact (V293_ready_OSSched_prefix_increment_switch unmap group rows high table target counter bt bg br bh bp bo bcounter
    tp lo hi entries rest tid tasks events now aop stack critical px). Qed.
Definition checked_ready_self_finish : forall c,
  lo < 256 -> hi < 256 -> (exists p, V293_bitmap_ready lo hi p) ->
  V293_bitmap_tasks lo hi tasks -> V293_priority_table entries tasks ->
  Forall (fun v => rule_type_val_match (Tptr tp) v = true) entries ->
  V293_highest_ready tasks tid -> GoodFrm px ->
  absinferfull V293_scheduler V293_shared_li (tail tid c) ready_resumed tid :=
  V293_ready_connected_self_finish unmap group rows high table target counter bt bg br bh bp bo bcounter
    tp lo hi entries rest tid tasks events now aop stack critical px.
End FixedConnect.
Print Assumptions checked_increment_under.
Print Assumptions checked_ready_connect_return.
Print Assumptions checked_ready_connect_switch.
Print Assumptions checked_ready_connect.
Definition checked_entry_witness : forall different c events now aop,
  exists s,
    V293_bitmap_tasks 0 16 (V293_current_mode_tasks different) /\
    V293_priority_table (V293_current_mode_entries different) (V293_current_mode_tasks different) /\
    V293_current_task (V293_current_mode_tasks different) V293_idle_tid (V293_current_mode_priority different) /\
    Forall (fun v => rule_type_val_match (Tptr Tvoid) v = true) (V293_current_mode_entries different) /\
    s |= checked_entry 100%Z 101%Z 102%Z 103%Z 106%Z 107%Z 108%Z
      1%positive 2%positive 3%positive 4%positive 8%positive 10%positive 12%positive Tvoid 0 16
      (V293_current_mode_entries different) nil V293_idle_tid
      (V293_current_mode_tasks different) events now aop nil nil Aemp V293_idle_tid (V293_byteval 0) //\\
      ((PV (12%positive, Int.zero) @ Tint32 |-> (Vint32 c)) ** Atrue) :=
  V293_storage_connected_entry_witness.
Print Assumptions checked_open.
Print Assumptions checked_return.
Print Assumptions checked_increment.
Print Assumptions checked_connect.
Print Assumptions checked_entry_witness.

(* Exact-priority interface is written independently of retained/priority aliases. *)
Section FixedPriority.
Variables unmap group rows high table target current : var.
Variables bt bg br bh bp bo bcur : block.
Variable tp : type.
Variables lo hi nc : nat.
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
Let pcells := (checked_cells bt 0 1 Tint8 256 ++
  checked_cells br 0 1 Tint8 2 ++ [((bg, 0%Z), Tint8)]) ++
  [((bh, 0%Z), Tint8)] ++ checked_cells bp 0 4 (Tptr tp) (length entries) ++
  ((bcur, 0%Z), Tint8) :: rest.
Let pkept := (PV (bcur, Int.zero) @ Tint8 |-> (V293_byteval nc)) ** V293_storage rest.
Let pbindings := (Agvarenv current Tint8 (bcur, 0%Z) //\\ A_notin_lenv current) ** px.
Let pheap hv :=
  ((checked_array true bt 0 1 Tint8 (map V293_byteval V293_ready_table) **
    checked_array true br 0 1 Tint8 (map V293_byteval [lo;hi])) **
    Amapsto (bg, 0%Z) Tint8 true (V293_byteval (V293_ready_group lo hi))) **
  ((PV (bh, Int.zero) @ Tint8 |-> hv) **
    (checked_array true bp 0 4 (Tptr tp) entries ** pkept)).
Definition checked_priority_entry old hv :=
  <||aop||> ** (((SWINV (V293_storage_inv pcells target tp) //\\
    (V293_storage_open target tp tid tasks events now old ** pheap hv)) ** CurTid tid) **
    ((Ais stack ** Acs critical) **
      ((V293_sched_globals unmap group rows high bt bg br bh **
        V293_prefix_bindings table high target tp bp bo) ** pbindings))).
Let psnapshot next := SWINV (V293_storage_inv pcells target tp) //\\
  (((CurTid tid ** V293_shared_fields tid tasks events now) **
    (GV target @ (Tptr tp) |-> (Vptr next))) **
    (pheap (V293_byteval (V293_ready_select lo hi (V293_ready_group lo hi))) ** Atrue)).
Let pclosed := EX next : Modules.tid, [|V293_highest_ready tasks next|] **
  ((<||aop||> ** ((psnapshot next ** CurTid tid) ** (Ais stack ** Acs critical))) **
    ((V293_sched_globals unmap group rows high bt bg br bh **
      V293_prefix_bindings table high target tp bp bo) ** (pbindings ** Atrue))).
Definition checked_priority_comparison : forall s,
  lo < 256 -> hi < 256 -> (exists p, V293_bitmap_ready lo hi p) -> nc < 256 ->
  s |= pclosed ->
  evalval (eunop oppsite (ebinop oeq (ecast (evar high) Tint32) (ecast (evar current) Tint32)))
    (getsmem s) = Some (Vint32
      (if Nat.eqb (V293_ready_select lo hi (V293_ready_group lo hi)) nc then Int.zero else Int.one)) /\
  evaltype (eunop oppsite (ebinop oeq (ecast (evar high) Tint32) (ecast (evar current) Tint32)))
    (getsmem s) = Some Tint32 :=
  V293_storage_priority_comparison unmap group rows high table target current bt bg br bh bp bo bcur
    tp lo hi nc entries rest tid tasks events now aop stack critical px.
Definition checked_priority_prefix : forall Spec r ri sched_id old hv,
  lo < 256 -> hi < 256 -> (exists p, V293_bitmap_ready lo hi p) -> nc < 256 ->
  V293_bitmap_tasks lo hi tasks -> V293_priority_table entries tasks ->
  Forall (fun v => rule_type_val_match (Tptr tp) v = true) entries -> GoodFrm px ->
  Spec sched_id = Some
    (V293_critical_fpre unmap group rows high bt bg br bh V293_shared_li V293_opened_inv V293_switch_li_good,
     V293_critical_fpost unmap group rows high bt bg br bh V293_shared_li V293_opened_inv V293_switch_li_good,
     (Tvoid, nil)) ->
  InfRules Spec V293_scheduler V293_shared_li (V293_storage_inv pcells target tp) r ri
    (checked_priority_entry old hv)
    (sseq (scall sched_id nil) (sassign (evar target) (earrayelem (evar table) (evar high))))
    pclosed tid :=
  V293_OSSched_storage_priority_prefix unmap group rows high table target current bt bg br bh bp bo bcur
    tp lo hi nc entries rest tid tasks events now aop stack critical px.
End FixedPriority.
Definition checked_priority_entry_witness : forall different events now aop,
  exists s,
    V293_bitmap_tasks 0 16 (V293_current_mode_tasks different) /\
    V293_priority_table (V293_current_mode_entries different) (V293_current_mode_tasks different) /\
    V293_current_task (V293_current_mode_tasks different) V293_idle_tid (V293_current_mode_priority different) /\
    Forall (fun v => rule_type_val_match (Tptr Tvoid) v = true) (V293_current_mode_entries different) /\
    s |= checked_priority_entry 100%Z 101%Z 102%Z 103%Z 106%Z 107%Z 108%Z
      1%positive 2%positive 3%positive 4%positive 8%positive 10%positive 12%positive Tvoid 0 16
      (V293_current_mode_priority different) (V293_current_mode_entries different) nil V293_idle_tid
      (V293_current_mode_tasks different) events now (sched;;aop) nil nil Aemp
      V293_idle_tid (V293_byteval 0) :=
  V293_storage_priority_entry_witness.
Print Assumptions checked_priority_comparison.
Print Assumptions checked_priority_prefix.
Print Assumptions checked_priority_entry_witness.

Section FixedConditional.
Variables unmap group rows high table target current counter : var.
Variables bt bg br bh bp bo bcur bcounter : block.
Variable tp : type.
Variables lo hi nc : nat.
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
Let pcells := (checked_cells bt 0 1 Tint8 256 ++
  checked_cells br 0 1 Tint8 2 ++ [((bg, 0%Z), Tint8)]) ++
  [((bh, 0%Z), Tint8)] ++ checked_cells bp 0 4 (Tptr tp) (length entries) ++
  ((bcounter, 0%Z), Tint32) :: ((bcur, 0%Z), Tint8) :: rest.
Let pkept := (EX v : val, [|rule_type_val_match Tint32 v = true|] **
  Amapsto (bcounter, 0%Z) Tint32 true v) ** (PV (bcur, Int.zero) @ Tint8 |-> (V293_byteval nc)) ** V293_storage rest.
Let pbindings := V293_counter_bindings counter bcounter **
  ((Agvarenv current Tint8 (bcur, 0%Z) //\\ A_notin_lenv current) ** px).
Let pheap hv :=
  ((checked_array true bt 0 1 Tint8 (map V293_byteval V293_ready_table) **
    checked_array true br 0 1 Tint8 (map V293_byteval [lo;hi])) **
    Amapsto (bg, 0%Z) Tint8 true (V293_byteval (V293_ready_group lo hi))) **
  ((PV (bh, Int.zero) @ Tint8 |-> hv) **
    (checked_array true bp 0 4 (Tptr tp) entries ** pkept)).
Definition checked_conditional_entry old hv :=
  <||sched;;aop||> ** (((SWINV (V293_storage_inv pcells target tp) //\\
    (V293_storage_open target tp tid tasks events now old ** pheap hv)) ** CurTid tid) **
    ((Ais stack ** Acs critical) **
      ((V293_sched_globals unmap group rows high bt bg br bh **
        V293_prefix_bindings table high target tp bp bo) ** pbindings))).
Let psnapshot next := SWINV (V293_storage_inv pcells target tp) //\\
  (((CurTid tid ** V293_shared_fields tid tasks events now) **
    (GV target @ (Tptr tp) |-> (Vptr next))) **
    (pheap (V293_byteval (V293_ready_select lo hi (V293_ready_group lo hi))) ** Atrue)).
Let pclosed := EX next : Modules.tid, [|V293_highest_ready tasks next|] **
  ((<||sched;;aop||> ** ((psnapshot next ** CurTid tid) ** (Ais stack ** Acs critical))) **
    ((V293_sched_globals unmap group rows high bt bg br bh **
      V293_prefix_bindings table high target tp bp bo) ** (pbindings ** Atrue))).
Let cresumed := <||aop||> ** SWINVt (V293_storage_inv pcells target tp) tid **
  Ais stack ** Acs critical **
  ((V293_sched_globals unmap group rows high bt bg br bh **
    V293_prefix_bindings table high target tp bp bo) ** (pbindings ** Atrue)).
Definition checked_conditional_comparison : forall s,
  lo < 256 -> hi < 256 -> (exists p, V293_bitmap_ready lo hi p) -> nc < 256 ->
  s |= pclosed ->
  evalval (eunop oppsite (ebinop oeq (ecast (evar high) Tint32) (ecast (evar current) Tint32)))
    (getsmem s) = Some (Vint32
      (if Nat.eqb (V293_ready_select lo hi (V293_ready_group lo hi)) nc then Int.zero else Int.one)) /\
  evaltype (eunop oppsite (ebinop oeq (ecast (evar high) Tint32) (ecast (evar current) Tint32)))
    (getsmem s) = Some Tint32 :=
  V293_conditional_comparison unmap group rows high table target current counter bt bg br bh bp bo bcur bcounter
    tp lo hi nc entries rest tid tasks events now aop stack critical px.
Definition checked_conditional_equal_finish :
  lo < 256 -> hi < 256 -> (exists p, V293_bitmap_ready lo hi p) -> nc < 256 ->
  V293_bitmap_tasks lo hi tasks -> V293_priority_table entries tasks ->
  Forall (fun v => rule_type_val_match (Tptr tp) v = true) entries ->
  V293_current_task tasks tid nc -> GoodFrm px ->
  V293_ready_select lo hi (V293_ready_group lo hi) = nc ->
  absinferfull V293_scheduler V293_shared_li pclosed cresumed tid :=
  V293_conditional_equal_finish unmap group rows high table target current counter bt bg br bh bp bo bcur bcounter
    tp lo hi nc entries rest tid tasks events now aop stack critical px.
Definition checked_conditional : forall Spec r ri sched_id old hv,
  lo < 256 -> hi < 256 -> (exists p, V293_bitmap_ready lo hi p) -> nc < 256 ->
  V293_bitmap_tasks lo hi tasks -> V293_priority_table entries tasks ->
  Forall (fun v => rule_type_val_match (Tptr tp) v = true) entries ->
  V293_current_task tasks tid nc -> indom tasks tid -> GoodFrm px ->
  (px ==> LINV V293_shared_li tid nil ** Atrue) ->
  Spec sched_id = Some
    (V293_critical_fpre unmap group rows high bt bg br bh V293_shared_li V293_opened_inv V293_switch_li_good,
     V293_critical_fpost unmap group rows high bt bg br bh V293_shared_li V293_opened_inv V293_switch_li_good,
     (Tvoid, nil)) ->
  InfRules Spec V293_scheduler V293_shared_li (V293_storage_inv pcells target tp) r ri
    (checked_conditional_entry old hv)
    (sseq (sseq (scall sched_id nil) (sassign (evar target) (earrayelem (evar table) (evar high))))
      (sifthen (eunop oppsite (ebinop oeq (ecast (evar high) Tint32) (ecast (evar current) Tint32)))
        (sseq (sassign (evar counter) (ebinop oplus (evar counter) (econst32 Int.one)))
          (sprim (switch target))))) cresumed tid :=
  V293_OSSched_storage_conditional unmap group rows high table target current counter bt bg br bh bp bo bcur bcounter
    tp lo hi nc entries rest tid tasks events now aop stack critical px.
End FixedConditional.
Definition checked_conditional_entry_witness : forall different c events now aop,
  exists s,
    V293_bitmap_tasks 0 16 (V293_current_mode_tasks different) /\
    V293_priority_table (V293_current_mode_entries different) (V293_current_mode_tasks different) /\
    V293_current_task (V293_current_mode_tasks different) V293_idle_tid (V293_current_mode_priority different) /\
    Forall (fun v => rule_type_val_match (Tptr Tvoid) v = true) (V293_current_mode_entries different) /\
    s |= (checked_conditional_entry 100%Z 101%Z 102%Z 103%Z 106%Z 107%Z 108%Z 109%Z
      1%positive 2%positive 3%positive 4%positive 8%positive 10%positive 12%positive 13%positive Tvoid 0 16
      (V293_current_mode_priority different) (V293_current_mode_entries different) nil V293_idle_tid
      (V293_current_mode_tasks different) events now aop nil nil Aemp
      V293_idle_tid (V293_byteval 0)) //\\
      ((PV (13%positive, Int.zero) @ Tint32 |-> (Vint32 c)) ** Atrue) :=
  V293_storage_conditional_entry_witness.
Print Assumptions checked_conditional_comparison.
Print Assumptions checked_conditional_equal_finish.
Print Assumptions checked_conditional.
Print Assumptions checked_conditional_entry_witness.

Section FixedGuards.
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
Let gb := (Agvarenv interrupt Tint8 (bi, 0%Z) //\\ A_notin_lenv interrupt) **
  ((Agvarenv lock Tint8 (bl, 0%Z) //\\ A_notin_lenv lock) ** px).
Let grest := ((bi, 0%Z), Tint8) :: ((bl, 0%Z), Tint8) :: rest.
Let gcells := (checked_cells bt 0 1 Tint8 256 ++
  checked_cells br 0 1 Tint8 2 ++ [((bg, 0%Z), Tint8)]) ++
  [((bh, 0%Z), Tint8)] ++ checked_cells bp 0 4 (Tptr tp) (length entries) ++
  ((bcounter, 0%Z), Tint32) :: ((bcur, 0%Z), Tint8) :: grest.
Definition checked_guarded_entry old hv :=
  checked_conditional_entry unmap group rows high table target current counter
    bt bg br bh bp bo bcur bcounter tp lo hi nc entries grest tid tasks events now aop
    stack critical gb old hv //\\
  ((((Agvarenv interrupt Tint8 (bi, 0%Z) //\\ A_notin_lenv interrupt) **
      Amapsto (bi, 0%Z) Tint8 false (V293_byteval ni)) **
    ((Agvarenv lock Tint8 (bl, 0%Z) //\\ A_notin_lenv lock) **
      Amapsto (bl, 0%Z) Tint8 false (V293_byteval nl))) ** Atrue).
Let gresumed := <||aop||> ** SWINVt (V293_storage_inv gcells target tp) tid **
  Ais stack ** Acs critical **
  ((V293_sched_globals unmap group rows high bt bg br bh **
    V293_prefix_bindings table high target tp bp bo) **
    ((V293_counter_bindings counter bcounter **
      ((Agvarenv current Tint8 (bcur, 0%Z) //\\ A_notin_lenv current) ** gb)) ** Atrue)).
Definition checked_guarded : forall Spec r ri sched_id old hv,
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
  InfRules Spec V293_scheduler V293_shared_li (V293_storage_inv gcells target tp) r ri
    (checked_guarded_entry old hv)
    (sifthen (ebinop oeq (ecast (evar interrupt) Tint32) (econst32 (Int.repr 0)))
      (sifthen (ebinop oeq (ecast (evar lock) Tint32) (econst32 (Int.repr 0)))
        (sseq (sseq (scall sched_id nil) (sassign (evar target) (earrayelem (evar table) (evar high))))
          (sifthen (eunop oppsite (ebinop oeq (ecast (evar high) Tint32) (ecast (evar current) Tint32)))
            (sseq (sassign (evar counter) (ebinop oplus (evar counter) (econst32 Int.one)))
              (sprim (switch target)))))))
    (if Nat.eqb ni 0 && Nat.eqb nl 0 then gresumed else checked_guarded_entry old hv) tid :=
  V293_OSSched_storage_guarded unmap group rows high table target current counter interrupt lock
    bt bg br bh bp bo bcur bcounter bi bl tp lo hi nc ni nl entries rest tid tasks events now aop stack critical px.
End FixedGuards.
Definition checked_guarded_entry_witness : forall different c ni nl events now aop,
  ni < 256 -> nl < 256 ->
  exists s,
    V293_bitmap_tasks 0 16 (V293_current_mode_tasks different) /\
    V293_priority_table (V293_current_mode_entries different) (V293_current_mode_tasks different) /\
    V293_current_task (V293_current_mode_tasks different) V293_idle_tid (V293_current_mode_priority different) /\
    Forall (fun v => rule_type_val_match (Tptr Tvoid) v = true) (V293_current_mode_entries different) /\
    s |= (checked_guarded_entry 100%Z 101%Z 102%Z 103%Z 106%Z 107%Z 108%Z 109%Z 110%Z 111%Z
      1%positive 2%positive 3%positive 4%positive 8%positive 10%positive 12%positive 13%positive 14%positive 15%positive
      Tvoid 0 16 (V293_current_mode_priority different) ni nl (V293_current_mode_entries different) nil V293_idle_tid
      (V293_current_mode_tasks different) events now aop nil nil Aemp
      V293_idle_tid (V293_byteval 0)) //\\
      ((PV (13%positive, Int.zero) @ Tint32 |-> (Vint32 c)) ** Atrue) :=
  V293_storage_guarded_entry_witness.
Print Assumptions checked_guarded.
Print Assumptions checked_guarded_entry_witness.

Definition checked_ready_connect_entry_witness : forall different c events now aop,
  exists s,
    V293_bitmap_tasks 0 16 (V293_current_mode_tasks different) /\
    V293_priority_table (V293_current_mode_entries different) (V293_current_mode_tasks different) /\
    V293_current_task (V293_current_mode_tasks different) V293_idle_tid (V293_current_mode_priority different) /\
    Forall (fun v => rule_type_val_match (Tptr Tvoid) v = true) (V293_current_mode_entries different) /\
    s |= checked_ready_connect_entry 100%Z 101%Z 102%Z 103%Z 106%Z 107%Z 108%Z
      1%positive 2%positive 3%positive 4%positive 8%positive 10%positive 12%positive Tvoid 0 16
      (V293_current_mode_entries different) nil V293_idle_tid
      (V293_current_mode_tasks different) events now aop nil nil Aemp (Vptr V293_idle_tid) (V293_byteval 0) //\\
      ((PV (12%positive, Int.zero) @ Tint32 |-> (Vint32 c)) ** Atrue).
Proof. apply V293_ready_connected_entry_witness. Qed.
Print Assumptions checked_ready_connect_entry_witness.

(* One abstract self-schedule mechanism, with task data from the same resource. *)
Definition checked_self_schedule_consume : forall resources tid tasks events now aop,
  can_change_aop resources ->
  (resources ==> (CurTid tid ** V293_shared_fields tid tasks events now) ** Atrue) ->
  V293_highest_ready tasks tid ->
  absinferfull V293_scheduler V293_shared_li
    (<||sched;;aop||> ** resources) (<||aop||> ** resources) tid :=
  V293_self_schedule_consume.
Print Assumptions checked_ready_self_finish.
Print Assumptions checked_self_schedule_consume.

Section FixedReadyConditional.
Variables unmap group rows high table target current counter : var.
Variables bt bg br bh bp bo bcur bcounter : block.
Variable tp : type.
Variables lo hi nc : nat.
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
Let extra := ((bcounter, 0%Z), Tint32) :: ((bcur, 0%Z), Tint8) :: rest.
Let readyI := V293_ready_inv bt bg br bh bp tp extra target.
Let pkept := (EX v : val, [|rule_type_val_match Tint32 v = true|] **
  Amapsto (bcounter, 0%Z) Tint32 true v) ** (PV (bcur, Int.zero) @ Tint8 |-> (V293_byteval nc)) ** V293_storage rest.
Let pbindings := V293_counter_bindings counter bcounter **
  ((Agvarenv current Tint8 (bcur, 0%Z) //\\ A_notin_lenv current) ** px).
Let pheap hv :=
  ((checked_array true bt 0 1 Tint8 (map V293_byteval V293_ready_table) **
    checked_array true br 0 1 Tint8 (map V293_byteval [lo;hi])) **
    Amapsto (bg, 0%Z) Tint8 true (V293_byteval (V293_ready_group lo hi))) **
  ((PV (bh, Int.zero) @ Tint8 |-> hv) **
    (checked_array true bp 0 4 (Tptr tp) entries ** pkept)).
Definition checked_ready_conditional_entry old hv :=
  <||sched;;aop||> ** (((SWINV readyI //\\
    ((V293_shared_flags ** ((CurTid tid ** V293_shared_fields tid tasks events now) **
      (GV target @ (Tptr tp) |-> old))) ** pheap hv)) ** CurTid tid) **
    ((Ais stack ** Acs critical) **
      ((V293_sched_globals unmap group rows high bt bg br bh **
        V293_prefix_bindings table high target tp bp bo) ** pbindings))).
Let pclosed := EX next : Modules.tid, [|V293_highest_ready tasks next|] **
  ((<||sched;;aop||> ** (((V293_storage_open target tp tid tasks events now next **
    pheap (V293_byteval (V293_ready_select lo hi (V293_ready_group lo hi)))) ** CurTid tid) **
    (Ais stack ** Acs critical))) **
    ((V293_sched_globals unmap group rows high bt bg br bh **
      V293_prefix_bindings table high target tp bp bo) ** (pbindings ** Atrue))).
Let cresumed := <||aop||> ** SWINVt readyI tid **
  Ais stack ** Acs critical **
  ((V293_sched_globals unmap group rows high bt bg br bh **
    V293_prefix_bindings table high target tp bp bo) ** (pbindings ** Atrue)).
Definition checked_ready_conditional_comparison : forall s,
  lo < 256 -> hi < 256 -> (exists p, V293_bitmap_ready lo hi p) -> nc < 256 ->
  s |= pclosed ->
  evalval (eunop oppsite (ebinop oeq (ecast (evar high) Tint32) (ecast (evar current) Tint32)))
    (getsmem s) = Some (Vint32
      (if Nat.eqb (V293_ready_select lo hi (V293_ready_group lo hi)) nc then Int.zero else Int.one)) /\
  evaltype (eunop oppsite (ebinop oeq (ecast (evar high) Tint32) (ecast (evar current) Tint32)))
    (getsmem s) = Some Tint32 :=
  V293_ready_conditional_comparison unmap group rows high table target current counter bt bg br bh bp bo bcur bcounter
    tp lo hi nc entries rest tid tasks events now aop stack critical px.
Definition checked_ready_conditional_equal_finish :
  lo < 256 -> hi < 256 -> (exists p, V293_bitmap_ready lo hi p) -> nc < 256 ->
  V293_bitmap_tasks lo hi tasks -> V293_priority_table entries tasks ->
  Forall (fun v => rule_type_val_match (Tptr tp) v = true) entries ->
  V293_current_task tasks tid nc -> GoodFrm px ->
  V293_ready_select lo hi (V293_ready_group lo hi) = nc ->
  absinferfull V293_scheduler V293_shared_li pclosed cresumed tid :=
  V293_ready_conditional_equal_finish unmap group rows high table target current counter bt bg br bh bp bo bcur bcounter
    tp lo hi nc entries rest tid tasks events now aop stack critical px.
Definition checked_ready_conditional : forall Spec r ri sched_id old hv,
  lo < 256 -> hi < 256 -> (exists p, V293_bitmap_ready lo hi p) -> nc < 256 ->
  V293_bitmap_tasks lo hi tasks -> V293_priority_table entries tasks ->
  Forall (fun v => rule_type_val_match (Tptr tp) v = true) entries ->
  V293_current_task tasks tid nc -> indom tasks tid -> GoodFrm px ->
  (px ==> LINV V293_shared_li tid nil ** Atrue) ->
  Spec sched_id = Some
    (V293_critical_fpre unmap group rows high bt bg br bh V293_shared_li V293_opened_inv V293_switch_li_good,
     V293_critical_fpost unmap group rows high bt bg br bh V293_shared_li V293_opened_inv V293_switch_li_good,
     (Tvoid, nil)) ->
  InfRules Spec V293_scheduler V293_shared_li readyI r ri
    (checked_ready_conditional_entry old hv)
    (sseq (sseq (scall sched_id nil) (sassign (evar target) (earrayelem (evar table) (evar high))))
      (sifthen (eunop oppsite (ebinop oeq (ecast (evar high) Tint32) (ecast (evar current) Tint32)))
        (sseq (sassign (evar counter) (ebinop oplus (evar counter) (econst32 Int.one)))
          (sprim (switch target))))) cresumed tid :=
  V293_ready_OSSched_conditional unmap group rows high table target current counter bt bg br bh bp bo bcur bcounter
    tp lo hi nc entries rest tid tasks events now aop stack critical px.
End FixedReadyConditional.
Definition checked_ready_conditional_entry_witness : forall different c events now aop,
  exists s,
    V293_bitmap_tasks 0 16 (V293_current_mode_tasks different) /\
    V293_priority_table (V293_current_mode_entries different) (V293_current_mode_tasks different) /\
    V293_current_task (V293_current_mode_tasks different) V293_idle_tid (V293_current_mode_priority different) /\
    Forall (fun v => rule_type_val_match (Tptr Tvoid) v = true) (V293_current_mode_entries different) /\
    s |= (checked_ready_conditional_entry 100%Z 101%Z 102%Z 103%Z 106%Z 107%Z 108%Z 109%Z
      1%positive 2%positive 3%positive 4%positive 8%positive 10%positive 12%positive 13%positive Tvoid 0 16
      (V293_current_mode_priority different) (V293_current_mode_entries different) nil V293_idle_tid
      (V293_current_mode_tasks different) events now aop nil nil Aemp
      (Vptr V293_idle_tid) (V293_byteval 0)) //\\
      ((PV (13%positive, Int.zero) @ Tint32 |-> (Vint32 c)) ** Atrue) :=
  V293_ready_conditional_entry_witness.
Print Assumptions checked_ready_conditional_comparison.
Print Assumptions checked_ready_conditional_equal_finish.
Print Assumptions checked_ready_conditional.
Print Assumptions checked_ready_conditional_entry_witness.
