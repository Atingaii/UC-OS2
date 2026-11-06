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
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedPointerCompare.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Fixpoint checked_array (w : bool) (b : block) (offset step : Z) (tau : type) (vs : list val) : asrt :=
  match vs with
  | nil => Aemp
  | v :: tail => Amapsto (b, offset) tau w v ** checked_array w b (offset + step)%Z step tau tail
  end.
Section FreshGuards.
Variables unmap group rows high table target counter interrupt lock : var.
Variables bt bg br bh bp bo bcounter bi bl : block.
Variable tp : type.
Variable rest : list (addr * type).
Variable tid : Modules.tid.
Variable aop : spec_code.
Variable stack : list hid.
Variable critical : list bool.
Variable px : asrt.
Let guardrest := ((bi, 0%Z), Tint8) :: ((bl, 0%Z), Tint8) :: rest.
Let extra := ((bcounter, 0%Z), Tint32) :: guardrest.
Let readyI := V293_ready_inv bt bg br bh bp tp extra target.
Let bindings := V293_sched_globals unmap group rows high bt bg br bh **
  V293_prefix_bindings table high target tp bp bo.
Let private := V293_counter_bindings counter bcounter **
  (((Agvarenv interrupt Tint8 (bi, 0%Z) //\\ A_notin_lenv interrupt) **
    (Agvarenv lock Tint8 (bl, 0%Z) //\\ A_notin_lenv lock)) ** px).
Let locals := bindings ** (private ** Atrue).
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
Definition checked_guard_observation :
  (<||sched;;aop||> ** ((checked_snapshot ** CurTid tid) **
      ((V293_shared_flags ** (Ais stack ** Acs critical)) ** (bindings ** private)))) ==>
  EX ni : nat, EX nl : nat, [|ni < 256 /\ nl < 256|] ** ((<||sched;;aop||> ** ((checked_snapshot ** CurTid tid) **
      ((V293_shared_flags ** (Ais stack ** Acs critical)) ** (bindings ** private)))) //\\ ((((Agvarenv interrupt Tint8 (bi, 0%Z) //\\ A_notin_lenv interrupt) ** Amapsto (bi, 0%Z) Tint8 false (V293_byteval ni)) ** ((Agvarenv lock Tint8 (bl, 0%Z) //\\ A_notin_lenv lock) ** Amapsto (bl, 0%Z) Tint8 false (V293_byteval nl))) ** Atrue)) :=
  V293_ready_guard_observe unmap group rows high table target counter interrupt lock bt bg br bh bp bo bcounter bi bl tp rest tid aop stack critical px.
Definition checked_guard_decision : forall Spec r ri sched_id ni nl,
  ni < 256 -> nl < 256 ->
  GoodFrm px -> (px ==> LINV V293_shared_li tid nil ** Atrue) ->
  (px ==> A_notin_lenv OSTCBCur ** Atrue) ->
  Spec sched_id = Some
    (V293_critical_fpre unmap group rows high bt bg br bh V293_shared_li V293_opened_inv V293_switch_li_good,
     V293_critical_fpost unmap group rows high bt bg br bh V293_shared_li V293_opened_inv V293_switch_li_good,
     (Tvoid, nil)) ->
  InfRules Spec V293_scheduler V293_shared_li readyI r ri
    ((<||sched;;aop||> ** ((checked_snapshot ** CurTid tid) **
      ((V293_shared_flags ** (Ais stack ** Acs critical)) ** (bindings ** private)))) //\\ ((((Agvarenv interrupt Tint8 (bi, 0%Z) //\\ A_notin_lenv interrupt) ** Amapsto (bi, 0%Z) Tint8 false (V293_byteval ni)) ** ((Agvarenv lock Tint8 (bl, 0%Z) //\\ A_notin_lenv lock) ** Amapsto (bl, 0%Z) Tint8 false (V293_byteval nl))) ** Atrue))
    (sifthen (ebinop oeq (ecast (evar interrupt) Tint32) (econst32 (Int.repr 0)))
      (sifthen (ebinop oeq (ecast (evar lock) Tint32) (econst32 (Int.repr 0)))
        (sseq (sseq (scall sched_id nil) (sassign (evar target) (earrayelem (evar table) (evar high))))
          (sifthen (eunop oppsite (ebinop oeq (evar target) (evar OSTCBCur)))
            (sseq (sassign (evar counter) (ebinop oplus (evar counter) (econst32 Int.one)))
              (sprim (switch target)))))))
    (<||(if Nat.eqb ni 0 && Nat.eqb nl 0 then aop else (sched;;aop))||> ** SWINVt readyI tid ** Ais stack ** Acs critical ** locals) tid :=
  fun Spec r ri sched_id =>
  V293_ready_OSSched_pointer_guards_observed unmap group rows high table target counter interrupt lock bt bg br bh bp bo bcounter bi bl tp rest
    Spec r ri sched_id tid aop stack critical px.
Definition checked_fresh_guards : forall Spec r ri sched_id,
  GoodFrm px -> (px ==> LINV V293_shared_li tid nil ** Atrue) ->
  (px ==> A_notin_lenv OSTCBCur ** Atrue) ->
  Spec sched_id = Some
    (V293_critical_fpre unmap group rows high bt bg br bh V293_shared_li V293_opened_inv V293_switch_li_good,
     V293_critical_fpost unmap group rows high bt bg br bh V293_shared_li V293_opened_inv V293_switch_li_good,
     (Tvoid, nil)) ->
  InfRules Spec V293_scheduler V293_shared_li readyI r ri
    (<||sched;;aop||> ** ((checked_snapshot ** CurTid tid) **
      ((V293_shared_flags ** (Ais stack ** Acs critical)) ** (bindings ** private))))
    (sifthen (ebinop oeq (ecast (evar interrupt) Tint32) (econst32 (Int.repr 0)))
      (sifthen (ebinop oeq (ecast (evar lock) Tint32) (econst32 (Int.repr 0)))
        (sseq (sseq (scall sched_id nil) (sassign (evar target) (earrayelem (evar table) (evar high))))
          (sifthen (eunop oppsite (ebinop oeq (evar target) (evar OSTCBCur)))
            (sseq (sassign (evar counter) (ebinop oplus (evar counter) (econst32 Int.one)))
              (sprim (switch target)))))))
    (EX ni : nat, EX nl : nat, [|ni < 256 /\ nl < 256|] ** (<||(if Nat.eqb ni 0 && Nat.eqb nl 0 then aop else (sched;;aop))||> ** SWINVt readyI tid ** Ais stack ** Acs critical ** locals)) tid :=
  fun Spec r ri sched_id =>
  V293_ready_OSSched_pointer_guards_fresh unmap group rows high table target counter interrupt lock bt bg br bh bp bo bcounter bi bl tp rest
    Spec r ri sched_id tid aop stack critical px.
Definition checked_guarded_critical : forall Spec r ri sched_id,
  GoodFrm px -> (px ==> LINV V293_shared_li tid nil ** Atrue) ->
  (px ==> A_notin_lenv OSTCBCur ** Atrue) ->
  Spec sched_id = Some
    (V293_critical_fpre unmap group rows high bt bg br bh V293_shared_li V293_opened_inv V293_switch_li_good,
     V293_critical_fpost unmap group rows high bt bg br bh V293_shared_li V293_opened_inv V293_switch_li_good,
     (Tvoid, nil)) ->
  InfRules Spec V293_scheduler V293_shared_li readyI r ri
    (<||sched;;aop||> ** OS[(fun _ : hid => false), true, nil, critical] **
      ATopis INUM ** (CurTid tid ** (bindings ** private)))
    (sseq (sprim encrit) (sseq (sifthen (ebinop oeq (ecast (evar interrupt) Tint32) (econst32 (Int.repr 0)))
      (sifthen (ebinop oeq (ecast (evar lock) Tint32) (econst32 (Int.repr 0)))
        (sseq (sseq (scall sched_id nil) (sassign (evar target) (earrayelem (evar table) (evar high))))
          (sifthen (eunop oppsite (ebinop oeq (evar target) (evar OSTCBCur)))
            (sseq (sassign (evar counter) (ebinop oplus (evar counter) (econst32 Int.one)))
              (sprim (switch target))))))) (sprim excrit)))
    (EX ni : nat, EX nl : nat, [|ni < 256 /\ nl < 256|] **
      (<||(if Nat.eqb ni 0 && Nat.eqb nl 0 then aop else (sched;;aop))||> ** OS[(fun _ : hid => false), true, nil, critical] **
        (CurTid tid ** (bindings ** (private ** Atrue))))) tid :=
  fun Spec r ri sched_id =>
  V293_ready_OSSched_pointer_guarded_critical unmap group rows high table target counter interrupt lock bt bg br bh bp bo bcounter bi bl tp rest
    Spec r ri sched_id tid aop critical px.
End FreshGuards.
Print Assumptions checked_guard_observation.
Print Assumptions checked_guard_decision.
Print Assumptions checked_fresh_guards.
Print Assumptions checked_guarded_critical.
