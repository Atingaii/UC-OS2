(* One shared physical layout connects the actual prefix, conditional,
   UINT32 increment / ordinary switch or abstract self-schedule, then both
   guards. Candidate critical wrapper is connected; frozen-C/source-port
   correspondence and the full OS proof remain open. *)
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedStoragePrefix.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedStorageTail.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchStorage.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedChange.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedSwitch.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedSwitchPre.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCurrent.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedPointerCompare.
Require Import CertiOS.framework.proof.auxdef.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.framework.proof.lmachLib.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchState.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedGuards.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCritical.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedShared.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedPrefix.
Require Import CertiOS.certiucos.v293.code.V293OSSchedDispatch.
Require Import CertiOS.certiucos.v293.code.V293OSSchedChange.
Require Import CertiOS.certiucos.v293.code.V293OSSchedGuards.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.sep_combine_lemmas.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import Coq.Lists.List Lia Coq.Logic.Classical_Prop.
Import ListNotations.
Local Open Scope nat_scope.

(* Flags are empty-memory observations, not a second copy of the core. *)
Lemma V293_storage_observation_flags : forall cells target tp P,
  SWINV (V293_storage_inv cells target tp) //\\ P ==> V293_shared_flags ** P.
Proof.
  intros cells target tp P s [HI HP].
  apply V293_storage_switch_open in HI.
  destruct s as [[[[[[ge le] M] ir] aux] O] op].
  assert (HC : forall i, ir i = false).
  { clear HP. eapply (V293_shared_clear_state ge le M ir aux O op). unfold V293_shared_flags in HI. sep auto. }
  assert (HE : getie (gettaskst (ge, le, M, ir, aux, O, op)) = false).
  { clear HP. assert (HK : (ge, le, M, ir, aux, O, op) |= Aie false ** Atrue)
      by (unfold V293_shared_flags in HI; sep auto).
    exact (proj1 (astar_l_aie_elim HK)). }
  clear HI.
  apply astar_l_atopis_intro with (i := gettopis (getis (gettaskst (ge, le, M, ir, aux, O, op)))) in HP;
    [ | reflexivity].
  apply astar_l_aie_intro with (i := false) in HP; [ | exact HE].
  apply astar_l_aisr_intro with (i := ir) in HP; [ | reflexivity].
  assert (HR : Aisr ir ==> isrclr).
  { intros st H. unfold isrclr. exists ir. split; [exact H | ].
    destruct st as [[[[[[g l] m] r] a] o] p]. simpl in *. tauto. }
  eapply astar_mono in HP; [ | exact HR | intros st H; exact H].
  unfold V293_shared_flags. sep auto.
Qed.

(* Abstract self-scheduling consumes sched without changing physical resources.
   The task table must be obtained from those SAME resources. *)
Lemma V293_self_schedule_consume : forall resources tid tasks events now aop,
  can_change_aop resources ->
  (resources ==> (CurTid tid ** V293_shared_fields tid tasks events now) ** Atrue) ->
  V293_highest_ready tasks tid ->
  absinferfull V293_scheduler V293_shared_li
    (<||sched;;aop||> ** resources) (<||aop||> ** resources) tid.
Proof.
  intros resources tid tasks events now aop Hfree Hfields Hhighest.
  eapply absinfer_trans' with (q := <||END None;;aop||> ** resources).
  - apply absinfer_seq'; try exact Hfree.
    eapply (absinfer_sched' _ (fun _ => True) _ _ _ _); try exact Hfree.
    + intros s H; exact H.
    + intros s Hs.
      destruct (V293_shared_fields_core_get _ _ _ _ _ _ (Hfields s Hs)) as [HC [HT _]].
      exists tid. split; [exact HC | exists tasks; auto].
  - apply absinfer_seq_end'; try exact Hfree. intros s H; exact H.
Qed.

(* A full named pointer cell supplies a real load in the encompassing memory. *)
Lemma V293_connected_pointer_cell_read : forall x tp t s,
  s |= (GV x @ (Tptr tp) |-> (Vptr t)) ** Atrue ->
  exists b, get (getgenv s) x = Some (b, Tptr tp) /\
    load (Tptr tp) (getmem s) (b, 0%Z) = Some (Vptr t).
Proof.
  intros x tp t s Hs. destruct s as [[[[[[ge le] M] ir] aux] O] op].
  apply sat_split in Hs.
  destruct Hs as (m1 & m2 & o1 & o2 & JM & JO & HC & HF).
  destruct (V293_dispatch_named_cell_parts _ _ _ _ _ _ _ _ _ _ HC) as (b & G & HM & HO).
  exists b. split; [exact G | ].
  assert (HL : load (Tptr tp) m1 (b, 0%Z) = Some (Vptr t)).
  { eapply mapstoval_load; [reflexivity | exact HM]. }
  eapply load_local; eauto.
Qed.

Section ConnectedPath.
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
Let cells := V293_prefix_cells bt bg br bh bp tp entries extra.
Let physical := V293_prefix_physical bt bg br bh bp tp lo hi entries rest.
Definition V293_storage_connected_locals :=
  (V293_sched_globals unmap group rows high bt bg br bh **
    V293_prefix_bindings table high target tp bp bo) **
    ((V293_counter_bindings counter bcounter ** px) ** Atrue).
Definition V293_storage_connected_payload next c :=
  <||sched;;aop||> ** ((V293_storage_open target tp tid tasks events now next ** CurTid tid) **
    ((Ais stack ** Acs critical) ** (physical ** (PV (bcounter, Int.zero) @ Tint32 |-> (Vint32 c))))).
Definition V293_storage_connected_tail next c :=
  V293_storage_connected_payload next c ** V293_storage_connected_locals.
Definition V293_storage_connected_resumed :=
  <||aop||> ** SWINVt (V293_storage_inv cells target tp) tid ** Ais stack ** Acs critical **
    V293_storage_connected_locals.
Let pre old hv := V293_storage_prefix_entry unmap group rows high table target bt bg br bh bp bo tp
  lo hi entries extra tid tasks events now (sched;;aop) stack critical
  (V293_counter_bindings counter bcounter ** px) old hv.
Let middle := V293_storage_prefix_closed unmap group rows high table target bt bg br bh bp bo tp
  lo hi entries extra tid tasks events now (sched;;aop) stack critical
  (V293_counter_bindings counter bcounter ** px).

Lemma V293_storage_connected_locals_good : GoodFrm px -> GoodFrm V293_storage_connected_locals.
Proof.
  intros H. unfold V293_storage_connected_locals, V293_sched_globals,
    V293_prefix_bindings, V293_counter_bindings. simpl. tauto.
Qed.

Lemma V293_storage_connected_prefix_open :
  middle ==> EX next : Modules.tid, EX c : int32, [|V293_highest_ready tasks next|] **
    V293_storage_connected_tail next c.
Proof.
  intros s [next Hs]. exists next.
  unfold V293_prefix_snapshot in Hs.
  assert (HP : V293_prefix_snapshot target bt bg br bh bp tp lo hi entries extra tid tasks events now next ==>
    V293_storage_open target tp tid tasks events now next **
      (V293_prefix_physical bt bg br bh bp tp lo hi entries extra ** Atrue)).
  { intros st H. apply V293_storage_observation_flags in H.
    unfold V293_storage_open. sep auto. }
  fold (V293_prefix_snapshot target bt bg br bh bp tp lo hi entries extra tid tasks events now next) in Hs.
  assert (HK : s |= V293_prefix_snapshot target bt bg br bh bp tp lo hi entries extra tid tasks events now next **
    ([|V293_highest_ready tasks next|] **
      ((<||sched;;aop||> ** CurTid tid) ** ((Ais stack ** Acs critical) **
        ((V293_sched_globals unmap group rows high bt bg br bh **
          V293_prefix_bindings table high target tp bp bo) **
          ((V293_counter_bindings counter bcounter ** px) ** Atrue)))))) by (sep auto).
  eapply astar_mono in HK; [ | exact HP | intros st H; exact H].
  unfold V293_prefix_physical in HK. cbn [extra V293_storage] in HK.
  unfold V293_storage_cell in HK. sep normal in HK. sep destruct HK. sep split in HK.
  destruct x; simpl in H; try discriminate.
  exists i. unfold V293_storage_connected_tail, V293_storage_connected_payload,
    V293_storage_connected_locals, physical, V293_prefix_physical.
  clear Hs. sep auto.
Qed.

Lemma V293_storage_connected_return : forall next c,
  lo < 256 -> hi < 256 -> (exists p, V293_bitmap_ready lo hi p) ->
  Forall (fun v => rule_type_val_match (Tptr tp) v = true) entries ->
  V293_storage_connected_payload next c ==>
  <||sched;;aop||> ** SWINVt (V293_storage_inv cells target tp) tid ** Ais stack ** Acs critical.
Proof.
  intros next c Hlo Hhi Hr Hptr s Hs.
  assert (HC : (PV (bcounter, Int.zero) @ Tint32 |-> (Vint32 c)) ==> V293_storage_cell (bcounter, 0%Z) Tint32).
  { intros st H. unfold V293_storage_cell. exists (Vint32 c). sep auto. }
  unfold V293_storage_connected_payload in Hs.
  eapply astar_mono in Hs.
  2: { intros st H; exact H. }
  2: { apply astar_mono; [intros st H; exact H | apply astar_mono;
    [intros st H; exact H | apply astar_mono; [intros st H; exact H | exact HC]]]. }
  assert (HP : s |= (V293_storage_open target tp tid tasks events now next **
      V293_prefix_physical bt bg br bh bp tp lo hi entries extra) **
    (<||sched;;aop||> ** (CurTid tid ** (Ais stack ** Acs critical)))).
  { unfold physical, V293_prefix_physical in *. cbn [extra V293_storage]. sep auto. }
  eapply astar_mono in HP.
  2: { apply astar_mono; [intros st H; exact H | apply V293_prefix_physical_return; assumption]. }
  2: { intros st H; exact H. }
  eapply astar_mono in HP; [ | apply V293_storage_return | intros st H; exact H].
  change (s |= <||sched;;aop||> **
    (SWINV (V293_storage_inv cells target tp) ** CurTid tid) ** Ais stack ** Acs critical).
  clear Hs. sep auto.
Qed.

(* Membership-independent scheduler precondition from the SAME physical tail. *)
Lemma V293_storage_connected_switch_highest : forall next c,
  V293_highest_ready tasks next ->
  V293_storage_connected_payload next c ==> SWPRE V293_scheduler target tid.
Proof.
  intros next c Hhighest s Hs.
  unfold V293_storage_connected_payload, V293_storage_open, V293_shared_fields in Hs.
  assert (HK : s |= (CurTid tid ** CurTid tid) **
    (Aabsdata abstcblsid (abstcblist tasks) **
      ((GV target @ (Tptr tp) |-> (Vptr next)) ** (isrclr ** Atrue)))).
  { unfold V293_shared_flags in Hs. sep auto. }
  eapply astar_mono in HK; [ | apply V293_current_halves_write | ].
  2: { apply astar_mono; [apply V293_tasks_highest_spatial; exact Hhighest | intros st H; exact H]. }
  unfold SWPRE. exists next. clear Hs. sep auto.
Qed.

Lemma V293_storage_connected_switch_pre : forall next c,
  indom tasks tid -> V293_highest_ready tasks next ->
  V293_storage_connected_payload next c ==> SWPRE_NDEAD V293_scheduler target tid.
Proof.
  intros next c Hmem Hhighest s Hs. unfold SWPRE_NDEAD. split.
  - eapply V293_storage_connected_switch_highest; eassumption.
  - exists tasks. unfold V293_storage_connected_payload, V293_storage_open,
      V293_shared_fields in Hs. sep auto.
Qed.

Lemma V293_storage_connected_increment_under : forall Spec (RI : Inv) r ri next c,
  (px ==> LINV V293_shared_li tid nil ** Atrue) ->
  InfRules Spec V293_scheduler V293_shared_li RI r ri
    (V293_storage_connected_tail next c) (V293_OSSched_increment counter)
    (V293_storage_connected_tail next (Int.add c Int.one)) tid.
Proof.
  intros Spec RI r ri next c Hlocal.
  eapply conseq_rule with
  (p := <||sched;;aop||> **
    ((((V293_storage_open target tp tid tasks events now next ** CurTid tid) **
      ((Ais stack ** Acs critical) ** (physical ** (px ** Atrue)))) **
      (V293_sched_globals unmap group rows high bt bg br bh **
        V293_prefix_bindings table high target tp bp bo)) ** V293_counter_cell counter bcounter c))
  (q := <||sched;;aop||> **
    ((((V293_storage_open target tp tid tasks events now next ** CurTid tid) **
      ((Ais stack ** Acs critical) ** (physical ** (px ** Atrue)))) **
      (V293_sched_globals unmap group rows high bt bg br bh **
        V293_prefix_bindings table high target tp bp bo)) ** V293_counter_cell counter bcounter (Int.add c Int.one))).
  - unfold V293_storage_connected_tail, V293_storage_connected_payload,
      V293_storage_connected_locals, V293_counter_cell. intros s H; sep auto.
  - unfold V293_storage_connected_tail, V293_storage_connected_payload,
      V293_storage_connected_locals, V293_counter_cell. intros s H; sep auto.
  - apply V293_OSSched_counter_increment. intros s Hs.
  unfold CurLINV. exists (nil : list logicvar).
  assert (HP : s |= CurTid tid ** (px ** Atrue)) by (sep auto).
  eapply astar_mono in HP; [ | intros st H; exact H | apply astar_mono; [exact Hlocal | intros st H; exact H]].
  clear Hs. sep auto.
Qed.

Theorem V293_storage_connected_increment : forall Spec r ri next c,
  (px ==> LINV V293_shared_li tid nil ** Atrue) ->
  InfRules Spec V293_scheduler V293_shared_li (V293_storage_inv cells target tp) r ri
    (V293_storage_connected_tail next c) (V293_OSSched_increment counter)
    (V293_storage_connected_tail next (Int.add c Int.one)) tid.
Proof. intros. apply V293_storage_connected_increment_under. assumption. Qed.

Theorem V293_storage_connected_switch : forall Spec r ri next c,
  lo < 256 -> hi < 256 -> (exists p, V293_bitmap_ready lo hi p) ->
  Forall (fun v => rule_type_val_match (Tptr tp) v = true) entries ->
  indom tasks tid -> V293_highest_ready tasks next -> GoodFrm px ->
  (px ==> LINV V293_shared_li tid nil ** Atrue) ->
  InfRules Spec V293_scheduler V293_shared_li (V293_storage_inv cells target tp) r ri
    (V293_storage_connected_tail next c) (sprim (switch target)) V293_storage_connected_resumed tid.
Proof.
  intros Spec r ri next c Hlo Hhi Hr Hptr Hmem Hhighest Hpx Hlocal.
  unfold V293_storage_connected_tail, V293_storage_connected_resumed.
  eapply switch_rule with (P' := V293_storage_connected_payload next c)
    (Px := V293_storage_connected_locals) (lg := nil).
  - apply V293_storage_connected_locals_good; exact Hpx.
  - intros s H; exact H.
  - apply V293_storage_connected_return; assumption.
  - apply V293_storage_connected_switch_pre; assumption.
  - intros s Hs. unfold V293_storage_connected_locals in Hs.
    assert (HP : s |= px ** Atrue) by (sep auto).
    eapply astar_mono in HP; [ | exact Hlocal | intros st H; exact H]. clear Hs. sep auto.
Qed.

Theorem V293_OSSched_storage_prefix_increment_switch : forall Spec r ri sched_id old hv,
  lo < 256 -> hi < 256 -> (exists p, V293_bitmap_ready lo hi p) ->
  V293_bitmap_tasks lo hi tasks -> V293_priority_table entries tasks ->
  Forall (fun v => rule_type_val_match (Tptr tp) v = true) entries ->
  indom tasks tid -> GoodFrm px -> (px ==> LINV V293_shared_li tid nil ** Atrue) ->
  Spec sched_id = Some
    (V293_critical_fpre unmap group rows high bt bg br bh V293_shared_li V293_opened_inv V293_switch_li_good,
     V293_critical_fpost unmap group rows high bt bg br bh V293_shared_li V293_opened_inv V293_switch_li_good,
     (Tvoid, nil)) ->
  InfRules Spec V293_scheduler V293_shared_li (V293_storage_inv cells target tp) r ri
    (pre old hv)
    (sseq (V293_OSSched_unlocked_prefix sched_id table high target)
      (sseq (V293_OSSched_increment counter) (sprim (switch target))))
    V293_storage_connected_resumed tid.
Proof.
  intros Spec r ri sched_id old hv Hlo Hhi Hr Hb Ht Hptr Hmem Hpx Hlocal Hspec.
  eapply seq_rule with (p' := middle).
  - apply V293_OSSched_storage_closed_prefix; try assumption.
    unfold V293_counter_bindings. simpl. tauto.
  - eapply conseq_rule.
    + apply V293_storage_connected_prefix_open.
    + intros s H; exact H.
    + apply ex_intro_rule. intro next. apply ex_intro_rule. intro c.
      eapply conseq_rule with (p := V293_storage_connected_tail next c ** [|V293_highest_ready tasks next|]).
      * intros s H; sep auto.
      * intros s H; exact H.
      * apply pure_split_rule. intro Hhighest.
        eapply seq_rule.
        -- apply V293_storage_connected_increment; exact Hlocal.
        -- apply V293_storage_connected_switch; assumption.
Qed.
(* No concrete switch is executed on the equal-priority branch. All shared
   bytes still return to the same invariant before abstract sched is consumed. *)
Theorem V293_storage_connected_self_finish : forall c,
  lo < 256 -> hi < 256 -> (exists p, V293_bitmap_ready lo hi p) ->
  Forall (fun v => rule_type_val_match (Tptr tp) v = true) entries ->
  V293_highest_ready tasks tid -> GoodFrm px ->
  absinferfull V293_scheduler V293_shared_li
    (V293_storage_connected_tail tid c) V293_storage_connected_resumed tid.
Proof.
  intros c Hlo Hhi Hr Hptr Hhighest Hpx.
  set (resources := ((V293_storage_open target tp tid tasks events now tid ** CurTid tid) **
    ((Ais stack ** Acs critical) **
      (physical ** (PV (bcounter, Int.zero) @ Tint32 |-> (Vint32 c))))) **
    V293_storage_connected_locals).
  assert (HG : forall p, GoodFrm p -> can_change_aop p).
  { induction p; simpl in *; intuition eauto. }
  assert (HL : can_change_aop V293_storage_connected_locals)
    by (apply HG; apply V293_storage_connected_locals_good; exact Hpx).
  assert (HP : can_change_aop physical).
  { apply HG. unfold physical, V293_prefix_physical, V293_inputs_full.
    simpl. repeat split; try exact I; try apply V293_array_good; apply V293_storage_frame_good. }
  assert (Hfree : can_change_aop resources).
  { unfold resources, V293_storage_open, V293_shared_flags, V293_shared_fields,
      CurTid, Agvarmapsto, Aptrmapsto, isrclr.
    cbn [can_change_aop] in HL, HP |- *. repeat split; intros; intuition. all: apply HG; first [apply V293_array_good | apply V293_storage_frame_good]. }
  eapply absinfer_conseq' with
    (p := <||sched;;aop||> ** resources) (q := <||aop||> ** resources).
  - intros s Hs.
    assert (HK : s |=
      (V293_storage_open target tp tid tasks events now tid **
        V293_prefix_physical bt bg br bh bp tp lo hi entries extra) **
      (<||aop||> ** ((CurTid tid ** (Ais stack ** Acs critical)) ** V293_storage_connected_locals))).
    { unfold resources, physical, V293_prefix_physical in Hs.
      assert (HC : PV (bcounter, Int.zero) @ Tint32 |-> (Vint32 c) ==>
          V293_storage_cell (bcounter, 0%Z) Tint32).
      { intros st H. unfold V293_storage_cell. exists (Vint32 c). sep auto. }
      assert (HB : s |= (PV (bcounter, Int.zero) @ Tint32 |-> (Vint32 c)) **
        (<||aop||> **
          ((V293_storage_open target tp tid tasks events now tid ** CurTid tid) **
            ((Ais stack ** Acs critical) **
              (V293_prefix_physical bt bg br bh bp tp lo hi entries rest ** V293_storage_connected_locals)))))
        by (sep auto).
      eapply astar_mono in HB; [ | exact HC | intros st H; exact H].
      clear Hs. unfold V293_prefix_physical in HB |- *. cbn [extra V293_storage]. sep auto. }
    eapply astar_mono in HK.
    2: { apply astar_mono; [intros st H; exact H | apply V293_prefix_physical_return; assumption]. }
    2: { intros st H; exact H. }
    eapply astar_mono in HK.
    2: { apply V293_storage_return. }
    2: { intros st H; exact H. }
    unfold V293_storage_connected_resumed, SWINVt. unfold CurTid in HK. clear Hs. sep auto.
  - eapply V293_self_schedule_consume; [exact Hfree | | exact Hhighest].
    intros s Hs. unfold resources, V293_storage_open in Hs. sep auto.
  - intros s Hs. unfold V293_storage_connected_tail, V293_storage_connected_payload in Hs.
    unfold resources. sep auto.
Qed.

(* The physical tail above is invariant-independent. Close it into the SAME
   ready relation before switching, and do not retain shared observations on
   resumption. This segment is not the conditional/full source function. *)
Let readyI := V293_ready_inv bt bg br bh bp tp extra target.
Definition V293_ready_connected_resumed :=
  <||aop||> ** SWINVt readyI tid ** Ais stack ** Acs critical **
    V293_storage_connected_locals.
Definition V293_ready_connected_entry old hv :=
  <||sched;;aop||> **
    (((SWINV readyI //\\
      ((V293_shared_flags ** ((CurTid tid ** V293_shared_fields tid tasks events now) **
        (GV target @ (Tptr tp) |-> old))) **
        V293_retained_prefix_entry_heap bt bg br bh bp tp lo hi entries (V293_storage extra) hv)) **
      CurTid tid) ** ((Ais stack ** Acs critical) **
        ((V293_sched_globals unmap group rows high bt bg br bh **
          V293_prefix_bindings table high target tp bp bo) **
          (V293_counter_bindings counter bcounter ** px)))).

Lemma V293_ready_connected_return : forall next c,
  lo < 256 -> hi < 256 -> (exists p, V293_bitmap_ready lo hi p) ->
  V293_bitmap_tasks lo hi tasks -> V293_priority_table entries tasks ->
  Forall (fun v => rule_type_val_match (Tptr tp) v = true) entries ->
  V293_storage_connected_payload next c ==>
  <||sched;;aop||> ** SWINVt readyI tid ** Ais stack ** Acs critical.
Proof.
  intros next c Hlo Hhi Hr Hb Ht Hp s Hs.
  assert (HC : (PV (bcounter, Int.zero) @ Tint32 |-> (Vint32 c)) ==>
    V293_storage_cell (bcounter, 0%Z) Tint32).
  { intros st H. unfold V293_storage_cell. exists (Vint32 c). sep auto. }
  assert (HK : s |= (PV (bcounter, Int.zero) @ Tint32 |-> (Vint32 c)) **
    ((V293_storage_open target tp tid tasks events now next ** physical) **
      (<||sched;;aop||> ** CurTid tid ** Ais stack ** Acs critical)))
    by (unfold V293_storage_connected_payload in Hs; sep auto).
  eapply astar_mono in HK; [ | exact HC | intros st H; exact H].
  assert (HR : s |= V293_retained_prefix_returned target bt bg br bh bp tp lo hi entries
    (V293_storage extra) tid tasks events now next **
      (<||sched;;aop||> ** CurTid tid ** Ais stack ** Acs critical)).
  { unfold V293_retained_prefix_returned, V293_retained_prefix_physical,
      physical, V293_prefix_physical in *. cbn [extra V293_storage]. clear Hs. sep auto. }
  eapply astar_mono in HR; [ | apply V293_ready_prefix_return; eassumption | intros st H; exact H].
  eapply astar_mono in HR; [ | intros st [H _]; exact H | intros st H; exact H].
  unfold SWINVt. unfold CurTid in HR. clear Hs HK. sep auto.
Qed.

Theorem V293_ready_connected_switch : forall Spec r ri next c,
  lo < 256 -> hi < 256 -> (exists p, V293_bitmap_ready lo hi p) ->
  V293_bitmap_tasks lo hi tasks -> V293_priority_table entries tasks ->
  Forall (fun v => rule_type_val_match (Tptr tp) v = true) entries ->
  indom tasks tid -> V293_highest_ready tasks next -> GoodFrm px ->
  (px ==> LINV V293_shared_li tid nil ** Atrue) ->
  InfRules Spec V293_scheduler V293_shared_li readyI r ri
    (V293_storage_connected_tail next c) (sprim (switch target)) V293_ready_connected_resumed tid.
Proof.
  intros Spec r ri next c Hlo Hhi Hr Hb Ht Hp Hmem Hhighest Hpx Hlocal.
  unfold V293_storage_connected_tail, V293_ready_connected_resumed.
  eapply switch_rule with (P' := V293_storage_connected_payload next c)
    (Px := V293_storage_connected_locals) (lg := nil).
  - apply V293_storage_connected_locals_good; exact Hpx.
  - intros s H; exact H.
  - apply V293_ready_connected_return; assumption.
  - apply V293_storage_connected_switch_pre; assumption.
  - intros s Hs. unfold V293_storage_connected_locals in Hs.
    assert (HP : s |= px ** Atrue) by (sep auto).
    eapply astar_mono in HP; [ | exact Hlocal | intros st H; exact H]. clear Hs. sep auto.
Qed.

(* A deleted current task does not resume. Afalse is weakened only AFTER
   switchdead_rule has established the actual non-returning switch. *)
Lemma V293_ready_connected_switch_dead : forall Spec r ri next c,
  lo < 256 -> hi < 256 -> (exists p, V293_bitmap_ready lo hi p) ->
  V293_bitmap_tasks lo hi tasks -> V293_priority_table entries tasks ->
  Forall (fun v => rule_type_val_match (Tptr tp) v = true) entries ->
  ~ indom tasks tid -> V293_highest_ready tasks next -> GoodFrm px ->
  (px ==> LINV V293_shared_li tid nil ** Atrue) ->
  InfRules Spec V293_scheduler V293_shared_li readyI r ri
    (V293_storage_connected_tail next c) (sprim (switch target)) Afalse tid.
Proof.
  intros Spec r ri next c Hlo Hhi Hr Hb Ht Hp Hdead Hhighest Hpx Hlocal.
  unfold V293_storage_connected_tail.
  eapply switchdead_rule with (P' := V293_storage_connected_payload next c)
    (Px := V293_storage_connected_locals) (lg := nil) (aop := aop)
    (is := stack) (cs := critical).
  - apply V293_storage_connected_locals_good; exact Hpx.
  - intros s H; exact H.
  - apply V293_ready_connected_return; assumption.
  - intros s Hs. unfold SWPRE_DEAD. split.
    + eapply V293_storage_connected_switch_highest; eassumption.
    + exists tasks. unfold V293_storage_connected_payload, V293_storage_open,
        V293_shared_fields in Hs. sep auto.
  - intros s Hs. unfold V293_storage_connected_locals in Hs.
    assert (HP : s |= px ** Atrue) by (sep auto).
    eapply astar_mono in HP; [ | exact Hlocal | intros st H; exact H]. clear Hs. sep auto.
Qed.

Lemma V293_ready_connected_switch_total : forall Spec r ri next c,
  lo < 256 -> hi < 256 -> (exists p, V293_bitmap_ready lo hi p) ->
  V293_bitmap_tasks lo hi tasks -> V293_priority_table entries tasks ->
  Forall (fun v => rule_type_val_match (Tptr tp) v = true) entries ->
  V293_highest_ready tasks next -> GoodFrm px ->
  (px ==> LINV V293_shared_li tid nil ** Atrue) ->
  InfRules Spec V293_scheduler V293_shared_li readyI r ri
    (V293_storage_connected_tail next c) (sprim (switch target)) V293_ready_connected_resumed tid.
Proof.
  intros Spec r ri next c Hlo Hhi Hr Hb Ht Hp Hhighest Hpx Hlocal.
  destruct (classic (indom tasks tid)) as [Hmem | Hdead].
  - apply V293_ready_connected_switch; assumption.
  - eapply conseq_rule with (q := Afalse).
    + intros s H; exact H.
    + intros s H; contradiction.
    + apply V293_ready_connected_switch_dead; assumption.
Qed.

Lemma V293_ready_connected_prefix : forall Spec r ri sched_id old hv,
  lo < 256 -> hi < 256 -> (exists p, V293_bitmap_ready lo hi p) ->
  V293_bitmap_tasks lo hi tasks -> V293_priority_table entries tasks ->
  Forall (fun v => rule_type_val_match (Tptr tp) v = true) entries ->
  GoodFrm px ->
  Spec sched_id = Some
    (V293_critical_fpre unmap group rows high bt bg br bh V293_shared_li V293_opened_inv V293_switch_li_good,
     V293_critical_fpost unmap group rows high bt bg br bh V293_shared_li V293_opened_inv V293_switch_li_good,
     (Tvoid, nil)) ->
  InfRules Spec V293_scheduler V293_shared_li readyI r ri
    (V293_ready_connected_entry old hv)
    (V293_OSSched_unlocked_prefix sched_id table high target)
    (EX next : Modules.tid, EX c : int32,
      [|V293_highest_ready tasks next|] ** V293_storage_connected_tail next c) tid.
Proof.
  intros Spec r ri sched_id old hv Hlo Hhi Hr Hb Ht Hp Hpx Hspec.
  eapply conseq_rule.
    3: { eapply V293_retained_OSSched_storage_prefix_returned with
        (RI := readyI) (kept := V293_storage extra)
        (lo := lo) (hi := hi) (entries := entries) (tid := tid) (tasks := tasks)
        (events := events) (now := now) (aop := (sched;;aop))
        (stack := stack) (critical := critical)
        (px := V293_counter_bindings counter bcounter ** px) (old := old);
        try eassumption; try apply V293_storage_frame_good.
      unfold V293_counter_bindings. simpl. tauto. }
    + intros s Hs. apply V293_retained_storage_prefix_lend_value with (hv := hv); try assumption.
      unfold V293_ready_connected_entry in Hs.
      eapply astar_mono in Hs; [ | intros st H; exact H | apply astar_mono].
      2: { apply astar_mono; [intros st [_ H]; exact H | intros st H; exact H]. }
      2: { intros st H; exact H. }
      unfold V293_storage_open in Hs. exact Hs.
    + intros s [next Hs]. unfold V293_retained_storage_prefix_returned,
        V293_retained_prefix_returned, V293_retained_prefix_physical in Hs.
      cbn [extra V293_storage] in Hs. unfold V293_storage_cell at 1 in Hs.
      sep normal in Hs. sep destruct Hs. sep split in Hs.
      destruct x; simpl in H; try discriminate.
      exists next. exists i.
      unfold V293_storage_connected_tail, V293_storage_connected_payload,
        V293_storage_connected_locals, physical, V293_prefix_physical.
      sep auto.
Qed.

Theorem V293_ready_OSSched_prefix_increment_switch : forall Spec r ri sched_id old hv,
  lo < 256 -> hi < 256 -> (exists p, V293_bitmap_ready lo hi p) ->
  V293_bitmap_tasks lo hi tasks -> V293_priority_table entries tasks ->
  Forall (fun v => rule_type_val_match (Tptr tp) v = true) entries ->
  indom tasks tid -> GoodFrm px -> (px ==> LINV V293_shared_li tid nil ** Atrue) ->
  Spec sched_id = Some
    (V293_critical_fpre unmap group rows high bt bg br bh V293_shared_li V293_opened_inv V293_switch_li_good,
     V293_critical_fpost unmap group rows high bt bg br bh V293_shared_li V293_opened_inv V293_switch_li_good,
     (Tvoid, nil)) ->
  InfRules Spec V293_scheduler V293_shared_li readyI r ri
    (V293_ready_connected_entry old hv)
    (sseq (V293_OSSched_unlocked_prefix sched_id table high target)
      (sseq (V293_OSSched_increment counter) (sprim (switch target))))
    V293_ready_connected_resumed tid.
Proof.
  intros Spec r ri sched_id old hv Hlo Hhi Hr Hb Ht Hp Hmem Hpx Hlocal Hspec.
  eapply seq_rule with (p' := EX next : Modules.tid, EX c : int32,
    [|V293_highest_ready tasks next|] ** V293_storage_connected_tail next c).
  - apply V293_ready_connected_prefix; assumption.
  - apply ex_intro_rule. intro next. apply ex_intro_rule. intro c.
    eapply conseq_rule with (p := V293_storage_connected_tail next c ** [|V293_highest_ready tasks next|]).
    + intros s H; sep auto.
    + intros s H; exact H.
    + apply pure_split_rule. intro Hhighest. eapply seq_rule.
      * apply V293_storage_connected_increment_under; exact Hlocal.
      * apply V293_ready_connected_switch; assumption.
Qed.

Theorem V293_ready_connected_self_finish : forall c,
  lo < 256 -> hi < 256 -> (exists p, V293_bitmap_ready lo hi p) ->
  V293_bitmap_tasks lo hi tasks -> V293_priority_table entries tasks ->
  Forall (fun v => rule_type_val_match (Tptr tp) v = true) entries ->
  V293_highest_ready tasks tid -> GoodFrm px ->
  absinferfull V293_scheduler V293_shared_li
    (V293_storage_connected_tail tid c) V293_ready_connected_resumed tid.
Proof.
  intros c Hlo Hhi Hr Hb Htable Hptr Hhighest Hpx.
  set (resources := ((V293_storage_open target tp tid tasks events now tid ** CurTid tid) **
    ((Ais stack ** Acs critical) **
      (physical ** (PV (bcounter, Int.zero) @ Tint32 |-> (Vint32 c))))) **
    V293_storage_connected_locals).
  assert (HG : forall p, GoodFrm p -> can_change_aop p).
  { induction p; simpl in *; intuition eauto. }
  assert (HL : can_change_aop V293_storage_connected_locals)
    by (apply HG; apply V293_storage_connected_locals_good; exact Hpx).
  assert (HP : can_change_aop physical).
  { apply HG. unfold physical, V293_prefix_physical, V293_inputs_full.
    simpl. repeat split; try exact I; try apply V293_array_good; apply V293_storage_frame_good. }
  assert (Hfree : can_change_aop resources).
  { unfold resources, V293_storage_open, V293_shared_flags, V293_shared_fields,
      CurTid, Agvarmapsto, Aptrmapsto, isrclr.
    cbn [can_change_aop] in HL, HP |- *. repeat split; intros; intuition.
    all: apply HG; first [apply V293_array_good | apply V293_storage_frame_good]. }
  eapply absinfer_conseq' with
    (p := <||sched;;aop||> ** resources) (q := <||aop||> ** resources).
  - intros s Hs.
    assert (HC : (PV (bcounter, Int.zero) @ Tint32 |-> (Vint32 c)) ==>
      V293_storage_cell (bcounter, 0%Z) Tint32).
    { intros st H. unfold V293_storage_cell. exists (Vint32 c). sep auto. }
    assert (HK : s |= (PV (bcounter, Int.zero) @ Tint32 |-> (Vint32 c)) **
      ((V293_storage_open target tp tid tasks events now tid ** physical) **
        (<||aop||> ** CurTid tid ** Ais stack ** Acs critical ** V293_storage_connected_locals)))
      by (unfold resources in Hs; sep auto).
    eapply astar_mono in HK; [ | exact HC | intros st H; exact H].
    assert (HR : s |= V293_retained_prefix_returned target bt bg br bh bp tp lo hi entries
        (V293_storage extra) tid tasks events now tid **
      (<||aop||> ** CurTid tid ** Ais stack ** Acs critical ** V293_storage_connected_locals)).
    { unfold V293_retained_prefix_returned, V293_retained_prefix_physical,
        physical, V293_prefix_physical in *. cbn [extra V293_storage]. clear Hs. sep auto. }
    eapply astar_mono in HR; [ | apply V293_ready_prefix_return; eassumption | intros st H; exact H].
    eapply astar_mono in HR; [ | intros st [H _]; exact H | intros st H; exact H].
    unfold V293_ready_connected_resumed, SWINVt. unfold CurTid in HR. clear Hs HK. sep auto.
  - eapply V293_self_schedule_consume; [exact Hfree | | exact Hhighest].
    intros s Hs. unfold resources, V293_storage_open in Hs. sep auto.
  - intros s Hs. unfold V293_storage_connected_tail, V293_storage_connected_payload in Hs.
    unfold resources. sep auto.
Qed.

(* Candidate pointer normalization only: NOT the frozen C comparison.
   The current global must not be shadowed by a local. This condition is
   obtained from the environment-only/private frame, not from SWINV. *)
Lemma V293_ready_pointer_comparison : forall next c s,
  (px ==> A_notin_lenv OSTCBCur ** Atrue) ->
  s |= V293_storage_connected_tail next c ->
  evalval (V293_OSSched_pointer_different target OSTCBCur) (getsmem s) =
    Some (Vint32 (if tid_eq_dec next tid then Int.zero else Int.one)) /\
  evaltype (V293_OSSched_pointer_different target OSTCBCur) (getsmem s) = Some Tint32.
Proof.
  intros next c s Hshadow Hs.
  assert (HP : s |= (CurTid tid ** CurTid tid) **
    ((GV target @ (Tptr tp) |-> (Vptr next)) **
      (V293_prefix_bindings table high target tp bp bo ** (px ** Atrue)))).
  { unfold V293_storage_connected_tail, V293_storage_connected_payload,
      V293_storage_connected_locals, V293_storage_open in Hs. sep auto. }
  eapply astar_mono in HP; [ | apply V293_current_halves_write | intros st H; exact H].
  apply astar_l_aexists_elim in HP. destruct HP as [tq HP].
  assert (HC : s |= (GV OSTCBCur @ (Tptr tq) |-> (Vptr tid)) ** Atrue) by (sep auto).
  assert (HT : s |= (GV target @ (Tptr tp) |-> (Vptr next)) ** Atrue) by (clear HC; sep auto).
  destruct (V293_connected_pointer_cell_read _ _ _ _ HC) as [bc [Gc Lc]].
  destruct (V293_connected_pointer_cell_read _ _ _ _ HT) as [btarg [Gt Lt]].
  assert (HB : s |= V293_prefix_bindings table high target tp bp bo ** Atrue) by (clear HC HT; sep auto).
  assert (Nt : get (getlenv s) target = None).
  { eapply V293_star_env_l with (E := fun _ le => get le target = None); [ | exact HB].
    intros st H. exact (proj2 (proj2 (proj2 (proj2 (V293_prefix_bindings_view _ _ _ _ _ _ _ H))))). }
  assert (HX : s |= px ** Atrue) by (clear HC HT HB; sep auto).
  eapply astar_mono in HX; [ | exact Hshadow | intros st H; exact H].
  assert (Nc : get (getlenv s) OSTCBCur = None).
  { assert (HN : s |= A_notin_lenv OSTCBCur ** Atrue) by (clear HP Hs; sep auto).
    eapply V293_star_env_l with (E := fun _ le => get le OSTCBCur = None); [ | exact HN].
    intros st [H _].
    destruct (get (getlenv st) OSTCBCur) eqn:E; [exfalso; apply H; eexists; exact E | reflexivity]. }
  destruct s as [[[[[[ge le] M] ir] aux] O] op].
  exact (V293_OSSched_pointer_comparison_eval ge le M target OSTCBCur btarg bc tp tq next tid
    Nt Nc Gt Gc Lt Lc).
Qed.

(* Each target is opened before the metalevel equality split; no old target
   or counter observation is carried through a concrete switch. *)
Theorem V293_ready_pointer_change_total : forall Spec r ri next c,
  lo < 256 -> hi < 256 -> (exists p, V293_bitmap_ready lo hi p) ->
  V293_bitmap_tasks lo hi tasks -> V293_priority_table entries tasks ->
  Forall (fun v => rule_type_val_match (Tptr tp) v = true) entries ->
  V293_highest_ready tasks next -> GoodFrm px ->
  (px ==> LINV V293_shared_li tid nil ** Atrue) ->
  (px ==> A_notin_lenv OSTCBCur ** Atrue) ->
  InfRules Spec V293_scheduler V293_shared_li readyI r ri
    (V293_storage_connected_tail next c)
    (sifthen (V293_OSSched_pointer_different target OSTCBCur)
      (sseq (V293_OSSched_increment counter) (sprim (switch target))))
    V293_ready_connected_resumed tid.
Proof.
  intros Spec r ri next c Hlo Hhi Hr Hb Htable Hptr Hhighest Hpx Hlocal Hshadow.
  destruct (tid_eq_dec next tid) as [Heq | Hneq].
  - subst next.
    eapply abscsq_rule_full with (p := V293_storage_connected_tail tid c)
      (q := V293_storage_connected_tail tid c).
    + apply absinfer_eq'.
    + apply V293_ready_connected_self_finish; assumption.
    + eapply ift_rule with (tp := Tint32).
      * intros s Hs. destruct (V293_ready_pointer_comparison tid c s Hshadow Hs) as [Ev Et].
        eexists. split; [exact Ev | ]. split; [exact Et | discriminate].
      * intros s [Hs _]. exact Hs.
      * eapply conseq_rule with (p := Afalse).
        -- intros s [Hs [v [Ev Hv]]].
           destruct (V293_ready_pointer_comparison tid c s Hshadow Hs) as [E _].
           destruct (tid_eq_dec tid tid); [ | contradiction].
           rewrite E in Ev. inversion Ev; subst v. vm_compute in Hv; discriminate.
        -- intros s H; exact H.
        -- apply pfalse_rule.
  - eapply ift_rule with (tp := Tint32).
    + intros s Hs. destruct (V293_ready_pointer_comparison next c s Hshadow Hs) as [Ev Et].
      eexists. split; [exact Ev | ]. split; [exact Et | discriminate].
    + intros s [Hs [v [Ev Hv]]].
      destruct (V293_ready_pointer_comparison next c s Hshadow Hs) as [E _].
      destruct (tid_eq_dec next tid); [contradiction | ].
      rewrite E in Ev. inversion Ev; subst v. vm_compute in Hv; discriminate.
    + eapply conseq_rule with (p := V293_storage_connected_tail next c).
      * intros s [Hs _]. exact Hs.
      * intros s H; exact H.
      * eapply seq_rule.
        -- apply V293_storage_connected_increment_under; exact Hlocal.
        -- apply V293_ready_connected_switch_total; assumption.
Qed.

Theorem V293_ready_pointer_change : forall Spec r ri next c,
  lo < 256 -> hi < 256 -> (exists p, V293_bitmap_ready lo hi p) ->
  V293_bitmap_tasks lo hi tasks -> V293_priority_table entries tasks ->
  Forall (fun v => rule_type_val_match (Tptr tp) v = true) entries ->
  indom tasks tid -> V293_highest_ready tasks next -> GoodFrm px ->
  (px ==> LINV V293_shared_li tid nil ** Atrue) ->
  (px ==> A_notin_lenv OSTCBCur ** Atrue) ->
  InfRules Spec V293_scheduler V293_shared_li readyI r ri
    (V293_storage_connected_tail next c)
    (sifthen (V293_OSSched_pointer_different target OSTCBCur)
      (sseq (V293_OSSched_increment counter) (sprim (switch target))))
    V293_ready_connected_resumed tid.
Proof.
  intros. apply V293_ready_pointer_change_total; assumption.
Qed.

Theorem V293_ready_OSSched_pointer_conditional_total : forall Spec r ri sched_id old hv,
  lo < 256 -> hi < 256 -> (exists p, V293_bitmap_ready lo hi p) ->
  V293_bitmap_tasks lo hi tasks -> V293_priority_table entries tasks ->
  Forall (fun v => rule_type_val_match (Tptr tp) v = true) entries ->
  GoodFrm px -> (px ==> LINV V293_shared_li tid nil ** Atrue) ->
  (px ==> A_notin_lenv OSTCBCur ** Atrue) ->
  Spec sched_id = Some
    (V293_critical_fpre unmap group rows high bt bg br bh V293_shared_li V293_opened_inv V293_switch_li_good,
     V293_critical_fpost unmap group rows high bt bg br bh V293_shared_li V293_opened_inv V293_switch_li_good,
     (Tvoid, nil)) ->
  InfRules Spec V293_scheduler V293_shared_li readyI r ri
    (V293_ready_connected_entry old hv)
    (sseq (V293_OSSched_unlocked_prefix sched_id table high target)
      (sifthen (V293_OSSched_pointer_different target OSTCBCur)
        (sseq (V293_OSSched_increment counter) (sprim (switch target)))))
    V293_ready_connected_resumed tid.
Proof.
  intros Spec r ri sched_id old hv Hlo Hhi Hr Hb Htable Hptr Hpx Hlocal Hshadow Hspec.
  eapply seq_rule with (p' := EX next : Modules.tid, EX c : int32,
    [|V293_highest_ready tasks next|] ** V293_storage_connected_tail next c).
  - apply V293_ready_connected_prefix; assumption.
  - apply ex_intro_rule. intro next. apply ex_intro_rule. intro c.
    eapply conseq_rule with (p := V293_storage_connected_tail next c ** [|V293_highest_ready tasks next|]).
    + intros s H; sep auto.
    + intros s H; exact H.
    + apply pure_split_rule. intro Hhighest. apply V293_ready_pointer_change_total; assumption.
Qed.

Theorem V293_ready_OSSched_pointer_conditional : forall Spec r ri sched_id old hv,
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
    (V293_ready_connected_entry old hv)
    (sseq (V293_OSSched_unlocked_prefix sched_id table high target)
      (sifthen (V293_OSSched_pointer_different target OSTCBCur)
        (sseq (V293_OSSched_increment counter) (sprim (switch target)))))
    V293_ready_connected_resumed tid.
Proof.
  intros. apply V293_ready_OSSched_pointer_conditional_total; assumption.
Qed.

End ConnectedPath.

(* The interrupt-enabled caller owns no ready snapshot. Each shared
   observation below is opened only after the real encrit has executed. *)
Section ReadyPointerCritical.
Variables unmap group rows high table target counter : var.
Variables bt bg br bh bp bo bcounter : block.
Variable tp : type.
Variable rest : list (addr * type).
Let extra := ((bcounter, 0%Z), Tint32) :: rest.
Let I := V293_ready_inv bt bg br bh bp tp extra target.
Let bindings := V293_sched_globals unmap group rows high bt bg br bh **
  V293_prefix_bindings table high target tp bp bo.
Let frame px := V293_counter_bindings counter bcounter ** px.
Let body sched_id := sseq (V293_OSSched_unlocked_prefix sched_id table high target)
  (sifthen (V293_OSSched_pointer_different target OSTCBCur)
    (sseq (V293_OSSched_increment counter) (sprim (switch target)))).

Theorem V293_ready_OSSched_pointer_fresh : forall Spec r ri sched_id tid aop stack critical px,
  GoodFrm px -> (px ==> LINV V293_shared_li tid nil ** Atrue) ->
  (px ==> A_notin_lenv OSTCBCur ** Atrue) ->
  Spec sched_id = Some
    (V293_critical_fpre unmap group rows high bt bg br bh V293_shared_li V293_opened_inv V293_switch_li_good,
     V293_critical_fpost unmap group rows high bt bg br bh V293_shared_li V293_opened_inv V293_switch_li_good,
     (Tvoid, nil)) ->
  InfRules Spec V293_scheduler V293_shared_li I r ri
    (V293_ready_prefix_open unmap group rows high table target bt bg br bh bp bo tp extra
      tid (sched;;aop) stack critical (frame px))
    (body sched_id)
    (V293_ready_connected_resumed unmap group rows high table target counter bt bg br bh bp bo bcounter
      tp rest tid aop stack critical px) tid.
Proof.
  intros Spec r ri sched_id tid aop stack critical px Hpx Hlocal Hshadow Hspec.
  eapply conseq_rule with (p := EX tasks : TcbMod.map, EX events : EcbMod.map,
    EX now : int32, EX lo : nat, EX hi : nat, EX entries : list val, EX old : val, EX hv : val,
    V293_ready_connected_entry unmap group rows high table target counter bt bg br bh bp bo bcounter
      tp lo hi entries rest tid tasks events now aop stack critical px old hv **
    [|lo < 256 /\ hi < 256 /\ (exists p, V293_bitmap_ready lo hi p) /\
      V293_bitmap_tasks lo hi tasks /\ V293_priority_table entries tasks /\
      Forall (fun v => rule_type_val_match (Tptr tp) v = true) entries /\
      rule_type_val_match Tint8 hv = true|]).
  - intros s Hs. unfold V293_ready_prefix_open, V293_ready_snapshot, V293_dispatch_cell in Hs.
    sep normal in Hs. sep destruct Hs. sep split in Hs.
    assert (E : x = tid).
    { eapply V293_shared_current_agree with (frame := Atrue) (s := s). sep auto. }
    subst x.
    destruct H0 as [Hlo [Hhi [Hr [Hb [Ht [Hp Hhv]]]]]].
    exists x0. exists x1. exists x2. exists x3. exists x4. exists x5. exists x7. exists x6.
    apply astar_comm. apply astar_l_apure_intro.
    2: { repeat first [assumption | split]. }
    assert (HP : s |=
      ((V293_shared_flags ** ((CurTid tid ** V293_shared_fields tid x0 x1 x2) **
        (GV target @ (Tptr tp) |-> x7))) **
        V293_retained_prefix_entry_heap bt bg br bh bp tp x3 x4 x5 (V293_storage extra) x6) **
      (<||sched;;aop||> ** (CurTid tid ** ((Ais stack ** Acs critical) ** (bindings ** frame px)))))
      by (unfold bindings; sep auto).
    eapply astar_mono with (P' := SWINV I //\\
      ((V293_shared_flags ** ((CurTid tid ** V293_shared_fields tid x0 x1 x2) **
        (GV target @ (Tptr tp) |-> x7))) **
        V293_retained_prefix_entry_heap bt bg br bh bp tp x3 x4 x5 (V293_storage extra) x6))
      (Q' := <||sched;;aop||> ** (CurTid tid **
        ((Ais stack ** Acs critical) ** (bindings ** frame px)))) in HP.
    2: { intros st Hcore. split; [ | exact Hcore]. apply V293_ready_switch_close.
      unfold V293_ready_core, V293_ready_resources, V293_dispatch_cell.
      sep auto. repeat first [assumption | split]. }
    2: { intros st Hrest; exact Hrest. }
    unfold V293_ready_connected_entry, bindings, frame in *. clear Hs. sep auto.
  - intros s H; exact H.
  - apply ex_intro_rule. intro tasks. apply ex_intro_rule. intro events.
    apply ex_intro_rule. intro now. apply ex_intro_rule. intro lo.
    apply ex_intro_rule. intro hi. apply ex_intro_rule. intro entries.
    apply ex_intro_rule. intro old. apply ex_intro_rule. intro hv.
    apply pure_split_rule. intros [Hlo [Hhi [Hr [Hb [Ht [Hp Hhv]]]]]].
    unfold body, I. apply V293_ready_OSSched_pointer_conditional_total; assumption.
Qed.

Theorem V293_ready_OSSched_pointer_critical : forall Spec r ri sched_id tid aop critical px,
  GoodFrm px -> (px ==> LINV V293_shared_li tid nil ** Atrue) ->
  (px ==> A_notin_lenv OSTCBCur ** Atrue) ->
  Spec sched_id = Some
    (V293_critical_fpre unmap group rows high bt bg br bh V293_shared_li V293_opened_inv V293_switch_li_good,
     V293_critical_fpost unmap group rows high bt bg br bh V293_shared_li V293_opened_inv V293_switch_li_good,
     (Tvoid, nil)) ->
  InfRules Spec V293_scheduler V293_shared_li I r ri
    (V293_ready_roundtrip_pre unmap group rows high table target bt bg br bh bp bo tp
      tid (sched;;aop) critical (frame px))
    (sseq (sprim encrit) (sseq (body sched_id) (sprim excrit)))
    (V293_ready_roundtrip_post unmap group rows high table target bt bg br bh bp bo tp
      tid aop critical (frame px)) tid.
Proof.
  intros Spec r ri sched_id tid aop critical px Hpx Hlocal Hshadow Hspec.
  assert (HF : GoodFrm (CurTid tid ** (bindings ** frame px))).
  { unfold CurTid, Agvarmapsto, Aptrmapsto, bindings, frame, V293_sched_globals,
      V293_prefix_bindings, V293_counter_bindings. simpl. repeat split; try exact Logic.I; exact Hpx. }
  eapply seq_rule with (p' := V293_ready_prefix_open unmap group rows high table target
    bt bg br bh bp bo tp extra tid (sched;;aop) nil (true::critical) (frame px)).
  - eapply conseq_rule.
    3: { apply V293_ready_enter_critical with (P := CurTid tid ** (bindings ** frame px)); exact HF. }
    + intros s Hs; exact Hs.
    + intros s Hs.
      assert (HP : s |= OS[(fun _ : hid => false), false, nil, true::critical] **
        (<||sched;;aop||> ** V293_ready_snapshot bt bg br bh bp tp extra target **
          (CurTid tid ** (bindings ** frame px)))) by (sep auto).
      eapply astar_mono in HP; [ | apply V293_ready_disabled_flags | intros st H; exact H].
      unfold V293_ready_prefix_open. clear Hs. sep auto.
  - eapply seq_rule.
    + apply V293_ready_OSSched_pointer_fresh; assumption.
    + eapply conseq_rule with
        (p := <||aop||> ** OS[(fun _ : hid => false), false, nil, true::critical] **
          ATopis INUM ** invlth_isr I 0 INUM **
          (CurTid tid ** (bindings ** (frame px ** Atrue))))
        (q := V293_ready_roundtrip_post unmap group rows high table target bt bg br bh bp bo tp
          tid aop critical (frame px)).
      * intros s Hs. unfold V293_ready_connected_resumed, V293_storage_connected_locals,
          SWINVt in Hs.
        apply V293_ready_exit_resources. unfold CurTid, bindings, frame in *. sep auto.
      * intros s Hs; exact Hs.
      * apply excrit1_rule.
        -- unfold CurTid, Agvarmapsto, Aptrmapsto, bindings, frame, V293_sched_globals,
            V293_prefix_bindings, V293_counter_bindings. simpl.
           repeat split; try exact Logic.I; exact Hpx.
        -- intros s Hs. unfold CurLINV. exists (nil : list logicvar).
           pose proof (V293_switch_local_empty tid nil) as HL.
           assert (HP : s |= CurTid tid ** Aemp ** Atrue) by (sep auto).
           eapply astar_mono in HP; [ | intros st H; exact H | apply astar_mono;
             [exact HL | intros st H; exact H]]. sep auto.
Qed.
End ReadyPointerCritical.


(* Guard bytes belong to the same shared storage as the ready relation.
   Only their bindings, never byte ownership, may cross a switch as a frame. *)
Lemma V293_typed_byte_value : forall v,
  rule_type_val_match Tint8 v = true ->
  exists n, n < 256 /\ v = V293_byteval n.
Proof.
  intros v H. destruct v; simpl in H; try discriminate.
  destruct (Int.unsigned i <=? Byte.max_unsigned)%Z eqn:E; [ | discriminate].
  apply Z.leb_le in E. pose proof (Int.unsigned_range i) as Hr.
  exists (Z.to_nat (Int.unsigned i)). split.
  - change (Int.unsigned i <= 255)%Z in E. lia.
  - unfold V293_byteval. rewrite Z2Nat.id by lia. rewrite Int.repr_unsigned. reflexivity.
Qed.

Section ReadyPointerGuards.
Variables unmap group rows high table target counter interrupt lock : var.
Variables bt bg br bh bp bo bcounter bi bl : block.
Variable tp : type.
Variable rest : list (addr * type).
Let guardrest := ((bi, 0%Z), Tint8) :: ((bl, 0%Z), Tint8) :: rest.
Let extra := ((bcounter, 0%Z), Tint32) :: guardrest.
Let I := V293_ready_inv bt bg br bh bp tp extra target.
Let bindings := V293_sched_globals unmap group rows high bt bg br bh **
  V293_prefix_bindings table high target tp bp bo.
Let guardbindings px :=
  ((Agvarenv interrupt Tint8 (bi, 0%Z) //\\ A_notin_lenv interrupt) **
   (Agvarenv lock Tint8 (bl, 0%Z) //\\ A_notin_lenv lock)) ** px.
Let frame px := V293_counter_bindings counter bcounter ** guardbindings px.
Let body sched_id := sseq (V293_OSSched_unlocked_prefix sched_id table high target)
  (sifthen (V293_OSSched_pointer_different target OSTCBCur)
    (sseq (V293_OSSched_increment counter) (sprim (switch target)))).
Definition V293_ready_guard_open tid aop stack critical px :=
  V293_ready_prefix_open unmap group rows high table target bt bg br bh bp bo tp extra
    tid (sched;;aop) stack critical (frame px).
Definition V293_ready_guard_observed tid aop stack critical px ni nl :=
  V293_ready_guard_open tid aop stack critical px //\\
    ((V293_guard_cell interrupt bi ni ** V293_guard_cell lock bl nl) ** Atrue).
Definition V293_ready_guard_resumed tid aop stack critical px :=
  V293_ready_connected_resumed unmap group rows high table target counter bt bg br bh bp bo bcounter
    tp guardrest tid aop stack critical (guardbindings px).
(* ni/nl describe the decision made before the body, NOT the shared values
   when a switched-out thread later resumes. No post-switch byte equality. *)
Definition V293_ready_guard_continuation ni nl aop :=
  if Nat.eqb ni 0 && Nat.eqb nl 0 then aop else (sched;;aop).

Lemma V293_ready_guard_observe : forall tid aop stack critical px,
  V293_ready_guard_open tid aop stack critical px ==>
  EX ni : nat, EX nl : nat, [|ni < 256 /\ nl < 256|] **
    V293_ready_guard_observed tid aop stack critical px ni nl.
Proof.
  intros tid aop stack critical px s Hs.
  assert (HP : s |=
    ((Agvarenv interrupt Tint8 (bi, 0%Z) //\\ A_notin_lenv interrupt) **
     (Agvarenv lock Tint8 (bl, 0%Z) //\\ A_notin_lenv lock)) **
    ((V293_storage_cell (bi, 0%Z) Tint8 ** V293_storage_cell (bl, 0%Z) Tint8) ** Atrue)).
  { unfold V293_ready_guard_open, V293_ready_prefix_open, V293_ready_snapshot,
      V293_retained_prefix_entry_heap, frame, guardbindings in Hs.
    cbn [extra guardrest V293_storage] in Hs.
    sep normal in Hs. sep destruct Hs. sep split in Hs. sep auto. }
  unfold V293_storage_cell in HP. sep normal in HP. sep destruct HP. sep split in HP.
  destruct (V293_typed_byte_value x H0) as [ni [Hni Ei]].
  destruct (V293_typed_byte_value x0 H) as [nl [Hnl El]]. subst x x0.
  assert (HR : s |=
    (Amapsto (bi, 0%Z) Tint8 true (V293_byteval ni) **
     Amapsto (bl, 0%Z) Tint8 true (V293_byteval nl)) **
    (((Agvarenv interrupt Tint8 (bi, 0%Z) //\\ A_notin_lenv interrupt) **
      (Agvarenv lock Tint8 (bl, 0%Z) //\\ A_notin_lenv lock)) ** Atrue)) by (sep auto).
  eapply astar_mono in HR; [ | apply astar_mono; apply separate_rw2ro | intros st Hst; exact Hst].
  exists ni. exists nl. apply astar_l_apure_intro; [ | split; assumption].
  split; [exact Hs | ]. unfold V293_guard_cell. clear Hs HP. sep auto.
Qed.

Lemma V293_ready_guard_skip_close : forall tid aop stack critical px,
  V293_ready_guard_open tid aop stack critical px ==>
  V293_ready_guard_resumed tid (sched;;aop) stack critical px.
Proof.
  intros tid aop stack critical px s Hs.
  assert (HP : s |= (V293_shared_flags ** V293_ready_snapshot bt bg br bh bp tp extra target) **
    (<||sched;;aop||> ** (CurTid tid ** ((Ais stack ** Acs critical) ** (bindings ** frame px))))).
  { unfold V293_ready_guard_open, V293_ready_prefix_open, bindings in Hs. sep auto. }
  eapply astar_mono with (P' := SWINV I)
    (Q' := <||sched;;aop||> ** (CurTid tid ** ((Ais stack ** Acs critical) ** (bindings ** frame px)))) in HP.
  2: { intros st Hcore. apply V293_ready_switch_close.
       unfold V293_ready_snapshot in Hcore. sep normal in Hcore. sep destruct Hcore.
       unfold V293_ready_core, V293_ready_resources. sep auto. }
  2: { intros st Hst; exact Hst. }
  unfold V293_ready_guard_resumed, V293_ready_connected_resumed, V293_storage_connected_locals,
    SWINVt, CurTid, bindings, frame, I, extra in *. clear Hs. sep auto.
Qed.

Theorem V293_ready_OSSched_pointer_guards_observed :
  forall Spec r ri sched_id tid aop stack critical px ni nl,
  ni < 256 -> nl < 256 -> GoodFrm px ->
  (px ==> LINV V293_shared_li tid nil ** Atrue) ->
  (px ==> A_notin_lenv OSTCBCur ** Atrue) ->
  Spec sched_id = Some
    (V293_critical_fpre unmap group rows high bt bg br bh V293_shared_li V293_opened_inv V293_switch_li_good,
     V293_critical_fpost unmap group rows high bt bg br bh V293_shared_li V293_opened_inv V293_switch_li_good,
     (Tvoid, nil)) ->
  InfRules Spec V293_scheduler V293_shared_li I r ri
    (V293_ready_guard_observed tid aop stack critical px ni nl)
    (V293_OSSched_guards interrupt lock (body sched_id))
    (V293_ready_guard_resumed tid (V293_ready_guard_continuation ni nl aop) stack critical px) tid.
Proof.
  intros Spec r ri sched_id tid aop stack critical px ni nl Hni Hnl Hpx Hlocal Hshadow Hspec.
  eapply conseq_rule with
    (q := if Nat.eqb ni 0 && Nat.eqb nl 0
      then V293_ready_guard_resumed tid aop stack critical px
      else V293_ready_guard_observed tid aop stack critical px ni nl).
  - intros s H; exact H.
  - intros s Hs. unfold V293_ready_guard_continuation.
    destruct (Nat.eqb ni 0 && Nat.eqb nl 0); [exact Hs | ].
    apply V293_ready_guard_skip_close. exact (proj1 Hs).
  - eapply V293_OSSched_guards_rule with (bi := bi) (bl := bl) (ni := ni) (nl := nl)
      (ri_mem := Atrue) (rl_mem := Atrue);
      try assumption.
    + intros s [_ H]; sep auto.
    + intros s [_ H]; sep auto.
    + intros Ei El. eapply conseq_rule.
      * intros s [H _]; exact H.
      * intros s H; exact H.
      * unfold V293_ready_guard_open, V293_ready_guard_resumed, body, I, frame.
        apply V293_ready_OSSched_pointer_fresh; try assumption.
        -- unfold guardbindings. simpl. tauto.
        -- intros s Hs. unfold guardbindings in Hs.
           assert (HP : s |= px ** Atrue) by (sep auto).
           eapply astar_mono in HP; [ | exact Hlocal | intros st H; exact H]. clear Hs. sep auto.
        -- intros s Hs. unfold guardbindings in Hs.
           assert (HP : s |= px ** Atrue) by (sep auto).
           eapply astar_mono in HP; [ | exact Hshadow | intros st H; exact H]. clear Hs. sep auto.
Qed.

(* Existentials are fresh at this disabled entry; the observation-specific
   theorem above retains the exact decision/continuation contract. *)
Theorem V293_ready_OSSched_pointer_guards_fresh : forall Spec r ri sched_id tid aop stack critical px,
  GoodFrm px -> (px ==> LINV V293_shared_li tid nil ** Atrue) ->
  (px ==> A_notin_lenv OSTCBCur ** Atrue) ->
  Spec sched_id = Some
    (V293_critical_fpre unmap group rows high bt bg br bh V293_shared_li V293_opened_inv V293_switch_li_good,
     V293_critical_fpost unmap group rows high bt bg br bh V293_shared_li V293_opened_inv V293_switch_li_good,
     (Tvoid, nil)) ->
  InfRules Spec V293_scheduler V293_shared_li I r ri
    (V293_ready_guard_open tid aop stack critical px)
    (V293_OSSched_guards interrupt lock (body sched_id))
    (EX ni : nat, EX nl : nat, [|ni < 256 /\ nl < 256|] **
      V293_ready_guard_resumed tid (V293_ready_guard_continuation ni nl aop) stack critical px) tid.
Proof.
  intros Spec r ri sched_id tid aop stack critical px Hpx Hlocal Hshadow Hspec.
  eapply conseq_rule with (p := EX ni : nat, EX nl : nat, [|ni < 256 /\ nl < 256|] **
    V293_ready_guard_observed tid aop stack critical px ni nl).
  - apply V293_ready_guard_observe.
  - intros s H; exact H.
  - apply ex_intro_rule. intro ni. apply ex_intro_rule. intro nl.
    eapply conseq_rule with (p := V293_ready_guard_observed tid aop stack critical px ni nl **
      [|ni < 256 /\ nl < 256|]).
    + intros s H; sep auto.
    + intros s H; exact H.
    + apply pure_split_rule. intros [Hni Hnl]. eapply conseq_rule.
      3: { apply V293_ready_OSSched_pointer_guards_observed with (ni := ni) (nl := nl)
          (px := px) (aop := aop); assumption. }
      * intros s H; exact H.
      * intros s H. exists ni. exists nl. sep auto.
Qed.
Theorem V293_ready_OSSched_pointer_guarded_critical : forall Spec r ri sched_id tid aop critical px,
  GoodFrm px -> (px ==> LINV V293_shared_li tid nil ** Atrue) ->
  (px ==> A_notin_lenv OSTCBCur ** Atrue) ->
  Spec sched_id = Some
    (V293_critical_fpre unmap group rows high bt bg br bh V293_shared_li V293_opened_inv V293_switch_li_good,
     V293_critical_fpost unmap group rows high bt bg br bh V293_shared_li V293_opened_inv V293_switch_li_good,
     (Tvoid, nil)) ->
  InfRules Spec V293_scheduler V293_shared_li I r ri
    (V293_ready_roundtrip_pre unmap group rows high table target bt bg br bh bp bo tp
      tid (sched;;aop) critical (frame px))
    (sseq (sprim encrit)
      (sseq (V293_OSSched_guards interrupt lock (body sched_id)) (sprim excrit)))
    (EX ni : nat, EX nl : nat, [|ni < 256 /\ nl < 256|] **
      V293_ready_roundtrip_post unmap group rows high table target bt bg br bh bp bo tp
        tid (V293_ready_guard_continuation ni nl aop) critical (frame px)) tid.
Proof.
  intros Spec r ri sched_id tid aop critical px Hpx Hlocal Hshadow Hspec.
  assert (HF : GoodFrm (CurTid tid ** (bindings ** frame px))).
  { unfold CurTid, Agvarmapsto, Aptrmapsto, bindings, frame, guardbindings, V293_sched_globals,
      V293_prefix_bindings, V293_counter_bindings. simpl. repeat split; try exact Logic.I; exact Hpx. }
  eapply seq_rule with (p' := V293_ready_guard_open tid aop nil (true::critical) px).
  - eapply conseq_rule.
    3: { apply V293_ready_enter_critical with (P := CurTid tid ** (bindings ** frame px)); exact HF. }
    + intros s Hs; exact Hs.
    + intros s Hs.
      assert (HP : s |= OS[(fun _ : hid => false), false, nil, true::critical] **
        (<||sched;;aop||> ** V293_ready_snapshot bt bg br bh bp tp extra target **
          (CurTid tid ** (bindings ** frame px)))) by (sep auto).
      eapply astar_mono in HP; [ | apply V293_ready_disabled_flags | intros st H; exact H].
      unfold V293_ready_guard_open, V293_ready_prefix_open. clear Hs. sep auto.
  - eapply seq_rule.
    + apply V293_ready_OSSched_pointer_guards_fresh; assumption.
    + apply ex_intro_rule. intro ni. apply ex_intro_rule. intro nl.
      eapply conseq_rule with (p :=
        V293_ready_guard_resumed tid (V293_ready_guard_continuation ni nl aop) nil (true::critical) px **
          [|ni < 256 /\ nl < 256|]).
      * intros s H; sep auto.
      * intros s H; exact H.
      * apply pure_split_rule. intros [Hni Hnl].
        eapply conseq_rule with
          (p := <||V293_ready_guard_continuation ni nl aop||> **
            OS[(fun _ : hid => false), false, nil, true::critical] **
            ATopis INUM ** invlth_isr I 0 INUM **
            (CurTid tid ** (bindings ** (frame px ** Atrue))))
          (q := V293_ready_roundtrip_post unmap group rows high table target bt bg br bh bp bo tp
            tid (V293_ready_guard_continuation ni nl aop) critical (frame px)).
        -- intros s Hs. unfold V293_ready_guard_resumed, V293_ready_connected_resumed,
             V293_storage_connected_locals, SWINVt in Hs.
           apply V293_ready_exit_resources. unfold CurTid, bindings, frame in *. sep auto.
        -- intros s Hs. exists ni. exists nl. sep auto.
        -- apply excrit1_rule.
           ++ unfold CurTid, Agvarmapsto, Aptrmapsto, bindings, frame, guardbindings, V293_sched_globals,
                V293_prefix_bindings, V293_counter_bindings. simpl.
              repeat split; try exact Logic.I; exact Hpx.
           ++ intros s Hs. unfold CurLINV. exists (nil : list logicvar).
              pose proof (V293_switch_local_empty tid nil) as HL.
              assert (HP : s |= CurTid tid ** Aemp ** Atrue) by (sep auto).
              eapply astar_mono in HP; [ | intros st H; exact H | apply astar_mono;
                [exact HL | intros st H; exact H]]. sep auto.
Qed.
End ReadyPointerGuards.

(* The priority byte belongs to the SAME shared storage, not Px. Its exact
   value survives the prefix as an ordinary same-state observation. *)
(* Evaluation depends only on physical bytes and environment bindings. *)
Lemma V293_storage_priority_reads : forall unmap group rows high table target current
  bt bg br bh bp bo bcur tp lo hi nc s,
  lo < 256 -> hi < 256 -> (exists p, V293_bitmap_ready lo hi p) -> nc < 256 ->
  s |= V293_sched_globals unmap group rows high bt bg br bh ** Atrue ->
  s |= ((PV (bh, Int.zero) @ Tint8 |->
      (V293_byteval (V293_ready_select lo hi (V293_ready_group lo hi)))) **
      (PV (bcur, Int.zero) @ Tint8 |-> (V293_byteval nc))) **
    ((V293_prefix_bindings table high target tp bp bo **
      (Agvarenv current Tint8 (bcur, 0%Z) //\\ A_notin_lenv current)) ** Atrue) ->
  evalval (V293_OSSched_different high current) (getsmem s) =
    Some (Vint32 (if Nat.eqb (V293_ready_select lo hi (V293_ready_group lo hi)) nc
      then Int.zero else Int.one)) /\
  evaltype (V293_OSSched_different high current) (getsmem s) = Some Tint32.
Proof.
  intros unmap group rows high table target current bt bg br bh bp bo bcur tp lo hi nc s
    Hlo Hhi Hr Hnc HG HP.
  assert (Hselected : V293_ready_select lo hi (V293_ready_group lo hi) < 256).
  { pose proof (V293_ready_selection_range lo hi (V293_ready_group lo hi) Hlo Hhi eq_refl Hr). lia. }
  assert (EH : evalval (ecast (evar high) Tint32) (getsmem s) =
    Some (V293_byteval (V293_ready_select lo hi (V293_ready_group lo hi))) /\
    evaltype (ecast (evar high) Tint32) (getsmem s) = Some Tint32).
  { eapply V293_byte_variable.
    - eapply V293_star_env_l with (E := fun ge _ => get ge high = Some (bh, Tint8)); [ | exact HG].
      intros st [_ [_ [_ [b [G [Eb _]]]]]]. inversion Eb; subst; exact G.
    - eapply V293_star_env_r with (E := fun _ le => get le high = None); [ | exact HP]. intros st H.
      eapply V293_star_env_l with (E := fun _ le => get le high = None); [ | exact H]. intros st0 H0.
      eapply V293_star_env_l with (E := fun _ le => get le high = None); [ | exact H0]. intros st1 H1.
      exact (proj1 (proj2 (proj2 (proj2 (V293_prefix_bindings_view _ _ _ _ _ _ _ H1))))).
    - eapply V293_star_load_l; [ | exact HP]. intros st H.
      eapply V293_star_load_l; [ | exact H]. intros; eapply V293_mapsto_load; eauto. }
  assert (EC : evalval (ecast (evar current) Tint32) (getsmem s) = Some (V293_byteval nc) /\
    evaltype (ecast (evar current) Tint32) (getsmem s) = Some Tint32).
  { eapply V293_byte_variable.
    - eapply V293_star_env_r with (E := fun ge _ => get ge current = Some (bcur, Tint8)); [ | exact HP]. intros st H.
      eapply V293_star_env_l with (E := fun ge _ => get ge current = Some (bcur, Tint8)); [ | exact H]. intros st0 H0.
      eapply V293_star_env_r with (E := fun ge _ => get ge current = Some (bcur, Tint8)); [ | exact H0]. intros st1 [G _].
      destruct G as [b [G [Eb _]]]. inversion Eb; subst; exact G.
    - eapply V293_star_env_r with (E := fun _ le => get le current = None); [ | exact HP]. intros st H.
      eapply V293_star_env_l with (E := fun _ le => get le current = None); [ | exact H]. intros st0 H0.
      eapply V293_star_env_r with (E := fun _ le => get le current = None); [ | exact H0]. intros st1 [_ [N _]].
      destruct (get (getlenv st1) current) as [v | ] eqn:E; [ | reflexivity].
      exfalso. apply N. exists v; exact E.
    - eapply V293_star_load_l; [ | exact HP]. intros st H.
      eapply V293_star_load_r; [ | exact H]. intros; eapply V293_mapsto_load; eauto. }
  destruct EH as [Eh Th]. destruct EC as [Ec Tc].
  unfold V293_OSSched_different. destruct s as [[[[[[ge le] M] irs] aux] O] op].
  cbn [getsmem get_smem evalval evaltype] in Eh, Th, Ec, Tc |- *. rewrite Eh, Ec, Th, Tc.
  unfold V293_byteval. cbn [bop_eval val_eq bop_type]. rewrite V293_byte_eq.
  - destruct (Nat.eqb (V293_ready_select lo hi (V293_ready_group lo hi)) nc); split; reflexivity.
  - pose proof (V293_ready_selection_range lo hi (V293_ready_group lo hi) Hlo Hhi eq_refl Hr). lia.
  - exact Hnc.
Qed.

Section PriorityObservation.
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
Let extra := ((bcur, 0%Z), Tint8) :: rest.
Definition V293_priority_kept :=
  (PV (bcur, Int.zero) @ Tint8 |-> (V293_byteval nc)) ** V293_storage rest.
Definition V293_priority_bindings :=
  (Agvarenv current Tint8 (bcur, 0%Z) //\\ A_notin_lenv current) ** px.
Definition V293_priority_entry old hv :=
  V293_retained_storage_prefix_entry unmap group rows high table target bt bg br bh bp bo tp
    lo hi entries extra V293_priority_kept tid tasks events now aop stack critical
    V293_priority_bindings old hv.
Definition V293_priority_closed :=
  V293_retained_storage_prefix_closed unmap group rows high table target bt bg br bh bp bo tp
    lo hi entries extra V293_priority_kept tid tasks events now aop stack critical
    V293_priority_bindings.
Lemma V293_priority_kept_erase : nc < 256 -> V293_priority_kept ==> V293_storage extra.
Proof.
  intros Hnc s Hs. unfold V293_priority_kept in Hs. cbn [extra V293_storage].
  eapply astar_mono; [ | intros st H; exact H | exact Hs].
  intros st H. unfold V293_storage_cell. exists (V293_byteval nc).
  sep auto. apply V293_byte_type; exact Hnc.
Qed.

(* The physical reads, not merely the abstract task relation, determine the
   branch condition. No task-status or highest-ready premise is needed here. *)
Theorem V293_storage_priority_comparison : forall s,
  lo < 256 -> hi < 256 -> (exists p, V293_bitmap_ready lo hi p) -> nc < 256 ->
  s |= V293_priority_closed ->
  evalval (V293_OSSched_different high current) (getsmem s) =
    Some (Vint32 (if Nat.eqb (V293_ready_select lo hi (V293_ready_group lo hi)) nc
      then Int.zero else Int.one)) /\
  evaltype (V293_OSSched_different high current) (getsmem s) = Some Tint32.
Proof.
  intros s Hlo Hhi Hr Hnc [next Hs].
  assert (HP : s |=
    ((PV (bh, Int.zero) @ Tint8 |->
      (V293_byteval (V293_ready_select lo hi (V293_ready_group lo hi)))) **
      (PV (bcur, Int.zero) @ Tint8 |-> (V293_byteval nc))) **
    ((V293_prefix_bindings table high target tp bp bo **
      (Agvarenv current Tint8 (bcur, 0%Z) //\\ A_notin_lenv current)) ** Atrue)).
  { assert (HK : s |=
      V293_retained_prefix_snapshot target bt bg br bh bp tp lo hi entries extra
        V293_priority_kept tid tasks events now next **
      (V293_prefix_bindings table high target tp bp bo **
        ((Agvarenv current Tint8 (bcur, 0%Z) //\\ A_notin_lenv current) ** Atrue)))
      by (unfold V293_priority_bindings in Hs; sep auto).
    eapply astar_mono in HK; [ | intros st [_ H]; exact H | intros st H; exact H].
    clear Hs. unfold V293_retained_prefix_physical, V293_priority_kept in HK. sep auto. }
  assert (HG : s |= V293_sched_globals unmap group rows high bt bg br bh ** Atrue) by (clear HP; sep auto).
  eapply V293_storage_priority_reads; eassumption.
Qed.

Theorem V293_OSSched_storage_priority_prefix : forall Spec r ri sched_id old hv,
  lo < 256 -> hi < 256 -> (exists p, V293_bitmap_ready lo hi p) -> nc < 256 ->
  V293_bitmap_tasks lo hi tasks -> V293_priority_table entries tasks ->
  Forall (fun v => rule_type_val_match (Tptr tp) v = true) entries -> GoodFrm px ->
  Spec sched_id = Some
    (V293_critical_fpre unmap group rows high bt bg br bh V293_shared_li V293_opened_inv V293_switch_li_good,
     V293_critical_fpost unmap group rows high bt bg br bh V293_shared_li V293_opened_inv V293_switch_li_good,
     (Tvoid, nil)) ->
  InfRules Spec V293_scheduler V293_shared_li
    (V293_storage_inv (V293_prefix_cells bt bg br bh bp tp entries extra) target tp) r ri
    (V293_priority_entry old hv) (V293_OSSched_unlocked_prefix sched_id table high target)
    V293_priority_closed tid.
Proof.
  intros Spec r ri sched_id old hv Hlo Hhi Hr Hnc Hb Ht Hptr Hpx Hspec.
  apply V293_retained_OSSched_storage_closed_prefix; try assumption.
  - unfold V293_priority_kept. simpl. split; [tauto | apply V293_storage_frame_good].
  - apply V293_priority_kept_erase; exact Hnc.
  - unfold V293_priority_bindings. simpl. tauto.
Qed.
End PriorityObservation.

(* Counter and accurate current byte share ONE layout. Neither is Px. *)
Section StorageConditional.
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
Let tailrest := ((bcur, 0%Z), Tint8) :: rest.
Let extra := ((bcounter, 0%Z), Tint32) :: tailrest.
Let cells := V293_prefix_cells bt bg br bh bp tp entries extra.
Let current_bindings := (Agvarenv current Tint8 (bcur, 0%Z) //\\ A_notin_lenv current) ** px.
Definition V293_conditional_kept := V293_storage_cell (bcounter, 0%Z) Tint32 **
  V293_priority_kept bcur nc rest.
Let bindings := V293_counter_bindings counter bcounter ** current_bindings.
Definition V293_conditional_entry old hv :=
  V293_retained_storage_prefix_entry unmap group rows high table target bt bg br bh bp bo tp
    lo hi entries extra V293_conditional_kept tid tasks events now (sched;;aop) stack critical bindings old hv.
Definition V293_conditional_closed :=
  V293_retained_storage_prefix_closed unmap group rows high table target bt bg br bh bp bo tp
    lo hi entries extra V293_conditional_kept tid tasks events now (sched;;aop) stack critical bindings.
Let middle := V293_storage_prefix_closed unmap group rows high table target bt bg br bh bp bo tp
  lo hi entries extra tid tasks events now (sched;;aop) stack critical bindings.
Let tail next c := V293_storage_connected_tail unmap group rows high table target counter
  bt bg br bh bp bo bcounter tp lo hi entries tailrest tid tasks events now aop stack critical
  current_bindings next c.
Definition V293_conditional_resumed := V293_storage_connected_resumed unmap group rows high table target counter
  bt bg br bh bp bo bcounter tp entries tailrest tid aop stack critical current_bindings.

Lemma V293_conditional_kept_erase : nc < 256 -> V293_conditional_kept ==> V293_storage extra.
Proof.
  intros Hnc. unfold V293_conditional_kept. cbn [extra V293_storage].
  apply astar_mono; [intros st H; exact H | apply V293_priority_kept_erase; exact Hnc].
Qed.
Theorem V293_conditional_comparison : forall s,
  lo < 256 -> hi < 256 -> (exists p, V293_bitmap_ready lo hi p) -> nc < 256 ->
  s |= V293_conditional_closed ->
  evalval (V293_OSSched_different high current) (getsmem s) =
    Some (Vint32 (if Nat.eqb (V293_ready_select lo hi (V293_ready_group lo hi)) nc
      then Int.zero else Int.one)) /\
  evaltype (V293_OSSched_different high current) (getsmem s) = Some Tint32.
Proof.
  intros s Hlo Hhi Hr Hnc [next Hs].
  assert (HP : s |=
    ((PV (bh, Int.zero) @ Tint8 |->
      (V293_byteval (V293_ready_select lo hi (V293_ready_group lo hi)))) **
      (PV (bcur, Int.zero) @ Tint8 |-> (V293_byteval nc))) **
    ((V293_prefix_bindings table high target tp bp bo **
      (Agvarenv current Tint8 (bcur, 0%Z) //\\ A_notin_lenv current)) ** Atrue)).
  { assert (HK : s |= V293_retained_prefix_snapshot target bt bg br bh bp tp lo hi entries extra
        V293_conditional_kept tid tasks events now next **
      (V293_prefix_bindings table high target tp bp bo **
        ((Agvarenv current Tint8 (bcur, 0%Z) //\\ A_notin_lenv current) ** Atrue)))
      by (unfold bindings, current_bindings in Hs; sep auto).
    eapply astar_mono in HK; [ | intros st [_ H]; exact H | intros st H; exact H].
    clear Hs. unfold V293_retained_prefix_physical, V293_conditional_kept, V293_priority_kept in HK. sep auto. }
  assert (HG : s |= V293_sched_globals unmap group rows high bt bg br bh ** Atrue) by (clear HP; sep auto).
  eapply V293_storage_priority_reads; eassumption.
Qed.

Lemma V293_conditional_forget : nc < 256 -> V293_conditional_closed ==> middle.
Proof.
  intros Hnc s [next Hs]. exists next.
  assert (HS : V293_retained_prefix_snapshot target bt bg br bh bp tp lo hi entries extra
      V293_conditional_kept tid tasks events now next ==>
    V293_prefix_snapshot target bt bg br bh bp tp lo hi entries extra tid tasks events now next).
  { assert (HF : V293_retained_prefix_physical bt bg br bh bp tp lo hi entries V293_conditional_kept ==>
        V293_prefix_physical bt bg br bh bp tp lo hi entries extra).
    { unfold V293_retained_prefix_physical, V293_prefix_physical.
      apply astar_mono; [intros st H; exact H | ].
      apply astar_mono; [intros st H; exact H | ].
      apply astar_mono; [intros st H; exact H | apply V293_conditional_kept_erase; exact Hnc]. }
    intros st [HI HP]. split; [exact HI | ].
    eapply astar_mono; [intros st0 H; exact H | | exact HP].
    apply astar_mono; [exact HF | intros st0 H; exact H]. }
  assert (HK : s |= V293_retained_prefix_snapshot target bt bg br bh bp tp lo hi entries extra
      V293_conditional_kept tid tasks events now next **
    ([|V293_highest_ready tasks next|] **
      ((<||sched;;aop||> ** CurTid tid) ** ((Ais stack ** Acs critical) **
        ((V293_sched_globals unmap group rows high bt bg br bh ** V293_prefix_bindings table high target tp bp bo) **
          (bindings ** Atrue)))))) by (sep auto).
  eapply astar_mono in HK; [ | exact HS | intros st H; exact H]. clear Hs. sep auto.
Qed.
Theorem V293_conditional_equal_finish :
  lo < 256 -> hi < 256 -> (exists p, V293_bitmap_ready lo hi p) -> nc < 256 ->
  V293_bitmap_tasks lo hi tasks -> V293_priority_table entries tasks ->
  Forall (fun v => rule_type_val_match (Tptr tp) v = true) entries ->
  V293_current_task tasks tid nc -> GoodFrm px ->
  V293_ready_select lo hi (V293_ready_group lo hi) = nc ->
  absinferfull V293_scheduler V293_shared_li V293_conditional_closed V293_conditional_resumed tid.
Proof.
  intros Hlo Hhi Hr Hnc Hb Htable Hptr Hcur Hpx Heq.
  eapply absinfer_conseq' with
    (p := EX next : Modules.tid, EX c : int32, [|V293_highest_ready tasks next|] ** tail next c).
  - intros s H; exact H.
  - apply absinfer_ex'. intro next. apply absinfer_ex'. intro c.
    eapply absinfer_conseq' with (p := tail tid c).
    + intros s H; exact H.
    + apply V293_storage_connected_self_finish; try assumption.
      * destruct (V293_ready_selection_task lo hi entries tasks Hlo Hhi Hr Hb Htable)
          as [chosen [m [Ht [Hp Hhighest]]]].
        pose proof (proj2 (V293_OSSched_current_target lo hi entries tasks tid nc chosen
          Hlo Hhi Hr Hb Htable Hcur Hhighest) Heq). subst chosen. exact Hhighest.
      * unfold current_bindings. simpl. tauto.
    + intros s Hs. apply astar_l_apure_elim in Hs. destruct Hs as [Hhighest Hs].
      pose proof (proj2 (V293_OSSched_current_target lo hi entries tasks tid nc next
        Hlo Hhi Hr Hb Htable Hcur Hhighest) Heq). subst next. exact Hs.
  - intros s Hs. apply V293_conditional_forget in Hs; [ | exact Hnc].
    apply V293_storage_connected_prefix_open in Hs. exact Hs.
Qed.

Definition V293_conditional_branch_post :=
  if Nat.eqb (V293_ready_select lo hi (V293_ready_group lo hi)) nc
  then V293_conditional_closed else V293_conditional_resumed.
Theorem V293_conditional_change : forall Spec r ri,
  lo < 256 -> hi < 256 -> (exists p, V293_bitmap_ready lo hi p) -> nc < 256 ->
  Forall (fun v => rule_type_val_match (Tptr tp) v = true) entries ->
  indom tasks tid -> GoodFrm px -> (px ==> LINV V293_shared_li tid nil ** Atrue) ->
  InfRules Spec V293_scheduler V293_shared_li (V293_storage_inv cells target tp) r ri
    V293_conditional_closed (V293_OSSched_change high current counter (sprim (switch target)))
    V293_conditional_branch_post tid.
Proof.
  intros Spec r ri Hlo Hhi Hr Hnc Hptr Hmem Hpx Hlocal.
  unfold V293_OSSched_change, V293_conditional_branch_post. eapply ift_rule with (tp := Tint32).
  - intros s Hs. destruct (V293_conditional_comparison s Hlo Hhi Hr Hnc Hs) as [Ev Et].
    eexists. split; [exact Ev | ]. split; [exact Et | discriminate].
  - intros s [Hs [v [Ev Hv]]].
    destruct (V293_conditional_comparison s Hlo Hhi Hr Hnc Hs) as [E _].
    rewrite E in Ev. inversion Ev; subst v.
    destruct (Nat.eqb (V293_ready_select lo hi (V293_ready_group lo hi)) nc);
      [exact Hs | vm_compute in Hv; discriminate].
  - destruct (Nat.eqb (V293_ready_select lo hi (V293_ready_group lo hi)) nc) eqn:En.
    + eapply conseq_rule with (p := Afalse).
      * intros s [Hs [v [Ev Hv]]].
        destruct (V293_conditional_comparison s Hlo Hhi Hr Hnc Hs) as [E _].
        rewrite En in E. rewrite E in Ev. inversion Ev; subst v. vm_compute in Hv; discriminate.
      * intros s H; exact H.
      * apply pfalse_rule.
    + eapply conseq_rule with (p := EX next : Modules.tid, EX c : int32,
        [|V293_highest_ready tasks next|] ** tail next c).
      * intros s [Hs _]. apply V293_conditional_forget in Hs; [ | exact Hnc].
        apply V293_storage_connected_prefix_open in Hs. exact Hs.
      * intros s H; exact H.
      * apply ex_intro_rule. intro next. apply ex_intro_rule. intro c.
        eapply conseq_rule with (p := tail next c ** [|V293_highest_ready tasks next|]).
        -- intros s H; sep auto.
        -- intros s H; exact H.
        -- apply pure_split_rule. intro Hhighest. eapply seq_rule.
           ++ apply V293_storage_connected_increment. intros s Hs.
              unfold current_bindings in Hs. assert (HP : s |= px ** Atrue) by (sep auto).
              eapply astar_mono in HP; [ | exact Hlocal | intros st H; exact H]. clear Hs. sep auto.
           ++ apply V293_storage_connected_switch; try assumption.
              ** unfold current_bindings. simpl. tauto.
              ** intros s Hs. unfold current_bindings in Hs.
                 assert (HP : s |= px ** Atrue) by (sep auto).
                 eapply astar_mono in HP; [ | exact Hlocal | intros st H; exact H]. clear Hs. sep auto.
Qed.

Theorem V293_OSSched_storage_conditional : forall Spec r ri sched_id old hv,
  lo < 256 -> hi < 256 -> (exists p, V293_bitmap_ready lo hi p) -> nc < 256 ->
  V293_bitmap_tasks lo hi tasks -> V293_priority_table entries tasks ->
  Forall (fun v => rule_type_val_match (Tptr tp) v = true) entries ->
  V293_current_task tasks tid nc -> indom tasks tid -> GoodFrm px ->
  (px ==> LINV V293_shared_li tid nil ** Atrue) ->
  Spec sched_id = Some
    (V293_critical_fpre unmap group rows high bt bg br bh V293_shared_li V293_opened_inv V293_switch_li_good,
     V293_critical_fpost unmap group rows high bt bg br bh V293_shared_li V293_opened_inv V293_switch_li_good,
     (Tvoid, nil)) ->
  InfRules Spec V293_scheduler V293_shared_li (V293_storage_inv cells target tp) r ri
    (V293_conditional_entry old hv)
    (sseq (V293_OSSched_unlocked_prefix sched_id table high target)
      (V293_OSSched_change high current counter (sprim (switch target))))
    V293_conditional_resumed tid.
Proof.
  intros Spec r ri sched_id old hv Hlo Hhi Hr Hnc Hb Htable Hptr Hcur Hmem Hpx Hlocal Hspec.
  eapply seq_rule with (p' := V293_conditional_closed).
  - apply V293_retained_OSSched_storage_closed_prefix; try assumption.
    + unfold V293_conditional_kept, V293_priority_kept. simpl.
      split; [unfold V293_storage_cell; simpl; auto | ].
      split; [tauto | apply V293_storage_frame_good].
    + apply V293_conditional_kept_erase; exact Hnc.
    + unfold bindings, current_bindings, V293_counter_bindings. simpl. tauto.
  - eapply abscsq_rule_full with (p := V293_conditional_closed) (q := V293_conditional_branch_post).
    + apply absinfer_eq'.
    + unfold V293_conditional_branch_post.
      destruct (Nat.eqb (V293_ready_select lo hi (V293_ready_group lo hi)) nc) eqn:E.
      * apply Nat.eqb_eq in E. apply V293_conditional_equal_finish; assumption.
      * apply absinfer_eq'.
    + apply V293_conditional_change; assumption.
Qed.
End StorageConditional.

(* Both guard bytes are shared storage, not a private frame across switch. *)
Section GuardedStorage.
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
Let guardbindings := (Agvarenv interrupt Tint8 (bi, 0%Z) //\\ A_notin_lenv interrupt) **
  ((Agvarenv lock Tint8 (bl, 0%Z) //\\ A_notin_lenv lock) ** px).
Let cells := V293_prefix_cells bt bg br bh bp tp entries
  (((bcounter, 0%Z), Tint32) :: ((bcur, 0%Z), Tint8) :: guardrest).
Definition V293_storage_guarded_entry old hv :=
  V293_conditional_entry unmap group rows high table target current counter
    bt bg br bh bp bo bcur bcounter tp lo hi nc entries guardrest tid tasks events now aop
    stack critical guardbindings old hv //\\
  ((V293_guard_cell interrupt bi ni ** V293_guard_cell lock bl nl) ** Atrue).
Definition V293_storage_guarded_resumed :=
  V293_conditional_resumed unmap group rows high table target current counter
    bt bg br bh bp bo bcur bcounter tp entries guardrest tid aop stack critical guardbindings.

Theorem V293_OSSched_storage_guarded : forall Spec r ri sched_id old hv,
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
  InfRules Spec V293_scheduler V293_shared_li (V293_storage_inv cells target tp) r ri
    (V293_storage_guarded_entry old hv)
    (V293_OSSched_guards interrupt lock
      (sseq (V293_OSSched_unlocked_prefix sched_id table high target)
        (V293_OSSched_change high current counter (sprim (switch target)))))
    (if Nat.eqb ni 0 && Nat.eqb nl 0 then V293_storage_guarded_resumed
     else V293_storage_guarded_entry old hv) tid.
Proof.
  intros Spec r ri sched_id old hv Hlo Hhi Hr Hnc Hni Hnl Hb Htable Hptr Hcur Hmem Hpx Hlocal Hspec.
  eapply V293_OSSched_guards_rule with (bi := bi) (bl := bl) (ri_mem := Atrue) (rl_mem := Atrue);
    try assumption.
  - intros s [_ H]. sep auto.
  - intros s [_ H]. sep auto.
  - intros Ei El. eapply conseq_rule.
    + intros s [H _]; exact H.
    + intros s H; exact H.
    + apply V293_OSSched_storage_conditional; try assumption.
      * unfold guardbindings. simpl. tauto.
      * intros s Hs. unfold guardbindings in Hs.
        assert (HP : s |= px ** Atrue) by (sep auto).
        eapply astar_mono in HP; [ | exact Hlocal | intros st H; exact H]. clear Hs. sep auto.
Qed.
End GuardedStorage.

(* Exact post-encrit current-priority observation is an explicit frontier,
   not a consequence of the existing readyI or a stale pre-encrit snapshot. *)
Section ReadyConditional.
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
Let tailrest := ((bcur, 0%Z), Tint8) :: rest.
Let extra := ((bcounter, 0%Z), Tint32) :: tailrest.
Let readyI := V293_ready_inv bt bg br bh bp tp extra target.
Let current_bindings := (Agvarenv current Tint8 (bcur, 0%Z) //\\ A_notin_lenv current) ** px.
Let bindings := V293_counter_bindings counter bcounter ** current_bindings.
Let kept := V293_conditional_kept bcur bcounter nc rest.
Definition V293_ready_conditional_entry old hv :=
  <||sched;;aop||> **
    (((SWINV readyI //\\
      ((V293_shared_flags ** ((CurTid tid ** V293_shared_fields tid tasks events now) **
        (GV target @ (Tptr tp) |-> old))) **
        V293_retained_prefix_entry_heap bt bg br bh bp tp lo hi entries kept hv)) ** CurTid tid) **
      ((Ais stack ** Acs critical) **
        ((V293_sched_globals unmap group rows high bt bg br bh **
          V293_prefix_bindings table high target tp bp bo) ** bindings))).
Definition V293_ready_conditional_open :=
  V293_retained_storage_prefix_returned unmap group rows high table target bt bg br bh bp bo tp
    lo hi entries kept tid tasks events now (sched;;aop) stack critical bindings.
Let tail next c := V293_storage_connected_tail unmap group rows high table target counter
  bt bg br bh bp bo bcounter tp lo hi entries tailrest tid tasks events now aop stack critical current_bindings next c.
Definition V293_ready_conditional_resumed :=
  V293_ready_connected_resumed unmap group rows high table target counter
    bt bg br bh bp bo bcounter tp tailrest tid aop stack critical current_bindings.

Theorem V293_ready_conditional_comparison : forall s,
  lo < 256 -> hi < 256 -> (exists p, V293_bitmap_ready lo hi p) -> nc < 256 ->
  s |= V293_ready_conditional_open ->
  evalval (V293_OSSched_different high current) (getsmem s) =
    Some (Vint32 (if Nat.eqb (V293_ready_select lo hi (V293_ready_group lo hi)) nc
      then Int.zero else Int.one)) /\
  evaltype (V293_OSSched_different high current) (getsmem s) = Some Tint32.
Proof.
  intros s Hlo Hhi Hr Hnc [next Hs].
  assert (HP : s |=
    ((PV (bh, Int.zero) @ Tint8 |->
      (V293_byteval (V293_ready_select lo hi (V293_ready_group lo hi)))) **
      (PV (bcur, Int.zero) @ Tint8 |-> (V293_byteval nc))) **
    ((V293_prefix_bindings table high target tp bp bo **
      (Agvarenv current Tint8 (bcur, 0%Z) //\\ A_notin_lenv current)) ** Atrue)).
  { unfold V293_retained_prefix_returned, V293_retained_prefix_physical,
      kept, V293_conditional_kept, V293_priority_kept, bindings, current_bindings in Hs. sep auto. }
  assert (HG : s |= V293_sched_globals unmap group rows high bt bg br bh ** Atrue) by (clear HP; sep auto).
  eapply V293_storage_priority_reads; eassumption.
Qed.

Lemma V293_ready_conditional_tail : nc < 256 ->
  V293_ready_conditional_open ==>
  EX next : Modules.tid, EX c : int32, [|V293_highest_ready tasks next|] ** tail next c.
Proof.
  intros Hnc s [next Hs].
  assert (HF : kept ==> V293_storage extra).
  { apply V293_conditional_kept_erase; exact Hnc. }
  assert (HP : s |= kept **
    ([|V293_highest_ready tasks next|] **
      ((<||sched;;aop||> ** ((V293_storage_open target tp tid tasks events now next ** CurTid tid) **
        (Ais stack ** Acs critical))) **
        ((V293_inputs_full bt bg br lo hi **
          ((PV (bh, Int.zero) @ Tint8 |-> (V293_byteval (V293_ready_select lo hi (V293_ready_group lo hi)))) **
            V293_array true bp 0 4 (Tptr tp) entries)) **
          ((V293_sched_globals unmap group rows high bt bg br bh ** V293_prefix_bindings table high target tp bp bo) **
            (bindings ** Atrue)))))).
  { unfold V293_retained_prefix_returned, V293_retained_prefix_physical in Hs. sep auto. }
  eapply astar_mono in HP; [ | exact HF | intros st H; exact H].
  cbn [extra V293_storage] in HP. unfold V293_storage_cell at 1 in HP.
  sep normal in HP. sep destruct HP. sep split in HP.
  destruct x; simpl in H; try discriminate.
  exists next. exists i. unfold tail, V293_storage_connected_tail, V293_storage_connected_payload,
    V293_storage_connected_locals, V293_prefix_physical, bindings. clear Hs. sep auto.
Qed.

Theorem V293_ready_conditional_equal_finish :
  lo < 256 -> hi < 256 -> (exists p, V293_bitmap_ready lo hi p) -> nc < 256 ->
  V293_bitmap_tasks lo hi tasks -> V293_priority_table entries tasks ->
  Forall (fun v => rule_type_val_match (Tptr tp) v = true) entries ->
  V293_current_task tasks tid nc -> GoodFrm px ->
  V293_ready_select lo hi (V293_ready_group lo hi) = nc ->
  absinferfull V293_scheduler V293_shared_li
    V293_ready_conditional_open V293_ready_conditional_resumed tid.
Proof.
  intros Hlo Hhi Hr Hnc Hb Htable Hptr Hcur Hpx Heq.
  eapply absinfer_conseq' with
    (p := EX next : Modules.tid, EX c : int32, [|V293_highest_ready tasks next|] ** tail next c).
  - intros s H; exact H.
  - apply absinfer_ex'. intro next. apply absinfer_ex'. intro c.
    eapply absinfer_conseq' with (p := tail tid c).
    + intros s H; exact H.
    + apply V293_ready_connected_self_finish; try assumption.
      * destruct (V293_ready_selection_task lo hi entries tasks Hlo Hhi Hr Hb Htable)
          as [chosen [m [Ht [Hp Hhighest]]]].
        pose proof (proj2 (V293_OSSched_current_target lo hi entries tasks tid nc chosen
          Hlo Hhi Hr Hb Htable Hcur Hhighest) Heq). subst chosen. exact Hhighest.
      * unfold current_bindings. simpl. tauto.
    + intros s Hs. apply astar_l_apure_elim in Hs. destruct Hs as [Hhighest Hs].
      pose proof (proj2 (V293_OSSched_current_target lo hi entries tasks tid nc next
        Hlo Hhi Hr Hb Htable Hcur Hhighest) Heq). subst next. exact Hs.
  - apply V293_ready_conditional_tail; exact Hnc.
Qed.

Definition V293_ready_conditional_branch_post :=
  if Nat.eqb (V293_ready_select lo hi (V293_ready_group lo hi)) nc
  then V293_ready_conditional_open else V293_ready_conditional_resumed.
Theorem V293_ready_conditional_change : forall Spec r ri,
  lo < 256 -> hi < 256 -> (exists p, V293_bitmap_ready lo hi p) -> nc < 256 ->
  V293_bitmap_tasks lo hi tasks -> V293_priority_table entries tasks ->
  Forall (fun v => rule_type_val_match (Tptr tp) v = true) entries ->
  indom tasks tid -> GoodFrm px -> (px ==> LINV V293_shared_li tid nil ** Atrue) ->
  InfRules Spec V293_scheduler V293_shared_li readyI r ri
    V293_ready_conditional_open (V293_OSSched_change high current counter (sprim (switch target)))
    V293_ready_conditional_branch_post tid.
Proof.
  intros Spec r ri Hlo Hhi Hr Hnc Hb Htable Hptr Hmem Hpx Hlocal.
  unfold V293_OSSched_change, V293_ready_conditional_branch_post. eapply ift_rule with (tp := Tint32).
  - intros s Hs. destruct (V293_ready_conditional_comparison s Hlo Hhi Hr Hnc Hs) as [Ev Et].
    eexists. split; [exact Ev | ]. split; [exact Et | discriminate].
  - intros s [Hs [v [Ev Hv]]].
    destruct (V293_ready_conditional_comparison s Hlo Hhi Hr Hnc Hs) as [E _].
    rewrite E in Ev. inversion Ev; subst v.
    destruct (Nat.eqb (V293_ready_select lo hi (V293_ready_group lo hi)) nc);
      [exact Hs | vm_compute in Hv; discriminate].
  - destruct (Nat.eqb (V293_ready_select lo hi (V293_ready_group lo hi)) nc) eqn:En.
    + eapply conseq_rule with (p := Afalse).
      * intros s [Hs [v [Ev Hv]]].
        destruct (V293_ready_conditional_comparison s Hlo Hhi Hr Hnc Hs) as [E _].
        rewrite En in E. rewrite E in Ev. inversion Ev; subst v. vm_compute in Hv; discriminate.
      * intros s H; exact H.
      * apply pfalse_rule.
    + eapply conseq_rule with (p := EX next : Modules.tid, EX c : int32,
        [|V293_highest_ready tasks next|] ** tail next c).
      * intros s [Hs _]. apply V293_ready_conditional_tail; assumption.
      * intros s H; exact H.
      * apply ex_intro_rule. intro next. apply ex_intro_rule. intro c.
        eapply conseq_rule with (p := tail next c ** [|V293_highest_ready tasks next|]).
        -- intros s H; sep auto.
        -- intros s H; exact H.
        -- apply pure_split_rule. intro Hhighest. eapply seq_rule.
           ++ apply V293_storage_connected_increment_under. intros s Hs.
              unfold current_bindings in Hs. assert (HP : s |= px ** Atrue) by (sep auto).
              eapply astar_mono in HP; [ | exact Hlocal | intros st H; exact H]. clear Hs. sep auto.
           ++ apply V293_ready_connected_switch; try assumption.
              ** unfold current_bindings. simpl. tauto.
              ** intros s Hs. unfold current_bindings in Hs.
                 assert (HP : s |= px ** Atrue) by (sep auto).
                 eapply astar_mono in HP; [ | exact Hlocal | intros st H; exact H]. clear Hs. sep auto.
Qed.

Theorem V293_ready_OSSched_conditional : forall Spec r ri sched_id old hv,
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
    (V293_ready_conditional_entry old hv)
    (sseq (V293_OSSched_unlocked_prefix sched_id table high target)
      (V293_OSSched_change high current counter (sprim (switch target))))
    V293_ready_conditional_resumed tid.
Proof.
  intros Spec r ri sched_id old hv Hlo Hhi Hr Hnc Hb Htable Hptr Hcur Hmem Hpx Hlocal Hspec.
  eapply seq_rule with (p' := V293_ready_conditional_open).
  - eapply conseq_rule.
    3: { eapply V293_retained_OSSched_storage_prefix_returned with (RI := readyI)
        (kept := kept) (lo := lo) (hi := hi) (entries := entries)
        (tid := tid) (tasks := tasks) (events := events) (now := now) (aop := (sched;;aop))
        (stack := stack) (critical := critical) (px := bindings) (old := old);
        try eassumption.
      - unfold kept, V293_conditional_kept, V293_priority_kept. simpl.
        split; [unfold V293_storage_cell; simpl; auto | ]. split; [tauto | apply V293_storage_frame_good].
      - unfold bindings, current_bindings, V293_counter_bindings. simpl. tauto. }
    + intros s Hs. apply V293_retained_storage_prefix_lend_value with (hv := hv); try assumption.
      unfold V293_ready_conditional_entry in Hs.
      eapply astar_mono in Hs; [ | intros st H; exact H | apply astar_mono].
      2: { apply astar_mono; [intros st [_ H]; exact H | intros st H; exact H]. }
      2: { intros st H; exact H. }
      unfold V293_storage_open in Hs. exact Hs.
    + intros s H; exact H.
  - eapply abscsq_rule_full with (p := V293_ready_conditional_open) (q := V293_ready_conditional_branch_post).
    + apply absinfer_eq'.
    + unfold V293_ready_conditional_branch_post.
      destruct (Nat.eqb (V293_ready_select lo hi (V293_ready_group lo hi)) nc) eqn:E.
      * apply Nat.eqb_eq in E. apply V293_ready_conditional_equal_finish; assumption.
      * apply absinfer_eq'.
    + apply V293_ready_conditional_change; assumption.
Qed.
End ReadyConditional.

(* Frozen-C priority comparison, not the candidate pointer comparison.
   The current-priority observation is explicitly post-encrit: this theorem
   does not derive cache accuracy from readyI or a pre-encrit snapshot. *)
Section ReadyPriorityGuards.
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
Let I := V293_ready_inv bt bg br bh bp tp extra target.
Let guardbindings := (Agvarenv interrupt Tint8 (bi, 0%Z) //\\ A_notin_lenv interrupt) **
  ((Agvarenv lock Tint8 (bl, 0%Z) //\\ A_notin_lenv lock) ** px).
Definition V293_ready_priority_guarded_entry old hv :=
  V293_ready_conditional_entry unmap group rows high table target current counter
    bt bg br bh bp bo bcur bcounter tp lo hi nc entries guardrest tid tasks events now
    aop stack critical guardbindings old hv //\\
    ((V293_guard_cell interrupt bi ni ** V293_guard_cell lock bl nl) ** Atrue).
Definition V293_ready_priority_guarded_resumed continuation :=
  V293_ready_conditional_resumed unmap group rows high table target current counter
    bt bg br bh bp bo bcur bcounter tp guardrest tid continuation stack critical guardbindings.

(* Disabled branches keep sched pending and already own the SAME closed
   readyI. Forget observations only; do not consume an abstract schedule. *)
Lemma V293_ready_priority_guarded_skip : forall old hv,
  V293_ready_priority_guarded_entry old hv ==>
  V293_ready_priority_guarded_resumed (sched;;aop).
Proof.
  intros old hv s [Hs _].
  unfold V293_ready_conditional_entry in Hs.
  unfold V293_ready_priority_guarded_resumed, V293_ready_conditional_resumed,
    V293_ready_connected_resumed, V293_storage_connected_locals, SWINVt, CurTid.
  eapply astar_mono in Hs.
  2: { intros st H; exact H. }
  2: { apply astar_mono.
       - apply astar_mono; [intros st [H _]; exact H | intros st H; exact H].
       - intros st H; exact H. }
  unfold CurTid in Hs. sep auto.
Qed.

Theorem V293_ready_OSSched_priority_guarded : forall Spec r ri sched_id old hv,
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
  InfRules Spec V293_scheduler V293_shared_li I r ri
    (V293_ready_priority_guarded_entry old hv)
    (V293_OSSched_guards interrupt lock
      (sseq (V293_OSSched_unlocked_prefix sched_id table high target)
        (V293_OSSched_change high current counter (sprim (switch target)))))
    (V293_ready_priority_guarded_resumed
      (if Nat.eqb ni 0 && Nat.eqb nl 0 then aop else (sched;;aop))) tid.
Proof.
  intros Spec r ri sched_id old hv Hlo Hhi Hr Hnc Hni Hnl Hb Htable Hptr Hcur Hmem Hpx Hlocal Hspec.
  eapply conseq_rule with
    (q := if Nat.eqb ni 0 && Nat.eqb nl 0
      then V293_ready_priority_guarded_resumed aop
      else V293_ready_priority_guarded_entry old hv).
  - intros s H; exact H.
  - intros s Hs. destruct (Nat.eqb ni 0 && Nat.eqb nl 0); [exact Hs | ].
    apply V293_ready_priority_guarded_skip with (old := old) (hv := hv); exact Hs.
  - eapply V293_OSSched_guards_rule with (bi := bi) (bl := bl) (ni := ni) (nl := nl)
      (ri_mem := Atrue) (rl_mem := Atrue); try assumption.
    + intros s [_ H]; sep auto.
    + intros s [_ H]; sep auto.
    + intros Ei El. eapply conseq_rule.
      * intros s [H _]; exact H.
      * intros s H; exact H.
      * unfold V293_ready_priority_guarded_resumed, I.
        apply V293_ready_OSSched_conditional; try assumption.
        -- unfold guardbindings. simpl. tauto.
        -- intros s Hs. unfold guardbindings in Hs.
           assert (HP : s |= px ** Atrue) by (sep auto).
           eapply astar_mono in HP; [ | exact Hlocal | intros st H; exact H]. clear Hs. sep auto.
Qed.
End ReadyPriorityGuards.

(* OSTaskChangePrio clears the old priority slot before assigning the new
   one (frozen os_task.c:119-120). This is the exact LIST effect of those
   writes, not a C execution or a proof of the rest of that API. *)
Local Lemma V293_update_nth_same : forall entries p v,
  p < length entries -> nth p (update_nth_val p entries v) Vnull = v.
Proof.
  induction entries as [ |x xs IH]; intros [ | p] v H; simpl in *; try lia;
    [reflexivity | apply IH; lia].
Qed.
Local Lemma V293_update_nth_other : forall entries p q v,
  p <> q -> nth p (update_nth_val q entries v) Vnull = nth p entries Vnull.
Proof.
  induction entries as [ |x xs IH]; intros [ | p] [ | q] v H;
    simpl in *; try reflexivity; try congruence. apply IH. congruence.
Qed.
Theorem V293_rekey_vacates_cache : forall entries cached new next,
  cached < length entries -> cached <> new ->
  nth cached (update_nth_val new (update_nth_val cached entries Vnull) (Vptr next)) Vnull = Vnull.
Proof.
  intros entries cached new next Hrange Hne.
  rewrite V293_update_nth_other by exact Hne. apply V293_update_nth_same. exact Hrange.
Qed.

(* Selection reads this SAME table. An empty cached-priority slot cannot be
   selected, even when the selected TCB IS the current TCB. No accuracy or
   current/target inequality is assumed. *)
Theorem V293_vacated_cache_selection : forall lo hi entries tasks cached,
  lo < 256 -> hi < 256 -> (exists p, V293_bitmap_ready lo hi p) ->
  V293_bitmap_tasks lo hi tasks -> V293_priority_table entries tasks ->
  nth cached entries Vnull = Vnull ->
  V293_ready_select lo hi (V293_ready_group lo hi) <> cached.
Proof.
  intros lo hi entries tasks cached Hlo Hhi Hr Hb Ht Hempty E.
  destruct (V293_ready_selection_task lo hi entries tasks Hlo Hhi Hr Hb Ht)
    as (next & m & Htask & Hentry & Hhighest).
  rewrite E, Hempty in Hentry. discriminate.
Qed.

(* Post-encrit source-priority branch for a vacated cached-priority slot.
   This closes the same real ready relation as the older accurate-cache
   interface, but needs no V293_current_task tasks tid cached premise.
   Ordinary switch does NOT write OSPrioCur, and is NOT OSCtxSw refinement. *)
Section ReadyVacatedCache.
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
Let guardbindings := (Agvarenv interrupt Tint8 (bi, 0%Z) //\\ A_notin_lenv interrupt) **
  ((Agvarenv lock Tint8 (bl, 0%Z) //\\ A_notin_lenv lock) ** px).
Let bindings := V293_counter_bindings counter bcounter **
  ((Agvarenv current Tint8 (bcur, 0%Z) //\\ A_notin_lenv current) ** guardbindings).
Let kept := V293_conditional_kept bcur bcounter nc guardrest.
Let entry old hv := V293_ready_priority_guarded_entry unmap group rows high table target
  current counter interrupt lock bt bg br bh bp bo bcur bcounter bi bl tp lo hi nc ni nl
  entries rest tid tasks events now aop stack critical px old hv.
Let resumed continuation := V293_ready_priority_guarded_resumed unmap group rows high table
  target current counter interrupt lock bt bg br bh bp bo bcur bcounter bi bl tp
  rest tid stack critical px continuation.
Let opened := V293_ready_conditional_open unmap group rows high table target current counter
  bt bg br bh bp bo bcur bcounter tp lo hi nc entries guardrest tid tasks events now
  aop stack critical guardbindings.

Theorem V293_ready_OSSched_vacated_cache : forall Spec r ri sched_id old hv,
  lo < 256 -> hi < 256 -> (exists p, V293_bitmap_ready lo hi p) -> nc < 256 ->
  ni < 256 -> nl < 256 ->
  V293_bitmap_tasks lo hi tasks -> V293_priority_table entries tasks ->
  Forall (fun v => rule_type_val_match (Tptr tp) v = true) entries ->
  nth nc entries Vnull = Vnull -> indom tasks tid -> GoodFrm px ->
  (px ==> LINV V293_shared_li tid nil ** Atrue) ->
  Spec sched_id = Some
    (V293_critical_fpre unmap group rows high bt bg br bh V293_shared_li V293_opened_inv V293_switch_li_good,
     V293_critical_fpost unmap group rows high bt bg br bh V293_shared_li V293_opened_inv V293_switch_li_good,
     (Tvoid, nil)) ->
  InfRules Spec V293_scheduler V293_shared_li readyI r ri
    (entry old hv)
    (V293_OSSched_guards interrupt lock
      (sseq (V293_OSSched_unlocked_prefix sched_id table high target)
        (V293_OSSched_change high current counter (sprim (switch target)))))
    (resumed (if Nat.eqb ni 0 && Nat.eqb nl 0 then aop else (sched;;aop))) tid.
Proof.
  intros Spec r ri sched_id old hv Hlo Hhi Hr Hnc Hni Hnl Hb Htable Hptr Hempty Hmem Hpx Hlocal Hspec.
  assert (Hdifferent : Nat.eqb (V293_ready_select lo hi (V293_ready_group lo hi)) nc = false).
  { apply Nat.eqb_neq. eapply V293_vacated_cache_selection; eassumption. }
  eapply conseq_rule with
    (q := if Nat.eqb ni 0 && Nat.eqb nl 0 then resumed aop else entry old hv).
  - intros s H; exact H.
  - intros s Hs. destruct (Nat.eqb ni 0 && Nat.eqb nl 0); [exact Hs | ].
    eapply V293_ready_priority_guarded_skip with (old := old) (hv := hv); exact Hs.
  - eapply V293_OSSched_guards_rule with (bi := bi) (bl := bl) (ni := ni) (nl := nl)
      (ri_mem := Atrue) (rl_mem := Atrue); try assumption.
    + intros s [_ H]; sep auto.
    + intros s [_ H]; sep auto.
    + intros Ei El. eapply conseq_rule.
      * intros s [H _]; exact H.
      * intros s H; exact H.
      * eapply seq_rule with (p' := opened).
        -- eapply conseq_rule.
           3: { eapply V293_retained_OSSched_storage_prefix_returned with (RI := readyI)
               (kept := kept) (lo := lo) (hi := hi) (entries := entries)
               (tid := tid) (tasks := tasks) (events := events) (now := now) (aop := (sched;;aop))
               (stack := stack) (critical := critical) (px := bindings) (old := old);
               try eassumption.
             - unfold kept, V293_conditional_kept, V293_priority_kept. simpl.
               split; [unfold V293_storage_cell; simpl; auto | ].
               split; [tauto | ]. change (GoodFrm (V293_storage guardrest)).
               apply V293_storage_frame_good.
             - unfold bindings, guardbindings, V293_counter_bindings. simpl. tauto. }
           ++ intros s Hs. apply V293_retained_storage_prefix_lend_value with (hv := hv); try assumption.
              unfold V293_ready_conditional_entry in Hs.
              eapply astar_mono in Hs; [ | intros st H; exact H | apply astar_mono].
              2: { apply astar_mono; [intros st [_ H]; exact H | intros st H; exact H]. }
              2: { intros st H; exact H. }
              unfold V293_storage_open in Hs. exact Hs.
           ++ intros s H; exact H.
        -- unfold opened. change (InfRules Spec V293_scheduler V293_shared_li readyI r ri
             (V293_ready_conditional_open unmap group rows high table target current counter
               bt bg br bh bp bo bcur bcounter tp lo hi nc entries guardrest tid tasks events now
               aop stack critical guardbindings)
             (V293_OSSched_change high current counter (sprim (switch target)))
             (V293_ready_conditional_resumed unmap group rows high table target current counter
               bt bg br bh bp bo bcur bcounter tp guardrest tid aop stack critical guardbindings) tid).
           assert (HC : InfRules Spec V293_scheduler V293_shared_li readyI r ri
             (V293_ready_conditional_open unmap group rows high table target current counter
               bt bg br bh bp bo bcur bcounter tp lo hi nc entries guardrest tid tasks events now
               aop stack critical guardbindings)
             (V293_OSSched_change high current counter (sprim (switch target)))
             (V293_ready_conditional_branch_post unmap group rows high table target current counter
               bt bg br bh bp bo bcur bcounter tp lo hi nc entries guardrest tid tasks events now
               aop stack critical guardbindings) tid).
           { apply V293_ready_conditional_change; try assumption.
             - unfold guardbindings. simpl. tauto.
             - intros s Hs. unfold guardbindings in Hs.
               assert (HP : s |= px ** Atrue) by (sep auto).
               eapply astar_mono in HP; [ | exact Hlocal | intros st H; exact H]. clear Hs. sep auto. }
           unfold V293_ready_conditional_branch_post in HC. rewrite Hdifferent in HC. exact HC.
Qed.
End ReadyVacatedCache.
