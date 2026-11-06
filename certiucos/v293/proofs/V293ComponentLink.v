(* A shared two-API/one-internal component, NOT the complete kernel.
   No dummy initialization, empty interrupt table, or new execution rule. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.toptheorem.
Require Import CertiOS.framework.proof.auxdef.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.certiucos.v293.code.V293OSVersion.
Require Import CertiOS.certiucos.v293.code.V293OSSchedNew.
Require Import CertiOS.certiucos.v293.proofs.V293OSVersionAPI.
Require Import CertiOS.certiucos.v293.proofs.V293TimeSetAPI.
Require Import CertiOS.certiucos.v293.proofs.V293TimeAccess.
Require Import CertiOS.certiucos.v293.proofs.V293TimeShared.
Require Import CertiOS.certiucos.v293.proofs.V293TimeNamesGood.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewInternal.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.

Definition V293_component_api_unit version settime now ticks saved : progunit :=
  pumerge (V293_OSVersion_api_unit version)
    (V293_TimeSet_api_unit settime now ticks saved).

Definition V293_component_api_spec version settime : osapispec :=
  fun f => if Z.eq_dec f version then Some V293_OSVersion_api
    else if Z.eq_dec f settime then Some V293_TimeSet_api else None.

Lemma V293_component_api_domains : forall version settime now ticks saved,
  EqDomAPI (V293_component_api_unit version settime now ticks saved)
    (V293_component_api_spec version settime).
Proof.
  intros version settime now ticks saved. split.
  - intros f. unfold V293_component_api_unit, V293_component_api_spec,
      pumerge, V293_OSVersion_api_unit, V293_TimeSet_api_unit.
    destruct (Z.eq_dec f version), (Z.eq_dec f settime);
      split; intros [x H]; try discriminate; eexists; reflexivity.
  - intros f fd fs Code Spec.
    unfold V293_component_api_unit, pumerge, V293_OSVersion_api_unit,
      V293_TimeSet_api_unit in Code.
    unfold V293_component_api_spec in Spec.
    destruct (Z.eq_dec f version), (Z.eq_dec f settime); try discriminate;
      inversion Code; inversion Spec; subst; split; simpl; auto.
Qed.

(* Both bodies are verified under the SAME complete API map and internal
   specification; builder equations are not borrowed from singleton maps. *)
Theorem V293_component_WFAPI : forall version settime now ticks saved bn
    Spec sd li lg,
  ticks <> saved -> now <> ticks -> now <> saved ->
  GoodLInvAsrt li -> NoAbs li ->
  (forall t args, p_local li t args ==>
    Agvarenv now Tint32 (bn,0%Z) ** p_local li t args) ->
  WFAPI (V293_component_api_unit version settime now ticks saved)
    (V293_component_api_spec version settime) li Spec sd
    (V293_time_shared_inv bn) lg.
Proof.
  intros version settime now ticks saved bn Spec sd li lg TS NT NS Good NA Names.
  split; [apply V293_component_api_domains | ].
  intros f ab vl pre post ft tid API Pre Post.
  unfold V293_component_api_spec in API.
  destruct (Z.eq_dec f version) as [Version | NotVersion].
  - inversion API; subst ab ft.
    assert (Code : V293_component_api_unit version settime now ticks saved f =
      Some V293_OSVersion_function).
    { unfold V293_component_api_unit, pumerge, V293_OSVersion_api_unit.
      destruct (Z.eq_dec f version); [reflexivity | contradiction]. }
    exists Tint16. exists dnil. exists dnil. exists V293_OSVersion_body.
    split; [exact Code | ].
    eapply V293_OSVersion_api_contract; eassumption.
  - destruct (Z.eq_dec f settime) as [SetTime | Missing]; [ | discriminate].
    inversion API; subst ab ft.
    assert (Code : V293_component_api_unit version settime now ticks saved f =
      Some (V293_TimeSet_function now ticks saved)).
    { unfold V293_component_api_unit, pumerge, V293_OSVersion_api_unit,
        V293_TimeSet_api_unit.
      destruct (Z.eq_dec f version), (Z.eq_dec f settime);
        try contradiction; reflexivity. }
    exists Tvoid. exists (dcons ticks Tint32 dnil). exists (dcons saved Tint32 dnil).
    exists (V293_TimeSet_body now ticks saved). split; [exact Code | ].
    eapply V293_TimeSet_api_contract; eassumption.
Qed.

(* WFFunEnv also checks declaration uniqueness, so projecting the original
   top-rule WFIFun loses no body proof obligation. This is only an adapter. *)
Local Lemma V293_WFFunEnv_top : forall P Spec sd li inv,
  WFFunEnv P Spec sd li inv -> WFIFun P Spec sd inv li.
Proof.
  intros P Spec sd li inv [Dom Bodies]. split; [exact Dom | ].
  intros f pre post t tl Lookup.
  destruct (Bodies f pre post t tl Lookup) as
    (d1 & d2 & body & Code & Types & Declarations & Checked).
  exists d1. exists d2. exists body. auto.
Qed.

Theorem V293_component_disjoint : forall version settime sched now ticks saved
    unmap group rows high y,
  sched <> version -> sched <> settime ->
  no_fun_same (V293_component_api_unit version settime now ticks saved)
    (V293_OSSchedNew_internal_unit sched unmap group rows high y).
Proof.
  intros version settime sched now ticks saved unmap group rows high y SV ST.
  unfold no_fun_same, V293_component_api_unit, pumerge,
    V293_OSVersion_api_unit, V293_TimeSet_api_unit, V293_OSSchedNew_internal_unit.
  split; intros f Bound;
    destruct (Z.eq_dec f version), (Z.eq_dec f settime), (Z.eq_dec f sched);
    congruence.
Qed.

Theorem V293_component_syntax : forall version settime sched now ticks saved
    unmap group rows high y,
  ticks <> saved ->
  good_os_pu (V293_component_api_unit version settime now ticks saved) /\
  good_os_pu (V293_OSSchedNew_internal_unit sched unmap group rows high y).
Proof.
  intros version settime sched now ticks saved unmap group rows high y TS.
  assert (Distinct : Zeq_bool ticks saved = false).
  { destruct (Zeq_bool ticks saved) eqn:E; [apply Zeq_bool_eq in E; contradiction | reflexivity]. }
  split; intros f t d1 d2 s Code.
  - unfold V293_component_api_unit, pumerge, V293_OSVersion_api_unit,
      V293_TimeSet_api_unit in Code.
    destruct (Z.eq_dec f version), (Z.eq_dec f settime); try discriminate;
      inversion Code; subst; cbn [revlcons good_decllist in_decllist];
      try rewrite Distinct; repeat split.
  - unfold V293_OSSchedNew_internal_unit in Code.
    destruct (Z.eq_dec f sched); [ | discriminate].
    inversion Code; subst. split; [reflexivity | repeat split].
Qed.

(* This proves actual merged lookups, not merely distinct identifier names. *)
Theorem V293_component_linked_entries : forall version settime sched now ticks saved
    unmap group rows high y,
  version <> settime -> sched <> version -> sched <> settime ->
  let P := pumerge (V293_component_api_unit version settime now ticks saved)
    (V293_OSSchedNew_internal_unit sched unmap group rows high y) in
  P version = Some V293_OSVersion_function /\
  P settime = Some (V293_TimeSet_function now ticks saved) /\
  P sched = Some (V293_OSSchedNew_function unmap group rows high y).
Proof.
  intros version settime sched now ticks saved unmap group rows high y VT SV ST P.
  unfold P, V293_component_api_unit, pumerge, V293_OSVersion_api_unit,
    V293_TimeSet_api_unit, V293_OSSchedNew_internal_unit.
  repeat destruct Z.eq_dec; try congruence; repeat split; reflexivity.
Qed.

(* Prospective single-factor ablation: move only the internal fid onto the
   version API fid. The original left-biased pumerge really selects the wrong
   body. No downstream execution or scheduling success is inferred. *)
Theorem V293_component_collision_shadows_internal : forall version settime now ticks saved
    unmap group rows high y,
  let P := pumerge (V293_component_api_unit version settime now ticks saved)
    (V293_OSSchedNew_internal_unit version unmap group rows high y) in
  P version = Some V293_OSVersion_function /\
  P version <> Some (V293_OSSchedNew_function unmap group rows high y).
Proof.
  intros version settime now ticks saved unmap group rows high y P.
  unfold P, V293_component_api_unit, pumerge, V293_OSVersion_api_unit.
  destruct (Z.eq_dec version version); [ | contradiction].
  split; [reflexivity | discriminate].
Qed.

(* Stable component interface. All three bodies use exactly the same Spec,
   scheduler, IRQ invariant and local invariant. No WFIFun/body premise is
   assumed. This is NOT a side_condition or complete production WFIFun. *)
Theorem V293_components_checked : forall version settime sched now ticks saved bn
    unmap group rows high y bt bg br bh lg,
  version <> settime -> sched <> version -> sched <> settime ->
  ticks <> saved -> now <> ticks -> now <> saved ->
  unmap <> y -> group <> y -> rows <> y -> high <> y ->
  let li := V293_time_names_li now bn in
  let Spec := V293_OSSchedNew_internal_spec sched unmap group rows high bt bg br bh
    li (V293_time_names_local_good now bn) in
  GoodI (V293_time_shared_inv bn) V293_scheduler li /\
  WFAPI (V293_component_api_unit version settime now ticks saved)
    (V293_component_api_spec version settime) li Spec V293_scheduler
    (V293_time_shared_inv bn) lg /\
  WFIFun (V293_OSSchedNew_internal_unit sched unmap group rows high y)
    Spec V293_scheduler (V293_time_shared_inv bn) li /\
  no_fun_same (V293_component_api_unit version settime now ticks saved)
    (V293_OSSchedNew_internal_unit sched unmap group rows high y).
Proof.
  intros version settime sched now ticks saved bn unmap group rows high y bt bg br bh lg
    VT SV ST TS NT NS UY GY RY HY li Spec.
  split; [apply V293_time_names_good | ].
  split.
  - apply V293_component_WFAPI; try assumption.
    + apply V293_time_names_local_good.
    + apply V293_time_names_noabs.
    + apply V293_time_names_global.
  - split.
    + apply V293_WFFunEnv_top. apply V293_OSSchedNew_WFFunEnv; assumption.
    + apply V293_component_disjoint; assumption.
Qed.
