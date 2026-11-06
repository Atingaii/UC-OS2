(* Extend the checked component with the source-identical clock getter.
   This is not the complete kernel, its initialization, or its ISR table. *)
Require Import CertiOS.certiucos.v293.proofs.V293ComponentLink.
Require Import CertiOS.certiucos.v293.proofs.V293TimeGetAPI.
Require Import CertiOS.certiucos.v293.proofs.V293TimeAccess.
Require Import CertiOS.certiucos.v293.proofs.V293TimeNamesGood.
Require Import CertiOS.certiucos.v293.proofs.V293TimeShared.
Require Import CertiOS.certiucos.v293.proofs.V293TimeSetAPI.
Require Import CertiOS.certiucos.v293.proofs.V293OSVersionAPI.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewInternal.
Require Import CertiOS.certiucos.v293.code.V293OSVersion.
Require Import CertiOS.certiucos.v293.code.V293OSSchedNew.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.toptheorem.
Require Import CertiOS.framework.proof.auxdef.

Definition V293_clock_api_unit version settime gettime now ticks saved : progunit :=
  pumerge (V293_component_api_unit version settime now ticks saved)
    (V293_TimeGet_api_unit gettime now ticks saved).
Definition V293_clock_api_spec version settime gettime : osapispec :=
  fun f => if Z.eq_dec f version then Some V293_OSVersion_api
    else if Z.eq_dec f settime then Some V293_TimeSet_api
    else if Z.eq_dec f gettime then Some V293_TimeGet_api else None.

Lemma V293_clock_api_domains : forall version settime gettime now ticks saved,
  EqDomAPI (V293_clock_api_unit version settime gettime now ticks saved)
    (V293_clock_api_spec version settime gettime).
Proof.
  intros version settime gettime now ticks saved. split.
  - intros f. unfold V293_clock_api_unit, V293_component_api_unit,
      V293_clock_api_spec, pumerge, V293_OSVersion_api_unit,
      V293_TimeSet_api_unit, V293_TimeGet_api_unit.
    repeat destruct Z.eq_dec;
      split; intros [x H]; try discriminate; eexists; reflexivity.
  - intros f fd fs Code Spec.
    unfold V293_clock_api_unit, V293_component_api_unit, pumerge,
      V293_OSVersion_api_unit, V293_TimeSet_api_unit, V293_TimeGet_api_unit in Code.
    unfold V293_clock_api_spec in Spec.
    repeat destruct Z.eq_dec; try discriminate;
      inversion Code; inversion Spec; subst; split; simpl; auto.
Qed.

(* Each real builder sees the entire SAME three-API map. *)
Theorem V293_clock_WFAPI : forall version settime gettime now ticks saved bn
    Spec sd li lg,
  ticks <> saved -> now <> ticks -> now <> saved ->
  GoodLInvAsrt li -> NoAbs li ->
  (forall t args, p_local li t args ==>
    Agvarenv now Tint32 (bn,0%Z) ** p_local li t args) ->
  WFAPI (V293_clock_api_unit version settime gettime now ticks saved)
    (V293_clock_api_spec version settime gettime) li Spec sd
    (V293_time_shared_inv bn) lg.
Proof.
  intros version settime gettime now ticks saved bn Spec sd li lg TS NT NS Good NA Names.
  split; [apply V293_clock_api_domains | ].
  intros f ab vl pre post ft tid API Pre Post.
  unfold V293_clock_api_spec in API.
  destruct (Z.eq_dec f version) as [Version | NotVersion].
  - inversion API; subst ab ft.
    assert (Code : V293_clock_api_unit version settime gettime now ticks saved f =
      Some V293_OSVersion_function).
    { unfold V293_clock_api_unit, V293_component_api_unit, pumerge, V293_OSVersion_api_unit.
      destruct (Z.eq_dec f version); [reflexivity | contradiction]. }
    exists Tint16. exists dnil. exists dnil. exists V293_OSVersion_body.
    split; [exact Code | ]. eapply V293_OSVersion_api_contract; eassumption.
  - destruct (Z.eq_dec f settime) as [SetTime | NotSet].
    + inversion API; subst ab ft.
      assert (Code : V293_clock_api_unit version settime gettime now ticks saved f =
        Some (V293_TimeSet_function now ticks saved)).
      { unfold V293_clock_api_unit, V293_component_api_unit, pumerge,
          V293_OSVersion_api_unit, V293_TimeSet_api_unit.
        destruct (Z.eq_dec f version), (Z.eq_dec f settime);
          try contradiction; reflexivity. }
      exists Tvoid. exists (dcons ticks Tint32 dnil). exists (dcons saved Tint32 dnil).
      exists (V293_TimeSet_body now ticks saved). split; [exact Code | ].
      eapply V293_TimeSet_api_contract; eassumption.
    + destruct (Z.eq_dec f gettime) as [GetTime | Missing]; [ | discriminate].
      inversion API; subst ab ft.
      assert (Code : V293_clock_api_unit version settime gettime now ticks saved f =
        Some (V293_TimeGet_function now ticks saved)).
      { unfold V293_clock_api_unit, V293_component_api_unit, pumerge,
          V293_OSVersion_api_unit, V293_TimeSet_api_unit, V293_TimeGet_api_unit.
        destruct (Z.eq_dec f version), (Z.eq_dec f settime), (Z.eq_dec f gettime);
          try contradiction; reflexivity. }
      exists Tint32. exists dnil. exists (dcons ticks Tint32 (dcons saved Tint32 dnil)).
      exists (V293_TimeGet_body now ticks saved). split; [exact Code | ].
      eapply V293_TimeGet_api_contract; eassumption.
Qed.

Theorem V293_clock_disjoint : forall version settime gettime sched now ticks saved
    unmap group rows high y,
  sched <> version -> sched <> settime -> sched <> gettime ->
  no_fun_same (V293_clock_api_unit version settime gettime now ticks saved)
    (V293_OSSchedNew_internal_unit sched unmap group rows high y).
Proof.
  intros version settime gettime sched now ticks saved unmap group rows high y SV ST SG.
  unfold no_fun_same, V293_clock_api_unit, V293_component_api_unit, pumerge,
    V293_OSVersion_api_unit, V293_TimeSet_api_unit, V293_TimeGet_api_unit,
    V293_OSSchedNew_internal_unit.
  split; intros f Bound; repeat destruct Z.eq_dec; congruence.
Qed.

Theorem V293_clock_syntax : forall version settime gettime sched now ticks saved
    unmap group rows high y,
  ticks <> saved ->
  good_os_pu (V293_clock_api_unit version settime gettime now ticks saved) /\
  good_os_pu (V293_OSSchedNew_internal_unit sched unmap group rows high y).
Proof.
  intros version settime gettime sched now ticks saved unmap group rows high y TS.
  assert (Distinct : Zeq_bool ticks saved = false).
  { destruct (Zeq_bool ticks saved) eqn:E; [apply Zeq_bool_eq in E; contradiction | reflexivity]. }
  split; intros f t d1 d2 s Code.
  - unfold V293_clock_api_unit, V293_component_api_unit, pumerge, V293_OSVersion_api_unit,
      V293_TimeSet_api_unit, V293_TimeGet_api_unit in Code.
    repeat destruct Z.eq_dec; try discriminate;
      inversion Code; subst; cbn [revlcons good_decllist in_decllist];
      try rewrite Distinct; repeat split.
  - unfold V293_OSSchedNew_internal_unit in Code.
    destruct (Z.eq_dec f sched); [ | discriminate].
    inversion Code; subst. split; [reflexivity | repeat split].
Qed.

Theorem V293_clock_linked_entries : forall version settime gettime sched now ticks saved
    unmap group rows high y,
  version <> settime -> gettime <> version -> gettime <> settime ->
  sched <> version -> sched <> settime -> sched <> gettime ->
  let P := pumerge (V293_clock_api_unit version settime gettime now ticks saved)
    (V293_OSSchedNew_internal_unit sched unmap group rows high y) in
  P version = Some V293_OSVersion_function /\
  P settime = Some (V293_TimeSet_function now ticks saved) /\
  P gettime = Some (V293_TimeGet_function now ticks saved) /\
  P sched = Some (V293_OSSchedNew_function unmap group rows high y).
Proof.
  intros version settime gettime sched now ticks saved unmap group rows high y VT GetVersion GetSet SV ST SG P.
  unfold P, V293_clock_api_unit, V293_component_api_unit, pumerge, V293_OSVersion_api_unit,
    V293_TimeSet_api_unit, V293_TimeGet_api_unit, V293_OSSchedNew_internal_unit.
  repeat destruct Z.eq_dec; try congruence; repeat split; reflexivity.
Qed.

(* Stable interface: three APIs and one internal function under one Spec,
   scheduler, partial shared invariant and name-only LocalInv. No assumed
   body correctness. Full production Inv / side_condition remain open. *)
Theorem V293_clock_components_checked : forall version settime gettime sched now ticks saved bn
    unmap group rows high y bt bg br bh lg,
  version <> settime -> gettime <> version -> gettime <> settime ->
  sched <> version -> sched <> settime -> sched <> gettime ->
  ticks <> saved -> now <> ticks -> now <> saved ->
  unmap <> y -> group <> y -> rows <> y -> high <> y ->
  let li := V293_time_names_li now bn in
  let Spec := V293_OSSchedNew_internal_spec sched unmap group rows high bt bg br bh
    li (V293_time_names_local_good now bn) in
  GoodI (V293_time_shared_inv bn) V293_scheduler li /\
  WFAPI (V293_clock_api_unit version settime gettime now ticks saved)
    (V293_clock_api_spec version settime gettime) li Spec V293_scheduler
    (V293_time_shared_inv bn) lg /\
  WFIFun (V293_OSSchedNew_internal_unit sched unmap group rows high y)
    Spec V293_scheduler (V293_time_shared_inv bn) li /\
  no_fun_same (V293_clock_api_unit version settime gettime now ticks saved)
    (V293_OSSchedNew_internal_unit sched unmap group rows high y).
Proof.
  intros version settime gettime sched now ticks saved bn unmap group rows high y bt bg br bh lg
    VT GetVersion GetSet SV ST SG TS NT NS UY GY RY HY li Spec.
  destruct (V293_components_checked version settime sched now ticks saved bn
    unmap group rows high y bt bg br bh lg VT SV ST TS NT NS UY GY RY HY)
    as [Good [_ [Internal _]]].
  split; [exact Good | ]. split.
  - apply V293_clock_WFAPI; try assumption.
    + apply V293_time_names_local_good.
    + apply V293_time_names_noabs.
    + apply V293_time_names_global.
  - split; [exact Internal | apply V293_clock_disjoint;assumption].
Qed.
