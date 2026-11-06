(* Both configured time bodies share the existing clock invariant and API
   contracts. This two-function unit is not the full kernel program. *)
Require Import CertiOS.certiucos.v293.code.V293TimeSource.
Require Import CertiOS.certiucos.v293.proofs.V293TimeGetAPI.
Require Import CertiOS.certiucos.v293.proofs.V293TimeSetAPI.
Require Import CertiOS.certiucos.v293.proofs.V293TimeAccess.
Require Import CertiOS.certiucos.v293.proofs.V293TimeShared.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.certiucos.v293.proofs.V293TimeNamesGood.
Require Import CertiOS.framework.include_frm.

Theorem V293_source_time_get_exact : forall now ticks saved,
  V293_source_OSTimeGet_function now ticks saved =
    V293_TimeGet_function now ticks saved.
Proof. reflexivity. Qed.

Theorem V293_source_time_set_exact : forall now ticks saved,
  V293_source_OSTimeSet_function now ticks saved =
    V293_TimeSet_function now ticks saved.
Proof. reflexivity. Qed.

Definition V293_source_time_program (fget fset : fid) now ticks saved : progunit :=
  fun f => if Z.eq_dec f fget then Some (V293_source_OSTimeGet_function now ticks saved)
    else if Z.eq_dec f fset then Some (V293_source_OSTimeSet_function now ticks saved)
    else None.
Definition V293_source_time_spec (fget fset : fid) : osapispec :=
  fun f => if Z.eq_dec f fget then Some V293_TimeGet_api
    else if Z.eq_dec f fset then Some V293_TimeSet_api else None.

Theorem V293_source_time_entries : forall fget fset now ticks saved,
  fget <> fset ->
  V293_source_time_program fget fset now ticks saved fget =
    Some (V293_source_OSTimeGet_function now ticks saved) /\
  V293_source_time_program fget fset now ticks saved fset =
    Some (V293_source_OSTimeSet_function now ticks saved) /\
  V293_source_time_spec fget fset fget = Some V293_TimeGet_api /\
  V293_source_time_spec fget fset fset = Some V293_TimeSet_api.
Proof.
  intros. unfold V293_source_time_program,V293_source_time_spec.
  repeat destruct Z.eq_dec;try congruence;repeat split;reflexivity.
Qed.

Theorem V293_source_time_domains : forall fget fset now ticks saved,
  EqDomAPI (V293_source_time_program fget fset now ticks saved)
    (V293_source_time_spec fget fset).
Proof.
  intros. split.
  - intro f. unfold V293_source_time_program,V293_source_time_spec.
    repeat destruct Z.eq_dec;split;intros [x H];try discriminate;eexists;reflexivity.
  - intros f fd fs Code Spec.
    unfold V293_source_time_program in Code.
    unfold V293_source_time_spec in Spec.
    repeat destruct Z.eq_dec;try discriminate;
      inversion Code;inversion Spec;subst;split;simpl;auto.
Qed.

(* The actual generated bodies, not a separate hand-written copy, discharge
   the two API obligations in the same program map and specification. *)
Theorem V293_source_time_api_rule : forall fget fset now ticks saved bn Spec sd li lg,
  fget <> fset -> ticks <> saved -> now <> ticks -> now <> saved ->
  GoodLInvAsrt li -> NoAbs li ->
  (forall t args, p_local li t args ==>
    Agvarenv now Tint32 (bn,0%Z) ** p_local li t args) ->
  APIRule (V293_source_time_program fget fset now ticks saved)
    (V293_source_time_spec fget fset) Spec sd li (V293_time_shared_inv bn) lg.
Proof.
  intros fget fset now ticks saved bn Spec sd li lg GS TS NT NS Good NA Globals.
  apply api_rule;[apply V293_source_time_domains | ].
  intros f ab vl pre post ft tid API Pre Post.
  unfold V293_source_time_spec in API.
  destruct (Z.eq_dec f fget) as [Get | NotGet].
  - inversion API;subst ab ft.
    assert (Code : V293_source_time_program fget fset now ticks saved f =
      Some (V293_TimeGet_function now ticks saved)).
    { unfold V293_source_time_program. destruct (Z.eq_dec f fget);
        [rewrite V293_source_time_get_exact;reflexivity | contradiction]. }
    exists Tint32. exists dnil. exists (dcons ticks Tint32 (dcons saved Tint32 dnil)).
    exists (V293_source_OSTimeGet_body now ticks saved). split.
    + exact Code.
    + change (InfRules Spec sd li (V293_time_shared_inv bn) post Afalse pre
        (V293_TimeGet_body now ticks saved) Afalse tid).
      eapply V293_TimeGet_api_contract; eassumption.
  - destruct (Z.eq_dec f fset) as [Setter | NotSetter];try discriminate.
    inversion API;subst ab ft.
    assert (Code : V293_source_time_program fget fset now ticks saved f =
      Some (V293_TimeSet_function now ticks saved)).
    { unfold V293_source_time_program. destruct (Z.eq_dec f fget);[contradiction | ].
      destruct (Z.eq_dec f fset);
        [rewrite V293_source_time_set_exact;reflexivity | contradiction]. }
    exists Tvoid. exists (dcons ticks Tint32 dnil). exists (dcons saved Tint32 dnil).
    exists (V293_source_OSTimeSet_body now ticks saved). split.
    + exact Code.
    + change (InfRules Spec sd li (V293_time_shared_inv bn) post Afalse pre
        (V293_TimeSet_body now ticks saved) Afalse tid).
      eapply V293_TimeSet_api_contract; eassumption.
Qed.

Theorem V293_source_time_coherent : forall fget fset now ticks saved bn Spec lg,
  fget <> fset -> ticks <> saved -> now <> ticks -> now <> saved ->
  GoodI (V293_time_shared_inv bn) V293_scheduler (V293_time_names_li now bn) /\
  APIRule (V293_source_time_program fget fset now ticks saved)
    (V293_source_time_spec fget fset) Spec V293_scheduler
    (V293_time_names_li now bn) (V293_time_shared_inv bn) lg.
Proof.
  intros. split;[apply V293_time_names_good | ].
  apply V293_source_time_api_rule;try assumption.
  - apply V293_time_names_local_good.
  - apply V293_time_names_noabs.
  - apply V293_time_names_global.
Qed.
