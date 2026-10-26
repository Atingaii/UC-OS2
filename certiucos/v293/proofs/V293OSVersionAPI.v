Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.code.V293OSVersion.
Require Import CertiOS.certiucos.v293.spec.V293OSVersionSpec.
Require Import CertiOS.certiucos.v293.proofs.V293OSVersionProof.

(* A one-function API unit, not the complete kernel program. The linker may
   choose any identifier; this theorem imposes no global identifier allocation. *)
Definition V293_OSVersion_api_unit (version_id : fid) : progunit :=
  fun f => if Z.eq_dec f version_id then Some V293_OSVersion_function else None.

Definition V293_OSVersion_api : osapi :=
  (fun _ => spec_done (Some V293_OSVersion_result), (Tint16, nil)).

Definition V293_OSVersion_api_spec (version_id : fid) : osapispec :=
  fun f => if Z.eq_dec f version_id then Some V293_OSVersion_api else None.

Lemma V293_OSVersion_api_domains : forall version_id,
  EqDomAPI (V293_OSVersion_api_unit version_id)
    (V293_OSVersion_api_spec version_id).
Proof.
  intros version_id. split.
  - intros f. unfold V293_OSVersion_api_unit, V293_OSVersion_api_spec.
    destruct (Z.eq_dec f version_id); split; intros [x H];
      try discriminate; eexists; reflexivity.
  - intros f fdef fspec Hcode Hspec.
    unfold V293_OSVersion_api_unit in Hcode.
    unfold V293_OSVersion_api_spec in Hspec.
    destruct (Z.eq_dec f version_id); try discriminate.
    inversion Hcode; inversion Hspec; subst. split; simpl; auto.
Qed.

(* Stable linking interface: accepts any surrounding API map with this exact
   function at f. No proof obligation about other functions is assumed away. *)
Theorem V293_OSVersion_api_contract : forall P f Spec sd li I lg tid vl pre post,
  P f = Some V293_OSVersion_function ->
  Some pre = BuildPreA' P f V293_OSVersion_api vl li tid lg ->
  Some post = BuildRetA' P f V293_OSVersion_api vl li tid lg ->
  InfRules Spec sd li I post Afalse pre V293_OSVersion_body Afalse tid.
Proof.
  intros P f Spec sd li I lg tid vl pre post Hcode Hpre Hpost.
  pose proof (V293_OSVersion_local_hoare Spec sd li I tid pre) as Hlocal.
  unfold BuildPreA' in Hpre. rewrite Hcode in Hpre.
  unfold V293_OSVersion_function in Hpre.
  destruct vl as [ | v vl].
  - simpl in Hpre. inversion Hpre; subst pre.
    unfold BuildRetA' in Hpost. rewrite Hcode in Hpost.
    simpl in Hpost. inversion Hpost; subst post.
    eapply r_conseq_rule.
    3: exact Hlocal.
    + intros result s H. apply V293_OSVersion_post_exact in H.
      destruct H as [Hresult Hframe]. subst result. exact Hframe.
    + intros s Hfalse. exact Hfalse.

  - simpl in Hpre.
    destruct (rev vl ++ v :: nil); discriminate.
Qed.

Theorem V293_OSVersion_api_rule : forall version_id Spec sd li I lg,
  APIRule (V293_OSVersion_api_unit version_id)
    (V293_OSVersion_api_spec version_id) Spec sd li I lg.
Proof.
  intros. apply api_rule.
  - apply V293_OSVersion_api_domains.
  - intros f ab vl pre post ft tid Hapi Hpre Hpost.
    unfold V293_OSVersion_api_spec in Hapi.
    destruct (Z.eq_dec f version_id); try discriminate.
    inversion Hapi; subst ab ft.
    exists Tint16. exists dnil. exists dnil. exists V293_OSVersion_body. split.
    + unfold V293_OSVersion_api_unit. destruct (Z.eq_dec f version_id);
        [reflexivity | contradiction].
    + eapply V293_OSVersion_api_contract; [ | exact Hpre | exact Hpost].
      unfold V293_OSVersion_api_unit. destruct (Z.eq_dec f version_id);
        [reflexivity | contradiction].
Qed.

Theorem V293_OSVersion_api_builders : forall version_id li tid lg,
  exists pre post,
    Some pre = BuildPreA' (V293_OSVersion_api_unit version_id) version_id
      V293_OSVersion_api nil li tid lg /\
    Some post = BuildRetA' (V293_OSVersion_api_unit version_id) version_id
      V293_OSVersion_api nil li tid lg.
Proof.
  intros. unfold BuildPreA', BuildRetA', V293_OSVersion_api_unit.
  destruct (Z.eq_dec version_id version_id); [ | contradiction].
  simpl. eexists. eexists. split; reflexivity.
Qed.
