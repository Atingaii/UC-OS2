Require Import CertiOS.certiucos.v293.code.V293OSVersion.
Require Import CertiOS.certiucos.v293.spec.V293OSVersionSpec.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.

Lemma V293_OSVersion_eval : forall m,
  evalval V293_OSVersion_expr m = Some V293_OSVersion_result /\
  evaltype V293_OSVersion_expr m = Some Tint16.
Proof.
  intros [[ge le] M].
  unfold V293_OSVersion_expr, V293_OSVersion_result.
  split; reflexivity.
Qed.

(* Stable interface, independent of the future kernel invariant and scheduler.
   The precondition is any supplied frame, not an inconsistent assertion. *)
Theorem V293_OSVersion_local_hoare : forall Spec sd li I tid frame,
  InfRules Spec sd li I (V293_OSVersion_post frame) Afalse
    frame V293_OSVersion_body Afalse tid.
Proof.
  intros. unfold V293_OSVersion_body.
  eapply rete_rule with (v := V293_OSVersion_result) (t := Tint16).
  intros s Hframe. split.
  - unfold V293_OSVersion_post.
    apply astar_l_apure_intro; [exact Hframe | reflexivity].
  - destruct (V293_OSVersion_eval (getsmem s)) as [Hv Ht].
    simpl. split; [exact Hv | ]. split; [exact Ht | discriminate].
Qed.

Theorem V293_OSVersion_post_exact : forall s frame result,
  s |= V293_OSVersion_post frame result ->
  result = Some V293_OSVersion_result /\ s |= frame.
Proof. intros. apply astar_l_apure_elim. exact H. Qed.

(* A concrete execution returns and restores the caller's environment without
   changing memory. The callee has no arguments and no local variables. *)
Theorem V293_OSVersion_execution : forall p ge caller M f ks,
  cstepstar p
    (curs V293_OSVersion_body,
      (kenil, kcall f V293_OSVersion_body caller ks)) (ge, emp, M)
    (curs (sskip (Some V293_OSVersion_result)), (kenil, ks)) (ge, caller, M).
Proof.
  intros. unfold V293_OSVersion_body, V293_OSVersion_expr.
  eapply c_stepstarn. { eapply stmt_step; [reflexivity | ]; constructor. }
  eapply c_stepstarn. { eapply expr_step; [reflexivity | ]. eapply ecastint_step; reflexivity. }
  eapply c_stepstarn. { eapply expr_step; [reflexivity | ]. apply ec32_step. }
  eapply c_stepstarn. { eapply expr_step; [reflexivity | ]. apply evcastint_step. reflexivity. }
  eapply c_stepstarn. { eapply stmt_step; [reflexivity | ]. eapply (sretv_step p f _ V293_OSVersion_body); try reflexivity; discriminate. }
  eapply c_stepstarn. { eapply stmt_step; [reflexivity | ]. eapply sfreeend_step; reflexivity. }
  apply c_stepstar0.
Qed.
