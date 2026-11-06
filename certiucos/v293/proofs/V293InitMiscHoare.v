(* The exact existing OS_InitMisc syntax, including its administrative skip.
   The running-task local invariant is an explicit premise. This theorem does
   not assert that the pre-start OSInit state satisfies that premise. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.code.V293OSInitMisc.
Require Import CertiOS.certiucos.v293.proofs.V293InitMisc.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.framework.proof.soundness.
Require CertiOS.framework.proof.simulation.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List.
Import Coq.Lists.List.ListNotations.
Local Open Scope list_scope.

Lemma V293_init_resources_CurLINV : forall slots z R li tid,
  (R ==> CurLINV li tid) ->
  V293_init_resources slots z R ==> CurLINV li tid.
Proof.
  induction slots as [ | d tail IH]; intros z R li tid HR; cbn [V293_init_resources].
  - exact HR.
  - apply V293_star_CurLINV_r. apply IH. exact HR.
Qed.

Lemma V293_init_one_hoare : forall Spec sd li I r ri tid aop d R,
  V293_init_scalar d -> (R ==> CurLINV li tid) ->
  InfRules Spec sd li I r ri
    (<||aop||> ** ((V293_init_binding d ** V293_init_memory d false) ** R))
    (V293_init_zero (init_name d) (init_type d))
    (<||aop||> ** ((V293_init_binding d ** V293_init_memory d true) ** R)) tid.
Proof.
  intros Spec sd li I r ri tid aop d R Scalar HR.
  unfold V293_init_zero. eapply conseq_rule with
    (p:=EX old : val, <||aop||> ** ((V293_init_binding d ** R) **
      Amapsto (init_block d,0%Z) (init_type d) true old))
    (q:=<||aop||> ** ((V293_init_binding d ** R) **
      Amapsto (init_block d,0%Z) (init_type d) true (Vint32 Int.zero))).
  - intros s Hs.
    assert (K : s |= (EX old : val, Amapsto (init_block d,0%Z) (init_type d) true old) **
      (<||aop||> ** V293_init_binding d ** R)).
    { cbn [V293_init_memory] in Hs. clear -Hs. sep auto. }
    apply astar_l_aexists_elim in K. destruct K as [old K].
    exists old. clear -K. sep auto.
  - intros s Hs. cbn [V293_init_memory]. clear -Hs. sep auto.
  - apply ex_intro_rule. intros old.
    eapply assign_rule with (tp2:=init_type d) (l:=(init_block d,Int.zero)).
    + destruct Scalar as [T|T]; rewrite T; apply eq_int; auto.
    + intros s Hs.
      destruct s as [[[[[[ge le] M] ir] aux] O] op].
      assert (Bind : (ge,le,M,ir,aux,O,op) |= V293_init_binding d ** Atrue).
      { clear -Hs. sep auto. }
      destruct (V293_init_binding_eval _ _ _ _ _ _ _ _ _ Bind) as [Ty Addr].
      split.
      * cbn [sat getsmem]. split; assumption.
      * cbn [sat getsmem evalval evaltype].
        destruct Scalar as [T|T]; rewrite T; repeat split; try reflexivity; discriminate.
    + apply V293_star_CurLINV_l. apply V293_star_CurLINV_r. exact HR.
Qed.

Theorem V293_init_sequence_hoare : forall slots Spec sd li I r ri tid aop R,
  Forall V293_init_scalar slots -> (R ==> CurLINV li tid) ->
  InfRules Spec sd li I r ri
    (<||aop||> ** V293_init_resources slots false R)
    (V293_init_program slots)
    (<||aop||> ** V293_init_resources slots true R) tid.
Proof.
  induction slots as [ | d tail IH]; intros Spec sd li I r ri tid aop R Valid HR.
  - apply skip_rule.
  - inversion Valid as [ | d' tail' HD HT]; subst.
    cbn [V293_init_program V293_init_zero_sequence map].
    eapply seq_rule.
    + apply V293_init_one_hoare; [exact HD | ].
      apply V293_init_resources_CurLINV. exact HR.
    + eapply conseq_rule.
      * apply astar_mono; [intros s H; exact H| ]. apply V293_init_frame_in.
      * apply astar_mono; [intros s H; exact H| ]. apply V293_init_frame_out.
      * apply IH; [exact HT| ]. apply V293_star_CurLINV_r. exact HR.
Qed.

Definition V293_InitMisc_post slots aop R (result : option val) :=
  [|result = None|] ** (<||aop||> ** V293_init_resources slots true R).

(* Stable interface: all ten actual stores, final administrative skip, and
   void return. No hook contract, execution trace, or Hoare premise is assumed. *)
Theorem V293_OS_InitMisc_body_hoare : forall Spec sd li I tid aop R
    time interrupt lock tasks running switches idle idle_run idle_max stat_ready
    bt bi bl bk br bc bd bdr bdm bs,
  (R ==> CurLINV li tid) ->
  let slots := V293_InitMisc_slots time interrupt lock tasks running switches idle idle_run idle_max stat_ready
    bt bi bl bk br bc bd bdr bdm bs in
  InfRules Spec sd li I (V293_InitMisc_post slots aop R) Afalse
    (<||aop||> ** V293_init_resources slots false R)
    (sseq (V293_InitMisc_updates time interrupt lock tasks running switches idle idle_run idle_max stat_ready) sret)
    Afalse tid.
Proof.
  intros Spec sd li I tid aop R time interrupt lock tasks running switches idle idle_run idle_max stat_ready
    bt bi bl bk br bc bd bdr bdm bs HR slots.
  eapply seq_rule with (p':=<||aop||> ** V293_init_resources slots true R).
  - change (InfRules Spec sd li I (V293_InitMisc_post slots aop R) Afalse
      (<||aop||> ** V293_init_resources slots false R) (V293_init_program slots)
      (<||aop||> ** V293_init_resources slots true R) tid).
    apply V293_init_sequence_hoare; [ | exact HR].
    unfold slots, V293_InitMisc_slots.
    repeat (apply Forall_cons; [unfold V293_init_scalar; cbn; auto| ]); apply Forall_nil.
  - apply ret_rule. intros s Hs. unfold V293_InitMisc_post.
    apply astar_l_apure_intro; [exact Hs|reflexivity].
Qed.

Theorem V293_OS_InitMisc_body_semantics : forall Spec sd li I tid aop R
    time interrupt lock tasks running switches idle idle_run idle_max stat_ready
    bt bi bl bk br bc bd bdr bdm bs,
  (R ==> CurLINV li tid) ->
  let slots := V293_InitMisc_slots time interrupt lock tasks running switches idle idle_run idle_max stat_ready
    bt bi bl bk br bc bd bdr bdm bs in
  simulation.RuleSem Spec sd li I (V293_InitMisc_post slots aop R) Afalse
    (<||aop||> ** V293_init_resources slots false R)
    (sseq (V293_InitMisc_updates time interrupt lock tasks running switches idle idle_run idle_max stat_ready) sret)
    Afalse tid.
Proof. intros. apply RuleSound. apply V293_OS_InitMisc_body_hoare. exact H. Qed.

Print Assumptions V293_OS_InitMisc_body_hoare.
Print Assumptions V293_OS_InitMisc_body_semantics.
