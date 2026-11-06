(* Full inference-rule soundness using the repaired generic call proofs.
   No inference constructor or program behavior is removed. *)
Require Import CertiOS.certiucos.v293.proofs.V293CallSoundness.
Require Import CertiOS.framework.proof.sound_include.
Require Import CertiOS.framework.proof.auxdef.
Require Import CertiOS.framework.proof.oscorrectness.
Require Import CertiOS.framework.proof.rulesound.
Require Import CertiOS.framework.proof.soundness.
Require Import CertiOS.framework.proof.lemmasfortoptheo.
Local Remove Hints RuleSound : core.

Theorem V293_rule_sound:
  forall (Spec:funspec) (sd : ossched) (I:Inv) (r:retasrt) (ri:asrt)
         (pre:asrt) (s:stmts) (post:asrt) lasrt tid,
    InfRules Spec sd lasrt I r ri pre s post tid ->
    RuleSem Spec sd lasrt I r ri pre s post tid.
Proof.
  introv Hspe.
  inductions Hspe.
  eapply pfalse_rule_sound;eauto.
  eapply pure_split_rule_sound;eauto.
  eapply genv_introret_rule_sound ;eauto.
  eapply genv_introexint_rule_sound ;eauto.
  eapply ret_rule_sound; eauto.
  eapply exitint_rule_sound; eauto.
  eapply rete_rule_sound;eauto.
  eapply V293_call_rule_sound;eauto.
  eapply V293_calle_rule_sound; eauto.
  eapply V293_calle_rule_lvar_sound; eauto.
  eapply conseq_rule_sound;eauto.
  eapply conseq_rule_r_sound;eauto.
  eapply abscsq_rule_sound;eauto.
  eapply seq_rule_sound;eauto.
  eapply if_rule_sound;eauto.
  eapply ift_rule_sound; eauto.
  eapply while_rule_sound; eauto.
  eapply frame_rule_sound;eauto.
  eapply frame_rule_all_sound;eauto.
  eapply retspec_intro_rule_sound;eauto.
  eapply assign_rule_sound;eauto.
  eapply encrit1_rule_sound ;eauto.
  eapply encrit2_rule_sound;eauto.
  eapply excrit1_rule_sound ;eauto.
  eapply excrit2_rule_sound;eauto.
  eapply cli1_rule_sound;eauto.
  eapply cli2_rule_sound;eauto.
  eapply sti1_rule_sound;eauto.
  eapply sti2_rule_sound;eauto.
  eapply switch_rule_sound;eauto.
  eapply switch_dead_rule_sound; eauto.
  eapply checkis_rule_sound;eauto.
  eapply eoi_ieon_rule_sound;eauto.
  eapply eoi_ieoff_rule_sound;eauto.
  eapply ex_intro_rule_sound;eauto.
  eapply disj_rule_sound;eauto.
  eapply task_crt_rule_sound; eauto.
  eapply task_delself_rule_sound; eauto.
  eapply task_delother_rule_sound;eauto.
  eapply skip_rule_sound.
Qed.

Local Hint Resolve V293_rule_sound : core.

Lemma V293_WFFunEnv_imply_WFFuncsSim :
  forall P FSpec sd I lasrt,
    WFFunEnv P FSpec sd lasrt I ->
    WFFuncsSim P FSpec sd lasrt I .
Proof.
  introv Hwfenv.
  unfolds in Hwfenv.
  destruct Hwfenv as [Heqd Hwfenv].
  unfolds.
  split; auto.
  introv Hf.
  lets Hre :  Hwfenv Hf.
  destruct Hre as (d1&d2&s & Hpf & Htm & Hgood & Hforal).
  do 3 eexists; splits; eauto.
Qed.

Lemma V293_ApiMethSim:
  forall (OS1:oscode) (A:osspec) Spec I lasrt,
    GoodI I (snd A) lasrt->
    (
      WFFuncsSim (snd (fst OS1)) Spec (snd A) lasrt I
    ) ->
    (
      forall (f:fid) ab vl p r ft G tid,
        (fst (fst A)) f = Some (ab,ft) ->
        Some p = BuildPreA (fst (fst OS1)) f (ab,ft) vl G lasrt tid init_lg->
        Some r = BuildRetA (fst (fst OS1)) f (ab,ft) vl G lasrt tid init_lg->
        (
          exists t d1 d2 s,
            (fst (fst OS1)) f = Some (t, d1, d2, s)/\ GoodStmt' s /\
            InfRules Spec (snd A) lasrt I r Afalse p s Afalse tid
        )
    )
    ->

    (
      forall (f:fid) ab vl p r ft G tid ,
        (fst (fst A)) f = Some (ab,ft) ->
        Some p = BuildPreA (fst (fst OS1)) f (ab,ft) vl G lasrt tid init_lg ->
        Some r = BuildRetA (fst (fst OS1)) f (ab,ft) vl G lasrt tid init_lg->
        (
          exists t d1 d2 s,
            (fst (fst OS1)) f = Some (t, d1, d2, s)/\ GoodStmt' s /\
            MethSimAsrt (snd (fst OS1)) (snd A) lasrt I r Afalse p s Afalse tid
        )
    ).
Proof.
  introv goodi.
  intros.
  eapply H0 in H1;eauto.
  destruct H1 as (t&d1&d2&s&Ha1&Ha2&Ha3).
  exists t d1 d2 s;splits;auto.
  unfold MethSimAsrt.
  eapply MethSim_to_Methsim';eauto.
Qed.
