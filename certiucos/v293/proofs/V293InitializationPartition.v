(* Original initialization partition contract, proved by ordinary induction.
   The initst premise is unchanged; this does not prove execution of OSInit. *)
Require Import CertiOS.framework.proof.step_prop.
Require Import CertiOS.framework.proof.joinmemLib.
Require Import CertiOS.framework.proof.lmachLib.
Require Import CertiOS.framework.proof.mem_join_lemmas.
Require Import CertiOS.framework.proof.invariant_prop_lemmas.

Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.framework.proof.oscorrectness.
Require Import CertiOS.framework.proof.simulation.
Require Import CertiOS.framework.proof.auxdef.
Require Import CertiOS.framework.proof.soundness.
Require Import CertiOS.framework.proof.absinfer_sound.
Require Import CertiOS.framework.proof.memory_prop.
Require Import CertiOS.framework.proof.rulesoundlib.
Require Import CertiOS.tactics.base_tac.
Require Import CertiOS.tactics.sep_auto.
Import DeprecatedTactic.

Lemma V293_init_partmo':
  forall S O I lasrt sd init T tc,
    get O curtid = Some (oscurt tc) ->
    eqdomto T O ->
    init S O ->
    side_condition' I lasrt sd init init_lg ->
    exists Tm To Ml Ms Ol Os,
      join Ml Ms (snd (fst (fst S))) /\
      join Ol Os O /\
      partM Ml T Tm /\ partO Ol T To /\
      (
        exists Mc Oc oc,
          Tm tc = Some Mc /\ To tc = Some Oc /\
          projS S tc = Some oc /\
          satp (substaskst oc Ms) Os (INV I) /\
          satp (substaskst oc Mc) Oc (CurTid tc ** LINV lasrt tc init_lg ** OS [empisr,true,nil,nil]) /\
          get_lenv (get_smem oc) = empenv
      ) /\
      (
        forall t,
          indomSt S t ->
          t <> tc ->
          exists Mr Or or,
            Tm t = Some Mr /\ To t = Some Or /\
            projS S t = Some or /\
            satp (substaskst or Mr) Or ( LINV lasrt t init_lg ** OS [empisr,true,nil,nil]) /\
            get_lenv (get_smem or) = empenv
      ).
Proof.
  intros.
  unfolds in H1; mytac.
  apply H2 in X; clear H2; mytac.

  gen sd init T H.
  gen tc H3.

  induction H2; intros.
  subst S. subst envs. subst lst. simpl snd.
  rename H4 into H0, H5 into H1, H6 into H4, H7 into H.
  
  unfold init_cur in H3.
  pose proof H3 absopx; clear H3.

  apply sat_split in H5; mytac.
  exists (TMSpecMod.put TMSpecMod.emp tc x0) (TOSpecMod.put TOSpecMod.emp tc x2).
  exists x0 x x2 x1.
  splits; auto.
  apply join_comm; auto.
  apply join_comm; auto.

  eapply partm_S.
  rewrite TMSpecMod.put_get_eq; eauto.
  apply join_comm; apply join_emp; auto.
  rewrite TMSpecMod.remove_cancel_put.

  eapply partm_O.
  intros; rewrite tmspecmod_remove_emp_eq_emp.
  unfolds; auto.

  eapply parto_S.
  rewrite TOSpecMod.put_get_eq; eauto.
  apply join_comm; apply join_emp; auto.
  rewrite TOSpecMod.remove_cancel_put.
  eapply parto_O.
  intros; rewrite tospecmod_remove_emp_eq_emp.
  unfolds; auto.

  do 3 eexists.
  splits.
  rewrite TMSpecMod.put_get_eq; eauto.
  rewrite TOSpecMod.put_get_eq; eauto.
  simpl.
  rewrite H2 in H; inverts H.
  rewrite get_sig_some.
  rewrite get_sig_some.
  eauto.

  simpl.
  intro.
  eapply rulesoundlib.INV_irrev_prop; eauto.

  simpl; intro.
  unfold CurTid.

  assert (
      (G, E, x0, isr, auxs, x2, aop)
        |= (EX tp : type, GV OSTCBCur @ Tptr tp |-r-> Vptr t) **
        init_rdy pa t lg).
  gen H7.
  eapply absop_irrel_sat.
  eapply ostcbcur_absop_irrel; eauto.
  
  eapply absop_irrel_init_rdy; eauto.
  rewrite H2 in H; inverts H.
  clear - H8.
  unfold init_rdy in H8.
  unfold LINV.
  sep auto.
  unfold init_rdy in H7.
  sep normal in H7; destruct H7.
  sep remember (8::nil)%list in H7.
  simpl in H7; mytac.
  simpl.
  eapply eqdomenv_nil_enil; eauto.

  intros.
  rewrite H2 in H; inverts H.
  clear - H8 H4 H9 H0.
  unfolds in H8.
  unfold indom in H8.
  destruct H8.
  assert (tc = t0 \/ tc <> t0) by tauto.
  destruct H1.
  tryfalse.
  rewrite get_sig_none in H; tryfalse.
  auto.

  subst S. simpl snd. rename m into m0, H10 into H.
  pose proof IHinitst as Hx; clear IHinitst.
  assert (subdomSO (G, envs', M', isr, lst') O ).
  eapply subdomSO_joinsig;eauto.
  eapply Hx in H10;eauto.
  simpl snd in H10.
  clear Hx.
  rewrite H in H3;inverts H3.
  mytac.

  assert ((exists Mt, x t = Some Mt) \/ x t = None).
  destruct (x t).
  left.
  eauto.
  right; auto.
  destruct H20.

  mytac.

  exists (TMSpecMod.put x t m0) (TOSpecMod.put x0 t empabst).
  exists (merge x1 m0) x2 x3 x4.
  splits;auto.

  eapply join_join_merge1; eauto.
  eapply partm_tl_irrel.

  eapply partm_disjoint_put; eauto.
  clear -H3 H2.
  unfolds;join auto.

  eapply parto_put_emp; eauto.

  exists x5 x6 (substaskst x7 M).
  splits;auto.
  rewrite TMSpecMod.put_noninterfere;auto.
  rewrite TOSpecMod.put_noninterfere;auto.

  clear -H16 H0 H1 H4.
  unfold projS in *.
  unfold projD in *.
  unfolddef.
  remember (get envs' tc) as X.
  destruct X.
  symmetry in HeqX.
  eapply join_get_r in HeqX;eauto.
  rewrite HeqX.
  remember (get lst' tc) as Y.
  destruct Y.
  symmetry in HeqY.
  eapply join_get_r in HeqY;eauto.
  rewrite HeqY.
  inverts H16;simpl;auto. 
  tryfalse.
  tryfalse.
  destruct x7 as [[[[]]]].
  simpl substaskst in *;auto.
  destruct x7 as [[[[]]]].
  simpl substaskst in *;auto.
  destruct x7 as [[[[]]]].
  simpl substaskst in *;auto.

  intros.
  assert (t0 = t \/ t0 <> t) by tauto.
  destruct H23.
  
  subst.
  
  exists m0 empabst (G, E, M, isr, auxs).
  splits; auto.
  rewrite TMSpecMod.put_get_eq; eauto.
  rewrite TOSpecMod.put_get_eq; eauto.
  unfolds.
  clear -H0 H1.
  unfold projD.
  assert (get (sig t E) t = Some E).
  apply map_get_sig.
  eapply join_get_l in H0;eauto.
  rewrite H0.
  assert (get (sig t auxs) t = Some auxs).
  apply map_get_sig.
  eapply join_get_l in H1;eauto.
  rewrite H1.
  auto.
  simpl.
  clear -H11 H3 H5 H2 H20.
  unfold init_rdy in *.
  unfold LINV.
  unfold satp.
  intro.
  pose proof H5 aop.
  sep auto.
  clear - H5.
  pose proof H5 absopx; clear H5.
  sep remember (2::nil)%list in H.
  simpl in H; mytac.
  simpl.
  eapply eqdomenv_nil_enil; auto.

  pose proof H14 t0; clear H14.
  assert (indomSt (G, envs', M', isr, lst') t0).
  clear - H21 H23 H0 H1.
  eapply indomSt_preserve; eauto.
  apply H24 in H14; auto.
  clear H24.
  mytac.
  exists x9 x10 (substaskst x11 M).
  splits; auto.
  rewrite TMSpecMod.put_noninterfere; auto.
  rewrite TOSpecMod.put_noninterfere; auto.

  clear - H25 H0 H1 H23.
  unfold projS in *.
  unfold projD in *.
  destruct (get envs' t0) eqn : eq1; tryfalse.
  destruct (get lst' t0) eqn : eq2; tryfalse.
  erewrite join_get_r; eauto.
  erewrite join_get_r; eauto.
  destruct x11 as [[[[]]]].
  inverts H25.
  simpl; auto.

  destruct x11 as [[[[]]]].
  simpl substaskst in *.
  auto.
  destruct x11 as [[[[]]]].
  simpl; simpl in H27; auto.

  exists (TMSpecMod.put x t m0) (TOSpecMod.put x0 t empenv).
  exists (merge x1 m0) x2 x3 x4.
  splits; auto.
  clear - H3 H2.
  eapply mem_join_join_merge13_join; eauto.
  apply join_comm; auto.
  clear - H20 H11 H2 H3.
  eapply partm_disjoint_put; eauto.
  eapply mem_join_join_disjoint; eauto.
  apply join_comm; eauto.
  eapply parto_put_emp; eauto.

  exists x5 x6 (substaskst x7 M).
  splits; auto.
  rewrite TMSpecMod.put_noninterfere; auto.
  rewrite TOSpecMod.put_noninterfere; auto.
  clear - H16 H0 H1 H4.
  unfold projS in *.
  unfold projD in *.
  destruct x7 as [[[[]]]].
  unfold get in H16; simpl in H16.
  destruct (CltEnvMod.get envs' tc) eqn : eq1; tryfalse.
  destruct (TaskLStMod.get lst' tc) eqn : eq2; tryfalse.
  inverts H16.
  erewrite join_get_r; eauto.
  erewrite join_get_r; eauto.
  simpl; auto.
  
  destruct x7 as [[[[]]]]; simpl substaskst in *; auto.
  destruct x7 as [[[[]]]]; simpl substaskst in *; auto.
  destruct x7 as [[[[]]]]; simpl; auto.

  intros.
  assert (t0 = t \/ t0 <> t) by tauto.
  destruct H23.
  
  subst.
  
  exists m0 empabst (G, E, M, isr, auxs).
  splits; auto.
  rewrite TMSpecMod.put_get_eq; eauto.
  rewrite TOSpecMod.put_get_eq; eauto.
  unfolds.
  clear -H0 H1.
  unfold projD.
  assert (get (sig t E) t = Some E).
  apply map_get_sig.
  eapply join_get_l in H0;eauto.
  rewrite H0.
  assert (get (sig t auxs) t = Some auxs).
  apply map_get_sig.
  eapply join_get_l in H1;eauto.
  rewrite H1.
  auto.
  simpl.
  clear -H11 H3 H5 H2 H20.
  unfold init_rdy in *.
  unfold LINV.
  unfold satp.
  intro.
  pose proof H5 aop.
  sep auto.
  clear - H5.
  pose proof H5 absopx; clear H5.
  sep remember (2::nil)%list in H.
  simpl in H; mytac.
  simpl.
  eapply eqdomenv_nil_enil; auto.

  pose proof H14 t0; clear H14.
  assert (indomSt (G, envs', M', isr, lst') t0).
  clear - H21 H23 H0 H1.
  eapply indomSt_preserve; eauto.
  apply H24 in H14; auto.
  clear H24.
  mytac.
  exists x8 x9 (substaskst x10 M).
  splits; auto.
  rewrite TMSpecMod.put_noninterfere; auto.
  rewrite TOSpecMod.put_noninterfere; auto.

  clear - H25 H0 H1 H23.
  unfold projS in *.
  unfold projD in *.
  destruct (get envs' t0) eqn : eq1; tryfalse.
  destruct (get lst' t0) eqn : eq2; tryfalse.
  erewrite join_get_r; eauto.
  erewrite join_get_r; eauto.
  destruct x10 as [[[[]]]].
  inverts H25.
  simpl; auto.

  destruct x10 as [[[[]]]].
  simpl substaskst in *.
  auto.
  destruct x10 as [[[[]]]].
  simpl; simpl in H27; auto.
  Unshelve.
  all: auto.
Qed.

Lemma V293_init_partmo :
  forall S O I lasrt sd init T tc,
    get O curtid = Some (oscurt tc) ->
    eqdomto T O ->
    init S O ->
    side_condition I lasrt sd init init_lg ->
    exists Tm To Ml Ms Ol Os,
      join Ml Ms (snd (fst (fst S))) /\
      join Ol Os O /\
      partM Ml T Tm /\ partO Ol T To /\
      (
        exists Mc Oc oc,
          Tm tc = Some Mc /\ To tc = Some Oc /\
          projS S tc = Some oc /\
          satp (substaskst oc Ms) Os (INV I) /\
          satp (substaskst oc Mc) Oc (CurTid tc ** LINV lasrt tc init_lg ** OS [empisr,true,nil,nil]) /\
          get_lenv (get_smem oc) = empenv
      ) /\
      (
        forall t,
          indom T t ->
          t <> tc ->
          exists Mr Or or,
            Tm t = Some Mr /\ To t = Some Or /\
            projS S t = Some or /\
            satp (substaskst or Mr) Or ( LINV lasrt t init_lg ** OS [empisr,true,nil,nil]) /\
            get_lenv (get_smem or) = empenv
      ).
Proof.
  intros.
  assert (side_condition' I lasrt sd init init_lg).
  unfold side_condition in H1; mytac.
  unfold side_condition'.
  split; auto.
  intros.
  eapply H2 in X0; mytac.
  auto.
  clear - H4.
  apply eqdomSO_impl_subdomSO; auto.

  lets Hx: V293_init_partmo' H H0 X H2.
  mytac.
  do 6 eexists;splits;eauto.
  do 3 eexists;splits;eauto.
  intros.
  assert (indomSt S t).
  unfold side_condition in H1.
  mytac.
  eapply H16 in X; mytac.
  clear - H18 H14 H0.
  destruct S as [[[[]]]].
  unfolds.
  unfolds in H18.
  unfolds in H0; mytac.
  rewrite H in H18; mytac.
  eapply H0 in H14; mytac.
  unfolds in H1.
  eapply H1.
  unfolds; eauto.

  eapply H8 in H16.
  eauto.
  auto.
Qed.

