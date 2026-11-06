(* The original global soundness contracts, with assumption-clean dependencies.
   This is conditional framework infrastructure, not a concrete kernel instance. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.auxdef.
Require Import CertiOS.framework.proof.oscorrectness.
Require Import CertiOS.framework.proof.simulation.
Require Import CertiOS.framework.proof.lemmasfortoptheo.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.framework.proof.toptheorem.
Require Import CertiOS.framework.proof.soundness.
Require Import CertiOS.tactics.base_tac.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.certiucos.v293.proofs.V293Soundness.
Require Import CertiOS.certiucos.v293.proofs.V293InitializationPartition.
Require Import CertiOS.certiucos.v293.proofs.V293TraceRefinement.
Import DeprecatedTactic.
Local Remove Hints RuleSound : core.
Local Hint Resolve V293_rule_sound : core.

Lemma V293_IntMethSim: 
  forall (OS1:oscode) (A:osspec) Spec I lasrt, 
    GoodI I (snd A) lasrt->
    (
      WFFuncsSim (snd (fst OS1)) Spec (snd A) lasrt I
    ) ->
    (
      forall (i:hid) ispec isrreg si G tid lg, 
        (snd (fst A)) i = Some ispec ->
        (
          exists (s:stmts) p r,
            (snd OS1) i = Some s /\ 
            p = ipreasrt i isrreg si (ispec ) I G lasrt tid lg /\ 
            r = iretasrt i isrreg si I G lasrt tid lg /\
            InfRules Spec (snd A) lasrt I retfalse r p s Afalse tid
        )
    )
    ->
    
    (
      forall (i:hid) ispec  isrreg si G lg tid, 
        (snd (fst A)) i = Some ispec ->
        (
          exists (s:stmts) p r,
            (snd OS1) i = Some s /\ 
            p = ipreasrt i isrreg si (ispec) I G lasrt tid lg /\ 
            r = iretasrt i isrreg si I G lasrt tid lg /\
            MethSimAsrt (snd (fst OS1)) (snd A) lasrt I retfalse r p s Afalse tid
        )
    ).
Proof.
  introv goodi.
  intros.
  eapply H0 in H1.
  destruct H1 as (s&p&r&Ha1&Ha2&Ha3&Ha4).
  exists s p r.
  splits;eauto.
  unfold MethSimAsrt.
  simpl.
  eapply MethSim_to_Methsim';eauto using V293_rule_sound.
Qed.

Theorem V293_toptheorem':
  forall (osc:oscode) (A:osspec) (init:InitAsrt) lasrt (I:Inv) (Spec:funspec),
    no_fun_same (get_afun osc)  (get_ifun osc)->
    True ->
    True ->

    no_call_api_os (get_afun osc) (get_ifun osc) (get_lint osc) -> 
    (forall f t d1 d2 s, (fst (fst osc)) f = Some (t,d1,d2,s) -> good_decllist (revlcons d1 d2) = true/\GoodStmt' s) ->
    (forall f t d1 d2 s, (snd (fst osc)) f = Some (t,d1,d2,s) -> good_decllist (revlcons d1 d2) = true/\GoodStmt' s) ->
    (forall (i : nat) (isrreg : isr) (si : is) 
            (p r : asrt) (lg : list logicvar) (t : tid) ,
       Some p = BuildintPre i  (snd (fst A)) isrreg si I lasrt t lg ->
       Some r = BuildintRet i  (snd (fst A)) isrreg si I lasrt t lg ->
       exists s,
         (get_lint osc) i = Some s /\
         {|Spec, snd A, lasrt, I, inferules.retfalse, r|}|- t {{p}} s
                                                              {{Afalse}}) ->
    (
      forall (f:fid) ab vl p r ft tid , 
        (fst (fst A)) f = Some (ab,ft) ->
        Some p = BuildPreA' (get_afun osc) f (ab,ft) vl lasrt tid init_lg ->
        Some r = BuildRetA' (get_afun osc) f (ab,ft) vl lasrt tid init_lg->
        (
          exists  t d1 d2 s,
            (get_afun osc) f = Some (t, d1, d2, s)/\ GoodStmt' s /\
            InfRules Spec (snd A) lasrt I r Afalse  p s Afalse tid
        )
    )->
    
    WFFunEnv (get_ifun osc) Spec (snd A) lasrt I-> 
    (
      eqdomOS osc A /\
      side_condition I lasrt (snd A) init init_lg
    ) ->
    OSCorrect osc A init.
Proof. 
  intros osc A init lasrt I Spec Hnofunsame Hxpo Hxpi Hnoos Hgoodpo Hgoodpi Hint Hapi Hifun Hside.
  unfold OSCorrect.
  introv Hitideq.
  intros.
  unfold WellClient in H1.
  destruct H1 as (H1&Hxpc).
  apply V293_progsim_imply_eref.
  unfold oscorrectness.prog_sim.
  subst.
  splits;auto.
  apply tsimtopsim.
  auto.
  destruct Hside as (Heqdomos&Hside).
  assert (eqdomTO T O) as HeqdomTO.
  unfolds in H.
  mytac.
  unfolds in H.
  unfolds.
  mytac.
  eexists;splits;eauto.
  intros.
  eapply H6;eauto.
  
  assert (eqdomto T O) as Heqdomto.
  unfolds in H.
  mytac.
  unfolds in H.
  unfolds.
  mytac.
  eexists;splits;eauto.
  
  lets Hx: V293_init_partmo T Hitideq H0 Hside.
  auto.
  destruct Hx as (Tm & To & Ml & Ms & Ol & Os & Hinitst).
  
  exists pc A (get_afun osc) (get_ifun osc) (get_lint osc) Tm.
  exists To Ol Os Ms Ml I.
  exists lasrt. 
  splits;auto.

  unfolds get_afun, get_ifun, get_lint.
  destruct osc.
  destruct p.
  simpl.
  auto.
  split;auto.
  inversion Hside.
  splits;auto.
  unfolds;auto.
  lets Hx:H4 H0.
  destruct Hx.
  unfolds in H.
  destruct H.
  unfolds.
  intros.
  apply H7 in H8.
  mytac.
  unfolds in H8.
  inverts H8.
  simpl.
  destruct osc.
  destruct p.
  auto.

  eapply init_goodis;eauto.
  mytac;auto.
  
  do 2 eexists.
  splits;eauto.
  unfold InitTasks in H.
  destruct H.
  unfolds in H.
  mytac.
  unfolds in H2.
  destruct H2.
  do 6 eexists;splits;eauto.
  unfold CurLINV.
  clear -H12.
  unfold satp in *.
  intros.
  lets Hx: H12 aop.
  clear H12.
  sep auto.
  instantiate (1:=init_lg).
  sep auto.

  apply SmCTaskSim;auto.

  eapply V293_ApiMethSim with (Spec:=Spec);auto.
  unfolds in Hside.
  destruct Hside;auto.
  apply V293_WFFunEnv_imply_WFFuncsSim;auto.
  eapply bpr'_to_bpr;eauto.
  split;auto.
  
  unfolds.
  splits;auto.
  unfolds.
  split;eauto.
  clear -H13.
  destruct x1 as [[[[]]]].
  simpl in H13.
  simpl;auto.
  apply H16 in H2.
  mytac.
  eexists;eauto.
  
  intros.
  lets Hx: H8 H16.
  unfolds;eauto.
  mytac.
  do 4 eexists;splits;eauto.
  exists init_lg.
  unfold satp in *.
  lets Hx:H22 aop.
  sep auto.
  
  intros.

  destruct H21.
  destruct x4 as [[[[]]]].
  destruct l as [[]].
  simpl substaskst in *.
  simpl RdyChange in *.
  eexists;split;auto.

  apply SmCTaskSim;auto.
  
  apply V293_ApiMethSim with (Spec:=Spec) .
  unfolds in Hside.
  destruct Hside;auto.
  apply V293_WFFunEnv_imply_WFFuncsSim;auto.
  eapply bpr'_to_bpr;eauto.
  split;auto.
  unfolds.
  splits;auto.
  unfold InitTaskSt.
  unfold satp in *.
  simpl fst in *.
  simpl snd.
  destruct H24.
  unfold RDYINV in H22.
  split.
  intros.
  lets Hx:H21 aop.
  lets Hy:H22 aop.
  destruct Hx.
  clear H21 H22.
  
  destruct H24.
  destruct H22;auto.
  unfold CurTid.
  eapply merge_star;eauto.
  unfolds;eauto.
  clear Hy.
  sep auto.
  clear -H25.
  simpl in *.
  mytac.
  auto.
  
  assert (i = empisr).
  simpl in Hy.
  mytac.
  subst i;auto.
  unfold SWINVt in H25.
  unfold SWINV in H25.
  assert (i0=true).
  clear -Hy.
  simpl in Hy;mytac.
  subst i0.
  clear -H25.
  simpl in H25;mytac;tryfalse.
  clear -H23.
  simpl in H23;simpl;auto.
  unfolds in H.
  destruct H.
  
  apply H21 in H17.
  mytac.
  eexists;splits;eauto.

  unfolds in H.
  destruct H;auto.

  destruct osc.
  destruct p.
  unfolds get_afun,get_ifun,get_lint.
  simpl fst.
  simpl snd.
  auto.
  
  apply V293_ApiMethSim with (Spec:=Spec) .
  unfolds in Hside.
  destruct Hside;auto.
  apply V293_WFFunEnv_imply_WFFuncsSim;auto.
  eapply bpr'_to_bpr;eauto.

  apply V293_IntMethSim with (Spec:=Spec).
  unfolds in Hside.
  destruct Hside;auto.
  apply V293_WFFunEnv_imply_WFFuncsSim;auto.
  eapply int_bpr'_to_bpr;eauto.
  unfold EqDomInt.
  clear -Heqdomos.
  unfolds in Heqdomos.
  destruct osc.
  destruct p.
  destruct A.
  destruct p1.
  simpl in *.
  mytac.
  auto.
Qed.

Theorem V293_toptheorem:
  forall osc A (init:InitAsrt) (I:Inv) (Spec:funspec) li,
    no_fun_same (get_afun osc)  (get_ifun osc)->
    no_call_api_os (get_afun osc) (get_ifun osc) (get_lint osc) ->
    (forall f t d1 d2 s, (fst (fst osc)) f = Some (t,d1,d2,s) ->
                         good_decllist (revlcons d1 d2) = true /\ GoodStmt' s) ->
    (forall f t d1 d2 s, (snd (fst osc)) f = Some (t,d1,d2,s) ->
                         good_decllist (revlcons d1 d2) = true/\GoodStmt' s) ->
    GoodI I (snd A) li->
    (
      forall i isrreg si p r tid lg,
        Some p = BuildintPre i (snd (fst A)) isrreg si I li tid lg ->
        Some r = BuildintRet i (snd (fst A)) isrreg si I li tid lg ->
        exists s,
          (get_lint osc) i = Some s /\
          {|Spec , (snd A), li, I, retfalse, r|}|-tid {{p}}s {{Afalse}}
      
    )->
    (
      forall (f:fid) ab vl p r ft tid, 
        (fst (fst A)) f = Some (ab,ft) ->
        Some p = BuildPreA' (get_afun osc) f (ab,ft) vl li tid init_lg ->
        Some r = BuildRetA' (get_afun osc) f (ab,ft) vl li tid init_lg ->
        (
          exists  t d1 d2 s,
            (get_afun osc) f = Some (t, d1, d2, s) /\
            InfRules Spec (snd A) li I r Afalse p s Afalse tid
        )
    )->
    WFFunEnv (get_ifun osc) Spec (snd A) li I ->
    (
      eqdomOS osc A /\ 
      side_condition I li (snd A) init init_lg
    )
->
OSCorrect osc A init.
Proof.
  intros.
  eapply V293_toptheorem';eauto.
  intros.
  lets Hx:H5 H8 H9 H10.
  mytac.
  do 4 eexists;splits;eauto.
  unfold get_afun in *.
  lets Hx:H1 H11.
  destruct Hx;auto.
Qed.

Theorem V293_verified_os':
  forall osc A (init:InitAsrt) li (I:Inv) (Spec:funspec) pa pi ip apispec intspec schedmethod,
    osc = (pa,pi,ip) ->
    A = (apispec,intspec,schedmethod) ->
    
    WFAPI pa apispec li Spec schedmethod I init_lg ->
    WFInt ip intspec li Spec schedmethod I ->
    WFIFun pi Spec schedmethod I li ->
    side_condition I li schedmethod init init_lg ->
    
    GOOD_OS osc A init.
Proof.
  introv Hosc HA.
  subst.
  intros.

  unfolds.
  intros.
  rename H9 into Hsc.
  assert (OSCorrect (pa,pi,ip) (apispec, intspec, schedmethod) init).
  unfolds in H5;mytac.
  
  eapply V293_toptheorem;eauto.
  simpl.
  unfolds.
  unfolds in H12.
  mytac;auto.
  simpl.
  unfolds in H2.
  mytac;eauto.
  unfolds in H0.
  mytac;auto.
  intros.
  eapply e0 in H5.
  mytac;eexists;mytac;eauto.
  simpl in H0;auto.
  
  unfolds in H.
  simpl.
  destruct H;auto.
  unfolds.
  unfolds in H1.
  mytac;auto.
  intros.
  apply H5 in H7.
  mytac.
  do 3 eexists;splits;eauto.
  unfolds in H14.
  apply H14 in H7.
  mytac;auto.
  unfolds in H2.
  split.
  simpl.
  unfolds in H.
  unfolds in  H0.
  destruct H0;destruct H;auto.
  unfolds in H0.
  unfolds in H.
  destruct H.
  splits;auto.
  split.
  mytac;auto.
  destruct H2;auto.

  unfolds in H9.
  eapply H9;eauto.
  
  unfolds.
  unfolds.
  mytac;auto.
  intros.
  unfolds in H5.
  mytac.
  simpl.
  clear -H12 H15 H7.
  unfolds in H12.
  mytac.
  unfolds in H2.
  lets Hx: H2 H7.
  unfolds in H15.
  lets Hy: H15 H7.
  mytac.
  clear -Hx H4.
  gen Hx H4.
  induction s;intros;simpl;auto.
  simpl in H4,Hx.
  mytac.
  apply IHs1;auto.
  apply IHs2;auto.
  simpl in Hx,H4.
  mytac.
  apply IHs1;auto.
  apply IHs2;auto.
  unfolds in H5.
  clear -H5.
  mytac.
  unfolds in H0;destruct H0.
  simpl;auto.
  unfolds in H5.
  clear -H5.
  mytac.
  unfolds in H0;destruct H0.
  simpl;auto.
Qed.

Theorem V293_Soundness:
  forall  osc A (init:InitAsrt),
    TopRule osc A init ->
    GOOD_OS osc A init.
Proof.
  intros.
  inverts H.
  inverts H2.
  inverts H3.
  inverts H4.
  eapply V293_verified_os';eauto.
  unfolds;split;eauto.
  unfolds;split;eauto.
  unfolds;split;eauto.
Qed.
