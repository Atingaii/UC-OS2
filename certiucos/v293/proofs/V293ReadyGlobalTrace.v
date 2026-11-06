(* Lift a finite source trace to the ORIGINAL global task semantics.
   An actual enclosing OS binding, not a synthetic interrupt, justifies InOS.
   This is an existence theorem, not reachability, WFIFun, or GOOD_OS. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.step_prop.
Require Import CertiOS.framework.proof.auxdef.
Require Import CertiOS.framework.proof.join_prop.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import Coq.Relations.Relation_Operators.

Definition V293_global_steps (p:lprog) (cst:clientst) :=
  clos_refl_trans_1n (tasks * osstate * tid)
    (fun x y => match x,y with
        |  (ts,st,t),(ts',st',t') => lpstep p ts cst st t ts' cst st' t'
       end).

Definition V293_enclose (C:code) (tail:stmtcont) : code :=
  match C with (c,(ke,ks)) => (c,(ke,ks ## tail)) end.

Definition V293_global_at (T:tasks) (les:cltenvs) (t:tid)
    (ir:isr) (aus:ltaskstset) (C:code) (m:smem) :=
  match m with (ge,le,M) =>
    (set T t C,(ge,set les t le,M,ir,aus),t)
  end.

Lemma V293_no_os_enclosing_false : forall pc po pi ip f s le ks tau d1 d2 inner,
  po f=Some (tau,d1,d2,s) ->
  ~ no_os (pc,(po,pi,ip)) (inner ## kcall f s le ks).
Proof.
  intros pc po pi ip f s le ks tau d1 d2 inner Bind.
  induction inner; simpl; try tauto.
  - unfold pumerge. rewrite Bind. tauto.
  - destruct (pumerge po pi f0); tauto.
Qed.

Lemma V293_enclosing_context : forall pc po pi ip f s le ks tau d1 d2 inner,
  po f=Some (tau,d1,d2,s) ->
  goodks (pc,(po,pi,ip)) (inner ## kcall f s le ks) ->
  (exists f' s' le' ks' tau' d1' d2' body,
    callcont (inner ## kcall f s le ks)=Some (kcall f' s' le' ks') /\
    pumerge po pi f'=Some (tau',d1',d2',body)) \/
  intcont (inner ## kcall f s le ks)<>None.
Proof.
  intros pc po pi ip f s le ks tau d1 d2 inner Bind.
  induction inner; simpl; intros Good; try solve [apply IHinner;exact Good].
  - left. exists f. exists s. exists le. exists ks. exists tau. exists d1. exists d2. exists s. split; [reflexivity |  ].
    unfold pumerge. rewrite Bind. reflexivity.
  - destruct (pumerge po pi f0) as [[[[ty da] db] body] |  ] eqn:Called.
    + left. exists f0. exists s0. exists e. exists (inner ## kcall f s le ks).
      exists ty. exists da. exists db. exists body.
      split; [reflexivity | exact Called].
    + exfalso. eapply V293_no_os_enclosing_false; eauto.
  - right. discriminate.
  - contradiction.
Qed.

Lemma V293_enclosing_inos : forall pc po pi ip f s le ks tau d1 d2 C,
  po f=Some (tau,d1,d2,s) ->
  goodks (pc,(po,pi,ip)) (snd (snd (V293_enclose C (kcall f s le ks)))) ->
  InOS (V293_enclose C (kcall f s le ks)) (pumerge po pi).
Proof.
  intros pc po pi ip f s le ks tau d1 d2 [c [ke inner]] Bind Good.
  exists c. exists ke. exists (inner ## kcall f s le ks). split; [reflexivity |  ].
  destruct (V293_enclosing_context pc po pi ip f s le ks tau d1 d2 inner Bind Good)
    as [(f' & s' & le' & ks' & ty & da & db & body & Call & Bound) | Interrupt].
  - right;left. exists f'. exists le'. exists ks'. exists ty. exists da. exists db. exists s'. exists body. auto.
  - right;right. exact Interrupt.
Qed.

Lemma V293_cstep_global : forall pc po pi ip f s saved tail tau d1 d2
    T les t ir aus au cst C m C' m',
  po f=Some (tau,d1,d2,s) -> get aus t=Some au ->
  goodks (pc,(po,pi,ip))
    (snd (snd (V293_enclose C (kcall f s saved tail)))) ->
  cstep (pumerge po pi) C m C' m' ->
  (match V293_global_at T les t ir aus (V293_enclose C (kcall f s saved tail)) m,
         V293_global_at T les t ir aus (V293_enclose C' (kcall f s saved tail)) m' with
    |  (Ti,Si,ti),(Tf,Sf,tf) => lpstep (pc,(po,pi,ip)) Ti cst Si ti Tf cst Sf tf
   end) /\
  goodks (pc,(po,pi,ip))
    (snd (snd (V293_enclose C' (kcall f s saved tail)))).
Proof.
  intros pc po pi ip f s saved tail tau d1 d2 T les t ir aus au cst
    [c [ke inner]] [[ge le] M] [c' [ke' inner']] [[ge' le'] M'] Bind Aux Good Step.
  pose proof (step_prop.cstep_cont_locality po pi _ _ _ _ _ _
    (kcall f s saved tail) _ _ Step) as Framed.
  assert (Local : ltstep (pc,(po,pi,ip)) t
      (c,(ke,inner ## kcall f s saved tail)) cst ((ge,le,M),ir,au)
      (c',(ke',inner' ## kcall f s saved tail)) cst ((ge',le',M'),ir,au)).
  { eapply inapi_step; [reflexivity |   |  ].
    - apply ostc_step. exact Framed.
    - exact (V293_enclosing_inos pc po pi ip f s saved tail tau d1 d2
        (c,(ke,inner)) Bind Good). }
  split.
  - cbn [V293_global_at V293_enclose]. eapply pt_step.
    + apply map_get_set.
    + symmetry. apply set_set_eq.
    + unfold projS,projD. rewrite map_get_set,Aux. reflexivity.
    + unfold projS,projD. rewrite map_get_set,Aux. reflexivity.
    + split; [unfold Dteq | unfold Piteq]; intros other Ne; simpl.
      * rewrite !map_get_set'. reflexivity. all:congruence.
      * reflexivity.
    + exact Local.
  - eapply ltstep_goodks; eauto.
Qed.

(* Stable lifting interface: one source trace supplies every global step.
   InOS is DERIVED from the enclosing binding and preserved goodks, not an
   input oracle for each intermediate state. No changes to client memory. *)
Theorem V293_csteps_global : forall pc po pi ip C m Cf mf,
  cstepstar (pumerge po pi) C m Cf mf ->
  forall f s saved tail tau d1 d2 T les t ir aus au cst,
  po f=Some (tau,d1,d2,s) -> get aus t=Some au ->
  goodks (pc,(po,pi,ip))
    (snd (snd (V293_enclose C (kcall f s saved tail)))) ->
  V293_global_steps (pc,(po,pi,ip)) cst
    (V293_global_at T les t ir aus (V293_enclose C (kcall f s saved tail)) m)
    (V293_global_at T les t ir aus (V293_enclose Cf (kcall f s saved tail)) mf).
Proof.
  intros pc po pi ip C m Cf mf Trace.
  remember (pumerge po pi) as program eqn:Program in Trace.
  induction Trace; subst p;
    intros f s saved tail tau d1 d2 T les t ir aus au cst Bind Aux Good.
  - apply rt1n_refl.
  - destruct (V293_cstep_global pc po pi ip f s saved tail tau d1 d2
      T les t ir aus au cst C m C' m' Bind Aux Good H) as [Step NextGood].
    eapply rt1n_trans; [exact Step |  ]. eapply IHTrace; eauto.
Qed.
