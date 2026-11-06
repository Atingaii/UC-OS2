(* Lift the EXISTING local OS semantics, including actual ir/aux changes.
   No interrupt/classification oracle and no new transition relation. *)
Require Import CertiOS.certiucos.v293.proofs.V293ReadyGlobalTrace.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.step_prop.
Require Import CertiOS.framework.proof.auxdef.
Require Import CertiOS.framework.proof.join_prop.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import Coq.Relations.Relation_Operators.

Definition V293_local_global_at (T:tasks) (les:cltenvs) (aus:ltaskstset)
    (t:tid) (C:code) (st:taskst) :=
  match st with (m,ir,au) => V293_global_at T les t ir (set aus t au) C m end.

Lemma V293_loststep_global : forall pc po pi ip f s saved tail tau d1 d2
    T les aus t cst C st C' st',
  po f=Some (tau,d1,d2,s) ->
  goodks (pc,(po,pi,ip))
    (snd (snd (V293_enclose C (kcall f s saved tail)))) ->
  loststep (pumerge po pi) C st C' st' ->
  (match V293_local_global_at T les aus t (V293_enclose C (kcall f s saved tail)) st,
         V293_local_global_at T les aus t (V293_enclose C' (kcall f s saved tail)) st' with
    | (Ti,Si,ti),(Tf,Sf,tf) => lpstep (pc,(po,pi,ip)) Ti cst Si ti Tf cst Sf tf
   end) /\
  goodks (pc,(po,pi,ip))
    (snd (snd (V293_enclose C' (kcall f s saved tail)))).
Proof.
  intros pc po pi ip f s saved tail tau d1 d2 T les aus t cst
    [c [ke inner]] [[[[ge le] M] ir] au]
    [c' [ke' inner']] [[[[ge' le'] M'] ir'] au'] Bind Good Step.
  pose proof (step_prop.loststep_cont_locality _ _ _ _ _ _ _ _ po pi
    (kcall f s saved tail) Step) as Framed.
  assert (Local : ltstep (pc,(po,pi,ip)) t
      (c,(ke,inner ## kcall f s saved tail)) cst ((ge,le,M),ir,au)
      (c',(ke',inner' ## kcall f s saved tail)) cst ((ge',le',M'),ir',au')).
  { eapply inapi_step; [reflexivity | exact Framed | ].
    exact (V293_enclosing_inos pc po pi ip f s saved tail tau d1 d2
      (c,(ke,inner)) Bind Good). }
  split.
  - cbn [V293_local_global_at V293_global_at V293_enclose]. eapply pt_step.
    + apply map_get_set.
    + symmetry. apply set_set_eq.
    + unfold projS,projD. rewrite !map_get_set. reflexivity.
    + unfold projS,projD. rewrite !map_get_set. reflexivity.
    + split; [unfold Dteq | unfold Piteq]; intros other Ne; simpl.
      * rewrite !map_get_set'. reflexivity. all:congruence.
      * rewrite !map_get_set'. reflexivity. all:congruence.
    + exact Local.
  - eapply ltstep_goodks; eauto.
Qed.

(* Stable interface. Reuse the already defined standard loststep closure;
   both endpoint auxiliary states are the ones in that actual local trace. *)
Theorem V293_local_steps_global : forall pc po pi ip C st Cf stf,
  V293_local_steps (pumerge po pi) C st Cf stf ->
  forall f s saved tail tau d1 d2 T les aus t cst,
  po f=Some (tau,d1,d2,s) ->
  goodks (pc,(po,pi,ip))
    (snd (snd (V293_enclose C (kcall f s saved tail)))) ->
  V293_global_steps (pc,(po,pi,ip)) cst
    (V293_local_global_at T les aus t (V293_enclose C (kcall f s saved tail)) st)
    (V293_local_global_at T les aus t (V293_enclose Cf (kcall f s saved tail)) stf).
Proof.
  intros pc po pi ip C st Cf stf Trace.
  unfold V293_local_steps in Trace.
  remember (C,st) as initial eqn:Initial in Trace.
  remember (Cf,stf) as final eqn:Final in Trace.
  revert C st Cf stf Initial Final.
  induction Trace as [x | x y z Step Rest IH];
    intros C st Cf stf Initial Final; subst x.
  - inversion Final; subst. intros. apply rt1n_refl.
  - destruct y as [Cmid stmid]. destruct z as [Clast stlast].
    inversion Final; subst Clast stlast.
    intros f s saved tail tau d1 d2 T les aus t cst Bind Good.
    destruct (V293_loststep_global pc po pi ip f s saved tail tau d1 d2
      T les aus t cst C st Cmid stmid Bind Good Step) as [Global NextGood].
    eapply rt1n_trans; [exact Global | ].
    eapply IH; eauto.
Qed.
