(* Actual OS call boundary: sfexec -> allocation -> body -> return.
   Only the existing global closure and lpstep/loststep rules are used.
   This does not turn an existential body trace into WFIFun or GOOD_OS. *)
Require Import CertiOS.certiucos.v293.proofs.V293ReadyFullCall.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyCriticalGlobal.
Require Import CertiOS.certiucos.v293.proofs.V293LocalGlobalTrace.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyGlobalTrace.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickStorage.
Require Import CertiOS.certiucos.v293.code.V293OSSchedDispatch.
Require Import CertiOS.certiucos.v293.code.V293OSSchedChange.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.auxdef.
Require Import CertiOS.framework.proof.join_prop.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Lists.List.
Import ListNotations.

Lemma V293_global_trans : forall p cst a b c,
  V293_global_steps p cst a b -> V293_global_steps p cst b c ->
  V293_global_steps p cst a c.
Proof.
  unfold V293_global_steps. intros p cst a b c A B.
  induction A;[exact B| ]. eapply rt1n_trans;eauto.
Qed.

(* Classification is explicit for this ONE step. The call theorems below
   derive it from the actual sfexec binding or the actual kcall frame. *)
Lemma V293_loststep_global_single : forall pc po pi ip T les aus t cst C st C' st',
  InOS C (pumerge po pi) -> loststep (pumerge po pi) C st C' st' ->
  V293_global_steps (pc,(po,pi,ip)) cst
    (V293_local_global_at T les aus t C st)
    (V293_local_global_at T les aus t C' st').
Proof.
  intros pc po pi ip T les aus t cst [c [ke ks]] [[[[ge le] M] ir] au]
    [c' [ke' ks']] [[[[ge' le'] M'] ir'] au'] Class Step.
  unfold V293_global_steps.
  eapply rt1n_trans;[ |apply rt1n_refl].
  cbn [V293_local_global_at V293_global_at]. eapply pt_step.
  - apply map_get_set.
  - symmetry. apply set_set_eq.
  - unfold projS,projD. rewrite !map_get_set. reflexivity.
  - unfold projS,projD. rewrite !map_get_set. reflexivity.
  - split;[unfold Dteq|unfold Piteq];intros other Ne;simpl;
      rewrite !map_get_set';reflexivity || congruence.
  - eapply inapi_step;[reflexivity|exact Step|exact Class].
Qed.

Lemma V293_bound_call_inos : forall po pi f tau d1 d2 body caller ks c ke,
  po f=Some (tau,d1,d2,body) ->
  InOS (c,(ke,kcall f body caller ks)) (pumerge po pi).
Proof.
  intros. exists c. exists ke. exists (kcall f body caller ks).
  split;[reflexivity| ]. right;left.
  exists f. exists caller. exists ks. exists tau. exists d1. exists d2.
  exists body. exists body. split;[reflexivity| ]. unfold pumerge. rewrite H. reflexivity.
Qed.

Theorem V293_sched_global_enter : forall pc po pi ip T les aus t cst ge caller M ir aux ks
    f saved interrupt lock schednew table high target current counter b Ms,
  po f=Some (V293_OSSched_success_function saved interrupt lock schednew table high target current counter) ->
  fresh M b ->
  store Tint32 (allocb M b 0%Z 4) (b,0%Z) (Vint32 Int.zero)=Some Ms ->
  goodks (pc,(po,pi,ip)) ks ->
  V293_global_steps (pc,(po,pi,ip)) cst
    (V293_local_global_at T les aus t (curs (sfexec f nil nil),(kenil,ks)) ((ge,caller,M),ir,aux))
    (V293_local_global_at T les aus t
      (curs (V293_sched_control interrupt lock
        (sseq (V293_OSSched_unlocked_prefix schednew table high target)
          (V293_OSSched_change high current counter (sprim (switch target))))),
        (kenil,kcall f (V293_OSSched_success_body saved interrupt lock schednew table high target current counter) caller ks))
      ((ge,V293_cpu_lenv saved b,Ms),ir,aux)).
Proof.
  intros pc po pi ip T les aus t cst ge caller M ir aux ks f saved interrupt lock schednew table high target current counter b Ms Bind Fresh Init Good.
  set (body:=V293_OSSched_success_body saved interrupt lock schednew table high target current counter).
  assert (Program : pumerge po pi f=Some (V293_OSSched_success_function saved interrupt lock schednew table high target current counter)).
  { unfold pumerge. rewrite Bind. reflexivity. }
  eapply V293_global_trans with
    (b:=V293_local_global_at T les aus t
      (curs (salloc nil (dcons saved Tint32 dnil)),(kenil,kcall f body caller ks)) ((ge,emp,M),ir,aux)).
  { apply V293_loststep_global_single.
    - exists (curs (sfexec f nil nil)). exists kenil. exists ks. split;[reflexivity| ].
      left. exists f. exists (@nil val). exists (V293_OSSched_success_function saved interrupt lock schednew table high target current counter).
      exists (@nil type). split;[reflexivity|exact Program].
    - apply ostc_step. eapply stmt_step;[reflexivity| ].
      eapply sfexec_step with (d1:=dnil) (d2:=dcons saved Tint32 dnil);
        [reflexivity|reflexivity|exact Program|exact I|reflexivity]. }
  eapply V293_global_trans with
    (b:=V293_local_global_at T les aus t
      (curs (salloc nil dnil),(kenil,kcall f body caller ks))
      ((ge,V293_cpu_lenv saved b,allocb M b 0%Z 4),ir,aux)).
  { apply V293_loststep_global_single.
    - eapply V293_bound_call_inos;exact Bind.
    - apply ostc_step. eapply stmt_step;[reflexivity| ]. eapply salloclv_step;
        [reflexivity|reflexivity| ]. exists b.
      split;[exact Fresh| ]. split;[reflexivity| ]. split.
      + intros [v E]. rewrite map_emp_get in E. discriminate.
      + reflexivity. }
  eapply V293_global_trans with
    (b:=V293_local_global_at T les aus t (curs body,(kenil,kcall f body caller ks))
      ((ge,V293_cpu_lenv saved b,allocb M b 0%Z 4),ir,aux)).
  { apply V293_loststep_global_single.
    - eapply V293_bound_call_inos;exact Bind.
    - apply ostc_step. eapply stmt_step;[reflexivity|apply sallocend_step]. }
  assert (Local : V293_local_steps (pumerge po pi) (curs body,(kenil,kstop))
      ((ge,V293_cpu_lenv saved b,allocb M b 0%Z 4),ir,aux)
      (curs (V293_sched_control interrupt lock
        (sseq (V293_OSSched_unlocked_prefix schednew table high target)
          (V293_OSSched_change high current counter (sprim (switch target))))),(kenil,kstop))
      ((ge,V293_cpu_lenv saved b,Ms),ir,aux)).
  { unfold body. rewrite V293_sched_control_exact.
    eapply V293_local_cons. { apply ostc_step. eapply stmt_step;[reflexivity|apply sseq_step]. }
    eapply V293_local_trans.
    { apply V293_csteps_local. eapply V293_success_assign_zero;
        [unfold V293_cpu_lenv;apply map_get_set|exact Init]. }
    eapply V293_local_cons. { apply ostc_step. eapply stmt_step;[reflexivity|apply sskip_step]. }
    apply V293_local_refl. }
  eapply (V293_local_steps_global pc po pi ip _ _ _ _ Local f body caller ks
    Tvoid dnil (dcons saved Tint32 dnil) T les aus t cst Bind).
  change (goodks (pc,(po,pi,ip)) (kcall f body caller ks)).
  cbn [goodks]. unfold pumerge. rewrite Bind. exact Good.
Qed.

(* Stop AFTER free, BEFORE restoring the saved environment. This boundary
   separates the independently measured release and caller restoration. *)
Theorem V293_sched_global_free : forall pc po pi ip T les aus t cst ge caller M Mf ir aux ks
    f body tau d1 d2 saved b,
  po f=Some (tau,d1,d2,body) -> free Tint32 b M=Some Mf ->
  V293_global_steps (pc,(po,pi,ip)) cst
    (V293_local_global_at T les aus t (curs sret,(kenil,kcall f body caller ks))
      ((ge,V293_cpu_lenv saved b,M),ir,aux))
    (V293_local_global_at T les aus t (curs (sfree nil None),(kenil,kcall f body caller ks))
      ((ge,V293_cpu_lenv saved b,Mf),ir,aux)).
Proof.
  intros. eapply V293_global_trans.
  - apply V293_loststep_global_single.
    + eapply V293_bound_call_inos;exact H.
    + apply ostc_step. eapply stmt_step;[reflexivity| ].
      eapply sret_step;[reflexivity|reflexivity|apply V293_cpu_layout].
  - apply V293_loststep_global_single.
    + eapply V293_bound_call_inos;exact H.
    + apply ostc_step. eapply stmt_step;[reflexivity| ].
      eapply sfree_step;[reflexivity|reflexivity|exact H0].
Qed.

Theorem V293_sched_global_restore : forall pc po pi ip T les aus t cst ge le M ir aux ks
    f body caller tau d1 d2,
  po f=Some (tau,d1,d2,body) ->
  V293_global_steps (pc,(po,pi,ip)) cst
    (V293_local_global_at T les aus t (curs (sfree nil None),(kenil,kcall f body caller ks))
      ((ge,le,M),ir,aux))
    (V293_local_global_at T les aus t (SKIP,(kenil,ks)) ((ge,caller,M),ir,aux)).
Proof.
  intros. apply V293_loststep_global_single.
  - eapply V293_bound_call_inos;exact H.
  - apply ostc_step. eapply stmt_step;[reflexivity| ]. eapply sfreeend_step;reflexivity.
Qed.

(* Stable complete-return interface. No extra enclosing kcall remains. *)
Theorem V293_sched_global_return : forall pc po pi ip T les aus t cst ge caller M Mf ir aux ks
    f body tau d1 d2 saved b,
  po f=Some (tau,d1,d2,body) -> free Tint32 b M=Some Mf ->
  V293_global_steps (pc,(po,pi,ip)) cst
    (V293_local_global_at T les aus t (curs sret,(kenil,kcall f body caller ks))
      ((ge,V293_cpu_lenv saved b,M),ir,aux))
    (V293_local_global_at T les aus t (SKIP,(kenil,ks)) ((ge,caller,Mf),ir,aux)).
Proof.
  intros. eapply V293_global_trans.
  - eapply V293_sched_global_free;eauto.
  - eapply V293_sched_global_restore;eauto.
Qed.
