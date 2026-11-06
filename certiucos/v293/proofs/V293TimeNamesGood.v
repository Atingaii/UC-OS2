(* One canonical name-only LocalInv for both shared-time GoodI and API.
   Names own zero bytes/abstract slots; this is not a full task invariant. *)
Require Import CertiOS.certiucos.v293.proofs.V293TimeSetAPI.
Require Import CertiOS.certiucos.v293.proofs.V293TimeSharedGood.
Require Import CertiOS.certiucos.v293.proofs.V293TimeShared.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List.

Definition V293_time_names_li now bn : LocalInv :=
  fun _ _ => Agvarenv now Tint32 (bn,0%Z).
Lemma V293_time_names_footprint : forall now bn t lg,
  V293_time_names_li now bn t lg ==> Aemp.
Proof.
  intros now bn t lg s H. apply agvarenv_elim in H. exact (proj2 H).
Qed.
Lemma V293_time_names_local_good : forall now bn, GoodLInvAsrt (V293_time_names_li now bn).
Proof.
  intros now bn t lg. split;[exact I | ].
  intros ge le M ir aux O le' M' aux' ir' O' H H'.
  specialize (H (END None)). specialize (H' (END None)).
  apply V293_time_names_footprint in H. apply V293_time_names_footprint in H'.
  change (M=emp /\ O=emp) in H. change (M'=emp /\ O'=emp) in H'.
  destruct H;destruct H';subst;split;reflexivity.
Qed.
Lemma V293_time_names_global : forall now bn t lg,
  p_local (V293_time_names_li now bn) t lg ==>
    Agvarenv now Tint32 (bn,0%Z) ** p_local (V293_time_names_li now bn) t lg.
Proof.
  intros now bn t lg s H. apply astar_l_agvarenv_intro;[exact H | ].
  destruct s as [[[[[[ge le] M] ir] aux] O] op].
  unfold p_local in H. apply sat_split in H.
  destruct H as (m1 & m2 & o1 & o2 & JM & JO & HC & HR).
  unfold LINV,V293_time_names_li in HR. apply astar_l_agvarenv_elim in HR.
  exact (proj1 HR).
Qed.
Lemma V293_time_names_noabs : forall now bn, NoAbs (V293_time_names_li now bn).
Proof.
  intros now bn o O t H O' op. specialize (H op).
  destruct o as [[[[ge le] M] ir] aux]. destruct H as [lg H].
  apply sat_split in H. destruct H as (m1 & m2 & o1 & o2 & JM & JO & HC & HR).
  assert (EO : o1=emp).
  { destruct HC as [tp [b HC]].
    apply sat_split in HC. destruct HC as (mb & mp & ob & optr & JM1 & JO1 & HB & HP).
    destruct HB as [b' [GE [BE [EM EB]]]]. destruct HP as [Points EP].
    change (ob=emp) in EB. change (optr=emp) in EP. subst ob optr.
    apply map_join_emp' in JO1. symmetry;exact JO1. }
  assert (GE : get ge now=Some (bn,Tint32)).
  { apply sat_split in HR. destruct HR as (ml & mf & ol & ofr & JM2 & JO2 & HL & HF).
    unfold LINV,V293_time_names_li in HL. apply astar_l_agvarenv_elim in HL.
    exact (proj2 (proj1 HL)). }
  subst o1. exists lg.
  apply sat_split'. exists m1. exists m2. exists (emp:osabst). exists O'.
  repeat first [assumption | solve [apply map_join_comm;apply map_join_emp] | split].
  apply sat_split'. exists (emp:mem). exists m2. exists (emp:osabst). exists O'.
  repeat first [solve [apply map_join_comm;apply map_join_emp] | split].
  unfold LINV,V293_time_names_li. apply astar_l_agvarenv_intro.
  - split;[apply V293_time_names_local_good | repeat split;reflexivity].
  - split;[reflexivity | exact GE].
Qed.

(* Reuse unchanged obligations, but explicitly discharge the changed one:
   a dead task's returned name-local resource cannot add memory or O slots. *)
Theorem V293_time_names_good : forall now bn,
  GoodI (V293_time_shared_inv bn) V293_scheduler (V293_time_names_li now bn).
Proof.
  intros now bn. destruct (V293_time_shared_good bn) as [Frame [Current [Switch Sched]]].
  split;[exact Frame | ]. split;[exact Current | ]. split;[ | exact Sched].
  intros o O op t b tp M' ct Hs Highest GE Store.
  destruct (Switch o O op t b tp M' ct Hs Highest GE Store) as [tls [Table [Live | Dead]]].
  - exists tls. split;[exact Table | ]. left;exact Live.
  - exists tls. split;[exact Table | ]. right. destruct Dead as [Absent Return].
    split;[exact Absent | ]. intros Mx Ox MM OO Local JM JO.
    assert (Empty : Mx=emp /\ Ox=emp).
    { specialize (Local op). destruct Local as [lg Local].
      apply V293_time_names_footprint in Local.
      destruct o as [[[[ge le] M] ir] aux]. exact Local. }
    destruct Empty as [EM EO]. subst Mx Ox.
    apply Return with (Mx:=emp) (Ox:=emp).
    + intro action. exists (nil:list logicvar).
      destruct o as [[[[ge le] M] ir] aux]. split;reflexivity.
    + exact JM.
    + exact JO.
Qed.

Theorem V293_time_names_compatible : forall fset now ticks saved bn lg Spec,
  ticks<>saved -> now<>ticks -> now<>saved ->
  GoodI (V293_time_shared_inv bn) V293_scheduler (V293_time_names_li now bn) /\
  APIRule (V293_TimeSet_api_unit fset now ticks saved) (V293_TimeSet_api_spec fset)
    Spec V293_scheduler (V293_time_names_li now bn) (V293_time_shared_inv bn) lg.
Proof.
  intros fset now ticks saved bn lg Spec TS NT NS. split.
  - apply V293_time_names_good.
  - apply V293_TimeSet_api_rule;try assumption.
    + apply V293_time_names_local_good.
    + apply V293_time_names_noabs.
    + apply V293_time_names_global.
Qed.

Print Assumptions V293_time_names_good.
Print Assumptions V293_time_names_compatible.
Print Assumptions V293_time_names_noabs.
