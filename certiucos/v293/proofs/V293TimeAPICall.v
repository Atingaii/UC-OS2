(* Real call and allocation of the unchanged time APIs. The spatial frame is
   evaluated in the final callee environment, not transported from the caller. *)
Require Import CertiOS.certiucos.v293.proofs.V293TimeReadyEntry.
Require Import CertiOS.certiucos.v293.proofs.V293TimeGetAPI.
Require Import CertiOS.certiucos.v293.proofs.V293TimeAccess.
Require Import CertiOS.certiucos.v293.proofs.V293TimeSetAPI.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickLifecycle.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.memory_prop.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.framework.proof.rulesoundlib.
Require Import CertiOS.framework.proof.lmachLib.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List.
Import ListNotations.
Local Open Scope nat_scope.

Definition V293_time_call_locals ticks saved bt bs : env :=
  set (set emp ticks (bt,Tint32)) saved (bs,Tint32).

Lemma V293_time_parameter_store : forall ge le M ir aux O op b n R,
  (ge,le,M,ir,aux,O,op) |= Amapsto (b,0%Z) Tint32 true Vundef ** R ->
  exists Mp, store Tint32 M (b,0%Z) (Vint32 n)=Some Mp /\
    (ge,le,Mp,ir,aux,O,op) |= Amapsto (b,0%Z) Tint32 true (Vint32 n) ** R.
Proof.
  intros ge le M ir aux O op b n R Owned. apply sat_split in Owned.
  destruct Owned as (part&rest&o1&o2&JM&JO&[Bytes Empty]&Frame).
  destruct (store_exist_join' _ _ _ (Vint32 n) _ _ _ Bytes JM) as [Mp Store].
  destruct (store_mapstoval_frame1 _ _ _ _ _ _ _ _ Bytes JM Store)
    as (part'&Bytes'&LocalStore&JM').
  exists Mp. split;[exact Store | ]. apply sat_split'.
  exists part'. exists rest. exists o1. exists o2.
  split;[exact JM' | ]. split;[exact JO | ]. split;[split;assumption | exact Frame].
Qed.

Theorem V293_time_get_call_entry :
  forall P ks ge caller M ir aux O op f now ticks saved bt bs R,
  P f=Some(V293_TimeGet_function now ticks saved) -> ticks<>saved ->
  fresh M bt -> fresh (allocb M bt 0%Z (typelen Tint32)) bs ->
  (ge,V293_time_call_locals ticks saved bt bs,M,ir,aux,O,op) |= R ->
  let Mf:=allocb (allocb M bt 0%Z (typelen Tint32)) bs 0%Z (typelen Tint32) in
  V293_local_steps P (curs(scall f []),(kenil,ks)) ((ge,caller,M),ir,aux)
    (curs(V293_TimeGet_body now ticks saved),
     (kenil,kcall f (V293_TimeGet_body now ticks saved) caller ks))
    ((ge,V293_time_call_locals ticks saved bt bs,Mf),ir,aux) /\
  (ge,V293_time_call_locals ticks saved bt bs,Mf,ir,aux,O,op) |=
    Amapsto(bs,0%Z) Tint32 true Vundef ** (Amapsto(bt,0%Z) Tint32 true Vundef ** R).
Proof.
  intros P ks ge caller M ir aux O op f now ticks saved bt bs R
    Program Different FreshTicks FreshSaved Held Mf.
  split.
  - eapply V293_local_cons. { apply ostc_step. eapply stmt_step;[reflexivity | apply snpcall_step]. }
    eapply V293_local_cons.
    { apply ostc_step. eapply stmt_step;[reflexivity | ].
      eapply sfexec_step with (d1:=dnil)(d2:=dcons ticks Tint32 (dcons saved Tint32 dnil));
        [reflexivity | reflexivity | exact Program | exact I | reflexivity]. }
    eapply V293_local_cons.
    { apply ostc_step. eapply stmt_step;[reflexivity | ]. eapply salloclv_step;
        [reflexivity | reflexivity | ]. exists bt. repeat split;try assumption;try reflexivity.
      intros [v E]. rewrite map_emp_get in E. discriminate. }
    eapply V293_local_cons.
    { apply ostc_step. eapply stmt_step;[reflexivity | ]. eapply salloclv_step;
        [reflexivity | reflexivity | ]. exists bs. repeat split;try assumption;try reflexivity.
      intros [v E]. rewrite map_get_set' in E by exact Different.
      rewrite map_emp_get in E. discriminate. }
    eapply V293_local_cons. { apply ostc_step. eapply stmt_step;[reflexivity | apply sallocend_step]. }
    apply V293_local_refl.
  - apply V293_tick_allocate_frame;[exact FreshSaved | ].
    apply V293_tick_allocate_frame;assumption.
Qed.

Lemma V293_time_fresh_after_alloc : forall M bt bs,
  bt<>bs -> fresh M bs -> fresh (allocb M bt 0%Z (typelen Tint32)) bs.
Proof.
  intros M bt bs Different Fresh l i E [v Bound]. subst l.
  change(get(allocb M bt 0%Z (typelen Tint32))(bs,i)=Some v)in Bound.
  rewrite V293_success_allocb_outside in Bound by(left;congruence).
  apply(Fresh (bs,i) i eq_refl). exists v;exact Bound.
Qed.
Lemma V293_time_fresh_after_store : forall M Mp bt bs n,
  bt<>bs -> fresh M bs -> store Tint32 M (bt,0%Z)(Vint32 n)=Some Mp -> fresh Mp bs.
Proof.
  intros M Mp bt bs n Different Fresh Store l i E [v Bound]. subst l.
  change(get Mp(bs,i)=Some v)in Bound.
  unfold store in Store. rewrite (V293_storebytes_outside _ _ _ _ _ _ _ Store (or_introl (not_eq_sym Different))) in Bound.
  apply(Fresh (bs,i) i eq_refl). exists v;exact Bound.
Qed.

Theorem V293_time_set_call_entry :
  forall P ks ge caller M ir aux O op f now ticks saved bt bs n R,
  P f=Some(V293_TimeSet_function now ticks saved) -> ticks<>saved ->
  fresh M bt -> fresh M bs -> bt<>bs ->
  (ge,V293_time_call_locals ticks saved bt bs,M,ir,aux,O,op) |= R ->
  exists Mp Mf,
    store Tint32 (allocb M bt 0%Z (typelen Tint32)) (bt,0%Z) (Vint32 n)=Some Mp /\
    Mf=allocb Mp bs 0%Z (typelen Tint32) /\
      V293_local_steps P (curs(scall f [econst32 n]),(kenil,ks)) ((ge,caller,M),ir,aux)
        (curs(V293_TimeSet_body now ticks saved),
         (kenil,kcall f (V293_TimeSet_body now ticks saved) caller ks))
        ((ge,V293_time_call_locals ticks saved bt bs,Mf),ir,aux) /\
      (ge,V293_time_call_locals ticks saved bt bs,Mf,ir,aux,O,op) |=
        Amapsto(bs,0%Z) Tint32 true Vundef **
          (Amapsto(bt,0%Z) Tint32 true (Vint32 n) ** R).
Proof.
  intros P ks ge caller M ir aux O op f now ticks saved bt bs n R
    Program Different FreshTicks FreshSaved0 Blocks Held.
  pose proof(V293_tick_allocate_frame _ _ _ _ _ _ _ bt Tint32 _ FreshTicks Held) as Allocated.
  destruct(V293_time_parameter_store _ _ _ _ _ _ _ bt n R Allocated) as (Mp&Store&ParamOwned).
  exists Mp. exists(allocb Mp bs 0%Z (typelen Tint32)). split;[exact Store | ].
  assert(FreshSaved:fresh Mp bs).
  { eapply V293_time_fresh_after_store;[exact Blocks | | exact Store].
    apply V293_time_fresh_after_alloc;assumption. }
  split;[reflexivity | ]. split.
  - eapply V293_local_cons. { apply ostc_step. eapply stmt_step;[reflexivity | apply spcall_step;reflexivity]. }
    eapply V293_local_cons. { apply ostc_step. eapply expr_step;[reflexivity | constructor]. }
    eapply V293_local_cons. { apply ostc_step. eapply stmt_step;[reflexivity | apply svfevalnil_step]. }
    eapply V293_local_cons.
    { apply ostc_step. eapply stmt_step;[reflexivity | ].
      eapply sfexec_step with (d1:=dcons ticks Tint32 dnil)(d2:=dcons saved Tint32 dnil);
        [reflexivity | reflexivity | exact Program | split;[exact I | reflexivity] | reflexivity]. }
    eapply V293_local_cons.
    { apply ostc_step. eapply stmt_step;[reflexivity | ]. eapply sallocp_step with (b:=bt);
        [reflexivity | reflexivity | | apply map_get_set | exact Store].
      exists bt. repeat split;try assumption;try reflexivity.
      intros [v E]. rewrite map_emp_get in E. discriminate. }
    eapply V293_local_cons.
    { apply ostc_step. eapply stmt_step;[reflexivity | ]. eapply salloclv_step;
        [reflexivity | reflexivity | ]. exists bs. repeat split;try assumption;try reflexivity.
      intros [v E]. rewrite map_get_set' in E by exact Different.
      rewrite map_emp_get in E. discriminate. }
    eapply V293_local_cons. { apply ostc_step. eapply stmt_step;[reflexivity | apply sallocend_step]. }
    apply V293_local_refl.
  - apply V293_tick_allocate_frame;assumption.
Qed.
