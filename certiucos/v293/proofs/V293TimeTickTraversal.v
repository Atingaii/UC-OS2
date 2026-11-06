(* One actual zero-delay iteration, with joint spatial return in the SAME
   final memory. No loop guard, hook, time increment, nonzero delay, function
   allocation/return, interleaving or complete Inv/GOOD_OS credit. *)
Require Import CertiOS.certiucos.v293.code.V293OSTimeTick.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewExec.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.cstepLib.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Theorem V293_tick_iteration_normalization : forall ptcb rows group saved enter exit,
  enter <> exit ->
  V293_port_normalize enter exit saved
    (V293_tick_raw_iteration ptcb rows group saved enter exit) =
  Some (V293_tick_iteration ptcb rows group).
Proof.
  intros. unfold V293_port_normalize,V293_tick_raw_iteration,V293_tick_iteration,
    V293_tick_delay,V293_tick_expiry,V293_tick_advance.
  cbn [V293_port_calls]. repeat destruct (Z.eq_dec _ _); congruence || reflexivity.
Qed.

Theorem V293_tick_body_normalization : forall ptcb rows group saved now running head hook enter exit,
  enter <> exit -> hook <> enter -> hook <> exit ->
  V293_port_normalize enter exit saved
    (V293_tick_raw_body ptcb rows group saved now running head hook enter exit) =
  Some (V293_tick_body ptcb rows group saved now running head hook).
Proof.
  intros. unfold V293_port_normalize,V293_tick_raw_body,V293_tick_body,
    V293_tick_raw_iteration,V293_tick_iteration,V293_tick_delay,V293_tick_expiry,V293_tick_advance.
  cbn [V293_port_calls]. repeat destruct (Z.eq_dec _ _); congruence || reflexivity.
Qed.

Theorem V293_tick_field_layout :
  typelen V293_tcb_type = 56 /\
  ftype 13%Z V293_tcb_fields = Some Tint32 /\
  field_offset 13%Z V293_tcb_fields = Some (Int.repr 44) /\
  ftype 7%Z V293_tcb_fields = Some (Tcom_ptr 410%Z) /\
  field_offset 7%Z V293_tcb_fields = Some (Int.repr 20).
Proof. repeat split; reflexivity. Qed.

Lemma V293_tick_field_eval : forall ge le M ptcb bc bt base field delta tp value,
  get le ptcb = Some (bc,Tptr V293_tcb_type) ->
  load (Tptr V293_tcb_type) M (bc,0%Z) = Some (Vptr (bt,Int.repr base)) ->
  ftype field V293_tcb_fields = Some tp ->
  field_offset field V293_tcb_fields = Some (Int.repr delta) ->
  (0 <= base)%Z -> (0 <= delta)%Z -> (base+delta <= Int.max_unsigned)%Z ->
  load tp M (bt,(base+delta)%Z) = Some value ->
  evaltype (V293_tick_field ptcb field) (ge,le,M) = Some tp /\
  evalval (V293_tick_field ptcb field) (ge,le,M) = Some value.
Proof.
  intros ge le M ptcb bc bt base field delta tp value Bptr Hptr Ft Fo B D R Read.
  assert (Tp : evaltype (ederef (evar ptcb)) (ge,le,M) = Some V293_tcb_type).
  { cbn [evaltype get_lenv get_genv get_mem]. rewrite Bptr. reflexivity. }
  assert (T : evaltype (V293_tick_field ptcb field) (ge,le,M) = Some tp).
  { cbn [V293_tick_field evaltype]. rewrite Bptr. exact Ft. }
  split; [exact T | ]. unfold V293_tick_field in *. cbn [evalval]. rewrite T.
  cbn [evaladdr evalval evaltype get_lenv get_genv get_mem]. rewrite Bptr.
  cbn beta iota. rewrite Hptr. unfold getoff. rewrite Tp.
  cbn [V293_tcb_type]. rewrite Fo. cbn [addrval_to_addr].
  rewrite Int.repr_unsigned. unfold Int.add.
  rewrite (Int.unsigned_repr base) by lia.
  rewrite (Int.unsigned_repr delta) by lia.
  rewrite Int.unsigned_repr by lia. exact Read.
Qed.

(* The shared bytes are still required for a ready / zero-delay task. This
   intentionally does not use the insufficient selected-record assertion. *)
Definition V293_tick_zero_node bt base next : asrt :=
  V293_owned_record_cell ((bt,(base+44)%Z),Tint32,Vint32 Int.zero) **
  V293_owned_record_cell ((bt,(base+20)%Z),Tcom_ptr 410%Z,Vptr next).

Theorem V293_tick_zero_iteration_owned_execution :
  forall P ks ge le M ir enabled si ci O op ptcb rows group bc bt base next R,
  get le ptcb = Some (bc,Tptr V293_tcb_type) ->
  (0 <= base)%Z -> (base+44 <= Int.max_unsigned)%Z ->
  (ge,le,M,ir,(enabled,si,ci),O,op) |=
    V293_owned_record_cell ((bc,0%Z),Tptr V293_tcb_type,Vptr (bt,Int.repr base)) **
    (V293_tick_zero_node bt base next ** R) ->
  exists Mf,
  store (Tptr V293_tcb_type) M (bc,0%Z) (Vptr next) = Some Mf /\
  V293_local_steps P (curs (V293_tick_iteration ptcb rows group),(kenil,ks))
    ((ge,le,M),ir,(enabled,si,ci))
    (curs (sskip None),(kenil,ks)) ((ge,le,Mf),ir,(enabled,si,ci)) /\
  load (Tptr V293_tcb_type) Mf (bc,0%Z) = Some (Vptr next) /\
  (ge,le,Mf,ir,(enabled,si,ci),O,op) |=
    V293_owned_record_cell ((bc,0%Z),Tptr V293_tcb_type,Vptr next) **
    (V293_tick_zero_node bt base next ** R) /\
  (forall c i, c <> bc \/ (i < 0)%Z \/ (4 <= i)%Z -> get Mf (c,i) = get M (c,i)).
Proof.
  intros P ks ge le M ir enabled si ci O op ptcb rows group bc bt base next R
    Bind Base Limit Owned.
  assert (Pointer : load (Tptr V293_tcb_type) M (bc,0%Z) = Some (Vptr (bt,Int.repr base))).
  { change (load (Tptr V293_tcb_type) (getmem (ge,le,M,ir,(enabled,si,ci),O,op)) (bc,0%Z) = Some (Vptr (bt,Int.repr base))).
    eapply V293_record_star_load_l; [apply V293_owned_record_cell_load | exact Owned]. }
  assert (Dly : load Tint32 M (bt,(base+44)%Z) = Some (Vint32 Int.zero)).
  { change (load Tint32 (getmem (ge,le,M,ir,(enabled,si,ci),O,op)) (bt,(base+44)%Z) = Some (Vint32 Int.zero)).
    eapply V293_record_star_load_r; [ | exact Owned].
    eapply V293_record_star_load_l. unfold V293_tick_zero_node.
    eapply V293_record_star_load_l. apply V293_owned_record_cell_load. }
  assert (Next : load (Tcom_ptr 410%Z) M (bt,(base+20)%Z) = Some (Vptr next)).
  { change (load (Tcom_ptr 410%Z) (getmem (ge,le,M,ir,(enabled,si,ci),O,op)) (bt,(base+20)%Z) = Some (Vptr next)).
    eapply V293_record_star_load_r; [ | exact Owned].
    eapply V293_record_star_load_l. unfold V293_tick_zero_node.
    eapply V293_record_star_load_r. apply V293_owned_record_cell_load. }
  destruct (V293_tick_field_eval ge le M ptcb bc bt base 13%Z 44%Z Tint32 _
    Bind Pointer eq_refl eq_refl Base ltac:(lia) Limit Dly) as [Dt Dv].
  destruct (V293_tick_field_eval ge le M ptcb bc bt base 7%Z 20%Z (Tcom_ptr 410%Z) _
    Bind Pointer eq_refl eq_refl Base ltac:(lia) ltac:(lia) Next) as [Nt Nv].
  assert (Test : evalval (V293_tick_ne (V293_tick_field ptcb 13%Z) 0) (ge,le,M) =
      Some (Vint32 Int.zero)).
  { unfold V293_tick_ne,V293_tick_eq. cbn [evalval evaltype]. rewrite Dt,Dv. reflexivity. }
  destruct (V293_owned_record_cell_update (bc,0%Z) (Tptr V293_tcb_type)
    (Vptr (bt,Int.repr base)) (Vptr next) _ _ _ _ _ _ _ _ eq_refl Owned) as [Mf [Store Returned]].
  assert (Advance : forall tail, cstepstar P
    (curs (V293_tick_advance ptcb),(kenil,tail)) (ge,le,M)
    (curs (sskip None),(kenil,tail)) (ge,le,Mf)).
  { intro tail. unfold V293_tick_advance.
    eapply V293_assign_pointer_execution with (tr:=Tcom_ptr 410%Z) (off:=0%Z);
      try eassumption.
    - cbn [evaltype]. rewrite Bind. reflexivity.
    - apply eq_vcomptr. split; left; eauto.
    - cbn [evaladdr get_lenv get_genv]. rewrite Bind. reflexivity.
    - change (0 <= 0 <= 4294967295)%Z. lia. }
  exists Mf. split; [exact Store | ]. split.
  - unfold V293_tick_iteration.
    eapply V293_local_cons. { apply ostc_step. eapply stmt_step; [reflexivity|apply sseq_step]. }
    eapply V293_local_cons. { apply encrit_step;reflexivity. }
    eapply V293_local_cons. { apply ostc_step. eapply stmt_step; [reflexivity|apply sskip_step]. }
    eapply V293_local_cons. { apply ostc_step. eapply stmt_step; [reflexivity|apply sseq_step]. }
    unfold V293_tick_delay at 1.
    eapply V293_local_cons. { apply ostc_step. eapply stmt_step; [reflexivity|apply sifthen_step]. }
    eapply V293_local_trans.
    { apply V293_csteps_local. apply V293_expr_steps. apply evalval_imply_estepstar. exact Test. }
    eapply V293_local_cons. { apply ostc_step. eapply stmt_step; [reflexivity|apply sviff_step;reflexivity]. }
    eapply V293_local_cons. { apply ostc_step. eapply stmt_step; [reflexivity|apply sskip_step]. }
    eapply V293_local_cons. { apply ostc_step. eapply stmt_step; [reflexivity|apply sseq_step]. }
    eapply V293_local_trans. { apply V293_csteps_local. apply Advance. }
    eapply V293_local_cons. { apply ostc_step. eapply stmt_step; [reflexivity|apply sskip_step]. }
    eapply V293_local_cons. { apply excrit_step;reflexivity. }
    apply V293_local_refl.
  - split; [eapply V293_store_readback; [reflexivity|exact Store] | ].
    split; [exact Returned | ]. intros c i Outside.
    eapply V293_storebytes_outside; [exact Store | ].
    rewrite encode_val_length. exact Outside.
Qed.

Print Assumptions V293_tick_iteration_normalization.
Print Assumptions V293_tick_body_normalization.
Print Assumptions V293_tick_field_layout.
Print Assumptions V293_tick_zero_iteration_owned_execution.
