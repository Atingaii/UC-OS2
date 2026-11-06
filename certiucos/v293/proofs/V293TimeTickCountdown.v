(* Fixed OSTimeTick: one actual iteration whose unsigned delay remains
   nonzero. Reuses the frozen AST; no full-function/ISR/GOOD_OS claim. *)
Require Import CertiOS.certiucos.v293.code.V293OSTimeTick.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickTraversal.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewExec.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.cstepLib.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import Coq.Lists.List Lia.
Local Open Scope nat_scope.

Lemma V293_tick_countdown_arithmetic : forall d,
  (2 <= d <= Int.max_unsigned)%Z ->
  Int.eq (Int.repr d) Int.zero = false /\
  Int.sub (Int.repr d) Int.one = Int.repr (d-1) /\
  Int.eq (Int.repr (d-1)) Int.zero = false.
Proof.
  intros d Range.
  assert (Nonzero : forall n, (0 < n <= Int.max_unsigned)%Z -> Int.repr n <> Int.zero).
  { intros n Bound E. apply (f_equal Int.unsigned) in E.
    rewrite Int.unsigned_repr, Int.unsigned_zero in E by lia. lia. }
  split; [apply Int.eq_false; apply Nonzero; lia | ]. split.
  - unfold Int.sub. rewrite Int.unsigned_repr by lia.
    rewrite Int.unsigned_one. reflexivity.
  - apply Int.eq_false. apply Nonzero. lia.
Qed.

Definition V293_tick_countdown_node bt base d next : asrt :=
  V293_owned_record_cell ((bt,(base+44)%Z),Tint32,Vint32 (Int.repr d)) **
  V293_owned_record_cell ((bt,(base+20)%Z),Tcom_ptr 410%Z,Vptr next).

(* Exchange two separated cells without dropping any fragment. *)
Local Lemma V293_tick_exchange : forall A B R s,
  s |= A ** (B ** R) -> s |= B ** (A ** R).
Proof.
  intros A B R s H. apply astar_assoc_elim.
  eapply astar_mono; [apply astar_comm | | apply astar_assoc_intro; exact H].
  intros st Held; exact Held.
Qed.

Lemma V293_tick_delay_address : forall ge le M ptcb bc bt base,
  get le ptcb = Some (bc,Tptr V293_tcb_type) ->
  load (Tptr V293_tcb_type) M (bc,0%Z) = Some (Vptr (bt,Int.repr base)) ->
  (0 <= base)%Z -> (base+44 <= Int.max_unsigned)%Z ->
  evaladdr (V293_tick_field ptcb 13%Z) (ge,le,M) =
    Some (Vptr (bt,Int.repr (base+44))).
Proof.
  intros ge le M ptcb bc bt base Bind Pointer Base Limit.
  assert (Td : evaltype (ederef (evar ptcb)) (ge,le,M) = Some V293_tcb_type).
  { cbn [evaltype get_lenv get_genv]. rewrite Bind. reflexivity. }
  unfold V293_tick_field. cbn [evaladdr evalval evaltype get_lenv get_genv get_mem].
  rewrite Bind. cbn beta iota. rewrite Pointer. unfold getoff. rewrite Td.
  cbn [V293_tcb_type field_offset]. rewrite Int.repr_unsigned. unfold Int.add.
  rewrite !Int.unsigned_repr by lia. reflexivity.
Qed.

(* Only the standard assignment transition; address/value are proved at the
   call site from the actual field and subtraction, not postulated oracles. *)
Lemma V293_tick_assign32_execution : forall P ks ge le M M' lhs rhs b off value,
  evaltype lhs (ge,le,M) = Some Tint32 ->
  evaltype rhs (ge,le,M) = Some Tint32 ->
  evaladdr lhs (ge,le,M) = Some (Vptr (b,Int.repr off)) ->
  evalval rhs (ge,le,M) = Some value ->
  (0 <= off <= Int.max_unsigned)%Z ->
  store Tint32 M (b,off) value = Some M' ->
  cstepstar P (curs (sassign lhs rhs),(kenil,ks)) (ge,le,M)
    (curs (sskip None),(kenil,ks)) (ge,le,M').
Proof.
  intros P ks ge le M M' lhs rhs b off value Tl Tr Addr Value Range Store.
  eapply c_stepstarn.
  { eapply stmt_step; [reflexivity | ]. eapply sassign_step; [exact Tl | exact Tr | ].
    apply eq_int. auto. }
  eapply V293_cstepstar_trans.
  { apply V293_expr_steps. apply evalval_imply_estepstar. exact Value. }
  eapply c_stepstarn. { eapply stmt_step; [reflexivity | constructor]. }
  eapply V293_cstepstar_trans.
  { apply V293_expr_steps. apply evalval_imply_estepstar.
    eapply evaladdr_val_eq; eassumption. }
  eapply c_stepstarn.
  { eapply stmt_step; [reflexivity | ]. eapply sassignend_step; try reflexivity.
    cbn [addrval_to_addr]. rewrite Int.unsigned_repr by exact Range. exact Store. }
  apply c_stepstar0.
Qed.

Theorem V293_tick_countdown_iteration_owned_execution :
  forall P ks ge le M ir enabled si ci O op ptcb rows group bc bt base d next R,
  get le ptcb = Some (bc,Tptr V293_tcb_type) ->
  (0 <= base)%Z -> (base+44 <= Int.max_unsigned)%Z ->
  (2 <= d <= Int.max_unsigned)%Z ->
  (ge,le,M,ir,(enabled,si,ci),O,op) |=
    V293_owned_record_cell ((bc,0%Z),Tptr V293_tcb_type,Vptr (bt,Int.repr base)) **
    (V293_tick_countdown_node bt base d next ** R) ->
  exists M1 Mf,
  store Tint32 M (bt,(base+44)%Z) (Vint32 (Int.repr (d-1))) = Some M1 /\
  store (Tptr V293_tcb_type) M1 (bc,0%Z) (Vptr next) = Some Mf /\
  V293_local_steps P (curs (V293_tick_iteration ptcb rows group),(kenil,ks))
    ((ge,le,M),ir,(enabled,si,ci))
    (curs (sskip None),(kenil,ks)) ((ge,le,Mf),ir,(enabled,si,ci)) /\
  load Tint32 Mf (bt,(base+44)%Z) = Some (Vint32 (Int.repr (d-1))) /\
  load (Tptr V293_tcb_type) Mf (bc,0%Z) = Some (Vptr next) /\
  (ge,le,Mf,ir,(enabled,si,ci),O,op) |=
    V293_owned_record_cell ((bc,0%Z),Tptr V293_tcb_type,Vptr next) **
    (V293_tick_countdown_node bt base (d-1)%Z next ** R) /\
  (forall c i,
    (c <> bc \/ (i < 0)%Z \/ (4 <= i)%Z) ->
    (c <> bt \/ (i < base+44)%Z \/ (base+48 <= i)%Z) ->
    get Mf (c,i) = get M (c,i)).
Proof.
  intros P ks ge le M ir enabled si ci O op ptcb rows group bc bt base d next R
    Bind Base Limit Range Owned.
  destruct (V293_tick_countdown_arithmetic d Range) as [InitialNE [Subtract LaterNE]].
  assert (Pointer : load (Tptr V293_tcb_type) M (bc,0%Z) = Some (Vptr (bt,Int.repr base))).
  { change (load (Tptr V293_tcb_type) (getmem (ge,le,M,ir,(enabled,si,ci),O,op)) (bc,0%Z) = Some (Vptr (bt,Int.repr base))).
    eapply V293_record_star_load_l; [apply V293_owned_record_cell_load | exact Owned]. }
  assert (Dly : load Tint32 M (bt,(base+44)%Z) = Some (Vint32 (Int.repr d))).
  { change (load Tint32 (getmem (ge,le,M,ir,(enabled,si,ci),O,op)) (bt,(base+44)%Z) = Some (Vint32 (Int.repr d))).
    eapply V293_record_star_load_r; [ | exact Owned].
    eapply V293_record_star_load_l. unfold V293_tick_countdown_node.
    eapply V293_record_star_load_l. apply V293_owned_record_cell_load. }
  destruct (V293_tick_field_eval ge le M ptcb bc bt base 13%Z 44%Z Tint32 _
    Bind Pointer eq_refl eq_refl Base ltac:(lia) Limit Dly) as [Dt Dv].
  assert (Test : evalval (V293_tick_ne (V293_tick_field ptcb 13%Z) 0) (ge,le,M) =
      Some (Vint32 Int.one)).
  { unfold V293_tick_ne,V293_tick_eq. cbn [evalval evaltype]. rewrite Dt,Dv.
    change (match (if Int.eq (Int.repr d) Int.zero then Some (Vint32 Int.one) else Some (Vint32 Int.zero)) with Some v => notint v | None => None end = Some (Vint32 Int.one)).
    rewrite InitialNE. reflexivity. }
  assert (First : (ge,le,M,ir,(enabled,si,ci),O,op) |=
    V293_owned_record_cell ((bt,(base+44)%Z),Tint32,Vint32 (Int.repr d)) **
    (V293_owned_record_cell ((bc,0%Z),Tptr V293_tcb_type,Vptr (bt,Int.repr base)) **
      (V293_owned_record_cell ((bt,(base+20)%Z),Tcom_ptr 410%Z,Vptr next) ** R))).
  { apply V293_tick_exchange. eapply astar_mono; [ | | exact Owned].
    - intros st H; exact H.
    - intros st H. unfold V293_tick_countdown_node in H. apply astar_assoc_elim. exact H. }
  destruct (V293_owned_record_cell_update (bt,(base+44)%Z) Tint32 _
    (Vint32 (Int.repr (d-1))) _ _ _ _ _ _ _ _ eq_refl First) as (M1 & S1 & Changed).
  pose proof (V293_tick_exchange _ _ _ _ Changed) as Mid.
  assert (Pointer1 : load (Tptr V293_tcb_type) M1 (bc,0%Z) = Some (Vptr (bt,Int.repr base))).
  { change (load (Tptr V293_tcb_type) (getmem (ge,le,M1,ir,(enabled,si,ci),O,op)) (bc,0%Z) = Some (Vptr (bt,Int.repr base))).
    eapply V293_record_star_load_l; [apply V293_owned_record_cell_load | exact Mid]. }
  assert (Dly1 : load Tint32 M1 (bt,(base+44)%Z) = Some (Vint32 (Int.repr (d-1)))).
  { change (load Tint32 (getmem (ge,le,M1,ir,(enabled,si,ci),O,op)) (bt,(base+44)%Z) = Some (Vint32 (Int.repr (d-1)))).
    eapply V293_record_star_load_l; [apply V293_owned_record_cell_load | exact Changed]. }
  assert (Next1 : load (Tcom_ptr 410%Z) M1 (bt,(base+20)%Z) = Some (Vptr next)).
  { change (load (Tcom_ptr 410%Z) (getmem (ge,le,M1,ir,(enabled,si,ci),O,op)) (bt,(base+20)%Z) = Some (Vptr next)).
    eapply V293_record_star_load_r; [ | exact Mid].
    eapply V293_record_star_load_r. eapply V293_record_star_load_l.
    apply V293_owned_record_cell_load. }
  destruct (V293_tick_field_eval ge le M1 ptcb bc bt base 13%Z 44%Z Tint32 _
    Bind Pointer1 eq_refl eq_refl Base ltac:(lia) Limit Dly1) as [Dt1 Dv1].
  assert (LaterTest : evalval (V293_tick_eq (V293_tick_field ptcb 13%Z) 0) (ge,le,M1) =
      Some (Vint32 Int.zero)).
  { unfold V293_tick_eq. cbn [evalval evaltype]. rewrite Dt1,Dv1.
    change ((if Int.eq (Int.repr (d-1)) Int.zero then Some (Vint32 Int.one) else Some (Vint32 Int.zero)) = Some (Vint32 Int.zero)).
    rewrite LaterNE. reflexivity. }
  assert (Decrement : forall tail, cstepstar P
    (curs (sassign (V293_tick_field ptcb 13%Z)
      (ebinop ominus (V293_tick_field ptcb 13%Z) (econst32 Int.one))),(kenil,tail))
    (ge,le,M) (curs (sskip None),(kenil,tail)) (ge,le,M1)).
  { intro tail. eapply V293_tick_assign32_execution with (off:=(base+44)%Z);
      try eassumption.
    - cbn [evaltype]. rewrite Dt. reflexivity.
    - eapply V293_tick_delay_address; eassumption.
    - cbn [evalval evaltype]. rewrite Dt,Dv. cbn [bop_eval sub]. rewrite Subtract. reflexivity.
    - lia. }
  assert (Middle : (ge,le,M1,ir,(enabled,si,ci),O,op) |=
    V293_owned_record_cell ((bc,0%Z),Tptr V293_tcb_type,Vptr (bt,Int.repr base)) **
    (V293_tick_countdown_node bt base (d-1)%Z next ** R)).
  { eapply astar_mono; [ | | exact Mid].
    - intros st H; exact H.
    - intros st H. unfold V293_tick_countdown_node. apply astar_assoc_intro. exact H. }
  destruct (V293_owned_record_cell_update (bc,0%Z) (Tptr V293_tcb_type) _
    (Vptr next) _ _ _ _ _ _ _ _ eq_refl Middle) as (Mf & S2 & Returned).
  destruct (V293_tick_field_eval ge le M1 ptcb bc bt base 7%Z 20%Z (Tcom_ptr 410%Z) _
    Bind Pointer1 eq_refl eq_refl Base ltac:(lia) ltac:(lia) Next1) as [Nt Nv].
  assert (Advance : forall tail, cstepstar P
    (curs (V293_tick_advance ptcb),(kenil,tail)) (ge,le,M1)
    (curs (sskip None),(kenil,tail)) (ge,le,Mf)).
  { intro tail. unfold V293_tick_advance.
    eapply V293_assign_pointer_execution with (tr:=Tcom_ptr 410%Z) (off:=0%Z);
      try eassumption.
    - cbn [evaltype]. rewrite Bind. reflexivity.
    - apply eq_vcomptr. split; left; eauto.
    - cbn [evaladdr get_lenv get_genv]. rewrite Bind. reflexivity.
    - change (0 <= 0 <= 4294967295)%Z. lia. }
  exists M1. exists Mf. split; [exact S1 | ]. split; [exact S2 | ]. split.
  - unfold V293_tick_iteration.
    eapply V293_local_cons. { apply ostc_step. eapply stmt_step; [reflexivity|apply sseq_step]. }
    eapply V293_local_cons. { apply encrit_step;reflexivity. }
    eapply V293_local_cons. { apply ostc_step. eapply stmt_step; [reflexivity|apply sskip_step]. }
    eapply V293_local_cons. { apply ostc_step. eapply stmt_step; [reflexivity|apply sseq_step]. }
    unfold V293_tick_delay at 1.
    eapply V293_local_cons. { apply ostc_step. eapply stmt_step; [reflexivity|apply sifthen_step]. }
    eapply V293_local_trans.
    { apply V293_csteps_local. apply V293_expr_steps. apply evalval_imply_estepstar. exact Test. }
    eapply V293_local_cons. { apply ostc_step. eapply stmt_step; [reflexivity|apply svift_step;reflexivity]. }
    eapply V293_local_cons. { apply ostc_step. eapply stmt_step; [reflexivity|apply sseq_step]. }
    eapply V293_local_trans. { apply V293_csteps_local. apply Decrement. }
    eapply V293_local_cons. { apply ostc_step. eapply stmt_step; [reflexivity|apply sskip_step]. }
    eapply V293_local_cons. { apply ostc_step. eapply stmt_step; [reflexivity|apply sifthen_step]. }
    eapply V293_local_trans.
    { apply V293_csteps_local. apply V293_expr_steps. apply evalval_imply_estepstar. exact LaterTest. }
    eapply V293_local_cons. { apply ostc_step. eapply stmt_step; [reflexivity|apply sviff_step;reflexivity]. }
    eapply V293_local_cons. { apply ostc_step. eapply stmt_step; [reflexivity|apply sskip_step]. }
    eapply V293_local_cons. { apply ostc_step. eapply stmt_step; [reflexivity|apply sseq_step]. }
    eapply V293_local_trans. { apply V293_csteps_local. apply Advance. }
    eapply V293_local_cons. { apply ostc_step. eapply stmt_step; [reflexivity|apply sskip_step]. }
    eapply V293_local_cons. { apply excrit_step;reflexivity. }
    apply V293_local_refl.
  - split.
    + change (load Tint32 (getmem (ge,le,Mf,ir,(enabled,si,ci),O,op)) (bt,(base+44)%Z) = Some (Vint32 (Int.repr (d-1)))).
      eapply V293_record_star_load_r; [ | exact Returned].
      eapply V293_record_star_load_l. unfold V293_tick_countdown_node.
      eapply V293_record_star_load_l. apply V293_owned_record_cell_load.
    + split; [eapply V293_store_readback; [reflexivity | exact S2] | ].
      split; [exact Returned | ]. intros c i LocalOutside DelayOutside.
      transitivity (get M1 (c,i)); eapply V293_storebytes_outside;
        [exact S2 | rewrite encode_val_length; exact LocalOutside |
         exact S1 | rewrite encode_val_length; cbn [typelen]; intuition lia].
Qed.

Print Assumptions V293_tick_countdown_arithmetic.
Print Assumptions V293_tick_countdown_iteration_owned_execution.
