(* Fixed OSTimeTick os_core.c:986-1005, Dly=1. The unchanged executable
   iteration is used, including the post-store reads and conditional bitmaps.
   This is not a function Hoare theorem, initialized Inv, or GOOD_OS. *)
Require Import CertiOS.certiucos.v293.code.V293OSTimeTick.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickTraversal.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickCountdown.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewExec.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.cstepLib.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Definition V293_tick_waiting s := negb (Nat.eqb (Nat.land s 55) 0).
Definition V293_tick_expired_stat s :=
  if V293_tick_waiting s then Nat.land s 200 else s.
Definition V293_tick_expired_pend s := if V293_tick_waiting s then 1 else 0.
Definition V293_tick_wakes s := Nat.eqb (Nat.land (V293_tick_expired_stat s) 8) 0.
Definition V293_tick_expired_group s g y :=
  if V293_tick_wakes s then Nat.setbit g y else g.
Definition V293_tick_expired_row s r x :=
  if V293_tick_wakes s then Nat.setbit r x else r.

(* Only the finite BYTE arithmetic is computed. Actual statement execution
   below is proved by the operational semantics, not an arithmetic oracle. *)
Lemma V293_tick_status_arithmetic : forall s,
  s < 256 ->
  Int.eq (Int.and (Int.repr (Z.of_nat s)) (Int.repr 55)) Int.zero =
    Nat.eqb (Nat.land s 55) 0 /\
  Int.eq (Int.and (Int.repr (Z.of_nat s)) (Int.repr 8)) Int.zero =
    Nat.eqb (Nat.land s 8) 0 /\
  Int.modu (Int.and (Int.repr (Z.of_nat s))
    (Int.modu (Int.not (Int.repr 55)) (Int.repr 256))) (Int.repr 256) =
    Int.repr (Z.of_nat (Nat.land s 200)) /\
  Nat.land s 200 < 256.
Proof.
  intros s Bound.
  do 256 (destruct s as [ | s]; [vm_compute; repeat split; try reflexivity; lia | ]).
  lia.
Qed.

Lemma V293_tick_pending_test_eval : forall ge le M stat s,
  s < 256 -> evaltype stat (ge,le,M) = Some Tint8 ->
  evalval stat (ge,le,M) = Some (V293_byteval s) ->
  evalval (V293_tick_ne (ebinop obitand (ecast stat Tint32) (econst32 (Int.repr 55))) 0)
    (ge,le,M) = Some (Vint32 (if V293_tick_waiting s then Int.one else Int.zero)).
Proof.
  intros ge le M stat s Bound T V.
  pose proof (proj1 (V293_tick_status_arithmetic s Bound)) as A.
  unfold V293_tick_ne,V293_tick_eq.
  cbn [evalval evaltype]. rewrite T,V.
  change (match (if Int.eq (Int.and (Int.repr (Z.of_nat s)) (Int.repr 55)) Int.zero
    then Some (Vint32 Int.one) else Some (Vint32 Int.zero)) with
    | Some v => notint v | None => None end =
    Some (Vint32 (if V293_tick_waiting s then Int.one else Int.zero))).
  rewrite A. unfold V293_tick_waiting. destruct (Nat.eqb (Nat.land s 55) 0); reflexivity.
Qed.

Lemma V293_tick_suspend_test_eval : forall ge le M stat s,
  s < 256 -> evaltype stat (ge,le,M) = Some Tint8 ->
  evalval stat (ge,le,M) = Some (V293_byteval s) ->
  evalval (V293_tick_eq (ebinop obitand (ecast stat Tint32) (econst32 (Int.repr 8))) 0)
    (ge,le,M) = Some (Vint32 (if Nat.eqb (Nat.land s 8) 0 then Int.one else Int.zero)).
Proof.
  intros ge le M stat s Bound T V.
  pose proof (proj1 (proj2 (V293_tick_status_arithmetic s Bound))) as A.
  unfold V293_tick_eq. cbn [evalval evaltype]. rewrite T,V.
  change ((if Int.eq (Int.and (Int.repr (Z.of_nat s)) (Int.repr 8)) Int.zero
    then Some (Vint32 Int.one) else Some (Vint32 Int.zero)) =
    Some (Vint32 (if Nat.eqb (Nat.land s 8) 0 then Int.one else Int.zero))).
  rewrite A. destruct (Nat.eqb (Nat.land s 8) 0); reflexivity.
Qed.

Lemma V293_tick_clear_status_eval : forall ge le M stat s,
  s < 256 -> evaltype stat (ge,le,M) = Some Tint8 ->
  evalval stat (ge,le,M) = Some (V293_byteval s) ->
  evaltype (V293_task_prio_clear_expr stat (econst32 (Int.repr 55))) (ge,le,M) = Some Tint8 /\
  evalval (V293_task_prio_clear_expr stat (econst32 (Int.repr 55))) (ge,le,M) =
    Some (V293_byteval (Nat.land s 200)).
Proof.
  intros ge le M stat s Bound T V.
  pose proof (proj1 (proj2 (proj2 (V293_tick_status_arithmetic s Bound)))) as A.
  unfold V293_task_prio_clear_expr. cbn [evalval evaltype]. rewrite T,V.
  split; [reflexivity | ].
  change (Some (Vint32 (Int.modu (Int.and (Int.repr (Z.of_nat s))
    (Int.modu (Int.not (Int.repr 55)) (Int.repr 256))) (Int.repr 256))) =
    Some (V293_byteval (Nat.land s 200))).
  rewrite A. reflexivity.
Qed.

(* Select an actual owned cell using the standard list index. Prefix, suffix
   and arbitrary R are returned by the same store. This is also used for the
   32-bit delay and local pointer; a raw load never creates write permission. *)
Lemma V293_tick_cells_store_at : forall cells n a tp old replacement R ge le M ir aux O op,
  (ge,le,M,ir,aux,O,op) |= V293_owned_record_cells cells ** R ->
  nth_error cells n = Some (a,tp,old) ->
  rule_type_val_match tp replacement = true ->
  exists Mf, store tp M a replacement = Some Mf /\
  (ge,le,Mf,ir,aux,O,op) |= V293_owned_record_cells
    (firstn n cells ++ (a,tp,replacement) :: skipn (S n) cells) ** R.
Proof.
  induction cells as [ | head rest IH]; intros n a tp old replacement R ge le M ir aux O op Owned At Valid;
    destruct n; cbn [nth_error] in At; try discriminate.
  - inversion At; subst head. cbn [firstn skipn app V293_owned_record_cells] in Owned |- *.
    apply astar_assoc_elim in Owned.
    destruct (V293_owned_record_cell_update _ _ _ _ _ _ _ _ _ _ _ _ Valid Owned)
      as (Mf & Store & Updated).
    exists Mf. split; [exact Store | apply astar_assoc_intro; exact Updated].
  - cbn [firstn skipn app V293_owned_record_cells] in Owned |- *.
    apply astar_assoc_elim in Owned. apply astar_comm in Owned. apply astar_assoc_elim in Owned.
    destruct (IH _ _ _ _ _ _ _ _ _ _ _ _ _ Owned At Valid) as (Mf & Store & Updated).
    exists Mf. split; [exact Store | ].
    apply astar_assoc_intro in Updated. apply astar_comm in Updated.
    apply astar_assoc_intro. exact Updated.
Qed.

(* Only bytes read/written by this iteration are selected. It is not a full
   TCB or the task/event invariant. The unselected ready row belongs to R. *)
Definition V293_tick_expiry_cells bc bt base pointer delay next stat pend y x bg g br r
    : list V293_record_cell :=
  [((bc,0%Z),Tptr V293_tcb_type,Vptr pointer);
   ((bt,(base+44)%Z),Tint32,Vint32 delay);
   ((bt,(base+20)%Z),Tcom_ptr 410%Z,Vptr next);
   ((bt,(base+48)%Z),Tint8,V293_byteval stat);
   ((bt,(base+49)%Z),Tint8,V293_byteval pend);
   ((bt,(base+52)%Z),Tint8,V293_byteval y);
   ((bt,(base+54)%Z),Tint8,V293_byteval (2^y));
   ((bt,(base+53)%Z),Tint8,V293_byteval (2^x));
   ((bg,0%Z),Tint8,V293_byteval g);
   ((br,Z.of_nat y),Tint8,V293_byteval r)].

Lemma V293_tick_expiry_cell_load : forall bc bt base pointer delay next stat pend y x bg g br r R
    ge le M ir aux O op a tp v,
  In (a,tp,v) (V293_tick_expiry_cells bc bt base pointer delay next stat pend y x bg g br r) ->
  (ge,le,M,ir,aux,O,op) |= V293_owned_record_cells
    (V293_tick_expiry_cells bc bt base pointer delay next stat pend y x bg g br r) ** R ->
  load tp M a = Some v.
Proof.
  intros bc bt base pointer delay next stat pend y x bg g br r R ge le M ir aux O op a tp v Member Owned.
  change (load tp (getmem (ge,le,M,ir,aux,O,op)) a = Some v).
  eapply V293_record_star_load_l; [apply V293_owned_record_cells_load; exact Member | exact Owned].
Qed.

Local Ltac expiry_load H :=
  eapply V293_tick_expiry_cell_load; [ | exact H]; unfold V293_tick_expiry_cells; simpl; tauto.


Local Lemma V293_tick_if_else_execution : forall P ks ge le M Mf cond yes no (flag : bool),
  evalval cond (ge,le,M) = Some (Vint32 (if flag then Int.one else Int.zero)) ->
  cstepstar P (curs (if flag then yes else no),(kenil,ks)) (ge,le,M)
    (curs (sskip None),(kenil,ks)) (ge,le,Mf) ->
  cstepstar P (curs (sif cond yes no),(kenil,ks)) (ge,le,M)
    (curs (sskip None),(kenil,ks)) (ge,le,Mf).
Proof.
  intros P ks ge le M Mf cond yes no flag Value Branch.
  eapply c_stepstarn. { eapply stmt_step; [reflexivity | apply sif_step]. }
  eapply V293_cstepstar_trans.
  { apply V293_expr_steps. apply evalval_imply_estepstar. exact Value. }
  destruct flag.
  - eapply c_stepstarn. { eapply stmt_step; [reflexivity | apply svift_step; reflexivity]. } exact Branch.
  - eapply c_stepstarn. { eapply stmt_step; [reflexivity | apply sviff_step; reflexivity]. } exact Branch.
Qed.

Lemma V293_tick_owned_field_eval : forall bc bt base delay next stat pend y x bg g br r R
    ge le M ir aux O op ptcb field delta tp v,
  get le ptcb = Some (bc,Tptr V293_tcb_type) ->
  (0 <= base)%Z -> (0 <= delta)%Z -> (base+delta <= Int.max_unsigned)%Z ->
  ftype field V293_tcb_fields = Some tp ->
  field_offset field V293_tcb_fields = Some (Int.repr delta) ->
  In ((bt,(base+delta)%Z),tp,v)
    (V293_tick_expiry_cells bc bt base (bt,Int.repr base) delay next stat pend y x bg g br r) ->
  (ge,le,M,ir,aux,O,op) |= V293_owned_record_cells
    (V293_tick_expiry_cells bc bt base (bt,Int.repr base) delay next stat pend y x bg g br r) ** R ->
  evaltype (V293_tick_field ptcb field) (ge,le,M) = Some tp /\
  evalval (V293_tick_field ptcb field) (ge,le,M) = Some v.
Proof.
  intros bc bt base delay next stat pend y x bg g br r R ge le M ir aux O op
    ptcb field delta tp v Bind Base Delta Limit Ft Fo Member Owned.
  eapply V293_tick_field_eval with (bc:=bc) (bt:=bt) (base:=base) (delta:=delta);
    [exact Bind | | exact Ft | exact Fo | exact Base | exact Delta | exact Limit | ].
  - expiry_load Owned.
  - eapply V293_tick_expiry_cell_load; [exact Member | exact Owned].
Qed.

Local Ltac expiry_eval H offset bind lower :=
  eapply V293_tick_owned_field_eval with (delta:=offset);
    [exact bind | exact lower | lia | lia | reflexivity | reflexivity | | exact H];
  unfold V293_tick_expiry_cells; simpl; tauto.

(* This helper handles the actual expiry statements, at any delay value.
   The outer stable theorem below supplies the actual Dly=1 decrement. *)
Lemma V293_tick_expiry_owned_execution :
  forall P ge le M ir aux O op ptcb rows group bc bt base delay next s pend y x bg g br r R,
  get le ptcb = Some (bc,Tptr V293_tcb_type) ->
  get le rows = None -> get ge rows = Some (br,Tarray Tint8 2) ->
  get le group = None -> get ge group = Some (bg,Tint8) ->
  (0 <= base)%Z -> (base+54 <= Int.max_unsigned)%Z ->
  s < 256 -> pend < 256 -> y < 2 -> x < 8 -> g < 256 -> r < 256 ->
  (ge,le,M,ir,aux,O,op) |= V293_owned_record_cells
    (V293_tick_expiry_cells bc bt base (bt,Int.repr base) delay next s pend y x bg g br r) ** R ->
  exists Mf,
  (forall ks, cstepstar P (curs (V293_tick_expiry ptcb rows group),(kenil,ks)) (ge,le,M)
    (curs (sskip None),(kenil,ks)) (ge,le,Mf)) /\
  (ge,le,Mf,ir,aux,O,op) |= V293_owned_record_cells
    (V293_tick_expiry_cells bc bt base (bt,Int.repr base) delay next
      (V293_tick_expired_stat s) (V293_tick_expired_pend s) y x bg
      (V293_tick_expired_group s g y) br (V293_tick_expired_row s r x)) ** R.
Proof.
  intros P ge le M ir aux O op ptcb rows group bc bt base delay next s pend y x bg g br r R
    Bind Nr Gr Ng Gg Base Limit S Pend Y X G Row Owned.
  destruct (V293_tick_status_arithmetic s S) as [A55 [A8 [Clear ClearBound]]].
  assert (Stat : evaltype (V293_tick_field ptcb 14%Z) (ge,le,M) = Some Tint8 /\
    evalval (V293_tick_field ptcb 14%Z) (ge,le,M) = Some (V293_byteval s)).
  { expiry_eval Owned 48%Z Bind Base. }
  destruct Stat as [St Sv].
  pose proof (V293_tick_pending_test_eval ge le M _ s S St Sv) as Test.
  assert (Pending : exists Mp,
    (forall ks, cstepstar P
      (curs (sif (V293_tick_ne (ebinop obitand (ecast (V293_tick_field ptcb 14%Z) Tint32)
        (econst32 (Int.repr 55))) 0)
        (sseq (sassign (V293_tick_field ptcb 14%Z)
            (V293_task_prio_clear_expr (V293_tick_field ptcb 14%Z) (econst32 (Int.repr 55))))
          (sassign (V293_tick_field ptcb 15%Z) (ecast (econst32 Int.one) Tint8)))
        (sassign (V293_tick_field ptcb 15%Z) (ecast (econst32 Int.zero) Tint8))),(kenil,ks))
      (ge,le,M) (curs (sskip None),(kenil,ks)) (ge,le,Mp)) /\
    (ge,le,Mp,ir,aux,O,op) |= V293_owned_record_cells
      (V293_tick_expiry_cells bc bt base (bt,Int.repr base) delay next
        (V293_tick_expired_stat s) (V293_tick_expired_pend s) y x bg g br r) ** R).
  { destruct (V293_tick_waiting s) eqn:Wait.
    - destruct (V293_tick_cells_store_at _ 3 (bt,(base+48)%Z) Tint8 _
        (V293_byteval (Nat.land s 200)) R ge le M ir aux O op Owned eq_refl
        (V293_byte_type _ ClearBound)) as (Ms & Ss & Hs).
      change ((ge,le,Ms,ir,aux,O,op) |= V293_owned_record_cells
        (V293_tick_expiry_cells bc bt base (bt,Int.repr base) delay next
          (Nat.land s 200) pend y x bg g br r) ** R) in Hs.
      destruct (V293_tick_cells_store_at _ 4 (bt,(base+49)%Z) Tint8 _
        (V293_byteval 1) R ge le Ms ir aux O op Hs eq_refl eq_refl) as (Mp & Sp & Hp).
      change ((ge,le,Mp,ir,aux,O,op) |= V293_owned_record_cells
        (V293_tick_expiry_cells bc bt base (bt,Int.repr base) delay next
          (Nat.land s 200) 1 y x bg g br r) ** R) in Hp.
      assert (Pointer : load (Tptr V293_tcb_type) M (bc,0%Z) = Some (Vptr (bt,Int.repr base))) by (expiry_load Owned).
      destruct (V293_tcb_byte_field_address ge le M ptcb bc bt base 14%Z 48%Z
        Bind Pointer eq_refl eq_refl Base ltac:(lia) ltac:(lia)) as [_ As].
      destruct (V293_tick_clear_status_eval ge le M _ s S St Sv) as [Tc Vc].
      assert (PointerS : load (Tptr V293_tcb_type) Ms (bc,0%Z) = Some (Vptr (bt,Int.repr base))) by (expiry_load Hs).
      destruct (V293_tcb_byte_field_address ge le Ms ptcb bc bt base 15%Z 49%Z
        Bind PointerS eq_refl eq_refl Base ltac:(lia) ltac:(lia)) as [Tp Ap].
      exists Mp. split.
      + intro ks. eapply V293_tick_if_else_execution with (flag:=true).
        * exact Test.
        * cbn beta iota. eapply V293_rekey_sequence_execution.
          -- intro tail. eapply V293_assign_byte_offset_execution; try eassumption; lia.
          -- eapply V293_assign_byte_offset_execution; try eassumption; try reflexivity; lia.
      + unfold V293_tick_expired_stat,V293_tick_expired_pend. rewrite Wait. exact Hp.
    - destruct (V293_tick_cells_store_at _ 4 (bt,(base+49)%Z) Tint8 _
        (V293_byteval 0) R ge le M ir aux O op Owned eq_refl eq_refl) as (Mp & Sp & Hp).
      change ((ge,le,Mp,ir,aux,O,op) |= V293_owned_record_cells
        (V293_tick_expiry_cells bc bt base (bt,Int.repr base) delay next s 0 y x bg g br r) ** R) in Hp.
      assert (Pointer : load (Tptr V293_tcb_type) M (bc,0%Z) = Some (Vptr (bt,Int.repr base))) by (expiry_load Owned).
      destruct (V293_tcb_byte_field_address ge le M ptcb bc bt base 15%Z 49%Z
        Bind Pointer eq_refl eq_refl Base ltac:(lia) ltac:(lia)) as [Tp Ap].
      exists Mp. split.
      + intro ks. eapply V293_tick_if_else_execution with (flag:=false).
        * exact Test.
        * cbn beta iota. eapply V293_assign_byte_offset_execution; try eassumption; try reflexivity; lia.
      + unfold V293_tick_expired_stat,V293_tick_expired_pend. rewrite Wait. exact Hp. }
  destruct Pending as (Mp & PendingExec & Hp).
  assert (ExpiredBound : V293_tick_expired_stat s < 256).
  { unfold V293_tick_expired_stat. destruct (V293_tick_waiting s); assumption. }
  assert (NewStat : evaltype (V293_tick_field ptcb 14%Z) (ge,le,Mp) = Some Tint8 /\
    evalval (V293_tick_field ptcb 14%Z) (ge,le,Mp) = Some (V293_byteval (V293_tick_expired_stat s))).
  { expiry_eval Hp 48%Z Bind Base. }
  destruct NewStat as [Nst Nsv].
  pose proof (V293_tick_suspend_test_eval ge le Mp _ _ ExpiredBound Nst Nsv) as SuspendTest.
  change (evalval (V293_tick_eq (ebinop obitand
    (ecast (V293_tick_field ptcb 14%Z) Tint32) (econst32 (Int.repr 8))) 0) (ge,le,Mp) =
    Some (Vint32 (if V293_tick_wakes s then Int.one else Int.zero))) in SuspendTest.
  assert (Ready : exists Mf,
    (forall ks, cstepstar P
      (curs (sifthen (V293_tick_eq (ebinop obitand
        (ecast (V293_tick_field ptcb 14%Z) Tint32) (econst32 (Int.repr 8))) 0)
        (sseq (sassign (evar group)
          (V293_task_prio_set_expr (evar group) (V293_tick_field ptcb 20%Z)))
          (sassign (earrayelem (evar rows) (V293_tick_field ptcb 18%Z))
            (V293_task_prio_set_expr (earrayelem (evar rows) (V293_tick_field ptcb 18%Z))
              (V293_tick_field ptcb 19%Z))))),(kenil,ks))
      (ge,le,Mp) (curs (sskip None),(kenil,ks)) (ge,le,Mf)) /\
    (ge,le,Mf,ir,aux,O,op) |= V293_owned_record_cells
      (V293_tick_expiry_cells bc bt base (bt,Int.repr base) delay next
        (V293_tick_expired_stat s) (V293_tick_expired_pend s) y x bg
        (V293_tick_expired_group s g y) br (V293_tick_expired_row s r x)) ** R).
  { destruct (V293_tick_wakes s) eqn:Wake.
    - destruct (V293_rekey_byte_arithmetic g y G ltac:(lia)) as [_ [GB [_ GE]]].
      destruct (V293_rekey_byte_arithmetic r x Row X) as [_ [RB [_ RE]]].
      destruct (V293_tick_cells_store_at _ 8 (bg,0%Z) Tint8 _
        (V293_byteval (Nat.setbit g y)) R ge le Mp ir aux O op Hp eq_refl
        (V293_byte_type _ GB)) as (Mg & Sg & Hg).
      change ((ge,le,Mg,ir,aux,O,op) |= V293_owned_record_cells
        (V293_tick_expiry_cells bc bt base (bt,Int.repr base) delay next
          (V293_tick_expired_stat s) (V293_tick_expired_pend s) y x bg
          (Nat.setbit g y) br r) ** R) in Hg.
      destruct (V293_tick_cells_store_at _ 9 (br,Z.of_nat y) Tint8 _
        (V293_byteval (Nat.setbit r x)) R ge le Mg ir aux O op Hg eq_refl
        (V293_byte_type _ RB)) as (Mf & Sr & Hf).
      change ((ge,le,Mf,ir,aux,O,op) |= V293_owned_record_cells
        (V293_tick_expiry_cells bc bt base (bt,Int.repr base) delay next
          (V293_tick_expired_stat s) (V293_tick_expired_pend s) y x bg
          (Nat.setbit g y) br (Nat.setbit r x)) ** R) in Hf.
      assert (By : evaltype (V293_tick_field ptcb 20%Z) (ge,le,Mp) = Some Tint8 /\
        evalval (V293_tick_field ptcb 20%Z) (ge,le,Mp) = Some (V293_byteval (2^y))).
      { expiry_eval Hp 54%Z Bind Base. }
      destruct By as [Byt Byv].
      destruct (V293_mask_byte_value y ltac:(lia)) as [_ ByEq]. rewrite ByEq in Byv.
      assert (Gt : evaltype (evar group) (ge,le,Mp) = Some Tint8).
      { cbn [evaltype get_lenv get_genv]. rewrite Ng,Gg. reflexivity. }
      assert (Ga : evaladdr (evar group) (ge,le,Mp) = Some (Vptr (bg,Int.repr 0))).
      { cbn [evaladdr get_lenv get_genv]. rewrite Ng,Gg. reflexivity. }
      assert (Gv : evalval (evar group) (ge,le,Mp) = Some (V293_byteval g)).
      { cbn [evalval evaltype get_lenv get_genv get_mem]. rewrite Ng,Gg. expiry_load Hp. }
      destruct (V293_task_prio_byte_expr_eval ge le Mp _ _ g y G ltac:(lia) Gt Byt Gv Byv)
        as [_ [Gst [_ Gsv]]].
      assert (Yi : evaltype (V293_tick_field ptcb 18%Z) (ge,le,Mg) = Some Tint8 /\
        evalval (V293_tick_field ptcb 18%Z) (ge,le,Mg) = Some (V293_byteval y)).
      { expiry_eval Hg 52%Z Bind Base. }
      destruct Yi as [Yt Yv].
      assert (Bx : evaltype (V293_tick_field ptcb 19%Z) (ge,le,Mg) = Some Tint8 /\
        evalval (V293_tick_field ptcb 19%Z) (ge,le,Mg) = Some (V293_byteval (2^x))).
      { expiry_eval Hg 53%Z Bind Base. }
      destruct Bx as [Bxt Bxv].
      destruct (V293_mask_byte_value x X) as [_ BxEq]. rewrite BxEq in Bxv.
      assert (At : evaltype (evar rows) (ge,le,Mg) = Some (Tarray Tint8 2)).
      { cbn [evaltype get_lenv get_genv]. rewrite Nr,Gr. reflexivity. }
      assert (Av : evalval (evar rows) (ge,le,Mg) = Some (Vptr (br,Int.repr 0))).
      { cbn [evalval evaltype get_lenv get_genv]. rewrite Nr,Gr. reflexivity. }
      assert (Rl : load Tint8 Mg (br,(0+Z.of_nat y)%Z) = Some (V293_byteval r)).
      { change (load Tint8 Mg (br,Z.of_nat y) = Some (V293_byteval r)). expiry_load Hg. }
      destruct (V293_byte_array_offset_eval ge le Mg _ _ br 0%Z y _ At Av Yt Yv
        ltac:(lia) ltac:(change (0+Z.of_nat y<=4294967295)%Z;lia) Y Rl) as [Rt [Ra RowValue]].
      destruct (V293_task_prio_byte_expr_eval ge le Mg _ _ r x Row X Rt Bxt RowValue Bxv)
        as [_ [Rst [_ Rsv]]].
      exists Mf. split.
      + intro ks. eapply V293_rekey_if_execution with (flag:=true).
        * exact SuspendTest.
        * intro WakeTrue. eapply V293_rekey_sequence_execution.
          -- intro tail. eapply V293_assign_byte_offset_execution; try eassumption;
              change (0<=0<=4294967295)%Z; lia.
          -- eapply V293_assign_byte_offset_execution with (off:=Z.of_nat y); try eassumption;
              change (0<=Z.of_nat y<=4294967295)%Z; lia.
        * discriminate.
      + unfold V293_tick_expired_group,V293_tick_expired_row. rewrite Wake. exact Hf.
    - exists Mp. split.
      + intro ks. eapply V293_rekey_if_execution with (flag:=false).
        * exact SuspendTest.
        * discriminate.
        * reflexivity.
      + unfold V293_tick_expired_group,V293_tick_expired_row. rewrite Wake. exact Hp. }
  destruct Ready as (Mf & ReadyExec & Returned).
  exists Mf. split; [ | exact Returned]. intro ks.
  unfold V293_tick_expiry. eapply V293_rekey_sequence_execution; [exact PendingExec | apply ReadyExec].
Qed.

Theorem V293_tick_expiry_iteration_owned_execution :
  forall P ks ge le M ir enabled si ci O op ptcb rows group bc bt base next s pend y x bg g br r R,
  get le ptcb = Some (bc,Tptr V293_tcb_type) ->
  get le rows = None -> get ge rows = Some (br,Tarray Tint8 2) ->
  get le group = None -> get ge group = Some (bg,Tint8) ->
  (0 <= base)%Z -> (base+54 <= Int.max_unsigned)%Z ->
  s < 256 -> pend < 256 -> y < 2 -> x < 8 -> g < 256 -> r < 256 ->
  (ge,le,M,ir,(enabled,si,ci),O,op) |= V293_owned_record_cells
    (V293_tick_expiry_cells bc bt base (bt,Int.repr base) Int.one next s pend y x bg g br r) ** R ->
  exists Mf,
  V293_local_steps P (curs (V293_tick_iteration ptcb rows group),(kenil,ks))
    ((ge,le,M),ir,(enabled,si,ci))
    (curs (sskip None),(kenil,ks)) ((ge,le,Mf),ir,(enabled,si,ci)) /\
  load Tint32 Mf (bt,(base+44)%Z) = Some (Vint32 Int.zero) /\
  load Tint8 Mf (bt,(base+48)%Z) = Some (V293_byteval (V293_tick_expired_stat s)) /\
  load Tint8 Mf (bt,(base+49)%Z) = Some (V293_byteval (V293_tick_expired_pend s)) /\
  load Tint8 Mf (bg,0%Z) = Some (V293_byteval (V293_tick_expired_group s g y)) /\
  load Tint8 Mf (br,Z.of_nat y) = Some (V293_byteval (V293_tick_expired_row s r x)) /\
  load (Tptr V293_tcb_type) Mf (bc,0%Z) = Some (Vptr next) /\
  (ge,le,Mf,ir,(enabled,si,ci),O,op) |= V293_owned_record_cells
    (V293_tick_expiry_cells bc bt base next Int.zero next
      (V293_tick_expired_stat s) (V293_tick_expired_pend s) y x bg
      (V293_tick_expired_group s g y) br (V293_tick_expired_row s r x)) ** R.
Proof.
  intros P ks ge le M ir enabled si ci O op ptcb rows group bc bt base next s pend y x bg g br r R
    Bind Nr Gr Ng Gg Base Limit S Pend Y X G Row Owned.
  assert (Dly : evaltype (V293_tick_field ptcb 13%Z) (ge,le,M) = Some Tint32 /\
    evalval (V293_tick_field ptcb 13%Z) (ge,le,M) = Some (Vint32 Int.one)).
  { expiry_eval Owned 44%Z Bind Base. }
  destruct Dly as [Dt Dv].
  assert (Test : evalval (V293_tick_ne (V293_tick_field ptcb 13%Z) 0) (ge,le,M) = Some (Vint32 Int.one)).
  { unfold V293_tick_ne,V293_tick_eq. cbn [evalval evaltype]. rewrite Dt,Dv. reflexivity. }
  destruct (V293_tick_cells_store_at _ 1 (bt,(base+44)%Z) Tint32 _
    (Vint32 Int.zero) R ge le M ir (enabled,si,ci) O op Owned eq_refl eq_refl) as (M1 & S1 & H1).
  change ((ge,le,M1,ir,(enabled,si,ci),O,op) |= V293_owned_record_cells
    (V293_tick_expiry_cells bc bt base (bt,Int.repr base) Int.zero next s pend y x bg g br r) ** R) in H1.
  assert (Pointer : load (Tptr V293_tcb_type) M (bc,0%Z) = Some (Vptr (bt,Int.repr base))) by (expiry_load Owned).
  assert (Decrement : forall tail, cstepstar P
    (curs (sassign (V293_tick_field ptcb 13%Z)
      (ebinop ominus (V293_tick_field ptcb 13%Z) (econst32 Int.one))),(kenil,tail))
    (ge,le,M) (curs (sskip None),(kenil,tail)) (ge,le,M1)).
  { intro tail. eapply V293_tick_assign32_execution with (off:=(base+44)%Z); try eassumption.
    - cbn [evaltype]. rewrite Dt. reflexivity.
    - eapply V293_tick_delay_address; try eassumption; lia.
    - cbn [evalval evaltype]. rewrite Dt,Dv. reflexivity.
    - lia. }
  assert (Dly1 : evaltype (V293_tick_field ptcb 13%Z) (ge,le,M1) = Some Tint32 /\
    evalval (V293_tick_field ptcb 13%Z) (ge,le,M1) = Some (Vint32 Int.zero)).
  { expiry_eval H1 44%Z Bind Base. }
  destruct Dly1 as [Dt1 Dv1].
  assert (LaterTest : evalval (V293_tick_eq (V293_tick_field ptcb 13%Z) 0) (ge,le,M1) = Some (Vint32 Int.one)).
  { unfold V293_tick_eq. cbn [evalval evaltype]. rewrite Dt1,Dv1. reflexivity. }
  destruct (V293_tick_expiry_owned_execution P ge le M1 ir (enabled,si,ci) O op ptcb rows group
    bc bt base Int.zero next s pend y x bg g br r R
    Bind Nr Gr Ng Gg Base Limit S Pend Y X G Row H1) as (Mc & ExpiryExec & Hc).
  assert (PointerC : load (Tptr V293_tcb_type) Mc (bc,0%Z) = Some (Vptr (bt,Int.repr base))) by (expiry_load Hc).
  assert (NextC : evaltype (V293_tick_field ptcb 7%Z) (ge,le,Mc) = Some (Tcom_ptr 410%Z) /\
    evalval (V293_tick_field ptcb 7%Z) (ge,le,Mc) = Some (Vptr next)).
  { expiry_eval Hc 20%Z Bind Base. }
  destruct NextC as [Nt Nv].
  destruct (V293_tick_cells_store_at _ 0 (bc,0%Z) (Tptr V293_tcb_type) _
    (Vptr next) R ge le Mc ir (enabled,si,ci) O op Hc eq_refl eq_refl) as (Mf & Sf & Returned).
  change ((ge,le,Mf,ir,(enabled,si,ci),O,op) |= V293_owned_record_cells
    (V293_tick_expiry_cells bc bt base next Int.zero next
      (V293_tick_expired_stat s) (V293_tick_expired_pend s) y x bg
      (V293_tick_expired_group s g y) br (V293_tick_expired_row s r x)) ** R) in Returned.
  assert (Advance : forall tail, cstepstar P
    (curs (V293_tick_advance ptcb),(kenil,tail)) (ge,le,Mc)
    (curs (sskip None),(kenil,tail)) (ge,le,Mf)).
  { intro tail. unfold V293_tick_advance.
    eapply V293_assign_pointer_execution with (tr:=Tcom_ptr 410%Z) (off:=0%Z); try eassumption.
    - cbn [evaltype]. rewrite Bind. reflexivity.
    - apply eq_vcomptr. split; left; eauto.
    - cbn [evaladdr get_lenv get_genv]. rewrite Bind. reflexivity.
    - change (0<=0<=4294967295)%Z. lia. }
  exists Mf. split.
  - unfold V293_tick_iteration.
    eapply V293_local_cons. { apply ostc_step. eapply stmt_step; [reflexivity | apply sseq_step]. }
    eapply V293_local_cons. { apply encrit_step; reflexivity. }
    eapply V293_local_cons. { apply ostc_step. eapply stmt_step; [reflexivity | apply sskip_step]. }
    eapply V293_local_cons. { apply ostc_step. eapply stmt_step; [reflexivity | apply sseq_step]. }
    unfold V293_tick_delay at 1.
    eapply V293_local_cons. { apply ostc_step. eapply stmt_step; [reflexivity | apply sifthen_step]. }
    eapply V293_local_trans.
    { apply V293_csteps_local. apply V293_expr_steps. apply evalval_imply_estepstar. exact Test. }
    eapply V293_local_cons. { apply ostc_step. eapply stmt_step; [reflexivity | apply svift_step; reflexivity]. }
    eapply V293_local_cons. { apply ostc_step. eapply stmt_step; [reflexivity | apply sseq_step]. }
    eapply V293_local_trans. { apply V293_csteps_local. apply Decrement. }
    eapply V293_local_cons. { apply ostc_step. eapply stmt_step; [reflexivity | apply sskip_step]. }
    eapply V293_local_cons. { apply ostc_step. eapply stmt_step; [reflexivity | apply sifthen_step]. }
    eapply V293_local_trans.
    { apply V293_csteps_local. apply V293_expr_steps. apply evalval_imply_estepstar. exact LaterTest. }
    eapply V293_local_cons. { apply ostc_step. eapply stmt_step; [reflexivity | apply svift_step; reflexivity]. }
    eapply V293_local_trans. { apply V293_csteps_local. apply ExpiryExec. }
    eapply V293_local_cons. { apply ostc_step. eapply stmt_step; [reflexivity | apply sskip_step]. }
    eapply V293_local_cons. { apply ostc_step. eapply stmt_step; [reflexivity | apply sseq_step]. }
    eapply V293_local_trans. { apply V293_csteps_local. apply Advance. }
    eapply V293_local_cons. { apply ostc_step. eapply stmt_step; [reflexivity | apply sskip_step]. }
    eapply V293_local_cons. { apply excrit_step; reflexivity. }
    apply V293_local_refl.
  - split; [expiry_load Returned | ]. split; [expiry_load Returned | ].
    split; [expiry_load Returned | ]. split; [expiry_load Returned | ].
    split; [expiry_load Returned | ]. split; [expiry_load Returned | exact Returned].
Qed.

Print Assumptions V293_tick_status_arithmetic.
Print Assumptions V293_tick_expiry_owned_execution.
Print Assumptions V293_tick_expiry_iteration_owned_execution.
